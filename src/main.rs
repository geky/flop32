#![allow(dead_code)]


mod sha256;
use sha256::Sha256;


const BLOCK_SIZE: usize = 8;

/// compute parity
/// p = Σ a[i] + Σ a[i]
fn mkparity<A: AsRef<[u8]>, B: AsRef<[u8]>>(
    a: &[A],
    b: &[B],
    p: &mut [u8],
) {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(p.len(), BLOCK_SIZE);

    p.fill(0);
    for i in 0..a.len() {
        for j in 0..BLOCK_SIZE {
            p[j] ^= a[i].as_ref()[j] ^ b[i].as_ref()[j];
        }
    }
}

/// hash a block
/// h = H(index | block)
fn hash(i: usize, a: &[u8]) -> Sha256 {
    [
        u32::try_from(i).unwrap()
            .to_le_bytes()
            .as_ref(),
        a
    ].into_iter().collect()
}

/// find parity hashes
/// p = Σ a[i] + Σ a[i]
/// q = Σ a[i] g^2i + Σ b[i] g^(2i+1)
fn mkhash<A: AsRef<[u8]>, B: AsRef<[u8]>>(
    a: &[A],
    b: &[B],
) -> (Sha256, Sha256) {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());

    let mut p = Sha256::ZERO;
    let mut q = Sha256::ZERO;
    let mut g0 = Sha256::ONE;
    let mut g1 = g0 * Sha256::G;
    for i in 0..a.len() {
        let a_hash = hash(i, a[i].as_ref());
        let b_hash = hash(i, b[i].as_ref());
        p += a_hash + b_hash;
        q += a_hash*g0 + b_hash*g1;
        g0 = g1 * Sha256::G;
        g1 = g0 * Sha256::G;
    }

    (p, q)
}

#[derive(Debug, Clone)]
enum Error {
    CorruptA(usize),
    CorruptB(usize),
    CorruptSwapA(usize),
    CorruptSwapB(usize),
    CleanSwap(usize),
    CorruptParity,
}

/// Find where we left off a swap, along with any single block error,
/// or a single block error at rest
///
/// at some point this must be true
///
///   a[x] = p - Σ a[i] + Σ b[i]
///              i!=x
///
///   a[x] g^2x = q - Σ a[i] g^(2i+1) + Σ a[i] g^2i + Σ b[i] g^2i + Σ b[i] g^(2i+1)
///                   i<x               i>x           i<x           i>=x
///
///   (a = bbbb?aaaaa)
///   (b = aaaabbbbbb)
///
/// or
///
///   b[x] = p - Σ a[i] + Σ b[i]
///                       i!=x
///
///   b[x] g^2x = q - Σ a[i] g^(2i+1) + Σ a[i] g^2i + Σ b[i] g^2i + Σ b[i] g^(2i+1)
///                   i<=x              i>x           i<x           i>x
///
///   (a = bbbbbaaaaa)
///   (b = aaaa?bbbbb)
///
///
fn find_error<A: AsRef<[u8]>, B: AsRef<[u8]>>(
    a: &[A],
    b: &[B],
    h: (Sha256, Sha256),
) -> Option<Error> {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());
    let (p, q) = h;

    // first thing first, do we have any errors?
    let (mut p_, mut q_) = mkhash(&a, &b);
    if p_ == p && q_ == q {
        return None;
    }

    // subtract from p and q
    p_ = p - p_;
    q_ = q - q_;
    let mut q_swapped = q_;

    // scan again trying to find the point where we left off the swap
    let mut g0 = Sha256::ONE;
    let mut g1 = g0 * Sha256::G;
    for i in 0..a.len() {
        let a_hash = hash(i, a[i].as_ref());
        let b_hash = hash(i, b[i].as_ref());

        // a[x] = swap?
        if a_hash == p_ - ((q_swapped - a_hash*g0) / g0) {
            // a[x] = corrupt?
            if p_ != Sha256::ZERO {
                return Some(Error::CorruptSwapA(i));
            } else {
                return Some(Error::CleanSwap(i));
            }
        }

        // b[x] = swap?
        if b_hash == p_ - ((q_swapped - a_hash*(g1-g0) - b_hash*g1) / g0) {
            // b[x] = corrupt?
            if p_ != Sha256::ZERO {
                return Some(Error::CorruptSwapB(i));
            }
        }

        // a[x] = error?
        if a_hash == p_ - ((q_ - a_hash*g0) / g0) {
            return Some(Error::CorruptA(i));
        }

        // b[x] = error?
        if b_hash == p_ - ((q_ - b_hash*g1) / g1) {
            return Some(Error::CorruptB(i));
        }

        // move on to next block, need to update q assuming a and b
        // have been swapped
        q_swapped += (b_hash-a_hash)*g0 + (a_hash-b_hash)*g1;

        g0 = g1 * Sha256::G;
        g1 = g0 * Sha256::G;
    }

    // if we reach here our parity hashes must be corrupt
    Some(Error::CorruptParity)
}

fn fix_error<A: AsMut<[u8]>+AsRef<[u8]>, B: AsMut<[u8]>+AsRef<[u8]>>(
    a: &mut [A],
    b: &mut [B],
    p: &[u8],
    h: (Sha256, Sha256),
) -> bool {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(p.len(), BLOCK_SIZE);

    // find error
    let error = match find_error(a, b, h) {
        Some(error) => error,
        None => {
            return false;
        }
    };

    // fix corruptions?
    match error {
        Error::CorruptA(i) | Error::CorruptSwapA(i) => {
            a[i].as_mut().copy_from_slice(p);
            for i_ in 0..a.len() {
                for j in 0..BLOCK_SIZE {
                    if i_ != i {
                        a[i].as_mut()[j] ^= a[i_].as_ref()[j];
                    }
                    a[i].as_mut()[j] ^= b[i_].as_ref()[j];
                }
            }
        }
        Error::CorruptB(i) | Error::CorruptSwapB(i) => {
            b[i].as_mut().copy_from_slice(p);
            for i_ in 0..a.len() {
                for j in 0..BLOCK_SIZE {
                    b[i].as_mut()[j] ^= a[i_].as_ref()[j];
                    if i_ != i {
                        b[i].as_mut()[j] ^= b[i_].as_ref()[j];
                    }
                }
            }
        }
        _ => {}
    }

    // finish swap?
    if let Some(i) = match error {
        Error::CorruptSwapA(i) => Some(i),
        Error::CorruptSwapB(i) => Some(i+1),
        Error::CleanSwap(i)    => Some(i),
        _                      => None,
    } {
        for i in i..a.len() {
            b[i].as_mut().swap_with_slice(a[i].as_mut());
        }
    }

    true
}


// emulate all steps of a swap
fn swap<'a, A: AsRef<[u8]>, B: AsRef<[u8]>>(
    a: &'a [A],
    b: &'a [B],
) -> impl Iterator<Item=(Vec<Vec<u8>>, Vec<Vec<u8>>)> + 'a {
    let mut a = a.iter().map(|a| a.as_ref().to_owned()).collect::<Vec<_>>();
    let mut b = b.iter().map(|b| b.as_ref().to_owned()).collect::<Vec<_>>();

    let mut steps = vec![];
    for i in 0..a.len() {
        let t = a[i].clone();
        a[i].fill(0xff);
        steps.push((a.clone(), b.clone()));
        a[i] = b[i].clone();
        steps.push((a.clone(), b.clone()));
        b[i].fill(0xff);
        steps.push((a.clone(), b.clone()));
        b[i] = t;
        steps.push((a.clone(), b.clone()));
    }

    steps.into_iter()
}

// emulate single block errors
fn errors<'a, A: AsRef<[u8]>, B: AsRef<[u8]>>(
    a: &'a [A],
    b: &'a [B],
) -> impl Iterator<Item=(Vec<Vec<u8>>, Vec<Vec<u8>>)> + 'a {
    let mut a = a.iter().map(|a| a.as_ref().to_owned()).collect::<Vec<_>>();
    let mut b = b.iter().map(|b| b.as_ref().to_owned()).collect::<Vec<_>>();

    let mut errors = vec![];
    for i in 0..a.len() {
        let t = a[i].clone();
        a[i].fill(0xff);
        errors.push((a.clone(), b.clone()));
        a[i] = t; 
    }
    for i in 0..b.len() {
        let t = b[i].clone();
        b[i].fill(0xff);
        errors.push((a.clone(), b.clone()));
        b[i] = t; 
    }

    errors.into_iter()
}


fn main() {
    use std::io::Write;

    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    fn blocks<A: AsRef<[u8]>, B: AsRef<[u8]>>(
        a: &[A],
        b: &[B],
        p: &[u8],
        h: (Sha256, Sha256)
    ) -> String {
        let mut buf = vec![];
        writeln!(buf, "\x1b[Ka = {} p = {}",
            a.iter()
                .map(|x| hex(x.as_ref()))
                .collect::<Vec<_>>()
                .join(" "),
            hex(p),
        ).unwrap();
        write!(buf, "\x1b[Kb = {} h = {} {}",
            b.iter()
                .map(|x| hex(x.as_ref()))
                .collect::<Vec<_>>()
                .join(" "),
            &hex(&h.0.0)[0..7],
            &hex(&h.1.0)[0..7],
        ).unwrap();
        String::from_utf8(buf).unwrap()
    }

    let a = [
        [12,34,56,78,90,12,34,56],
        [78,90,12,34,56,78,90,12],
        [34,56,78,90,12,34,56,78],
        [90,12,34,56,78,90,12,34],
    ];
    let b = [
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
    ];
    let mut p = [ 0, 0, 0, 0, 0, 0, 0, 0];
    mkparity(&a, &b, &mut p);
    let h = mkhash(&a, &b);

    println!("before:");
    println!("{}", blocks(&a, &b, &p, h));
    println!("swap = {:?}", find_error(&a, &b, h));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    println!("clean swap:");
    println!("{}", blocks(&a_, &b_, &p, h));
    println!("swap = {:?}", find_error(&a_, &b_, h));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2].fill(0xff);
    println!("dirty a swap:");
    println!("{}", blocks(&a_, &b_, &p, h));
    println!("swap = {:?}", find_error(&a_, &b_, h));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2] = b_[2];
    println!("half swap:");
    println!("{}", blocks(&a_, &b_, &p, h));
    println!("swap = {:?}", find_error(&a_, &b_, h));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);
    b_[2].fill(0xff);
    println!("dirty b swap:");
    println!("{}", blocks(&a_, &b_, &p, h));
    println!("swap = {:?}", find_error(&a_, &b_, h));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);
    println!("clean swap:");
    println!("{}", blocks(&a_, &b_, &p, h));
    println!("swap = {:?}", find_error(&a_, &b_, h));

    println!();

    // print exhaustive runs in the background
    use std::sync::{Arc, Mutex};
    struct BackgroundLog {
        log: Arc<Mutex<(bool, Vec<u8>)>>,
        local: Vec<u8>,
        handle: Option<std::thread::JoinHandle<()>>,
    }

    impl BackgroundLog {
        fn new() -> Self {
            let log = Arc::new(Mutex::new((false, vec![])));
            let handle = std::thread::spawn({
                let log = log.clone();
                move || {
                    let mut lines = 0;
                    loop {
                        let (done, log) = log.lock().unwrap().clone();

                        if lines > 0 {
                            println!("\x1b[{}A", lines+1);
                        }
                        lines = 0;
                        for line in std::str::from_utf8(&log).unwrap().lines() {
                            println!("\x1b[K{}", line);
                            lines += 1;
                        }

                        if done {
                            break;
                        }

                        std::thread::sleep(std::time::Duration::from_millis(10));
                    }
                }
            });
            Self {
                log,
                local: vec![],
                handle: Some(handle),
            }
        }

        fn reset(&mut self) {
            std::mem::swap(&mut self.log.lock().unwrap().1, &mut self.local);
            self.local.clear();
        }
    }

    impl Write for BackgroundLog {
        fn write(&mut self, data: &[u8]) -> Result<usize, std::io::Error> {
            self.local.write(data)
        }

        fn flush(&mut self) -> Result<(), std::io::Error> {
            self.local.flush()
        }
    }

    impl Drop for BackgroundLog {
        fn drop(&mut self) {
            self.log.lock().unwrap().0 = true;
            self.handle.take().unwrap().join().unwrap();
        }
    }


    // try every step in a swap
    let mut log = BackgroundLog::new();
    for (i, (mut a_, mut b_)) in swap(&a, &b).enumerate() {
        writeln!(log, "step {}:", i).unwrap();
        writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
        writeln!(log, "found = {:?}", find_error(&a_, &b_, h)).unwrap();

        fix_error(&mut a_, &mut b_, &p, h);
        writeln!(log, "fixed:").unwrap();
        writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
        log.reset();

        if !((a_ == b && b_ == a) || (a_ == a && b_ == b)) {
            drop(log);
            panic!("failure");
        }
    }

    drop(log);
    println!();

    // try every single block error
    let mut log = BackgroundLog::new();
    for (i, (mut a_, mut b_)) in errors(&a, &b).enumerate() {
        writeln!(log, "error {}:", i).unwrap();
        writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
        writeln!(log, "found = {:?}", find_error(&a_, &b_, h)).unwrap();

        fix_error(&mut a_, &mut b_, &p, h);
        writeln!(log, "fixed:").unwrap();
        writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
        log.reset();

        if !((a_ == b && b_ == a) || (a_ == a && b_ == b)) {
            drop(log);
            panic!("failure");
        }
    }

    drop(log);
    println!();

    // try every permutation of 2x4 blocks
    let mut log = BackgroundLog::new();
    for perm in 0..8u32.pow(8) {
        let mut a = [[0; 8]; 4];
        let mut b = [[0; 8]; 4];
        let mut p = [0; 8];
        for i in 0..4 {
            a[i as usize].fill(((perm/8u32.pow(i+0)) % 8) as u8);
            b[i as usize].fill(((perm/8u32.pow(i+4)) % 8) as u8);
        }
        mkparity(&a, &b, &mut p);
        let h = mkhash(&a, &b);

        // try every step in a swap
        for (i, (mut a_, mut b_)) in swap(&a, &b).enumerate() {
            writeln!(log, "{}-block permutations {}/{}:", 8, perm, 8u32.pow(8)).unwrap();
            writeln!(log, "{}", blocks(&a, &b, &p, h)).unwrap();

            writeln!(log, "step {}:", i).unwrap();
            writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
            writeln!(log, "found = {:?}", find_error(&a_, &b_, h)).unwrap();

            fix_error(&mut a_, &mut b_, &p, h);
            writeln!(log, "fixed:").unwrap();
            writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
            log.reset();

            if !((a_ == b && b_ == a) || (a_ == a && b_ == b)) {
                drop(log);
                panic!("failure");
            }
        }

        // try every single block error
        for (i, (mut a_, mut b_)) in errors(&a, &b).enumerate() {
            writeln!(log, "{}-block permutations {}/{}:", 8, perm, 8u32.pow(8)).unwrap();
            writeln!(log, "{}", blocks(&a, &b, &p, h)).unwrap();

            writeln!(log, "error {}:", i).unwrap();
            writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
            writeln!(log, "found = {:?}", find_error(&a_, &b_, h)).unwrap();

            fix_error(&mut a_, &mut b_, &p, h);
            writeln!(log, "fixed:").unwrap();
            writeln!(log, "{}", blocks(&a_, &b_, &p, h)).unwrap();
            log.reset();

            if !((a_ == b && b_ == a) || (a_ == a && b_ == b)) {
                drop(log);
                panic!("failure");
            }
        }
    }

    drop(log);
    println!();
}
