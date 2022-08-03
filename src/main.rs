#![allow(dead_code)]


// gf(256) stuff
const GF256_P: u16 = 0x11d;
const GF256_G: u8 = 0x2;

const GF256_TABLES: ([u8; 256], [u8; 256]) = {
    let mut tables = ([0; 256], [0; 256]);
    let mut x: u16 = 1;
    let mut i: u16 = 0;
    while i < 256 {
        tables.0[x as usize] = i as u8;
        tables.1[i as usize] = x as u8;

        x = x << 1;
        if x > 255 {
            x ^= GF256_P;
        }
        i += 1;
    }

    tables.0[0] = 255; // log(0) = undefined
    tables.0[1] = 0;   // log(1) = 0
    tables
};
const GF256_LOG: [u8; 256] = GF256_TABLES.0;
const GF256_EXP: [u8; 256] = GF256_TABLES.1;

fn gf256_mul(a: u8, b: u8) -> u8 {
    if a == 0 || b == 0 {
        return 0;
    }

    match GF256_LOG[a as usize].overflowing_add(GF256_LOG[b as usize]) {
        (x, true) => GF256_EXP[x.wrapping_sub(255) as usize],
        (x, false) => GF256_EXP[x as usize],
    }
}

fn gf256_div(a: u8, b: u8) -> u8 {
    assert_ne!(b, 0);
    if a == 0 {
        return 0;
    }

    match GF256_LOG[a as usize].overflowing_add(255-GF256_LOG[b as usize]) {
        (x, true) => GF256_EXP[x.wrapping_sub(255) as usize],
        (x, false) => GF256_EXP[x as usize],
    }
}



// parity stuff
const BLOCK_SIZE: usize = 8;

// populates
// p = Σ a[i] g^2i + Σ a[i] g^(2i+1)
// q = Σ a[i] g^4i + Σ b[i] g^(4i+2)
fn mkparity<B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
    a: &[B1],
    b: &[B2],
    p: &mut [u8],
    q: &mut [u8],
) {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(p.len(), BLOCK_SIZE);
    debug_assert_eq!(q.len(), BLOCK_SIZE);

    p.fill(0);
    q.fill(0);
    let mut g0 = 1;
    let mut g1 = gf256_mul(g0, GF256_G);
    let mut h0 = 1;
    let mut h1 = gf256_mul(gf256_mul(h0, GF256_G), GF256_G);
    for i in 0..a.len() {
        let ai = a[i].as_ref();
        let bi = b[i].as_ref();
        for j in 0..BLOCK_SIZE {
            p[j] ^= gf256_mul(ai[j], g0) ^ gf256_mul(bi[j], g1);
            q[j] ^= gf256_mul(ai[j], h0) ^ gf256_mul(bi[j], h1);
        }
        g0 = gf256_mul(g1, GF256_G);
        g1 = gf256_mul(g0, GF256_G);
        h0 = gf256_mul(gf256_mul(h1, GF256_G), GF256_G);
        h1 = gf256_mul(gf256_mul(h0, GF256_G), GF256_G);
    }
}

#[derive(Debug, Clone)]
enum Swap {
    CorruptA(usize, Vec<u8>),
    CorruptB(usize, Vec<u8>),
    Clean(usize),
    Parity,
}

// find where we left off a swap
//
// at some point this must be true
//
//   a[x] g^2x = p - Σ a[i] g^(2i+1) + Σ a[i] g^2i + Σ b[i] g^2i + Σ b[i] g^(2i+1)
//                   i<x               i>x           i<x           i>=x
//
//   a[x] g^4x = q - Σ a[i] g^(4i+2) + Σ a[i] g^4i + Σ b[i] g^4i + Σ b[i] g^(4i+2)
//                   i<x               i>x           i<x           i>=x
//
//   (a = bbbb?aaaaa)
//   (b = aaaabbbbbb)
//
// or 
//
//   b[x] g^(2x+1) = p - Σ a[i] g^(2i+1) + Σ a[i] g^2i + Σ b[i] g^2i + Σ b[i] g^(2i+1)
//                       i<=x              i>x           i<x           i>x
//
//   b[x] g^(4x+2) = q - Σ a[i] g^(4i+2) + Σ a[i] g^4i + Σ b[i] g^4i + Σ b[i] g^(4i+2)
//                       i<=x              i>x           i<x           i>x
//
//   (a = bbbbbaaaaa)
//   (b = aaaa?bbbbb)
//
//
fn find_swap<B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
    a: &[B1],
    b: &[B2],
    p: &[u8],
    q: &[u8],
) -> Option<Swap> {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(p.len(), BLOCK_SIZE);
    debug_assert_eq!(q.len(), BLOCK_SIZE);

    // first thing first, do we have any errors?
    let mut p_ = vec![0; BLOCK_SIZE];
    let mut q_ = vec![0; BLOCK_SIZE];
    mkparity(&a, &b, &mut p_,  &mut q_);
    if p_ == p && q_ == q {
        return None;
    }

    // subtract from p and q
    for j in 0..BLOCK_SIZE {
        p_[j] ^= p[j];
        q_[j] ^= q[j];
    }

    // scan again trying to find the point of inflection
    let mut g0 = 1;
    let mut g1 = gf256_mul(g0, GF256_G);
    let mut h0 = 1;
    let mut h1 = gf256_mul(gf256_mul(h0, GF256_G), GF256_G);
    for i in 0..a.len() {
        let ai = a[i].as_ref();
        let bi = b[i].as_ref();

        // a[x] = inflection?
        if (0..BLOCK_SIZE).all(|j| {
            gf256_div(p_[j] ^ gf256_mul(ai[j], g0), g0)
                == gf256_div(q_[j] ^ gf256_mul(ai[j], h0), h0)
        }) {
            // a[x] = corrupt?
            if (0..BLOCK_SIZE).any(|j| ai[j] != gf256_div(p_[j] ^ gf256_mul(ai[j], g0), g0)) {
                return Some(Swap::CorruptA(i,
                    (0..BLOCK_SIZE).map(|j| {
                        gf256_div(p_[j] ^ gf256_mul(ai[j], g0), g0)
                    }).collect::<Vec<_>>()
                ));
            } else {
                return Some(Swap::Clean(i));
            }
        }

        // b[x] = inflection?
        if (0..BLOCK_SIZE).all(|j| {
            gf256_div(p_[j] ^ gf256_mul(bi[j], g1) ^ gf256_mul(ai[j], g0^g1), g0)
                == gf256_div(q_[j] ^ gf256_mul(bi[j], h1) ^ gf256_mul(ai[j], h0^h1), h0)
        }) {
            // b[x] = corrupt?
            if (0..BLOCK_SIZE).any(|j| bi[j] != gf256_div(p_[j] ^ gf256_mul(bi[j], g1) ^ gf256_mul(ai[j], g0^g1), g0)) {
                return Some(Swap::CorruptB(i,
                    (0..BLOCK_SIZE).map(|j| {
                        gf256_div(p_[j] ^ gf256_mul(bi[j], g1) ^ gf256_mul(ai[j], g0^g1), g0)
                    }).collect::<Vec<_>>()
                ));
            }
        }

        // move on to next block, need to update q assuming a and b
        // have been swapped
        for j in 0..BLOCK_SIZE {
            p_[j] ^= gf256_mul(ai[j]^bi[j], g0) ^ gf256_mul(ai[j]^bi[j], g1);
            q_[j] ^= gf256_mul(ai[j]^bi[j], h0) ^ gf256_mul(ai[j]^bi[j], h1);
        }
        
        g0 = gf256_mul(g1, GF256_G);
        g1 = gf256_mul(g0, GF256_G);
        h0 = gf256_mul(gf256_mul(h1, GF256_G), GF256_G);
        h1 = gf256_mul(gf256_mul(h0, GF256_G), GF256_G);
    }

    // if we reach here one of our parity blocks must be corrupt
    Some(Swap::Parity)
}

fn fix_swap<B1: AsMut<[u8]>+AsRef<[u8]>, B2: AsMut<[u8]>+AsRef<[u8]>>(
    a: &mut [B1],
    b: &mut [B2],
    p: &mut [u8],
    q: &mut [u8],
) -> bool {
    debug_assert!(a.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|x| x.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(p.len(), BLOCK_SIZE);
    debug_assert_eq!(q.len(), BLOCK_SIZE);

    // fix corruptions?
    let i = match find_swap(a, b, p, q) {
        Some(Swap::CorruptA(i, p_)) => {
            a[i].as_mut().copy_from_slice(&p_);
            i
        },
        Some(Swap::CorruptB(i, p_)) => {
            b[i].as_mut().copy_from_slice(&p_);
            i+1
        },
        Some(Swap::Clean(i)) => {
            i
        },
        Some(Swap::Parity) => {
            a.len()
        },
        None => {
            return false;
        }
    };

    // finish swap
    for i in i..a.len() {
        b[i].as_mut().swap_with_slice(a[i].as_mut());
    }
    mkparity(a, b, p, q);

    true
}


// emulate all steps of a swap
fn swap<'a, B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
    a: &'a [B1],
    b: &'a [B2],
    p: &'a [u8],
    q: &'a [u8],
) -> impl Iterator<Item=(Vec<Vec<u8>>, Vec<Vec<u8>>, Vec<u8>, Vec<u8>)> + 'a {
    let mut a = a.iter().map(|a| a.as_ref().to_owned()).collect::<Vec<_>>();
    let mut b = b.iter().map(|b| b.as_ref().to_owned()).collect::<Vec<_>>();
    let mut p = p.to_owned();
    let mut q = q.to_owned();

    let mut steps = vec![];
    for i in 0..a.len() {
        let t = a[i].clone();
        a[i].fill(0xff);
        steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
        a[i] = b[i].clone();
        steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
        b[i].fill(0xff);
        steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
        b[i] = t;
        steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
    }

    // TODO check these
    p.fill(0xff);
    //steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
    mkparity(&a, &b, &mut p, &mut vec![0; BLOCK_SIZE]);
    //steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
    q.fill(0xff);
    //steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));
    mkparity(&a, &b, &mut vec![0; BLOCK_SIZE], &mut q);
    //steps.push((a.clone(), b.clone(), p.to_owned(), q.to_owned()));

    steps.into_iter()
}


fn main() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    fn print_blocks<B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
        a: &[B1],
        b: &[B2],
        p: &[u8],
        q: &[u8]
    ) {
        println!("a = {} p = {}",
            a.iter()
                .map(|x| hex(x.as_ref()))
                .collect::<Vec<_>>()
                .join(" "),
            hex(p)
        );
        println!("b = {} q = {}",
            b.iter()
                .map(|x| hex(x.as_ref()))
                .collect::<Vec<_>>()
                .join(" "),
            hex(q)
        );
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
    let mut q = [ 0, 0, 0, 0, 0, 0, 0, 0];
    mkparity(&a, &b, &mut p, &mut q);

    println!("before:");
    print_blocks(&a, &b, &p, &q);
    println!("inflection = {:?}", find_swap(&a, &b, &p, &q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    println!("clean swap:");
    print_blocks(&a_, &b_, &p, &q);
    println!("inflection = {:?}", find_swap(&a_, &b_, &p, &q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2].fill(0xff);
    println!("dirty a swap:");
    print_blocks(&a_, &b_, &p, &q);
    println!("inflection = {:?}", find_swap(&a_, &b_, &p, &q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2] = b_[2];
    println!("half swap:");
    print_blocks(&a_, &b_, &p, &q);
    println!("inflection = {:?}", find_swap(&a_, &b_, &p, &q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);
    b_[2].fill(0xff);
    println!("dirty b swap:");
    print_blocks(&a_, &b_, &p, &q);
    println!("inflection = {:?}", find_swap(&a_, &b_, &p, &q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);
    println!("clean swap:");
    print_blocks(&a_, &b_, &p, &q);
    println!("inflection = {:?}", find_swap(&a_, &b_, &p, &q));

    println!();

    for (i, (mut a_, mut b_, mut p, mut q)) in
        swap(&a, &b, &p, &q).enumerate()
    {
        if i != 0 {
            print!("\x1b[7A");
        }
        println!("\x1b[Kstep {}:", i);
        print_blocks(&a_, &b_, &p, &q);
        println!("\x1b[Kinflection = {:?}", find_swap(&a_, &b_, &p, &q));

        fix_swap(&mut a_, &mut b_, &mut p, &mut q);
        println!("\x1b[Kfixed:");
        print_blocks(&a_, &b_, &p, &q);

        assert!(a_ == b);
        assert!(b_ == a);
        let mut p_ = vec![0; BLOCK_SIZE];
        let mut q_ = vec![0; BLOCK_SIZE];
        mkparity(&a_, &b_, &mut p_, &mut q_);
        assert!(p == p_);
        assert!(q == q_);
    }

    println!();

    // try every permutation of n unique blocks
    for n in 2u32..8u32 {
        for perm in 0..n.pow(8) {
            let mut a = [[0; 8]; 4];
            let mut b = [[0; 8]; 4];
            let mut p = [0; 8];
            let mut q = [0; 8];
            for i in 0..4 {
                a[i as usize].fill(((perm/n.pow(i+0)) % n) as u8);
                b[i as usize].fill(((perm/n.pow(i+4)) % n) as u8);
            }
            mkparity(&a, &b, &mut p, &mut q);

            if perm != 0 {
                print!("\x1b[10A");
            }
            println!("\x1b[K{}-block permutations {}/{}:", n, perm, n.pow(8));
            print_blocks(&a, &b, &p, &q);

            for (i, (mut a_, mut b_, mut p, mut q)) in
                swap(&a, &b, &p, &q).enumerate()
            {
                if i != 0 {
                    print!("\x1b[7A");
                }
                println!("\x1b[Kstep {}:", i);
                print_blocks(&a_, &b_, &p, &q);
                println!("\x1b[Kinflection = {:?}", find_swap(&a_, &b_, &p, &q));

                fix_swap(&mut a_, &mut b_, &mut p, &mut q);
                println!("\x1b[Kfixed:");
                print_blocks(&a_, &b_, &p, &q);

                assert!(a_ == b || a_ == a);
                assert!(b_ == a || b_ == b);
                let mut p_ = vec![0; BLOCK_SIZE];
                let mut q_ = vec![0; BLOCK_SIZE];
                mkparity(&a_, &b_, &mut p_, &mut q_);
                assert!(p == p_);
                assert!(q == q_);
            }

            if perm == n.pow(8)-1 {
                println!();
            }
        }
    }
}
