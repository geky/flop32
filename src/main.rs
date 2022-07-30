#![allow(dead_code)]


// crc32c stuff
const CRC32C_TABLE: [u32; 16] = [
    0x00000000, 0x105ec76f, 0x20bd8ede, 0x30e349b1,
    0x417b1dbc, 0x5125dad3, 0x61c69362, 0x7198540d,
    0x82f63b78, 0x92a8fc17, 0xa24bb5a6, 0xb21572c9,
    0xc38d26c4, 0xd3d3e1ab, 0xe330a81a, 0xf36e6f75,
];

const fn crc32c(crc: u32, data: &[u8]) -> u32 {
    let mut crc_ = crc ^ 0xffffffff;

    let mut i = 0;
    while i < data.len() {
        crc_ = (crc_ >> 4) ^ CRC32C_TABLE[(((crc_ as u8) ^ (data[i] >> 0)) & 0xf) as usize];
        crc_ = (crc_ >> 4) ^ CRC32C_TABLE[(((crc_ as u8) ^ (data[i] >> 0)) & 0xf) as usize];
        i += 1;
    }

    crc_ ^ 0xffffffff
}


// gf(2^32) stuff
const GF2P32_P: u32 = 0x000000af;
const GF2P32_G: u32 = 0x2;

const GF2P32_B: u32 = {
    let mut a = 1u128 << 64;
    let b = (1u128 << 32) | (GF2P32_P as u128);
    let mut x = 0u128;
    while a.leading_zeros() <= b.leading_zeros() {
        x ^= 1 << (b.leading_zeros()-a.leading_zeros());
        a ^= b << (b.leading_zeros()-a.leading_zeros());
    }
    x as u32
};

fn pmul32(a: u32, b: u32) -> (u32, u32) {
    let mut lo = 0;
    let mut hi = 0;
    for i in 0..32 {
        let mask = (((a as i32) << (31-i)) >> 31) as u32;
        lo ^= mask & (b << i);
        hi ^= mask & (b >> (31-i));
    }
    (lo, hi >> 1)
}

fn gmul32(a: u32, b: u32) -> u32 {
    // via Barret reduction
    let (lo, hi) = pmul32(a, b);
    lo ^ pmul32(pmul32(hi, GF2P32_B).1 ^ hi, GF2P32_P).0
}

fn gpow32(a: u32, x: usize) -> u32 {
    let mut a_ = a;
    let mut x_ = x;
    let mut p = 1;
    loop {
        if x_ & 1 != 0 {
            p = gmul32(p, a_);
        }

        x_ >>= 1;
        if x_ == 0 {
            return p;
        }
        a_ = gmul32(a_, a_);
    }
}

fn gdiv32(a: u32, b: u32) -> u32 {
    assert_ne!(b, 0);
    gmul32(a, gpow32(b, (u32::MAX-1) as usize))
}


// parity stuff, assumes last block is parity block
const BLOCK_SIZE: usize = 8;
const BLOCK_NULLCRC: u32 = crc32c(0, &[0; BLOCK_SIZE]);

fn mkparity<B: AsMut<[u8]>+AsRef<[u8]>>(blocks: &mut [B]) {
    debug_assert!(blocks.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));

    let (p, blocks) = blocks.split_last_mut().unwrap();
    let p = p.as_mut();

    p.fill(0);
    for b in blocks.iter().map(|b| b.as_ref()) {
        for i in 0..BLOCK_SIZE {
            p[i] ^= b[i];
        }
    }
}


fn find_parity<B: AsRef<[u8]>>(blocks: &[B]) -> (u32, u32) {
    debug_assert!(blocks.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));

    let mut p = if blocks.len() & 1 != 0 { BLOCK_NULLCRC } else { 0 };
    let mut q = 0;
    let mut g = 1;
    for b in blocks.iter().map(|b| b.as_ref()) {
        let crc = crc32c(0, b);
        p ^= crc;
        q ^= gmul32(crc, g);
        g = gmul32(g, GF2P32_G);
    }
    (p, q)
}

fn find_inflection<B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
    a: &[B1],
    b: &[B2],
    q: u32,
) -> Option<(usize, Option<usize>)> {
    debug_assert!(a.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());

    let (a_p, a_q) = find_parity(a);
    let (b_p, b_q) = find_parity(b);
    // no errors?
    if a_p == 0 && b_p == 0 {
        return None
    }

    // at some point this must be true:
    //
    // ax = Σai + Σbi
    //     i<x   i>x
    //
    let (mut a_lp, mut a_rp) = (0, a_p);
    let (mut b_lp, mut b_rp) = (0, b_p);
    let (mut a_lq, mut a_rq) = (0, a_q);
    let (mut b_lq, mut b_rq) = (0, b_q);
    let mut g = 1;

    let mut prev_b_crc = 0;
    let mut prev_g = 1;

    for i in 0..a.len() {
        let a_crc = crc32c(0, a[i].as_ref());
        let b_crc = crc32c(0, b[i].as_ref());

        // found inflection?
        if a_lp == b_rp {
            // calculate what bi and ai+1 should be
            //
            //      (q - Σ di*g^i) - (p - Σ di)*g^y
            //         i!=x,y           i!=x,y
            // dx = -------------------------------
            //                 g^x - g^y
            //
            let mut expected_prev_b_crc = 0;
            if i > 0 {
                expected_prev_b_crc = gdiv32(
                    (q^a_lq^b_rq^b_lq^gmul32(prev_b_crc, prev_g)^a_rq^gmul32(a_crc, g))
                        ^ gmul32(b_lp^prev_b_crc^a_rp^a_crc, g),
                    g^prev_g
                );
                if expected_prev_b_crc != prev_b_crc {
                    return Some((i, Some(i-1)));
                }
            }

            // dy = p - Σ di - dx
            //        i!=x,y
            //
            let expected_a_crc = b_lp^a_rp^prev_b_crc^a_crc^expected_prev_b_crc;
            if expected_a_crc != a_crc {
                return Some((i, Some(i)));
            }
            
            return Some((i, None));
        }

        prev_b_crc = b_crc;
        prev_g = g;

        a_rp ^= a_crc;
        b_rp ^= b_crc;
        a_rq ^= gmul32(a_crc, g);
        b_rq ^= gmul32(b_crc, g);

        a_lp ^= a_crc;
        b_lp ^= b_crc;
        a_lq ^= gmul32(a_crc, g);
        b_lq ^= gmul32(b_crc, g);
        g = gmul32(g, GF2P32_G);
    }

    // the only other situation is if our last parity block is corrupt
    Some((a.len(), Some(a.len()-1)))
}

fn fix_inflection<B1: AsMut<[u8]>+AsRef<[u8]>, B2: AsMut<[u8]>+AsRef<[u8]>>(
    a: &mut [B1],
    b: &mut [B2],
    q: u32,
) -> bool {
    debug_assert!(a.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());

    let (inflection, error) = match find_inflection(a, b, q) {
        Some(x) => x,
        None => {
            return false;
        }
    };

    // complete swaps
    for i in inflection..b.len() {
        b[i].as_mut().swap_with_slice(a[i].as_mut());
    }

    // fix error?
    if let Some(error) = error {
        let (head, tail) = b.split_at_mut(error);
        let (d, tail) = tail.split_first_mut().unwrap();
        let d = d.as_mut();

        d.fill(0);
        for b in head.iter().chain(tail.iter()).map(|b| b.as_ref()) {
            for i in 0..BLOCK_SIZE {
                d[i] ^= b[i];
            }
        }
    }

    true
}


fn main() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    fn blocks<B: AsRef<[u8]>>(blocks: &[B]) -> String {
        let (p, q) = find_parity(blocks);
        format!("{} ({:08x} {:08x})",
            blocks.iter()
                .map(|b| hex(b.as_ref()))
                .collect::<Vec<_>>()
                .join(" "),
            p,
            q,
        )
    }

    let mut a = [
        [12,34,56,78,90,12,34,56],
        [78,90,12,34,56,78,90,12],
        [34,56,78,90,12,34,56,78],
        [90,12,34,56,78,90,12,34],
        [ 0, 0, 0, 0, 0, 0, 0, 0],
    ];
    mkparity(&mut a);
    let a_q = find_parity(&a).1;

    let mut b = [
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [ 0, 0, 0, 0, 0, 0, 0, 0],
    ];
    mkparity(&mut b);
    let b_q = find_parity(&b).1;

    let q = a_q ^ b_q;

    println!("before:");
    println!("a = {}", blocks(&a));
    assert_eq!(find_parity(&a).0, 0);
    println!("b = {}", blocks(&b));
    assert_eq!(find_parity(&b).0, 0);
    println!("inflection = {:?}", find_inflection(&a, &b, q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);

    println!("clean swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(find_parity(&a_).0, 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(find_parity(&b_).0, 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_, q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2].fill(0xff);

    println!("dirty a swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(find_parity(&a_).0, 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(find_parity(&b_).0, 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_, q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2] = b_[2];

    println!("half swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(find_parity(&a_).0, 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(find_parity(&b_).0, 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_, q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);
    b_[2].fill(0xff);

    println!("dirty b swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(find_parity(&a_).0, 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(find_parity(&b_).0, 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_, q));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);

    println!("clean swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(find_parity(&a_).0, 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(find_parity(&b_).0, 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_, q));

    b_[2].fill(0xff);
    fix_inflection(&mut a_, &mut b_, q);

    println!("fixed:");
    println!("a = {}", blocks(&a_));
    assert_eq!(find_parity(&a_).0, 0);
    println!("b = {}", blocks(&b_));
    assert_eq!(find_parity(&b_).0, 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_, q));

    // simulate each step of a swap
    fn sim_swap<'a, B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
        a: &'a [B1],
        b: &'a [B2],
    ) -> impl Iterator<Item=(Vec<Vec<u8>>, Vec<Vec<u8>>)> + 'a {
        let mut a = a.iter().map(|a| a.as_ref().to_owned()).collect::<Vec<_>>();
        let mut b = b.iter().map(|b| b.as_ref().to_owned()).collect::<Vec<_>>();
        (0..a.len()).flat_map(move |i| {
            let mut steps = vec![];
            let t = a[i].clone();
            a[i].fill(0xff);
            steps.push((a.clone(), b.clone()));
            a[i] = b[i].clone();
            steps.push((a.clone(), b.clone()));
            b[i].fill(0xff);
            steps.push((a.clone(), b.clone()));
            b[i] = t;
            steps.push((a.clone(), b.clone()));
            steps
        })
    }

    println!();
    println!("simulating...");
    println!();
    println!();
    println!();
    for (mut a_, mut b_) in sim_swap(&a, &b) {
        print!("\x1b[3A");
        println!("\x1b[Ka = {}", blocks(&a_));
        println!("\x1b[Kb = {}", blocks(&b_));
        println!("\x1b[Kinflection = {:?}", find_inflection(&a_, &b_, q));

        fix_inflection(&mut a_, &mut b_, q);
        if a_ != b || b_ != a {
            println!("fixed:");
            println!("a = {}", blocks(&a_));
            println!("b = {}", blocks(&b_));
            println!();
            assert!(a_ == b);
            assert!(b_ == a);
            break;
        }
    }

    println!();
    println!("permutations...");
    println!();
    println!();
    println!();
    println!();
    println!();
    println!();
    for a_perm in 0..2u32.pow(4) {
        for b_perm in 0..2u32.pow(4) {
            let mut a = [
                if a_perm & 1 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                if a_perm & 2 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                if a_perm & 4 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                if a_perm & 8 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                [0; BLOCK_SIZE],
            ];
            let mut b = [
                if b_perm & 1 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                if b_perm & 2 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                if b_perm & 4 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                if b_perm & 8 != 0 { [10; BLOCK_SIZE] } else { [11; BLOCK_SIZE] },
                [0; BLOCK_SIZE],
            ];
            mkparity(&mut a);
            mkparity(&mut b);
            let q =  find_parity(&a).1 ^ find_parity(&b).1;
            print!("\x1b[6A");
            println!("\x1b[Ka = {}", blocks(&a));
            println!("\x1b[Kb = {}", blocks(&b));
            println!("\x1b[Ksimulating...");
            println!();
            println!();
            println!();

            for (mut a_, mut b_) in sim_swap(&a, &b) {
                print!("\x1b[3A");
                println!("\x1b[Ka = {}", blocks(&a_));
                println!("\x1b[Kb = {}", blocks(&b_));
                println!("\x1b[Kinflection = {:?}", find_inflection(&a_, &b_, q));

                fix_inflection(&mut a_, &mut b_, q);
                if a_ != b || b_ != a {
                    println!("fixed:");
                    println!("a = {}", blocks(&a_));
                    println!("b = {}", blocks(&b_));
                    println!();
                    assert!(a_ == b);
                    assert!(b_ == a);
                    break;
                }
            }
        }
    }
}
