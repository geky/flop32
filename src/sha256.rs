
use sha2::Digest;


/// A sha256 type with GF(256) operations
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sha256(pub [u8; 32]);

impl Sha256 {
    pub const fn zero() -> Self {
        Sha256([0; 32])
    }

    pub const fn one() -> Self {
        Sha256([1; 32])
    }
}

impl core::fmt::Display for Sha256 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        for x in self.0.iter() {
            write!(f, "{:02x}", x)?;
        }
        Ok(())
    }
}

impl<'a> core::iter::FromIterator<&'a [u8]> for Sha256 {
    fn from_iter<T: IntoIterator<Item=&'a [u8]>>(iter: T) -> Self {
        let mut hasher = sha2::Sha256::new();
        for x in iter {
            hasher.update(x);
        }
        Sha256(hasher.finalize().into())
    }
}

// add/sub = xor

impl core::ops::BitXor for Sha256 {
    type Output = Sha256;
    fn bitxor(self, other: Sha256) -> Sha256 {
        let mut res = Sha256::zero();
        for i in 0..self.0.len() {
            res.0[i] = self.0[i] ^ other.0[i];
        }
        res
    }
}

impl core::ops::Add for Sha256 {
    type Output = Sha256;
    fn add(self, other: Sha256) -> Sha256 {
        self ^ other
    }
}

impl core::ops::Sub for Sha256 {
    type Output = Sha256;
    fn sub(self, other: Sha256) -> Sha256 {
        self ^ other
    }
}

// multiplication = multiplication over GF(256)

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

const GF256P32_P: [u8; 33] = [
    0xec,0x01,0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x01,
];
const FG256P32_G: [u8; 32] = [
    0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
];

fn gf256p32_mul(a: &[u8], b: &[u8]) -> [u8; 32] {
    p32x256_divrem(&p32x256_mul(a, b), &GF256P32_P).1
}

fn gf256p32_recip(a: &[u8]) -> [u8; 32] {
    // multiplicative inverse using extended Euclidean algorithm
    let mut t0 = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    let mut t1 = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    let mut r0 = GF256P32_P;
    let mut r1 = [0; 32];
    r1[..a.len()].copy_from_slice(a);

    while !r1.iter().all(|x| *x == 0) {
        let (q, r) = p32x256_divrem(&r0, &r1);
        let t = p32x256_xor(&t0, &p32x256_mul(&q, &t1)[..32]);
        r0[r1.len()..].fill(0);
        r0[..r1.len()].copy_from_slice(&r1);
        r1 = r;
        (t0, t1) = (t1, t);
    }

    // p not irreducible?
    debug_assert!(r0[1..].iter().all(|x| *x == 0));

    // scale by constant
    for i in 0..t0.len() {
        t0[i] = gf256_div(t0[i], r0[0]);
    }

    t0
}

fn gf256p32_div(a: &[u8], b: &[u8]) -> [u8; 32] {
    gf256p32_mul(a, &gf256p32_recip(b))
}

#[test]
fn test_gf256p32() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    let a = [17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17];
    println!("       a = {}", hex(&a));
    println!("     1/a = {}", hex(&gf256p32_recip(&a)));
    println!(" a*(1/a) = {}", hex(&gf256p32_mul(&a, &gf256p32_recip(&a))));
    println!();

    let b = [34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34];
    println!("       b = {}", hex(&b));
    println!("     a*b = {}", hex(&gf256p32_mul(&a, &b)));
    println!(" (a*b)/b = {}", hex(&gf256p32_div(&gf256p32_mul(&a, &b), &b)));
    println!(" (a*b)/a = {}", hex(&gf256p32_div(&gf256p32_mul(&a, &b), &a)));
    println!();

    let c = [51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51];
    println!("       c = {}", hex(&c));
    println!("     b+c = {}", hex(&p32x256_xor(&b, &c)));
    println!("     a*b = {}", hex(&gf256p32_mul(&a, &b)));
    println!("     a*c = {}", hex(&gf256p32_mul(&a, &c)));
    println!(" a*(b+c) = {}", hex(&gf256p32_mul(&a, &p32x256_xor(&b, &c))));
    println!(" a*b+a*c = {}", hex(&p32x256_xor(&gf256p32_mul(&a, &b), &gf256p32_mul(&a, &c))));
    
}

#[test]
fn test_gf256p32_more() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    let perms = [
        [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
        [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
        [7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
        [0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7],
        [17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17],
        [34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34],
        [51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51],
        [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff],
        [0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff],
        [0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff],
    ];

    for a in perms {
        for b in perms {
            for c in perms {
                assert_eq!(
                    gf256p32_mul(&a, &gf256p32_recip(&a)),
                    [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
                    "a*(1/a) = a"
                );
                assert_eq!(
                    gf256p32_div(&gf256p32_mul(&a, &b), &b),
                    a,
                    "(a*b)/b = a"
                );
                assert_eq!(
                    gf256p32_mul(&a, &p32x256_xor(&b, &c)),
                    p32x256_xor(&gf256p32_mul(&a, &b), &gf256p32_mul(&a, &c)),
                    "a*(b+c) = a*b+a*c"
                );
            }
        }
    }
}


fn p32x256_xor(a: &[u8], b: &[u8]) -> [u8; 32] {
    let mut d = [0; 32];
    for i in 0..32 {
        d[i] = a[i] ^ b[i];
    }
    d
}

fn p32x256_mul(a: &[u8], b: &[u8]) -> [u8; 64] {
    let mut d = [0; 64];
    for i in 0..32 {
        for j in 0..32 {
            d[i+j] ^= gf256_mul(a[i], b[j]);
        }
    }
    d
}

fn p32x256_divrem(mut a: &[u8], mut b: &[u8]) -> ([u8; 64], [u8; 32]) {
    // find leading coefficients
    while a.len() > 0 && a[a.len()-1] == 0 {
        a = &a[..a.len()-1];
    }
    while b.len() > 0 && b[b.len()-1] == 0 {
        b = &b[..b.len()-1];
    }
    debug_assert!(b.len() != 0);
    if a.len() == 0 {
        return ([0; 64], [0; 32]);
    }
    if a.len() < b.len() {
        let mut rem = [0; 32];
        rem[..a.len()].copy_from_slice(a);
        return ([0; 64], rem);
    }
    let leading_coeff = b[b.len()-1];

    // perform synthetic division
    let mut a_ = [0; 64];
    a_[..a.len()].copy_from_slice(a);

    for i in 0..a.len()-b.len()+1 {
        a_[a.len()-1-i] = gf256_div(a_[a.len()-1-i], leading_coeff);
        for j in 1..b.len() {
            a_[a.len()-1-(i+j)] ^= gf256_mul(a_[a.len()-1-i], b[b.len()-1-j]);
        }
    }

    let mut div = [0; 64];
    let mut rem = [0; 32];
    div[..a.len()-b.len()+1].copy_from_slice(&a_[b.len()-1..a.len()]);
    rem[..b.len()-1].copy_from_slice(&a_[..b.len()-1]);
    (div, rem)
}

fn p32x256_gcd(a: &[u8], b: &[u8]) -> [u8; 32] {
    // Euclidean's algorithm
    let mut a_ = [0; 64];
    a_[..a.len()].copy_from_slice(a);
    let mut b_ = [0; 32];
    b_[..b.len()].copy_from_slice(b);
    loop {
        if b_.iter().all(|x| *x == 0) {
            return a_[..32].try_into().unwrap();
        }

        let (_, r) = p32x256_divrem(&a_, &b_);
        a_[32..].fill(0);
        a_[..32].copy_from_slice(&b_);
        b_ = r;
    }
}

fn p32x256_is_irreducible(
    a: &[u8]
) -> (bool, u32, u32, Option<([u8; 32], [u8; 32])>) {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    // Ben-Or's irreducbility test
    // https://www.math.clemson.edu/~sgao/papers/GP97a.pdf
    let mut x = [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    for i in 0..(32/2)-1 {
        // find x^256^i mod a
        for _ in 0..8 {
            let (_, r) = p32x256_divrem(&p32x256_mul(&x, &x), a);
            x = r;
        }

        // find x^256^i - x mod a
        let x_ = p32x256_xor(&x, &[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);

        // test gcd(a, x^256^i - x mod a) == constant
        let g = p32x256_gcd(a, &x_);
        if !g[1..].iter().all(|x| *x == 0) {
            return (false, i, (32/2)-1, Some((x_, g)));
        }
    }

    (true, (32/2)-1, (32/2)-1, None)
}

fn p32x256_is_generator(g: &[u8], p: &[u8]) -> bool {
    if g.iter().all(|x| *x == 0) {
        return false;
    }

    let gf256p32_mul = |a: &[u8], b: &[u8]| -> [u8; 32] {
        p32x256_divrem(&p32x256_mul(a, b), p).1
    };

    let gf256p32_pow = |a: &[u8], hex: &str| -> [u8; 32] {
        let mut d = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
        let mut a_ = [0; 32];
        a_[..a.len()].copy_from_slice(a);
        for bit in hex.chars()
            .rev()
            .flat_map(|nibble| {
                let nibble = nibble.to_digit(16).unwrap();
                (0..4).map(move |bit| nibble & (1 << bit) != 0)
            })
        {
            if bit {
                d = gf256p32_mul(&d, &a_);
            }

            a_ = gf256p32_mul(&a_, &a_);
        }

        d
    };

    // prime factors of 2^256-1
    // 3*5*17*257*641*65537*274177*6700417*67280421310721*59649589127497217*5704689200685129054721
    //
    // we need to test that there are no cycles of the form (2^256-1)/m where m
    // is each of the prime facors of 2^256-1. unfortunately these numbers are
    // problematically large.
    //
    // To make them work here I've precalculated (2^256-1)/m and converted them
    // to hex strings.
    //
    for cycle in [
        "5555555555555555555555555555555555555555555555555555555555555555", // 2^256-1 / 3
        "3333333333333333333333333333333333333333333333333333333333333333", // 2^256-1 / 5
        "f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f", // 2^256-1 / 17
        "ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff", // 2^256-1 / 257
        "663d80ff99c27f00663d80ff99c27f00663d80ff99c27f00663d80ff99c27f", // 2^256-1 / 641
        "ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff", // 2^256-1 / 65537
        "3d30f19cd100ffffc2cf0e632eff00003d30f19cd100ffffc2cf0e632eff", // 2^256-1 / 274177
        "280fffffd7f00000280fffffd7f00000280fffffd7f00000280fffffd7f", // 2^256-1 / 6700417
        "42f00fffffffffffbd0ff0000000000042f00fffffffffffbd0ff", // 2^256-1 / 67280421310721
        "13540775b48cc32ba00fffffffffffffecabf88a4b733cd45ff", // 2^256-1 / 59649589127497217
        "d3eafc3af14600ffffffffffffffffff2c1503c50eb9ff", // 2^256-1 / 5704689200685129054721
    ] {
        // found tighter cycle?
        if gf256p32_pow(g, cycle) == [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] {
            return false;
        }
    }

    // test that g^256-1 = 1
    gf256p32_pow(g, "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
        == [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
}

#[test]
fn find_irreducible() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    let thread_count = std::env::var("THREADS")
        .map(|x| x.parse::<u8>().unwrap())
        .unwrap_or(1);

    #[derive(Debug, Clone)]
    struct Best {
        p: [u8; 33],
        passed: u32,
        needed: u32,
        generator: Option<[u8; 32]>,
        failure: Option<([u8; 32], [u8; 32])>,
    }

    use std::sync::{Arc, Mutex};
    let last: Arc<Mutex<Option<Best>>> = Arc::new(Mutex::new(None));
    let best: Arc<Mutex<Option<Best>>> = Arc::new(Mutex::new(None));
    let last_best: Arc<Mutex<Option<Best>>> = Arc::new(Mutex::new(None));

    for t in 0..thread_count {
        std::thread::spawn({
            let last = last.clone();
            let best = best.clone();
            let last_best = last_best.clone();
            move || {
                let mut p: [u8; 33] = [t,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1];
                let mut cached_best = 0;
                loop {
                    let (found, mut passed, mut needed, failure) = p32x256_is_irreducible(&p);

                    let mut generator = None;
                    needed += 1;
                    if found {
                        // we know its irreducible, but is it primitive?
                        let g = [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
                        if p32x256_is_generator(&g, &p) {
                            generator = Some(g);
                            passed += 1;
                        }
                    }

                    if let Ok(mut last) = last.try_lock() {
                        *last = Some(Best{p, passed, needed, generator, failure});
                    }

                    if passed >= cached_best {
                        let mut best = best.lock().unwrap();
                        if best.is_none()
                            || passed > best.as_ref().unwrap().passed
                            || (passed == best.as_ref().unwrap().passed
                                && p.iter().rev().lt(best.as_ref().unwrap().p.iter().rev()))
                        {
                            *best = Some(Best{p, passed, needed, generator, failure});
                            *last_best.lock().unwrap() = Some(Best{p, passed, needed, generator, failure});
                        }
                        cached_best = best.as_ref().map(|best| best.passed).unwrap_or(0);

                        let mut last_best = last_best.lock().unwrap();
                        if last_best.is_none() || passed == last_best.as_ref().unwrap().passed {
                            *last_best = Some(Best{p, passed, needed, generator, failure});
                        }
                    }

                    // increment p
                    let mut carry = thread_count;
                    for i in 0..p.len() {
                        let (x, v) = p[i].overflowing_add(carry);
                        p[i] = x;
                        if !v {
                            break;
                        }
                        carry = 1;
                    }
                }
            }
        });
    }

    // print in our main thread
    let mut lines = 0;
    loop {
        if lines > 0 {
            println!("\x1b[{}A", lines+1);
        }

        if let Some(last) = last.lock().unwrap().clone() {
            println!("\x1b[Ktesting {}...", hex(&last.p));
            if let Some((x, g)) = last.failure {
                println!("\x1b[Kfailure gcd({})", hex(&x));
                println!("\x1b[K          = {}", hex(&g));
            } else if let Some(g) = last.generator {
                println!("\x1b[Kgen = {}", hex(&g));
                println!("\x1b[K");
            } else {
                println!("\x1b[K");
                println!("\x1b[K");
            }
        } else {
            println!("\x1b[K");
            println!("\x1b[K");
            println!("\x1b[K");
        }

        if let Some(last_best) = last_best.lock().unwrap().clone() {
            println!("\x1b[Klast passed {}/{} {}", last_best.passed, last_best.needed, hex(&last_best.p));
            if let Some((x, g)) = last_best.failure {
                println!("\x1b[Kfailure gcd({})", hex(&x));
                println!("\x1b[K          = {}", hex(&g));
            } else if let Some(g) = last_best.generator {
                println!("\x1b[Kgen = {}", hex(&g));
                println!("\x1b[K");
            } else {
                println!("\x1b[K");
                println!("\x1b[K");
            }
        } else {
            println!("\x1b[K");
            println!("\x1b[K");
            println!("\x1b[K");
        }

        if let Some(best) = best.lock().unwrap().clone() {
            println!("\x1b[Kbest passed {}/{} {}", best.passed, best.needed, hex(&best.p));
            if let Some((x, g)) = best.failure {
                println!("\x1b[Kfailure gcd({})", hex(&x));
                println!("\x1b[K          = {}", hex(&g));
            } else if let Some(g) = best.generator {
                println!("\x1b[Kgen = {}", hex(&g));
                println!("\x1b[K");
            } else {
                println!("\x1b[K");
                println!("\x1b[K");
            }
        } else {
            println!("\x1b[K");
            println!("\x1b[K");
            println!("\x1b[K");
        }

        std::thread::sleep(std::time::Duration::from_millis(10));
        lines = 9;
    }
}

#[test]
fn sanity() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    let a = [1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    let b = [3,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    println!("a = {}", hex(&a));
    println!("b = {}", hex(&b));
    let d = p32x256_mul(&a, &b);
    println!("a*b = {}", hex(&d));
    let (q, r) = p32x256_divrem(&d, &b);
    println!("(a*b)/b = {}", hex(&q));
    println!("(a*b)%b = {}", hex(&r));
    let gcd = p32x256_gcd(&d, &a);
    println!("gcd = {}", hex(&gcd));
}

impl Sha256 {
    pub const G: Sha256 = Sha256([GF256_G; 32]);
}

impl core::ops::Mul for Sha256 {
    type Output = Sha256;
    fn mul(self, other: Sha256) -> Sha256 {
        let mut res = Sha256::zero();
        for i in 0..self.0.len() {
            res.0[i] = gf256_mul(self.0[i], other.0[i]);
        }
        res
    }
}

impl core::ops::Div for Sha256 {
    type Output = Sha256;
    fn div(self, other: Sha256) -> Sha256 {
        let mut res = Sha256::zero();
        for i in 0..self.0.len() {
            res.0[i] = gf256_div(self.0[i], other.0[i]);
        }
        res
    }
}


// Assignment variants blablabla

impl core::ops::BitXorAssign for Sha256 {
    fn bitxor_assign(&mut self, other: Sha256) {
        *self = *self ^ other;
    }
}

impl core::ops::AddAssign for Sha256 {
    fn add_assign(&mut self, other: Sha256) {
        *self = *self + other;
    }
}

impl core::ops::SubAssign for Sha256 {
    fn sub_assign(&mut self, other: Sha256) {
        *self = *self - other;
    }
}

impl core::ops::MulAssign for Sha256 {
    fn mul_assign(&mut self, other: Sha256) {
        *self = *self * other;
    }
}

impl core::ops::DivAssign for Sha256 {
    fn div_assign(&mut self, other: Sha256) {
        *self = *self / other;
    }
}
