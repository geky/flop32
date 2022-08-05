
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

fn p32x256_divrem(mut a: &[u8], mut b: &[u8]) -> ([u8; 32], [u8; 32]) {
    // find leading coefficients
    while a.len() > 0 && a[a.len()-1] == 0 {
        a = &a[..a.len()-1];
    }
    while b.len() > 0 && b[b.len()-1] == 0 {
        b = &b[..b.len()-1];
    }
    debug_assert!(b.len() != 0);
    if a.len() == 0 {
        return ([0; 32], [0; 32]);
    }
    if a.len() < b.len() {
        let mut rem = [0; 32];
        rem[..a.len()].copy_from_slice(a);
        return ([0; 32], rem);
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

    let mut div = [0; 32];
    let mut rem = [0; 32];
    use std::cmp::min;
    div[..min(a.len()-b.len()+1, 32)].copy_from_slice(&a_[b.len()-1..min(a.len(), b.len()-1+32)]);
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
    for i in 0..32/2 {
        // find x^256^i mod a
        for _ in 0..8 {
            let (_, r) = p32x256_divrem(&p32x256_mul(&x, &x), a);
            x = r;
        }

        // find x^256^i - x mod a
        let x_ = p32x256_xor(&x, &[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);

        // test gcd(a, x^256^i - x mod a) == 1
        let g = p32x256_gcd(a, &x_);

        if g != [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] {
            return (false, i, 32/2, Some((x_, g)));
        }
    }

    (true, 32/2, 32/2, None)
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
        t: u8,
        p: [u8; 33],
        found: bool,
        passed: u32,
        needed: u32,
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
                    let (found, passed, needed, failure) = p32x256_is_irreducible(&p);

                    if let Ok(mut last) = last.try_lock() {
                        *last = Some(Best{t, p, found, passed, needed, failure});
                    }

                    if passed >= cached_best {
                        if passed > cached_best {
                            let mut best = best.lock().unwrap();
                            if best.is_none()
                                || passed > best.as_ref().unwrap().passed
                                || (passed == best.as_ref().unwrap().passed
                                    && t < best.as_ref().unwrap().t)
                            {
                                *best = Some(Best{t, p, found, passed, needed, failure});
                                *last_best.lock().unwrap() = Some(Best{t, p, found, passed, needed, failure});
                            }
                            cached_best = best.as_ref().map(|best| best.passed).unwrap_or(0);
                        }

                        if passed == cached_best {
                            let mut last_best = last_best.lock().unwrap();
                            if last_best.is_none()
                                || (passed == last_best.as_ref().unwrap().passed
                                    && t >= last_best.as_ref().unwrap().t)
                            {
                                *last_best = Some(Best{t, p, found, passed, needed, failure});
                            }
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
