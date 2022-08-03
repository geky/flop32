
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
