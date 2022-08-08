

/// A crc32c type with GF(2^32) operations
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(non_camel_case_types)]
#[repr(transparent)]
pub struct crc32c(pub u32);

impl crc32c {
    pub const ZERO: crc32c = crc32c(0);
    pub const ONE: crc32c = crc32c(1);

    /// The irreducible polynomial defining the field
    pub const P: u64 = 0x1000000af;

    /// A generator in the field
    pub const G: crc32c = crc32c(0x00000002);

    /// Barret's constant
    const B: u32 = {
        let mut a = 1u128 << 64;
        let b = Self::P as u128;
        let mut x = 0u128;
        while a.leading_zeros() <= b.leading_zeros() {
            x ^= 1 << (b.leading_zeros()-a.leading_zeros());
            a ^= b << (b.leading_zeros()-a.leading_zeros());
        }
        x as u32
    };
}

impl core::fmt::Display for crc32c {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{:08x}", self.0)
    }
}

impl<'a> core::iter::FromIterator<&'a [u8]> for crc32c {
    fn from_iter<T: IntoIterator<Item=&'a [u8]>>(iter: T) -> Self {
        let mut crc = 0;
        for x in iter {
            crc = ::crc32c::crc32c_append(crc, x);
        }
        crc32c(crc)
    }
}

// add/sub = xor

impl core::ops::BitXorAssign for crc32c {
    fn bitxor_assign(&mut self, other: crc32c) {
        self.0 ^= other.0
    }
}

impl core::ops::AddAssign for crc32c {
    fn add_assign(&mut self, other: crc32c) {
        self.0 ^= other.0
    }
}

impl core::ops::SubAssign for crc32c {
    fn sub_assign(&mut self, other: crc32c) {
        self.0 ^= other.0
    }
}

impl core::ops::BitXor for crc32c {
    type Output = crc32c;
    fn bitxor(mut self, other: crc32c) -> crc32c {
        self ^= other;
        self
    }
}

impl core::ops::Add for crc32c {
    type Output = crc32c;
    fn add(mut self, other: crc32c) -> crc32c {
        self += other;
        self
    }
}

impl core::ops::Sub for crc32c {
    type Output = crc32c;
    fn sub(mut self, other: crc32c) -> crc32c {
        self -= other;
        self
    }
}

// multiplication = multiplication over GF(2^32)

fn p32_mul(a: u32, b: u32) -> (u32, u32) {
    let mut lo = 0;
    let mut hi = 0;
    for i in 0..32 {
        let mask = (((a as i32) << (31-i)) >> 31) as u32;
        lo ^= mask & (b << i);
        hi ^= mask & (b >> (31-i));
    }
    (lo, hi >> 1)
}

impl core::ops::MulAssign for crc32c {
    fn mul_assign(&mut self, other: crc32c) {
        // via Barret reduction
        let (lo, hi) = p32_mul(self.0, other.0);
        self.0 = lo ^ p32_mul(p32_mul(hi, Self::B).1 ^ hi, Self::P as u32).0;
    }
}

impl crc32c {
    fn pow(mut self, mut pow: u32) -> Self {
        let mut x = crc32c::ONE;
        loop {
            if pow & 1 != 0 {
                x *= self;
            }

            pow >>= 1;
            if pow == 0 {
                return x;
            }
            self *= self;
        }
    }
}

impl core::ops::DivAssign for crc32c {
    fn div_assign(&mut self, other: crc32c) {
        assert_ne!(other, crc32c::ZERO);
        *self *= other.pow(u32::MAX-1);
    }
}

impl core::ops::Mul for crc32c {
    type Output = crc32c;
    fn mul(mut self, other: crc32c) -> crc32c {
        self *= other;
        self
    }
}

impl core::ops::Div for crc32c {
    type Output = crc32c;
    fn div(mut self, other: crc32c) -> crc32c {
        self /= other;
        self
    }
}


// some quick tests
#[cfg(test)]
mod test {
    use super::*;
    const XS: &[crc32c] = &[
        crc32c(0x00000001),
        crc32c(0x00000002),
        crc32c(0x80000000),
        crc32c(0x11111111),
        crc32c(0x22222222),
        crc32c(0x33333333),
        crc32c(0xffffffff),
        crc32c(0xffff0000),
        crc32c(0xffffff00),
    ];

    #[test]
    fn test_algebra_add_sub() {
        for a in XS.iter().copied() {
            for b in XS.iter().copied() {
                assert_eq!(
                    (a+b)-b,
                    a,
                    "(a+b)-b = a"
                );
            }
        }
    }

    #[test]
    fn test_algebra_recip() {
        for a in XS.iter().copied() {
            assert_eq!(
                a*(crc32c::ONE/a),
                crc32c::ONE,
                "a*(1/a) = 1"
            );
        }
    }

    #[test]
    fn test_algebra_mul_div() {
        for a in XS.iter().copied() {
            for b in XS.iter().copied() {
                assert_eq!(
                    (a*b)/b,
                    a,
                    "(a*b)/b = a"
                );
            }
        }
    }

    #[test]
    fn test_algebra_distributive() {
        for a in XS.iter().copied() {
            for b in XS.iter().copied() {
                for c in XS.iter().copied() {
                    assert_eq!(
                        a*(b+c),
                        a*b + a*c,
                        "a*(b+c) = a*b + a*c"
                    );
                }
            }
        }
    }
}

