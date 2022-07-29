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

const BLOCK_SIZE: usize = 8;
const BLOCK_NULLCRC: u32 = crc32c(0, &[0; BLOCK_SIZE]);


// parity stuff, assumes last block is parity block
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


fn parity_check<B: AsRef<[u8]>>(blocks: &[B]) -> u32 {
    debug_assert!(blocks.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));

    let mut check = if blocks.len() & 1 != 0 { BLOCK_NULLCRC } else { 0 };
    for b in blocks.iter().map(|b| b.as_ref()) {
        check ^= crc32c(0, b);
    }
    check
}

fn find_inflection<B1: AsRef<[u8]>, B2: AsRef<[u8]>>(
    a: &[B1],
    b: &[B2],
) -> Option<(usize, bool)> {
    debug_assert!(a.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));
    debug_assert!(b.iter().all(|b| b.as_ref().len() == BLOCK_SIZE));
    debug_assert_eq!(a.len(), b.len());

    let a_check = parity_check(a);
    let b_check = parity_check(b);
    // no errors?
    if a_check == 0 && b_check == 0 {
        return None
    }

    // at some point this must be true:
    //
    // ax = Σai + Σbi
    //      i<x   i>x
    //
    let mut a_lparity = 0;
    let mut b_lparity = 0;
    let mut a_rparity = a_check;
    let mut b_rparity = b_check;

    for i in 0..a.len() {
        let a_crc = crc32c(0, a[i].as_ref());
        let b_crc = crc32c(0, b[i].as_ref());
        a_rparity ^= a_crc;
        b_rparity ^= b_crc;

        let a_inflection = a_crc == a_lparity ^ b_rparity;
        let b_inflection = b_crc == b_lparity ^ a_rparity;
        if a_inflection {
            return Some((i+1, b_inflection));
        }

        a_lparity ^= a_crc;
        b_lparity ^= b_crc;
    }

    unreachable!();
}


fn main() {
    fn hex(xs: &[u8]) -> String {
        xs.iter()
            .map(|x| format!("{:02x}", x))
            .collect()
    }

    fn blocks<B: AsRef<[u8]>>(blocks: &[B]) -> String {
        format!("{} ({:08x})",
            blocks.iter()
                .map(|b| hex(b.as_ref()))
                .collect::<Vec<_>>()
                .join(" "),
            parity_check(blocks)
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

    let mut b = [
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [11,11,11,11,11,11,11,11],
        [ 0, 0, 0, 0, 0, 0, 0, 0],
    ];
    mkparity(&mut b);

    println!("before:");
    println!("a = {}", blocks(&a));
    assert_eq!(parity_check(&a), 0);
    println!("b = {}", blocks(&b));
    assert_eq!(parity_check(&b), 0);
    println!("inflection = {:?}", find_inflection(&a, &b));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);

    println!("clean swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(parity_check(&a_), 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(parity_check(&b_), 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_));
    
    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2].fill(0xff);

    println!("dirty a swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(parity_check(&a_), 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(parity_check(&b_), 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_));

    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    a_[2] = b_[2];

    println!("half swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(parity_check(&a_), 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(parity_check(&b_), 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_));
    
    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);
    b_[2].fill(0xff);

    println!("dirty b swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(parity_check(&a_), 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(parity_check(&b_), 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_));
    
    let mut a_ = a;
    let mut b_ = b;
    std::mem::swap(&mut a_[0], &mut b_[0]);
    std::mem::swap(&mut a_[1], &mut b_[1]);
    std::mem::swap(&mut a_[2], &mut b_[2]);

    println!("clean swap:");
    println!("a = {}", blocks(&a_));
    assert_ne!(parity_check(&a_), 0);
    println!("b = {}", blocks(&b_));
    assert_ne!(parity_check(&b_), 0);
    println!("inflection = {:?}", find_inflection(&a_, &b_));
}
