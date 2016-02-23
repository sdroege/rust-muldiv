use std::u64;
use std::mem::uninitialized;

struct U128 { pub h: u64, pub l: u64 }

fn u128_correct(mut c: U128, val: u64) -> Option<U128> {
    if val == 0 { return Some(c); }

    if u64::MAX - c.l < val {
        if c.h == u64::MAX { return None; }
        c.h += 1;
    }
    c.l = c.l.wrapping_add(val);

    Some(c)
}

fn u64_mul_u64(v: u64, n: u64) -> U128 {
    unsafe {
        let mut r: U128 = uninitialized();
        asm!("mulq $3"
        : "={rax}"(r.l), "={rdx}"(r.h)
        : "{rax}"(v), "r"(n)
        : "rax", "rdx");

        r
    }
}

fn u128_div_u64(num: U128, denom: u64) -> u64 {
    unsafe {
        let r: u64;
        asm!("divq $3"
        : "={rax}"(r)
        : "{rax}"(num.l), "{rdx}"(num.h), "r"(denom)
        : "rax", "rdx");

        r
    }
}

fn u64_scale_u64_unchecked(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
    Some(u64_mul_u64(val, num))
        .and_then(|r| u128_correct(r, correct))
        .and_then(|r| if r.h >= denom as u64 { None } else { Some(u128_div_u64(r, denom)) })
}

pub fn u64_scale(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
    assert!(denom != 0);
    assert!(correct <= denom);

    if num == 0 { return Some(0); }

    if num == denom { return Some(val); }

    return u64_scale_u64_unchecked(val, num, denom, correct);
}
