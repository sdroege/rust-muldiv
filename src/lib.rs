#![crate_name = "muldiv"]

use std::u8;
use std::u16;
use std::u32;
use std::u64;

// Port of gst_util_uint64_scale() and friends from
// https://cgit.freedesktop.org/gstreamer/gstreamer/tree/gst/gstutils.c

const U32_MAX: u64 = u32::MAX as u64;

struct U96 { pub h: u64, pub l: u32 }

fn u96_correct(mut c: U96, val: u32) -> Option<U96> {
    if val == 0 { return Some(c); }

    if u32::MAX - c.l < val {
        if c.h == u64::MAX { return None; }
        c.h += 1;
    }
    c.l = c.l.wrapping_add(val);

    Some(c)
}

fn u64_mul_u32(v: u64, n: u32) -> U96 {
    let vh = v >> 32;
    let vl = v & U32_MAX;

    let l = vl * (n as u64);
    let h = vh * (n as u64) + (l >> 32);

    U96 {h: h, l: (l & U32_MAX) as u32}
}

fn u96_div_u32(num: U96, denom: u32) -> u64 {
    let r = (num.l as u64) + ((num.h % (denom as u64)) << 32);

    ((num.h / (denom as u64)) << 32) + (r / (denom as u64))
}

fn u64_scale_u32_unchecked(val: u64, num: u32, denom: u32, correct: u32) -> Option<u64> {
    Some(u64_mul_u32(val, num))
        .and_then(|r| u96_correct(r, correct))
        .and_then(|r| if r.h >> 32 >= denom as u64 { None } else { Some(u96_div_u32(r, denom)) })
}

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
    /* do 128 bits multiply
     *                   nh   nl
     *                *  vh   vl
     *                ----------
     * a0 =              vl * nl
     * a1 =         vl * nh
     * b0 =         vh * nl
     * b1 =  + vh * nh
     *       -------------------
     *        c1h  c1l  c0h  c0l
     *
     * "a0" is optimized away, result is stored directly in c0.  "b1" is
     * optimized away, result is stored directly in c1.
     */

    let mut c0 = (v & U32_MAX) * (n & U32_MAX);
    let a1 = (v & U32_MAX) * (n >> 32);
    let b0 = (v >> 32) * (n & U32_MAX);

    /* add the high word of a0 to the low words of a1 and b0 using c1 as
     * scrach space to capture the carry.  the low word of the result becomes
     * the final high word of c0 */
    let mut c1 = (c0 >> 32) + (a1 & U32_MAX) + (b0 & U32_MAX);

    c0 = ((c1 & U32_MAX) << 32) | (c0 & U32_MAX);

    /* add the carry from the result above (found in the high word of c1) and
     * the high words of a1 and b0 to b1, the result is c1. */
    c1 = (v >> 32) * (n >> 32) + (c1 >> 32) + (a1 >> 32) + (b0 >> 32);

    U128 {h: c1, l: c0}
}

/* based on Hacker's Delight p152 */

// count leading zeroes
fn u32_clz(val: u32) -> u32 {
    let mut s = val | (val >> 1);
    s |= s >> 2;
    s |= s >> 4;
    s |= s >> 8;
    s = !(s | (s >> 16));
    s = s - ((s >> 1) & 0x55555555);
    s = (s & 0x33333333) + ((s >> 2) & 0x33333333);
    s = (s + (s >> 4)) & 0x0f0f0f0f;
    s += s >> 8;
    s = (s + (s >> 16)) & 0x3f;

    return s;
}

fn u128_div_u64(num: U128, denom: u64) -> u64 {
    assert!(denom > U32_MAX);

    let mut c1 = num.h;
    let mut c0 = num.l;

    /* count number of leading zeroes, we know they must be in the high
     * part of denom since denom > G_MAXUINT32. */
    let s = u32_clz((denom >> 32) as u32);

    let v;
    if s > 0 {
        /* normalize divisor and dividend */
        v = denom << s;
        c1 = (c1 << s) | ((c0 >> 32) >> (32 - s));
        c0 <<= s;
    } else {
        v = denom;
    }

    let mut q1 = c1 / (v >> 32);
    let mut rhat = c1.wrapping_sub(q1.wrapping_mul(v >> 32));

    let mut cmp1 = ((rhat & U32_MAX) << 32) | (c0 >> 32);
    let mut cmp2 = q1.wrapping_mul(v & U32_MAX);

    while (q1 >> 32 != 0) || cmp2 > cmp1 {
        q1 -= 1;
        rhat += v >> 32;
        if (rhat >> 32) != 0 { break; }

        cmp1 = ((rhat & U32_MAX) << 32) | (cmp1 & U32_MAX);
        cmp2 -= v & U32_MAX;
    }

    c1 = ((c1 & U32_MAX) << 32) | (c0 >> 32);
    c1 = c1.wrapping_sub(q1.wrapping_mul(v));

    let mut q0 = c1 / (v >> 32);

    rhat = c1.wrapping_sub(q0.wrapping_mul(v >> 32));

    cmp1 = ((rhat & U32_MAX) << 32) | (c0 & U32_MAX);
    cmp2 = q0.wrapping_mul(v & U32_MAX);

    while (q0 >> 32 != 0) || cmp2 > cmp1 {
        q0 -= 1;
        rhat += v >> 32;
        if (rhat >> 32) != 0 { break; }

        cmp1 = ((rhat & U32_MAX) << 32) | (cmp1 & U32_MAX);
        cmp2 -= v & U32_MAX;
    }

    q0 = (((q0 >> 32) + (q1 & U32_MAX)) << 32) | (q0 & U32_MAX);

    return q0;
}

fn u64_scale_u64_unchecked(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
    Some(u64_mul_u64(val, num))
        .and_then(|r| u128_correct(r, correct))
        .and_then(|r| if r.h >= denom as u64 { None } else { Some(u128_div_u64(r, denom)) })
}

fn u64_scale(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
    assert!(denom != 0);
    assert!(correct <= denom);

    if num == 0 { return Some(0); }

    if num == denom { return Some(val); }

    // denom is low --> try to use 96 bit muldiv
    if denom <= U32_MAX {
        // val and num low --> use 64 bit muldiv
        if val <= U32_MAX && num <= U32_MAX {
            return Some((val * num + correct) / denom);
        }

        // num is low --> use 96 bit muldiv
        if num <= U32_MAX {
            return u64_scale_u32_unchecked(val, num as u32, denom as u32, correct as u32);
        }

        // num is high but val is low --> swap and use 96-bit muldiv
        if val <= U32_MAX {
            return u64_scale_u32_unchecked(num, val as u32, denom as u32, correct as u32);
        }
    }

    // val is high and num is high --> use 128-bit muldiv
    return u64_scale_u64_unchecked(val, num, denom, correct);
}

pub trait MulDiv<RHS = Self> {
    type Output;

    fn mul_div_floor(self, num: RHS, denom: RHS) -> Self::Output;
    fn mul_div_round(self, num: RHS, denom: RHS) -> Self::Output;
    fn mul_div_ceil(self, num: RHS, denom: RHS) -> Self::Output;
}

impl MulDiv for u64 {
    type Output = Option<u64>;

    fn mul_div_floor(self, num: u64, denom: u64) -> Option<u64> {
        assert!(denom != 0);
        u64_scale(self, num, denom, 0)
    }

    fn mul_div_round(self, num: u64, denom: u64) -> Option<u64> {
        assert!(denom != 0);
        u64_scale(self, num, denom, denom >> 1)
    }

    fn mul_div_ceil(self, num: u64, denom: u64) -> Option<u64> {
        assert!(denom != 0);
        u64_scale(self, num, denom, denom - 1)
    }
}

#[cfg(test)]
mod muldiv_u64_tests {
    use super::*;
    use std::u32;
    use std::u64;

    extern crate num;
    extern crate rand;

    use self::num::bigint::ToBigUint;
    use self::rand::thread_rng;
    use self::rand::Rng;

    #[test]
    fn scale_floor() {
        assert_eq!(Some(1), 1u64.mul_div_floor(1, 1));

        assert_eq!(Some(100), 10u64.mul_div_floor(10, 1));
        assert_eq!(Some(50), 10u64.mul_div_floor(10, 2));

        assert_eq!(Some(0), 0u64.mul_div_floor(10, 2));
        assert_eq!(Some(0), 0u64.mul_div_floor(0, 2));

        assert_eq!(Some((u32::MAX as u64) * 5), (u32::MAX as u64).mul_div_floor(5, 1));
        assert_eq!(Some((u32::MAX as u64) * 5), (u32::MAX as u64).mul_div_floor(10, 2));

        assert_eq!(Some((u32::MAX as u64) / 5), (u32::MAX as u64).mul_div_floor(1, 5));
        assert_eq!(Some((u32::MAX as u64) / 5), (u32::MAX as u64).mul_div_floor(2, 10));

        // not quite overflow
        assert_eq!(Some(0xe666666666666664), (u64::MAX - 1).mul_div_floor(9, 10));
        assert_eq!(Some(0xfffffffefffffffd), (u64::MAX - 1).mul_div_floor(u32::MAX as u64 - 1, u32::MAX as u64));
        assert_eq!(Some(0xfffffffeffffff9a), (u64::MAX - 100).mul_div_floor(u32::MAX as u64 - 1, u32::MAX as u64));

        assert_eq!(Some(0xfffffffffffffffd), (u64::MAX - 1).mul_div_floor(u64::MAX - 1, u64::MAX));
        assert_eq!(Some(0xffffffffffffff9a), (u64::MAX - 100).mul_div_floor(u64::MAX - 1, u64::MAX));

        // overflow
        assert_eq!(None, (u64::MAX - 1).mul_div_floor(10, 1));
        assert_eq!(None, (u64::MAX - 1).mul_div_floor(u64::MAX, 1));
    }

    #[test]
    fn scale_floor_rng() {
        let mut rng = thread_rng();

        // 64 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = (val as u64).mul_div_floor(num as u64, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 96 bit scaling
        for _ in 0..10000 {
            let val: u64 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_floor(num as u64, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 96 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u64 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = (val as u64).mul_div_floor(num, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 128 bit scaling
        for _ in 0..10000 {
            let val: u64 = rng.gen();
            let num: u64 = rng.gen();
            let den: u64 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_floor(num, den);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }
    }


    #[test]
    fn scale_round_rng() {
        let mut rng = thread_rng();

        // 64 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = (val as u64).mul_div_round(num as u64, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() >> 1)) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 96 bit scaling
        for _ in 0..10000 {
            let val: u64 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_round(num as u64, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() >> 1)) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 96 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u64 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = (val as u64).mul_div_round(num, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() >> 1)) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 128 bit scaling
        for _ in 0..10000 {
            let val: u64 = rng.gen();
            let num: u64 = rng.gen();
            let den: u64 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_round(num, den);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() >> 1)) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }
    }

    #[test]
    fn scale_ceil_rng() {
        let mut rng = thread_rng();

        // 64 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = (val as u64).mul_div_ceil(num as u64, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() - 1.to_biguint().unwrap())) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 96 bit scaling
        for _ in 0..10000 {
            let val: u64 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_ceil(num as u64, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() - 1.to_biguint().unwrap())) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 96 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u64 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = (val as u64).mul_div_ceil(num, den as u64);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() - 1.to_biguint().unwrap())) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }

        // 128 bit scaling
        for _ in 0..10000 {
            let val: u64 = rng.gen();
            let num: u64 = rng.gen();
            let den: u64 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_ceil(num, den);

            let val_big = val.to_biguint().unwrap();
            let num_big = num.to_biguint().unwrap();
            let den_big = den.to_biguint().unwrap();
            let expected = (val_big * num_big + (den_big.clone() - 1.to_biguint().unwrap())) / den_big;

            if expected > u64::MAX.to_biguint().unwrap() {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap().to_biguint().unwrap() == expected, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }
    }

}

/* FIXME: Having this here breaks "1u64.mul_div_floor(1, 1)" without a i32 implementation
 * as there is no unambiguous choice, resulting in i32 to be used

fn u64_scale_u32(val: u64, num: u32, denom: u32, correct: u32) -> Option<u64> {
    assert!(denom != 0);
    assert!(correct <= denom);

    if num == 0 { return Some(0); }

    if num == denom { return Some(val); }

    // val and num low --> use 64 bit muldiv
    if val <= U32_MAX {
        return Some((val * (num as u64) + (correct as u64)) / (denom as u64));
    }

    return u64_scale_u32_unchecked(val, num, denom, correct);
}

impl MulDiv<u32> for u64 {
    fn mul_div_floor(self, num: u32, denom: u32) -> Option<u64> {
        assert!(denom != 0);
        u64_scale_u32(self, num, denom, 0)
    }

    fn mul_div_round(self, num: u32, denom: u32) -> Option<u64> {
        assert!(denom != 0);
        u64_scale_u32(self, num, denom, denom >> 1)
    }

    fn mul_div_ceil(self, num: u32, denom: u32) -> Option<u64> {
        assert!(denom != 0);
        u64_scale_u32(self, num, denom, denom - 1)
    }
}

// FIXME: Workaround for integer literal defaulting rules
impl MulDiv<i32> for u64 {
    fn mul_div_floor(self, num: i32, denom: i32) -> Option<u64> {
        assert!(denom != 0);
        assert!(num >= 0 && denom >= 0);

        u64_scale_u32(self, num as u32, denom as u32, 0)
    }

    fn mul_div_round(self, num: i32, denom: i32) -> Option<u64> {
        assert!(denom != 0);
        assert!(num >= 0 && denom >= 0);

        u64_scale_u32(self, num as u32, denom as u32, (denom as u32) >> 1)
    }

    fn mul_div_ceil(self, num: i32, denom: i32) -> Option<u64> {
        assert!(denom != 0);
        assert!(num >= 0 && denom >= 0);

        u64_scale_u32(self, num as u32, denom as u32, (denom as u32) - 1)
    }
}
*/

impl MulDiv for u32 {
    type Output = Option<u32>;

    fn mul_div_floor(self, num: u32, denom: u32) -> Option<u32> {
        assert!(denom != 0);
        let r = ((self as u64) * (num as u64)) / (denom as u64);
        if r > U32_MAX { None } else { Some(r as u32) }
    }

    fn mul_div_round(self, num: u32, denom: u32) -> Option<u32> {
        assert!(denom != 0);
        let r = ((self as u64) * (num as u64) + ((denom >> 1) as u64)) / (denom as u64);
        if r > U32_MAX { None } else { Some(r as u32) }
    }

    fn mul_div_ceil(self, num: u32, denom: u32) -> Option<u32> {
        assert!(denom != 0);
        let r = ((self as u64) * (num as u64) + ((denom - 1) as u64)) / (denom as u64);
        if r > U32_MAX { None } else { Some(r as u32) }
    }
}

#[cfg(test)]
mod muldiv_u32_tests {
    use super::*;

    extern crate num;
    extern crate rand;

    use self::rand::thread_rng;
    use self::rand::Rng;
    use std::u32;

    #[test]
    fn scale_floor_rng() {
        let mut rng = thread_rng();

        // 64 bit scaling
        for _ in 0..10000 {
            let val: u32 = rng.gen();
            let num: u32 = rng.gen();
            let den: u32 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_floor(num, den);

            let expected = ((val as u64) * (num as u64)) / (den as u64);

            if expected > u32::MAX as u64 {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap() == expected as u32, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }
    }
}

const U16_MAX: u32 = u16::MAX as u32;

impl MulDiv for u16 {
    type Output = Option<u16>;

    fn mul_div_floor(self, num: u16, denom: u16) -> Option<u16> {
        assert!(denom != 0);
        let r = ((self as u32) * (num as u32)) / (denom as u32);
        if r > U16_MAX { None } else { Some(r as u16) }
    }

    fn mul_div_round(self, num: u16, denom: u16) -> Option<u16> {
        assert!(denom != 0);
        let r = ((self as u32) * (num as u32) + ((denom >> 1) as u32)) / (denom as u32);
        if r > U16_MAX { None } else { Some(r as u16) }
    }

    fn mul_div_ceil(self, num: u16, denom: u16) -> Option<u16> {
        assert!(denom != 0);
        let r = ((self as u32) * (num as u32) + ((denom - 1) as u32)) / (denom as u32);
        if r > U16_MAX { None } else { Some(r as u16) }
    }
}

#[cfg(test)]
mod muldiv_u16_tests {
    use super::*;

    extern crate num;
    extern crate rand;

    use self::rand::thread_rng;
    use self::rand::Rng;
    use std::u16;

    #[test]
    fn scale_floor_rng() {
        let mut rng = thread_rng();

        // 32 bit scaling
        for _ in 0..10000 {
            let val: u16 = rng.gen();
            let num: u16 = rng.gen();
            let den: u16 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_floor(num, den);

            let expected = ((val as u32) * (num as u32)) / (den as u32);

            if expected > u16::MAX as u32 {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap() == expected as u16, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }
    }
}

const U8_MAX: u16 = u8::MAX as u16;

impl MulDiv for u8 {
    type Output = Option<u8>;

    fn mul_div_floor(self, num: u8, denom: u8) -> Option<u8> {
        assert!(denom != 0);
        let r = ((self as u16) * (num as u16)) / (denom as u16);
        if r > U8_MAX { None } else { Some(r as u8) }
    }

    fn mul_div_round(self, num: u8, denom: u8) -> Option<u8> {
        assert!(denom != 0);
        let r = ((self as u16) * (num as u16) + ((denom >> 1) as u16)) / (denom as u16);
        if r > U8_MAX { None } else { Some(r as u8) }
    }

    fn mul_div_ceil(self, num: u8, denom: u8) -> Option<u8> {
        assert!(denom != 0);
        let r = ((self as u16) * (num as u16) + ((denom - 1) as u16)) / (denom as u16);
        if r > U8_MAX { None } else { Some(r as u8) }
    }
}

#[cfg(test)]
mod muldiv_u8_tests {
    use super::*;

    extern crate num;
    extern crate rand;

    use self::rand::thread_rng;
    use self::rand::Rng;
    use std::u8;

    #[test]
    fn scale_floor_rng() {
        let mut rng = thread_rng();

        // 16 bit scaling
        for _ in 0..10000 {
            let val: u8 = rng.gen();
            let num: u8 = rng.gen();
            let den: u8 = rng.gen();

            if den == 0 { continue; }

            let res = val.mul_div_floor(num, den);

            let expected = ((val as u16) * (num as u16)) / (den as u16);

            if expected > u8::MAX as u16 {
                assert!(res.is_none(), format!("{} * {} / {}: expected overflow, got {}", val, num, den, res.unwrap()));
            } else {
                assert!(res.is_some(), format!("{} * {} / {}: expected {} but got overflow", val, num, den, expected));
                assert!(res.unwrap() == expected as u8, format!("{} * {} / {}: expected {} but got {}", val, num, den, expected, res.unwrap()));
            }
        }
    }
}

