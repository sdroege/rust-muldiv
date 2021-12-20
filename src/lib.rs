// Copyright (C) 2016,2017 Sebastian Dröge <sebastian@centricular.com>
//
// Licensed under the MIT license, see the LICENSE file or <http://opensource.org/licenses/MIT>

use std::u128;
use std::u64;

const U64_MAX: u128 = u64::MAX as u128;

// Helper trait to get the upper and lower part of an integer
trait LoHi {
    fn lo(self) -> Self;
    fn hi(self) -> Self;
}

impl LoHi for u128 {
    fn lo(self) -> u128 {
        self & U64_MAX
    }
    fn hi(self) -> u128 {
        self >> 64
    }
}

// Port of gst_util_uint64_scale() and friends from
// https://cgit.freedesktop.org/gstreamer/gstreamer/tree/gst/gstutils.c
// Kindly relicensed to the MIT license by the copyright holders of the C code:
// - Andy Wingo
// - Wim Taymans
// - Tim-Philipp Müller
// - Kipp Cannon
// - Sebastian Dröge

#[derive(Copy, Clone)]
struct U192 {
    pub h: u128,
    pub l: u64,
}

fn u192_correct(mut c: U192, val: u64) -> Option<U192> {
    if val == 0 {
        return Some(c);
    }

    if u64::MAX - c.l < val {
        if c.h == u128::MAX {
            return None;
        }
        c.h += 1;
    }
    c.l = c.l.wrapping_add(val);

    Some(c)
}

fn u128_mul_u64(v: u128, n: u64) -> U192 {
    let vh = v.hi();
    let vl = v.lo();

    let l = vl * (n as u128);
    let h = vh * (n as u128) + l.hi();

    U192 {
        h: h,
        l: l.lo() as u64,
    }
}

fn u192_div_u64(num: U192, denom: u64) -> u128 {
    let r = (num.l as u128) + ((num.h % (denom as u128)) << 64);

    ((num.h / (denom as u128)) << 64) + (r / (denom as u128))
}

fn u128_scale_u64_unchecked(val: u128, num: u64, denom: u64, correct: u64) -> Option<u128> {
    Some(u128_mul_u64(val, num))
        .and_then(|r| u192_correct(r, correct))
        .and_then(|r| {
            if r.h >> 64 >= denom as u128 {
                None
            } else {
                Some(u192_div_u64(r, denom))
            }
        })
}

#[derive(Copy, Clone)]
struct U256 {
    pub h: u128,
    pub l: u128,
}

fn u256_correct(mut c: U256, val: u128) -> Option<U256> {
    if val == 0 {
        return Some(c);
    }

    if u128::MAX - c.l < val {
        if c.h == u128::MAX {
            return None;
        }
        c.h += 1;
    }
    c.l = c.l.wrapping_add(val);

    Some(c)
}

fn u128_mul_u128(v: u128, n: u128) -> U256 {
    // do 256 bits multiply
    //                   nh   nl
    //                *  vh   vl
    //                ----------
    // a0 =              vl * nl
    // a1 =         vl * nh
    // b0 =         vh * nl
    // b1 =  + vh * nh
    //       -------------------
    //        c1h  c1l  c0h  c0l
    //
    // "a0" is optimized away, result is stored directly in c0.  "b1" is
    // optimized away, result is stored directly in c1.
    //

    let mut c0 = v.lo() * n.lo();
    let a1 = v.lo() * n.hi();
    let b0 = v.hi() * n.lo();

    // add the high word of a0 to the low words of a1 and b0 using c1 as
    // scrach space to capture the carry.  the low word of the result becomes
    // the final high word of c0
    let mut c1 = c0.hi() + a1.lo() + b0.lo();

    c0 = (c1.lo() << 64) | c0.lo();

    // add the carry from the result above (found in the high word of c1) and
    // the high words of a1 and b0 to b1, the result is c1.
    c1 = v.hi() * n.hi() + c1.hi() + a1.hi() + b0.hi();

    U256 { h: c1, l: c0 }
}

// based on Hacker's Delight p152

fn u256_div_u128(num: U256, denom: u128) -> u128 {
    assert!(denom > U64_MAX);

    let mut c1 = num.h;
    let mut c0 = num.l;

    // count number of leading zeroes, we know they must be in the high
    // part of denom since denom > G_MAXUINT64.
    let s = (denom.hi() as u64).leading_zeros();

    let v;
    if s > 0 {
        // normalize divisor and dividend
        v = denom << s;
        c1 = (c1 << s) | (c0.hi() >> (64 - s));
        c0 <<= s;
    } else {
        v = denom;
    }

    let mut q1 = c1 / v.hi();
    let mut rhat = c1.wrapping_sub(q1.wrapping_mul(v.hi()));

    let mut cmp1 = (rhat.lo() << 64) | c0.hi();
    let mut cmp2 = q1.wrapping_mul(v.lo());

    while (q1 >> 64 != 0) || cmp2 > cmp1 {
        q1 -= 1;
        rhat += v.hi();
        if rhat.hi() != 0 {
            break;
        }

        cmp1 = (rhat.lo() << 64) | cmp1.lo();
        cmp2 -= v.lo();
    }

    c1 = (c1.lo() << 64) | c0.hi();
    c1 = c1.wrapping_sub(q1.wrapping_mul(v));

    let mut q0 = c1 / v.hi();

    rhat = c1.wrapping_sub(q0.wrapping_mul(v.hi()));

    cmp1 = (rhat.lo() << 64) | c0.lo();
    cmp2 = q0.wrapping_mul(v.lo());

    while q0.hi() != 0 || cmp2 > cmp1 {
        q0 -= 1;
        rhat += v.hi();
        if rhat.hi() != 0 {
            break;
        }

        cmp1 = (rhat.lo() << 64) | cmp1.lo();
        cmp2 -= v.lo();
    }

    q0 = ((q0.hi() + q1.lo()) << 64) | q0.lo();

    q0
}

fn u128_scale_u128_unchecked(val: u128, num: u128, denom: u128, correct: u128) -> Option<u128> {
    Some(u128_mul_u128(val, num))
        .and_then(|r| u256_correct(r, correct))
        .and_then(|r| {
            if r.h >= denom as u128 {
                None
            } else {
                Some(u256_div_u128(r, denom))
            }
        })
}

pub fn u128_scale(val: u128, num: u128, denom: u128, correct: u128) -> Option<u128> {
    assert_ne!(denom, 0);
    assert!(correct <= denom);

    if num == 0 {
        return Some(0);
    }

    if num == denom {
        return Some(val);
    }

    // denom is low --> try to use 192 bit muldiv
    if denom <= U64_MAX {
        // val and num low --> use 128 bit muldiv
        if val <= U64_MAX && num <= U64_MAX {
            return Some((val * num + correct) / denom);
        }

        // num is low --> use 192 bit muldiv
        if num <= U64_MAX {
            return u128_scale_u64_unchecked(val, num as u64, denom as u64, correct as u64);
        }

        // num is high but val is low --> swap and use 192-bit muldiv
        if val <= U64_MAX {
            return u128_scale_u64_unchecked(num, val as u64, denom as u64, correct as u64);
        }
    }

    // val is high and num is high --> use 256-bit muldiv
    u128_scale_u128_unchecked(val, num, denom, correct)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u192_correct_h() {
        let c = U192 { h: 100, l: 200 };
        let val = u64::MAX - c.l + 1;
        let result = u192_correct(c, val).unwrap();
        assert_eq!(result.h, 101);
        assert_eq!(result.l, 0);
    }

    #[test]
    fn u192_correct_l() {
        let c = U192 { h: 100, l: 200 };
        let val = 300u64;
        let result = u192_correct(c, val).unwrap();
        assert_eq!(result.h, 100);
        assert_eq!(result.l, 500);
    }

    #[test]
    #[should_panic]
    fn u192_correct_none() {
        let c = U192 {
            h: u128::MAX,
            l: 200,
        };
        let val = u64::MAX - c.l + 1;
        u192_correct(c, val).unwrap();
    }

    #[test]
    fn u128_mul_u64_max() {
        let v = u128::MAX;
        let n = u64::MAX;
        let result = u128_mul_u64(v, n);
        assert_eq!(result.h, u128::MAX - U64_MAX - 1);
        assert_eq!(result.l, 1);
    }

    #[test]
    fn u192_div_u64_max() {
        let v = u128::MAX;
        let n = u64::MAX;
        let num = u128_mul_u64(v, n);
        let result = u192_div_u64(num, n);
        assert_eq!(result, v);
    }

    #[test]
    fn u128_scale_u64_unchecked_some() {
        let val = u128::MAX;
        let num = u64::MAX;
        let denom = u64::MAX;
        let correct = 0u64;
        let result = u128_scale_u64_unchecked(val, num, denom, correct).unwrap();
        assert_eq!(result, u128::MAX);
    }

    #[test]
    #[should_panic]
    fn u128_scale_u64_unchecked_none_0() {
        let val = u128::MAX;
        let num = u64::MAX - 1;
        let denom = u64::MAX - 2;
        let correct = u64::MAX;
        u128_scale_u64_unchecked(val, num, denom, correct).unwrap();
    }

    #[test]
    #[should_panic]
    fn u128_scale_u64_unchecked_none_1() {
        let val = u128::MAX;
        let num = u64::MAX;
        let denom = u64::MAX - 1;
        let correct = 0u64;
        u128_scale_u64_unchecked(val, num, denom, correct).unwrap();
    }

    #[test]
    fn u256_correct_h() {
        let c = U256 { h: 100, l: 200 };
        let val = u128::MAX - c.l + 1;
        let result = u256_correct(c, val).unwrap();
        assert_eq!(result.h, 101);
        assert_eq!(result.l, 0);
    }

    #[test]
    fn u256_correct_l() {
        let c = U256 { h: 100, l: 200 };
        let val = 300u128;
        let result = u256_correct(c, val).unwrap();
        assert_eq!(result.h, 100);
        assert_eq!(result.l, 500);
    }

    #[test]
    #[should_panic]
    fn u256_correct_none() {
        let c = U256 {
            h: u128::MAX,
            l: 200,
        };
        let val = u128::MAX - c.l + 1;
        u256_correct(c, val).unwrap();
    }

    #[test]
    fn u128_mul_u128_max() {
        let v = u128::MAX;
        let n = u128::MAX;
        let result = u128_mul_u128(v, n);
        assert_eq!(result.h, u128::MAX - 1);
        assert_eq!(result.l, 1);
    }

    #[test]
    fn u256_div_u128_max() {
        let v = u128::MAX;
        let n = u128::MAX;
        let num = u128_mul_u128(v, n);
        let result = u256_div_u128(num, n);
        assert_eq!(result, v);
    }

    #[test]
    fn u128_scale_u128_unchecked_some() {
        let val = u128::MAX;
        let num = u128::MAX;
        let denom = u128::MAX;
        let correct = 0u128;
        let result = u128_scale_u128_unchecked(val, num, denom, correct).unwrap();
        assert_eq!(result, u128::MAX);
    }

    #[test]
    #[should_panic]
    fn u128_scale_u128_unchecked_none_0() {
        let val = u128::MAX;
        let num = u128::MAX - 1;
        let denom = u128::MAX - 2;
        let correct = u128::MAX;
        u128_scale_u128_unchecked(val, num, denom, correct).unwrap();
    }

    #[test]
    #[should_panic]
    fn u128_scale_u128_unchecked_none_1() {
        let val = u128::MAX;
        let num = u128::MAX;
        let denom = u128::MAX - 1;
        let correct = 0u128;
        u128_scale_u128_unchecked(val, num, denom, correct).unwrap();
    }

    #[test]
    fn u128_scale_for_u128_some() {
        let val = u128::MAX;
        let num = u128::MAX;
        let denom = u128::MAX;
        let correct = 0u128;
        let result = u128_scale(val, num, denom, correct).unwrap();
        assert_eq!(result, u128::MAX);
    }

    #[test]
    #[should_panic]
    fn u128_scale_for_u128_none_0() {
        let val = u128::MAX;
        let num = u128::MAX - 1;
        let denom = u128::MAX - 2;
        let correct = u128::MAX;
        u128_scale(val, num, denom, correct).unwrap();
    }

    #[test]
    #[should_panic]
    fn u128_scale_for_u128_none_1() {
        let val = u128::MAX;
        let num = u128::MAX;
        let denom = u128::MAX - 1;
        let correct = 0u128;
        u128_scale(val, num, denom, correct).unwrap();
    }

    #[test]
    fn u128_scale_for_u64_some() {
        let val = u128::MAX;
        let num = u64::MAX as u128;
        let denom = u64::MAX as u128;
        let correct = 0u128;
        let result = u128_scale(val, num, denom, correct).unwrap();
        assert_eq!(result, u128::MAX);
    }

    #[test]
    #[should_panic]
    fn u128_scale_for_u64_none_0() {
        let val = u128::MAX;
        let num = u64::MAX as u128 - 1;
        let denom = u64::MAX as u128 - 2;
        let correct = u64::MAX as u128;
        u128_scale(val, num, denom, correct).unwrap();
    }

    #[test]
    #[should_panic]
    fn u128_scale_for_u64_none_1() {
        let val = u128::MAX;
        let num = u64::MAX as u128;
        let denom = u64::MAX as u128 - 1;
        let correct = 0u128;
        u128_scale(val, num, denom, correct).unwrap();
    }
}
