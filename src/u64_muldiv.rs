use std::u32;
use std::u64;

const U32_MAX: u64 = u32::MAX as u64;

// Helper trait to get the upper and lower part of an integer
trait LoHi {
    fn lo(self) -> Self;
    fn hi(self) -> Self;
}

impl LoHi for u64 {
    fn lo(self) -> u64 {
        self & U32_MAX
    }
    fn hi(self) -> u64 {
        self >> 32
    }
}

// Port of gst_util_uint64_scale() and friends from
// https://cgit.freedesktop.org/gstreamer/gstreamer/tree/gst/gstutils.c

#[derive(Copy, Clone)]
struct U96 {
    pub h: u64,
    pub l: u32,
}

fn u96_correct(mut c: U96, val: u32) -> Option<U96> {
    if val == 0 {
        return Some(c);
    }

    if u32::MAX - c.l < val {
        if c.h == u64::MAX {
            return None;
        }
        c.h += 1;
    }
    c.l = c.l.wrapping_add(val);

    Some(c)
}

fn u64_mul_u32(v: u64, n: u32) -> U96 {
    let vh = v.hi();
    let vl = v.lo();

    let l = vl * (n as u64);
    let h = vh * (n as u64) + l.hi();

    U96 {
        h: h,
        l: l.lo() as u32,
    }
}

fn u96_div_u32(num: U96, denom: u32) -> u64 {
    let r = (num.l as u64) + ((num.h % (denom as u64)) << 32);

    ((num.h / (denom as u64)) << 32) + (r / (denom as u64))
}

fn u64_scale_u32_unchecked(val: u64, num: u32, denom: u32, correct: u32) -> Option<u64> {
    Some(u64_mul_u32(val, num))
        .and_then(|r| u96_correct(r, correct))
        .and_then(|r| if r.h >> 32 >= denom as u64 {
            None
        } else {
            Some(u96_div_u32(r, denom))
        })
}

#[derive(Copy, Clone)]
struct U128 {
    pub h: u64,
    pub l: u64,
}

fn u128_correct(mut c: U128, val: u64) -> Option<U128> {
    if val == 0 {
        return Some(c);
    }

    if u64::MAX - c.l < val {
        if c.h == u64::MAX {
            return None;
        }
        c.h += 1;
    }
    c.l = c.l.wrapping_add(val);

    Some(c)
}

fn u64_mul_u64(v: u64, n: u64) -> U128 {
    // do 128 bits multiply
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

    c0 = (c1.lo() << 32) | c0.lo();

    // add the carry from the result above (found in the high word of c1) and
    // the high words of a1 and b0 to b1, the result is c1.
    c1 = v.hi() * n.hi() + c1.hi() + a1.hi() + b0.hi();

    U128 { h: c1, l: c0 }
}

// based on Hacker's Delight p152

fn u128_div_u64(num: U128, denom: u64) -> u64 {
    assert!(denom > U32_MAX);

    let mut c1 = num.h;
    let mut c0 = num.l;

    // count number of leading zeroes, we know they must be in the high
    // part of denom since denom > G_MAXUINT32.
    let s = (denom.hi() as u32).leading_zeros();

    let v;
    if s > 0 {
        // normalize divisor and dividend
        v = denom << s;
        c1 = (c1 << s) | (c0.hi() >> (32 - s));
        c0 <<= s;
    } else {
        v = denom;
    }

    let mut q1 = c1 / v.hi();
    let mut rhat = c1.wrapping_sub(q1.wrapping_mul(v.hi()));

    let mut cmp1 = (rhat.lo() << 32) | c0.hi();
    let mut cmp2 = q1.wrapping_mul(v.lo());

    while (q1 >> 32 != 0) || cmp2 > cmp1 {
        q1 -= 1;
        rhat += v.hi();
        if rhat.hi() != 0 {
            break;
        }

        cmp1 = (rhat.lo() << 32) | cmp1.lo();
        cmp2 -= v.lo();
    }

    c1 = (c1.lo() << 32) | c0.hi();
    c1 = c1.wrapping_sub(q1.wrapping_mul(v));

    let mut q0 = c1 / v.hi();

    rhat = c1.wrapping_sub(q0.wrapping_mul(v.hi()));

    cmp1 = (rhat.lo() << 32) | c0.lo();
    cmp2 = q0.wrapping_mul(v.lo());

    while q0.hi() != 0 || cmp2 > cmp1 {
        q0 -= 1;
        rhat += v.hi();
        if rhat.hi() != 0 {
            break;
        }

        cmp1 = (rhat.lo() << 32) | cmp1.lo();
        cmp2 -= v.lo();
    }

    q0 = ((q0.hi() + q1.lo()) << 32) | q0.lo();

    q0
}

fn u64_scale_u64_unchecked(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
    Some(u64_mul_u64(val, num))
        .and_then(|r| u128_correct(r, correct))
        .and_then(|r| if r.h >= denom as u64 {
            None
        } else {
            Some(u128_div_u64(r, denom))
        })
}

pub fn u64_scale(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
    assert_ne!(denom, 0);
    assert!(correct <= denom);

    if num == 0 {
        return Some(0);
    }

    if num == denom {
        return Some(val);
    }

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
    u64_scale_u64_unchecked(val, num, denom, correct)
}
