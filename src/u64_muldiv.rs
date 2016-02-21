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

pub fn u64_scale(val: u64, num: u64, denom: u64, correct: u64) -> Option<u64> {
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

