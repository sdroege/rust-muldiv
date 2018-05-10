// Copyright (C) 2016,2017 Sebastian Dröge <sebastian@centricular.com>
//
// Licensed under the MIT license, see the LICENSE file or <http://opensource.org/licenses/MIT>

//! Provides a trait for numeric types to perform combined multiplication and division with
//! overflow protection.
//!
//! The `MulDiv` trait provides functions for performing combined multiplication and division for
//! numeric types and comes with implementations for all the primitive integer types. Three
//! variants with different rounding characteristics are provided: `mul_div_floor()`,
//! `mul_div_round()` and `mul_div_ceil()`.
//!
//! ## Example
//!
//! ```rust
//! extern crate muldiv;
//! use muldiv::MulDiv;
//! # fn main() {
//! // Calculates 127 * 23 / 42 rounded down
//! let x = 127u8.mul_div_floor(23, 42);
//! # }
//! ```

use std::u8;
use std::u16;
use std::u32;
use std::u64;

use std::i8;
use std::i16;
use std::i32;
use std::i64;

use std::cmp;

/// Trait for calculating `val * num / denom` with different rounding modes and overflow
/// protection.
///
/// Implementations of this trait have to ensure that even if the result of the multiplication does
/// not fit into the type, as long as it would fit after the division the correct result has to be
/// returned instead of `None`. `None` only should be returned if the overall result does not fit
/// into the type.
///
/// This specifically means that e.g. the `u64` implementation must, depending on the arguments, be
/// able to do 128 bit integer multiplication.
pub trait MulDiv<RHS = Self> {
    type Output;

    /// Calculates `floor(val * num / denom)`, i.e. the next integer to the result of the division
    /// with the smaller absolute value.
    ///
    /// ## Example
    ///
    /// ```rust
    /// extern crate muldiv;
    /// use muldiv::MulDiv;
    ///
    /// # fn main() {
    /// // Returns x==Some(6)
    /// let x = 3i8.mul_div_floor(4, 2);
    ///
    /// // Returns x==Some(3)
    /// let x = 5i8.mul_div_floor(2, 3);
    ///
    /// // Returns x==Some(-3)
    /// let x = (-5i8).mul_div_floor(2, 3);
    ///
    /// // Returns x==Some(4)
    /// let x = 3i8.mul_div_floor(3, 2);
    ///
    /// // Returns x==Some(-4)
    /// let x = (-3i8).mul_div_floor(3, 2);
    ///
    /// // Returns x==None
    /// let x = 127i8.mul_div_floor(4, 3);
    /// # }
    /// ```
    fn mul_div_floor(self, num: RHS, denom: RHS) -> Option<Self::Output>;

    /// Calculates `round(val * num / denom)`, i.e. the closest integer to the result of the
    /// division. If both surrounding integers are the same distance, the one with the bigger
    /// absolute value is returned.
    ///
    /// ## Example
    ///
    /// ```rust
    /// extern crate muldiv;
    /// use muldiv::MulDiv;
    ///
    /// # fn main() {
    /// // Returns x==Some(6)
    /// let x = 3i8.mul_div_round(4, 2);
    ///
    /// // Returns x==Some(3)
    /// let x = 5i8.mul_div_round(2, 3);
    ///
    /// // Returns x==Some(-3)
    /// let x = (-5i8).mul_div_round(2, 3);
    ///
    /// // Returns x==Some(5)
    /// let x = 3i8.mul_div_round(3, 2);
    ///
    /// // Returns x==Some(-5)
    /// let x = (-3i8).mul_div_round(3, 2);
    ///
    /// // Returns x==None
    /// let x = 127i8.mul_div_floor(4, 3);
    /// # }
    /// ```
    fn mul_div_round(self, num: RHS, denom: RHS) -> Option<Self::Output>;

    /// Calculates `ceil(val * num / denom)`, i.e. the next integer to the result of the division
    /// with the bigger absolute value.
    ///
    /// ## Example
    ///
    /// ```rust
    /// extern crate muldiv;
    /// use muldiv::MulDiv;
    ///
    /// # fn main() {
    /// // Returns x==Some(6)
    /// let x = 3i8.mul_div_ceil(4, 2);
    ///
    /// // Returns x==Some(4)
    /// let x = 5i8.mul_div_ceil(2, 3);
    ///
    /// // Returns x==Some(-4)
    /// let x = (-5i8).mul_div_ceil(2, 3);
    ///
    /// // Returns x==Some(5)
    /// let x = 3i8.mul_div_ceil(3, 2);
    ///
    /// // Returns x==Some(-5)
    /// let x = (-3i8).mul_div_ceil(3, 2);
    ///
    /// // Returns x==None
    /// let x = (127i8).mul_div_ceil(4, 3);
    /// # }
    /// ```
    fn mul_div_ceil(self, num: RHS, denom: RHS) -> Option<Self::Output>;
}

macro_rules! mul_div_impl_unsigned {
    ($t:ident, $u:ident) => (

    impl MulDiv for $t {
        type Output = $t;

        fn mul_div_floor(self, num: $t, denom: $t) -> Option<$t> {
            assert_ne!(denom, 0);
            let r = ((self as $u) * (num as $u)) / (denom as $u);
            if r > $t::MAX as $u { None } else { Some(r as $t) }
        }

        fn mul_div_round(self, num: $t, denom: $t) -> Option<$t> {
            assert_ne!(denom, 0);
            let r = ((self as $u) * (num as $u) + ((denom >> 1) as $u)) / (denom as $u);
            if r > $t::MAX as $u { None } else { Some(r as $t) }
        }

        fn mul_div_ceil(self, num: $t, denom: $t) -> Option<$t> {
            assert_ne!(denom, 0);
            let r = ((self as $u) * (num as $u) + ((denom - 1) as $u)) / (denom as $u);
            if r > $t::MAX as $u { None } else { Some(r as $t) }
        }
    }
    )
}

#[cfg(test)]
macro_rules! mul_div_impl_unsigned_tests {
    ($t:ident, $u:ident) => (
        use super::*;

        extern crate rand;

        use self::rand::thread_rng;
        use self::rand::Rng;
        use std::$t;

        #[test]
        fn scale_floor_rng() {
            let mut rng = thread_rng();

            for _ in 0..10000 {
                let val: $t = rng.gen();
                let num: $t = rng.gen();
                let den: $t = rng.gen();

                if den == 0 { continue; }

                let res = val.mul_div_floor(num, den);

                let expected = ((val as $u) * (num as $u)) / (den as $u);

                if expected > $t::MAX as $u {
                    assert!(res.is_none(),
                            "{} * {} / {}: expected overflow, got {}",
                                    val, num, den, res.unwrap());
                } else {
                    assert!(res.is_some(),
                            "{} * {} / {}: expected {} but got overflow",
                                    val, num, den, expected);
                    assert_eq!(res.unwrap(), expected as $t,
                            "{} * {} / {}: expected {} but got {}",
                                    val, num, den, expected, res.unwrap());
                }
            }
        }

        #[test]
        fn scale_round_rng() {
            let mut rng = thread_rng();

            for _ in 0..10000 {
                let val: $t = rng.gen();
                let num: $t = rng.gen();
                let den: $t = rng.gen();

                if den == 0 { continue; }

                let res = val.mul_div_round(num, den);

                let mut expected = ((val as $u) * (num as $u)) / (den as $u);
                let expected_rem = ((val as $u) * (num as $u)) % (den as $u);

                if expected_rem >= ((den as $u) + 1) >> 1 { expected = expected + 1 }

                if expected > $t::MAX as $u {
                    assert!(res.is_none(),
                            "{} * {} / {}: expected overflow, got {}",
                                    val, num, den, res.unwrap());
                } else {
                    assert!(res.is_some(),
                            "{} * {} / {}: expected {} but got overflow",
                                    val, num, den, expected);
                    assert_eq!(res.unwrap(), expected as $t,
                            "{} * {} / {}: expected {} but got {}",
                                    val, num, den, expected, res.unwrap());
                }
            }
        }

        #[test]
        fn scale_ceil_rng() {
            let mut rng = thread_rng();

            for _ in 0..10000 {
                let val: $t = rng.gen();
                let num: $t = rng.gen();
                let den: $t = rng.gen();

                if den == 0 { continue; }

                let res = val.mul_div_ceil(num, den);

                let mut expected = ((val as $u) * (num as $u)) / (den as $u);
                let expected_rem = ((val as $u) * (num as $u)) % (den as $u);

                if expected_rem != 0 { expected = expected + 1 }

                if expected > $t::MAX as $u {
                    assert!(res.is_none(),
                            "{} * {} / {}: expected overflow, got {}",
                                    val, num, den, res.unwrap());
                } else {
                    assert!(res.is_some(),
                            "{} * {} / {}: expected {} but got overflow",
                                    val, num, den, expected);
                    assert_eq!(res.unwrap(), expected as $t,
                            "{} * {} / {}: expected {} but got {}",
                                    val, num, den, expected, res.unwrap());
                }
            }
        }

    )
}

mul_div_impl_unsigned!(u64, u128);
mul_div_impl_unsigned!(u32, u64);
mul_div_impl_unsigned!(u16, u32);
mul_div_impl_unsigned!(u8, u16);

// FIXME: https://github.com/rust-lang/rust/issues/12249
#[cfg(test)]
mod muldiv_u64_tests {
    mul_div_impl_unsigned_tests!(u64, u128);
}

#[cfg(test)]
mod muldiv_u32_tests {
    mul_div_impl_unsigned_tests!(u32, u64);
}

#[cfg(test)]
mod muldiv_u16_tests {
    mul_div_impl_unsigned_tests!(u16, u32);
}

#[cfg(test)]
mod muldiv_u8_tests {
    mul_div_impl_unsigned_tests!(u8, u16);
}

macro_rules! mul_div_impl_signed {
    ($t:ident, $u:ident, $v:ident, $b:expr) => (

    impl MulDiv for $t {
        type Output = $t;

        fn mul_div_floor(self, num: $t, denom: $t) -> Option<$t> {
            assert_ne!(denom, 0);

            let sgn = self.signum() * num.signum() * denom.signum();

            let min_val : $u = 1 << ($b - 1);
            let abs = |x: $t| if x != $t::MIN { x.abs() as $u } else { min_val };

            let self_u = abs(self);
            let num_u = abs(num);
            let denom_u = abs(denom);

            if sgn < 0 {
                self_u.mul_div_ceil(num_u, denom_u)
            } else {
                self_u.mul_div_floor(num_u, denom_u)
            }.and_then(|r| if r <= $t::MAX as $u { Some(sgn * (r as $t)) }
                              else if sgn < 0 && r == min_val { Some($t::MIN) }
                              else { None }
                      )
        }

        fn mul_div_round(self, num: $t, denom: $t) -> Option<$t> {
            assert_ne!(denom, 0);

            let sgn = self.signum() * num.signum() * denom.signum();

            let min_val : $u = 1 << ($b - 1);
            let abs = |x: $t| if x != $t::MIN { x.abs() as $u } else { min_val };

            let self_u = abs(self);
            let num_u = abs(num);
            let denom_u = abs(denom);

            if sgn < 0 {
                let r = ((self_u as $v) * (num_u as $v) +
                         ((cmp::max(denom_u >> 1, 1) - 1) as $v)) / (denom_u as $v);
                if r > $u::MAX as $v { None } else { Some(r as $u) }
            } else {
                self_u.mul_div_round(num_u, denom_u)
            }.and_then(|r| if r <= $t::MAX as $u { Some(sgn * (r as $t)) }
                           else if sgn < 0 && r == min_val { Some($t::MIN) }
                           else { None }
                      )
        }

        fn mul_div_ceil(self, num: $t, denom: $t) -> Option<$t> {
            assert_ne!(denom, 0);

            let sgn = self.signum() * num.signum() * denom.signum();

            let min_val : $u = 1 << ($b - 1);
            let abs = |x: $t| if x != $t::MIN { x.abs() as $u } else { min_val };

            let self_u = abs(self);
            let num_u = abs(num);
            let denom_u = abs(denom);

            if sgn < 0 {
                self_u.mul_div_floor(num_u, denom_u)
            } else {
                self_u.mul_div_ceil(num_u, denom_u)
            }.and_then(|r| if r <= $t::MAX as $u { Some(sgn * (r as $t)) }
                           else if sgn < 0 && r == min_val { Some($t::MIN) }
                           else { None }
                      )
        }
    }
    )
}

mul_div_impl_signed!(i64, u64, u128, 64);
mul_div_impl_signed!(i32, u32, u64, 32);
mul_div_impl_signed!(i16, u16, u32, 16);
mul_div_impl_signed!(i8, u8, u16, 8);

#[cfg(test)]
macro_rules! mul_div_impl_signed_tests {
    ($t:ident, $u:ident) => (
        use super::*;

        extern crate rand;

        use self::rand::thread_rng;
        use self::rand::Rng;
        use std::$t;

        #[test]
        fn scale_floor_rng() {
            let mut rng = thread_rng();

            for _ in 0..10000 {
                let val: $t = rng.gen();
                let num: $t = rng.gen();
                let den: $t = rng.gen();
                let sgn = val.signum() * num.signum() * den.signum();

                if den == 0 { continue; }

                let res = val.mul_div_floor(num, den);

                let mut expected = ((val as $u) * (num as $u)) / (den as $u);
                let expected_rem = ((val as $u) * (num as $u)) % (den as $u);

                if sgn < 0 && expected_rem.abs() != 0 { expected = expected - 1 }

                if expected > $t::MAX as $u || expected < $t::MIN as $u {
                    assert!(res.is_none(),
                            "{} * {} / {}: expected overflow, got {}",
                                    val, num, den, res.unwrap());
                } else {
                    assert!(res.is_some(),
                            "{} * {} / {}: expected {} but got overflow",
                                    val, num, den, expected);
                    assert_eq!(res.unwrap(), expected as $t,
                            "{} * {} / {}: expected {} but got {}",
                                    val, num, den, expected, res.unwrap());
                }
            }
        }
        #[test]
        fn scale_round_rng() {
            let mut rng = thread_rng();

            for _ in 0..10000 {
                let val: $t = rng.gen();
                let num: $t = rng.gen();
                let den: $t = rng.gen();
                let sgn = val.signum() * num.signum() * den.signum();

                if den == 0 { continue; }

                let res = val.mul_div_round(num, den);

                let mut expected = ((val as $u) * (num as $u)) / (den as $u);
                let expected_rem = ((val as $u) * (num as $u)) % (den as $u);

                if sgn < 0 && expected_rem.abs() > ((den as $u).abs() + 1) >> 1 {
                    expected = expected - 1
                } else if sgn > 0 && expected_rem.abs() >= ((den as $u).abs() + 1) >> 1 {
                    expected = expected + 1
                }

                if expected > $t::MAX as $u || expected < $t::MIN as $u {
                    assert!(res.is_none(),
                            "{} * {} / {}: expected overflow, got {}",
                                    val, num, den, res.unwrap());
                } else {
                    assert!(res.is_some(),
                            "{} * {} / {}: expected {} but got overflow",
                                    val, num, den, expected);
                    assert_eq!(res.unwrap(), expected as $t,
                            "{} * {} / {}: expected {} but got {}",
                                    val, num, den, expected, res.unwrap());
                }
            }
        }

        #[test]
        fn scale_ceil_rng() {
            let mut rng = thread_rng();

            for _ in 0..10000 {
                let val: $t = rng.gen();
                let num: $t = rng.gen();
                let den: $t = rng.gen();
                let sgn = val.signum() * num.signum() * den.signum();

                if den == 0 { continue; }

                let res = val.mul_div_ceil(num, den);

                let mut expected = ((val as $u) * (num as $u)) / (den as $u);
                let expected_rem = ((val as $u) * (num as $u)) % (den as $u);

                if sgn > 0 && expected_rem.abs() != 0 { expected = expected + 1 }

                if expected > $t::MAX as $u || expected < $t::MIN as $u {
                    assert!(res.is_none(),
                            "{} * {} / {}: expected overflow, got {}",
                                    val, num, den, res.unwrap());
                } else {
                    assert!(res.is_some(),
                            "{} * {} / {}: expected {} but got overflow",
                                    val, num, den, expected);
                    assert_eq!(res.unwrap(), expected as $t,
                            "{} * {} / {}: expected {} but got {}",
                                    val, num, den, expected, res.unwrap());
                }
            }
        }
    )
}

// FIXME: https://github.com/rust-lang/rust/issues/12249
#[cfg(test)]
mod muldiv_i64_tests {
    mul_div_impl_signed_tests!(i64, i128);
}

#[cfg(test)]
mod muldiv_i32_tests {
    mul_div_impl_signed_tests!(i32, i64);
}

#[cfg(test)]
mod muldiv_i16_tests {
    mul_div_impl_signed_tests!(i16, i32);
}

#[cfg(test)]
mod muldiv_i8_tests {
    mul_div_impl_signed_tests!(i8, i16);
}
