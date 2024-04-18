//! Comet Pool Arithmetic Primitives

use c_consts::BONE;
use soroban_fixed_point_math::{FixedPoint, SorobanFixedPoint};
use soroban_sdk::{assert_with_error, unwrap::UnwrapOptimized, Env, I256};

use crate::{
    c_consts::{self, CPOW_PRECISION, MAX_CPOW_BASE, MIN_CPOW_BASE},
    c_pool::error::Error,
};

// Add 2 numbers
pub fn c_add(a: i128, b: i128) -> Result<i128, Error> {
    let c = a.checked_add(b);
    match c {
        Some(val) => Ok(val),
        None => Err(Error::ErrAddOverflow),
    }
}

// Subtract 2 numbers
pub fn c_sub(a: i128, b: i128) -> Result<i128, Error> {
    let (c, flag) = c_sub_sign(a, b);
    if flag {
        return Err(Error::ErrSubUnderflow);
    }
    Ok(c)
}

// Determine the sign of the input numbers
pub fn c_sub_sign(a: i128, b: i128) -> (i128, bool) {
    if a >= b {
        (a.checked_sub(b).unwrap_optimized(), false)
    } else {
        (b.checked_sub(a).unwrap_optimized(), true)
    }
}

// Multiply 2 numbers
pub fn c_mul(a: i128, b: i128) -> Result<i128, Error> {
    match a.fixed_mul_floor(b, BONE) {
        Some(val) => Ok(val),
        None => Err(Error::ErrMulOverflow),
    }
}

// Divide 2 numbers
pub fn c_div(a: i128, b: i128) -> Result<i128, Error> {
    match a.fixed_div_floor(b, BONE) {
        Some(val) => Ok(val),
        None => Err(Error::ErrDivInternal),
    }
}

/// Calculate base^exp where base and exp are fixed point numbers with 18 decimals.
///
/// Approximates the result such that:
/// -> base^(int exp) * approximate of base^(decimal exp)
pub fn c_pow(e: &Env, base: &I256, exp: &I256, round_up: bool) -> I256 {
    assert_with_error!(
        e,
        base >= &I256::from_i128(e, MIN_CPOW_BASE),
        Error::ErrCPowBaseTooLow
    );
    assert_with_error!(
        e,
        base <= &I256::from_i128(e, MAX_CPOW_BASE),
        Error::ErrCPowBaseTooHigh
    );

    let bone = I256::from_i128(e, BONE);
    let int = exp.div(&bone);
    let remain = exp.sub(&int.mul(&bone));
    let whole_pow = c_powi(e, &base, &(int.to_i128().unwrap_optimized() as u32));
    if remain == I256::from_i128(e, 0) {
        return whole_pow;
    }
    let partial_result = c_pow_approx(
        e,
        &base,
        &remain,
        &I256::from_i128(e, CPOW_PRECISION),
        round_up,
    );
    if round_up {
        whole_pow.fixed_mul_ceil(e, &partial_result, &bone)
    } else {
        whole_pow.fixed_mul_floor(e, &partial_result, &bone)
    }
}

// Calculate a^n where n is an integer
fn c_powi(e: &Env, a: &I256, n: &u32) -> I256 {
    let bone = I256::from_i128(e, BONE);
    let mut z = if n % 2 != 0 { a.clone() } else { bone.clone() };

    let mut a = a.clone();
    let mut n = n / 2;
    while n != 0 {
        a = a.fixed_mul_floor(e, &a, &bone);
        if n % 2 != 0 {
            z = z.fixed_mul_floor(e, &a, &bone);
        }
        n = n / 2
    }
    z
}

// Calculate approximate Power Value
fn c_pow_approx(e: &Env, base: &I256, exp: &I256, precision: &I256, round_up: bool) -> I256 {
    // term 0
    let bone = I256::from_i128(e, BONE);
    let zero = I256::from_i32(e, 0);
    let n_1 = I256::from_i32(e, -1);
    let x = base.sub(&bone);
    let mut term = bone.clone();
    let mut sum = term.clone();
    let prec = precision.clone();
    // Capped to limit iterations in the event of a poor approximation
    // Max resource impact at 50 iterations:
    //  -> CPU: 5M inst
    //  -> Mem: 150 kB
    for i in 1..51 {
        let big_k = I256::from_i128(e, i * BONE);
        let c = exp.sub(&big_k.sub(&bone));
        term = term.fixed_mul_floor(e, &c.fixed_mul_floor(e, &x, &bone), &bone);
        term = term.fixed_div_floor(e, &big_k, &bone);
        sum = sum.add(&term);

        let abs_term = if term < zero {
            term.mul(&n_1)
        } else {
            term.clone()
        };
        if abs_term <= prec {
            break;
        }
    }
    // the series has predicatable approximations bounds, so we can adjust the final sum by
    // the final term to (almost) ensure the sum is either an under or over estimate based
    // on the rounding direction.
    if x > zero {
        // series will oscillate due to negative `c` values and a starting positive value.
        if term > zero && !round_up {
            // the final applied term was additive - the current sum is likely an overestimate
            sum = sum.sub(&term);
        } else if term < zero && round_up {
            // the final applied term was subtractive - the current sum is likely an understimate
            sum = sum.sub(&term);
        }
    } else if !round_up {
        // series is monotonically decreasing, so the final term is an overestimate
        sum = sum.add(&term);
    }
    sum
}
