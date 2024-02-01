//! Comet Pool Arithmetic Primitives

use c_consts_256::*;
use soroban_fixed_point_math::{FixedPoint, STROOP};
use soroban_sdk::{panic_with_error, unwrap::UnwrapOptimized, Env};
use soroban_sdk::{I256, Env};

use crate::c_consts_256::get_bone;
use crate::c_pool::error::Error;

// Divide by BONE
fn c_toi(e: &Env, a: i128) -> I256 {
    let a = I256::from_i128(e, a);
    a.div(&get_bone(e))
}

// Multiply by BONE after dividing by BONE
fn c_floor(e: &Env, a: i128) -> I256 {
    c_toi(e, a).mul(&get_bone(e))
}

// Add 2 numbers
pub fn c_add(e: &Env, a: i128, b: i128) -> Result<i128, Error> {
    let a = I256::from_i128(e, a);
    let b = I256::from_i128(e, b);

    a.checked_add(&b)
    
}

// Subtract 2 numbers
pub fn c_sub(e: &Env, a: i128, b: i128) -> Result<i128, Error> {
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
pub fn c_mul(e: &Env, a: i128, b: i128) -> Result<i128, Error> {
    match a.fixed_mul_floor(b, BONE) {
        Some(val) => Ok(val),
        None => Err(Error::ErrMulOverflow),
    }
}

// Divide 2 numbers
pub fn c_div(e: &Env, a: i128, b: i128) -> Result<i128, Error> {
    match a.fixed_div_floor(b, BONE) {
        Some(val) => Ok(val),
        None => Err(Error::ErrDivInternal),
    }
}

// Calculate a^n
pub fn c_powi(e: &Env, a: i128, n: i128) -> i128 {
    let mut z = if n.checked_rem_euclid(2).unwrap_or(0) != 0 {
        a
    } else {
        BONE
    };

    let mut a = a;
    let mut n = n.checked_div(2).unwrap_optimized();

    while n != 0 {
        a = c_mul(e, a, a).unwrap_optimized();

        if n.checked_rem_euclid(2).unwrap_or(0) != 0 {
            z = c_mul(e, z, a).unwrap_optimized();
        }

        n = n.checked_div(2).unwrap_optimized();
    }

    z
}

// Calculate Power of a Base Value
pub fn c_pow(e: &Env, base: i128, exp: i128) -> Result<i128, Error> {
    if base < MIN_CPOW_BASE {
        return Err(Error::ErrCPowBaseTooLow);
    }

    if base > MAX_CPOW_BASE {
        return Err(Error::ErrCPowBaseTooHigh);
    }

    let whole = c_floor(e, exp);

    let remain = c_sub(e, exp, whole).unwrap_optimized();

    let whole_pow = c_powi(e, base, c_toi(e, whole));

    if remain == 0 {
        return Ok(whole_pow);
    }

    let partial_result = c_pow_approx(e, base, remain, CPOW_PRECISION);
    Ok(c_mul(e, whole_pow, partial_result).unwrap_optimized())
}

// Calculate approximate Power Value
pub fn c_pow_approx(e: &Env, base: i128, exp: i128, precision: i128) -> i128 {
    let a = exp;
    let (x, xneg) = c_sub_sign(base, BONE);
    let mut term = BONE;
    let mut sum = term;
    let mut negative = false;
    let mut i: i128 = 1;
    while term >= precision {
        let big_k = i.checked_mul(BONE).unwrap_optimized();
        let (c, cneg) = c_sub_sign(a, c_sub(e, big_k, BONE).unwrap_optimized());
        term = c_mul(e, term, c_mul(e, c, x).unwrap_optimized()).unwrap_optimized();
        term = c_div(e, term, big_k).unwrap_optimized();

        if term == 0 {
            break;
        }

        if xneg {
            negative = !negative;
        }

        if cneg {
            negative = !negative;
        }

        if negative {
            sum = c_sub(e, sum, term).unwrap_optimized();
        } else {
            sum = c_add(e, sum, term).unwrap_optimized();
        }

        i = i.checked_add(1).unwrap_optimized();
    }

    sum
}
