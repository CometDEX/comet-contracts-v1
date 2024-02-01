//! Comet Pool Arithmetic Primitives

use soroban_sdk::{panic_with_error, unwrap::UnwrapOptimized, Env};
use soroban_sdk::I256;
use soroban_fixed_point_math::*;
use crate::c_consts_256::*;
use crate::c_pool::error::Error;

// Divide bsy BONE
use soroban_fixed_point_math::{FixedPoint, STROOP};
use crate::c_consts_256::get_bone;

// Divide by BONE
fn c_toi(e: &Env, a: I256) -> I256 {
    a.div(&get_bone(e))
}

// Multiply by BONE after dividing by BONE
fn c_floor(e: &Env, a: I256) -> I256 {
    c_toi(e, a).mul(&get_bone(e))
}

// Add 2 numbers
pub fn c_add(e: &Env, a: I256, b: I256) -> Result<I256, Error> {
    
    Ok(a.add(&b))
}


// Subtract 2 numbers using I256
pub fn c_sub(e: &Env, a: I256, b: I256) -> Result<I256, Error> {
    if b > a {
        // This mimics the Solidity _require statement for underflow checking
        return Err(Error::ErrSubUnderflow);
    } else {
        // Perform safe subtraction
        Ok(a.sub(&b))
    }
}

pub fn c_sub_sign(env: &Env, a: I256, b: I256) -> (I256, bool) {

    if a >= b {
        // Perform the subtraction a - b, assuming subtraction does not underflow
        (a.sub(&b), false)
    } else {
        // Perform the subtraction b - a, to avoid negative result
        (b.sub(&a), true)
    }
    // Note: Ensure `sub` method exists and behaves as expected; adjust accordingly
}

pub fn c_mul(e: &Env, a: I256, b: I256) -> Result<I256, Error> {    

    Ok(a.fixed_mul_floor(e, b, get_bone(e)))
}
// Divide 2 numbers
pub fn c_div(e: &Env, a: I256, b: I256) -> Result<I256, Error> {
    
    // Ok(a.div(&b))
    Ok(a.fixed_div_floor(e, b, get_bone(e)))
}

// Calculate a^n
pub fn c_powi(e: &Env, a: I256, n: I256) -> I256 {
   
    let mut z = if n.rem_euclid(&I256::from_i128(e, 2)) != I256::from_i128(e,0) {
        a.clone()
    } else {
        get_bone(e)
    };

    let mut a = a.clone();
    let mut n = n.div(&I256::from_i128(e, 2));
    
    while n != I256::from_i128(e,0) {
        a = c_mul(e, a.clone(), a.clone()).unwrap_optimized();

        if n.rem_euclid(&I256::from_i128(e, 2)) != I256::from_i128(e,0) {
            z = c_mul(e, z, a.clone()).unwrap_optimized();
        }

        n = n.div(&I256::from_i128(e, 2));
    }

    z
}

// Calculate Power of a Base Value
pub fn c_pow(e: &Env, base: I256, exp: I256) -> Result<I256, Error> {
    if base < get_min_cpow_base(e) {
        return Err(Error::ErrCPowBaseTooLow);
    }

    if base > get_max_cpow_base(e) {
        return Err(Error::ErrCPowBaseTooHigh);
    }

    let whole = c_floor(e, exp.clone());

    let remain = c_sub(e, exp, whole.clone()).unwrap_optimized();

    let whole_pow = c_powi(e, base.clone(), c_toi(e, whole));

    if remain == I256::from_i128(e,0) {
        return Ok(whole_pow);
    }

    let partial_result = c_pow_approx(e, base, remain, get_cpow_precision(e));
    Ok(c_mul(e, whole_pow, partial_result).unwrap_optimized())
}


// Calculate approximate Power Value
pub fn c_pow_approx(e: &Env, base: I256, exp: I256, precision: I256) -> I256 {
    let a = exp;
    let (x, xneg) = c_sub_sign(e, base, get_bone(e));
    let mut term = get_bone(e);
    let mut sum = term.clone();
    let mut negative = false;
    let mut i: I256 = I256::from_i128(e, 1);
    while term >= precision {
        let big_k = i.mul(&get_bone(e));
        let (c, cneg) = c_sub_sign(e, a.clone(), c_sub(e, big_k.clone(), get_bone(e)).unwrap_optimized());
        term = c_mul(e, term, c_mul(e, c, x.clone()).unwrap_optimized()).unwrap_optimized();
        term = c_div(e, term, big_k).unwrap_optimized();

        if term == I256::from_i128(e, 0) {
            break;
        }

        if xneg {
            negative = !negative;
        }

        if cneg {
            negative = !negative;
        }

        if negative {
            sum = c_sub(e, sum, term.clone()).unwrap_optimized();
        } else {
            sum = c_add(e, sum, term.clone()).unwrap_optimized();
        }

        i = i.add(&I256::from_i128(e, 1));
    }

    sum
}
