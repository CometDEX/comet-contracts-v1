#![cfg(test)]
extern crate std;
use std::println;

use soroban_sdk::{I256, Env};
use soroban_sdk::unwrap::UnwrapOptimized;

use crate::c_num_256::{c_add, c_div, c_mul, c_pow, c_sub};
use crate::c_pool::error::Error;

#[test]
#[should_panic]
fn test_c_add_overflow() {
    let env: Env = Env::default();

    // Maximum values for each part
    let hi_hi = i64::MAX; // Maximum positive value for a signed 64-bit integer
    let hi_lo = u64::MAX; // Maximum value for an unsigned 64-bit integer
    let lo_hi = u64::MAX;
    let lo_lo = u64::MAX;

    // Create the I256 value with maximum possible positive value
    let val = I256::from_parts(&env, hi_hi, hi_lo, lo_hi, lo_lo);

    c_add(&env, val , I256::from_i128(&env, 1)).unwrap_optimized();
}

#[test]
fn test_c_sub_underflow() {
    let env: Env = Env::default();
    // Example for subtracting with underflow, adjust as per actual usage
    assert_eq!(
        c_sub(&env, I256::from_i128(&env, 1), I256::from_i128(&env, 2)).err().unwrap_optimized(),
        Error::ErrSubUnderflow
    );
}

#[test]
#[should_panic]
fn test_c_mul_overflow() {
    let env: Env = Env::default();
    // Example for multiplying, adjust for actual overflow scenario
    // Maximum values for each part
    let hi_hi = i64::MAX; // Maximum positive value for a signed 64-bit integer
    let hi_lo = u64::MAX; // Maximum value for an unsigned 64-bit integer
    let lo_hi = u64::MAX;
    let lo_lo = u64::MAX;

    // Create the I256 value with maximum possible positive value
    let val = I256::from_parts(&env, hi_hi, hi_lo, lo_hi, lo_lo);
    c_mul(&env, I256::from_i128(&env, 2), val).err().unwrap_optimized();

}

#[test]
#[should_panic]
fn test_c_div_error_on_div_by_zero() {
    let env: Env = Env::default();
    c_div(&env, I256::from_i128(&env, 1), I256::from_i128(&env, 0));
   
}

#[test]
fn test_c_pow() {
    let env: Env = Env::default();
    // Adjust this test based on how `c_pow` is implemented to handle edge cases
    
    assert_eq!(
        c_pow(&env, I256::from_i128(&env, 0), I256::from_i128(&env, 2)).err().unwrap_optimized(),
        Error::ErrCPowBaseTooLow
    )
}

#[test]
fn test_c_pow_high() {
    let env: Env = Env::default();
    let hi_hi = i64::MAX; // Maximum positive value for a signed 64-bit integer
    let hi_lo = u64::MAX; // Maximum value for an unsigned 64-bit integer
    let lo_hi = u64::MAX;
    let lo_lo = u64::MAX;

    // Create the I256 value with maximum possible positive value
    let val = I256::from_parts(&env, hi_hi, hi_lo, lo_hi, lo_lo);
    
    // For testing power function with high base, adjust as necessary
    assert_eq!(
        c_pow(&env,val, I256::from_i128(&env, 2) ).err().unwrap_optimized(),
        Error::ErrCPowBaseTooHigh
    );

}
