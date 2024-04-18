#![cfg(test)]
extern crate std;
use soroban_sdk::unwrap::UnwrapOptimized;
use soroban_sdk::Env;
use soroban_sdk::I256;

use crate::c_consts::BONE;
use crate::c_num::c_add;
use crate::c_num::c_div;
use crate::c_num::c_mul;
use crate::c_num::c_pow;
use crate::c_num::c_sub;
use crate::c_pool::error::Error;

#[test]
fn test_c_add_overflow() {
    assert_eq!(
        c_add(1, i128::MAX).err().unwrap_optimized(),
        Error::ErrAddOverflow
    );
}

#[test]
fn test_c_sub_underflow() {
    assert_eq!(c_sub(1, 2).err().unwrap_optimized(), Error::ErrSubUnderflow);
}

#[test]
fn test_c_mul_overflow() {
    assert_eq!(
        c_mul(2, i128::MAX).err().unwrap_optimized(),
        Error::ErrMulOverflow
    );
}

#[test]
fn test_c_div_error_on_div_by_zero() {
    assert_eq!(c_div(1, 0).err().unwrap_optimized(), Error::ErrDivInternal);
}

#[test]
#[should_panic = "Error(Contract, #34)"]
fn test_c_pow() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i32(&env, 0),
        &I256::from_i32(&env, 2),
        false,
    );
}

#[test]
#[should_panic = "Error(Contract, #35)"]
fn test_c_pow_high() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i128(&env, 2 * BONE),
        &I256::from_i32(&env, 2),
        false,
    );
}
