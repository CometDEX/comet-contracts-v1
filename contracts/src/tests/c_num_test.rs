#![cfg(test)]
extern crate std;
use std::println;

use soroban_sdk::Env;

use crate::c_num::c_add;    
use crate::c_num::c_div;
use crate::c_num::c_mul;
use crate::c_num::c_pow;
use crate::c_num::c_sub;
use crate::c_pool::error::Error;

#[test]
fn test_c_add_overflow() {
    let env: Env = Env::default();
    assert_eq!(
        c_add(&env, 1, i128::MAX).err().unwrap(),
        Error::ErrAddOverflow
    );
}

#[test]
fn test_c_sub_underflow() {
    let env: Env = Env::default();
    assert_eq!(c_sub(&env, 1, 2).err().unwrap(), Error::ErrSubUnderflow);
}

#[test]
fn test_c_mul_overflow() {
    let env: Env = Env::default();
    assert_eq!(
        c_mul(&env, 2, i128::MAX).err().unwrap(),
        Error::ErrMulOverflow
    );
}

#[test]
fn test_c_div_error_on_div_by_zero() {
    let env: Env = Env::default();
    assert_eq!(c_div(&env, 1, 0).err().unwrap(), Error::ErrDivInternal);
}

#[test]
fn test_c_pow() {
    let env: Env = Env::default();
    assert_eq!(c_pow(&env, 0, 2).err().unwrap(), Error::ErrCPowBaseTooLow)
}

#[test]
fn test_c_pow_high() {
    let env: Env = Env::default();
    assert_eq!(
        c_pow(&env, i128::MAX, 2).err().unwrap(),
        Error::ErrCPowBaseTooHigh
    );
}
