#![cfg(test)]
extern crate std;
use std::println;

use soroban_sdk::xdr::ScStatusType;
use soroban_sdk::Env;
use soroban_sdk::Status;

use crate::c_num::c_add;
use crate::c_num::c_div;
use crate::c_num::c_mul;
use crate::c_num::c_pow;
use crate::c_num::c_sub;
use crate::c_pool::error::Error;

#[test]
#[should_panic(expected = "Status(ContractError(30))")]
fn test_c_add_overflow() {
    let env: Env = Env::default();
    assert_eq!(
        c_add(&env, 1, i128::MAX).err().unwrap(),
        Error::ErrAddOverflow
    );
}

#[test]
#[should_panic(expected = "Status(ContractError(31))")]
fn test_c_sub_underflow() {
    let env: Env = Env::default();
    assert_eq!(c_sub(&env, 1, 2).err().unwrap(), Error::ErrSubUnderflow);
}

#[test]
#[should_panic(expected = "Status(ContractError(33))")]
fn test_c_mul_overflow() {
    let env: Env = Env::default();
    assert_eq!(
        c_mul(&env, 2, i128::MAX).err().unwrap(),
        Error::ErrMulOverflow
    );
}

#[test]
#[should_panic(expected = "Status(ContractError(32))")]
fn test_c_div_error_on_div_by_zero() {
    let env: Env = Env::default();
    assert_eq!(c_div(&env, 1, 0).err().unwrap(), Error::ErrDivInternal);
}

#[test]
#[should_panic(expected = "Status(ContractError(34))")]
fn test_c_pow() {
    let env: Env = Env::default();
    assert_eq!(c_pow(&env, 0, 2).err().unwrap(), Error::ErrCPowBaseTooLow)
}

#[test]
#[should_panic(expected = "Status(ContractError(35))")]
fn test_c_pow_high() {
    let env: Env = Env::default();
    assert_eq!(
        c_pow(&env, i128::MAX, 2).err().unwrap(),
        Error::ErrCPowBaseTooHigh
    );
}
