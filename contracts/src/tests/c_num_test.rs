#![cfg(test)]
extern crate std;
use soroban_sdk::Env;
use soroban_sdk::I256;

use crate::c_consts::BONE;
use crate::c_num::c_pow;

#[test]
#[should_panic = "Error(Contract, #34)"]
fn test_c_pow_low() {
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
