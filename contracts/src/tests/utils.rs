use std::println;

use std::vec as std_vec;
use std::vec::Vec as std_Vec;

use sep_41_token::testutils::{MockTokenClient, MockTokenWASM};
use soroban_fixed_point_math::FixedPoint;
use soroban_sdk::{token::TokenClient, Address, Env, String, Vec};

use crate::{
    c_consts::STROOP,
    c_pool::comet::{CometPoolContract, CometPoolContractClient},
    tests::balancer::F64Utils,
};

use super::balancer::BalancerPool;

pub fn create_comet_pool(
    env: &Env,
    controller: &Address,
    tokens: &Vec<Address>,
    weights: &Vec<i128>,
    balances: &Vec<i128>,
    swap_fee: i128,
) -> Address {
    let contract_id = env.register_contract(None, CometPoolContract);
    let client = CometPoolContractClient::new(&env, &contract_id);

    client.init(&controller, &tokens, &weights, &balances, &swap_fee);
    contract_id
}

pub fn create_stellar_token(env: &Env, admin: &Address) -> Address {
    let contract_id = env.register_stellar_asset_contract(admin.clone());
    contract_id
}

pub fn create_soroban_token(env: &Env, admin: &Address, decimal: u32) -> Address {
    let contract_id = env.register_contract_wasm(None, MockTokenWASM);
    let client = MockTokenClient::new(&env, &contract_id);
    client.initialize(
        &admin,
        &decimal,
        &String::from_str(env, "NAME"),
        &String::from_str(env, "SYMBOL"),
    );
    contract_id
}

/// Asset that `b` is within `percentage` of `a` where `percentage`
/// is a percentage in decimal form as a fixed-point number with 7 decimal
/// places
pub fn assert_approx_eq_rel(a: i128, b: i128, percentage: i128) {
    let rel_delta = b.fixed_mul_floor(percentage, STROOP).unwrap();

    assert_approx_eq_abs(a, b, rel_delta);
}

/// Asset that `b` is within `abs` of `a`
pub fn assert_approx_eq_abs(a: i128, b: i128, abs: i128) {
    assert!(
        a > b - abs && a < b + abs,
        "assertion failed: `(left != right)` \
         (left: `{:?}`, right: `{:?}`, epsilon: `{:?}`)",
        a,
        b,
        abs
    );
}

#[allow(dead_code)]
pub fn print_compare(e: &Env, balancer: &BalancerPool, comet: &Address) {
    println!("## Comparing: ");
    let client = CometPoolContractClient::new(&e, &comet);
    let tokens = client.get_tokens();
    let mut balances: std_Vec<i128> = std_vec![];
    let mut difs: std_Vec<f64> = std_vec![];
    for i in 0..tokens.len() {
        let token = tokens.get_unchecked(i);
        let token_client = TokenClient::new(&e, &token);
        let balance = token_client.balance(&comet);

        let b_balance = balancer.balances[i as usize].to_i128(&7);
        let per_dif = percent_dif(b_balance, balance);
        balances.push(balance);
        difs.push(per_dif);
    }
    let supply_dif = percent_dif(balancer.supply.to_i128(&7), client.get_total_supply());
    balancer.print();
    println!("CometPool: ");
    println!("  balances: {:?}", balances);
    println!("  supply: {:?}", client.get_total_supply());
    println!("Diffs to f64: ");
    println!("  balances: {:?}", difs);
    println!("  supply: {:?}", supply_dif);
    println!("");
}

fn percent_dif(a: i128, b: i128) -> f64 {
    let a = a as f64;
    let b = b as f64;
    (a - b) / a
}
