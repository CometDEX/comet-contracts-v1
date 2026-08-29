use std::println;

use std::vec as std_vec;
use std::vec::Vec as std_Vec;

use soroban_fixed_point_math::FixedPoint;
use soroban_sdk::{
    testutils::Events as _,
    token::{StellarAssetClient, TokenClient},
    xdr::{ContractEventBody, ScAddress, ScVal},
    Address, Env, TryFromVal, Val, Vec,
};

use crate::{
    c_consts::STROOP,
    c_pool::comet::{CometPoolContract, CometPoolContractClient},
    tests::balancer::F64Utils,
};

use super::balancer::BalancerPool;

/// Test helper exposing both the SAC administrator and standard token interfaces.
pub struct MockTokenClient<'a> {
    pub address: Address,
    admin: StellarAssetClient<'a>,
    token: TokenClient<'a>,
}

impl<'a> MockTokenClient<'a> {
    pub fn new(env: &'a Env, address: &Address) -> Self {
        Self {
            address: address.clone(),
            admin: StellarAssetClient::new(env, address),
            token: TokenClient::new(env, address),
        }
    }

    pub fn mint(&self, to: &Address, amount: &i128) {
        self.admin.mint(to, amount);
    }

    pub fn balance(&self, id: &Address) -> i128 {
        self.token.balance(id)
    }

    pub fn approve(
        &self,
        from: &Address,
        spender: &Address,
        amount: &i128,
        expiration_ledger: &u32,
    ) {
        self.token.approve(from, spender, amount, expiration_ledger);
    }
}

pub fn create_comet_pool(
    env: &Env,
    controller: &Address,
    tokens: &Vec<Address>,
    weights: &Vec<i128>,
    balances: &Vec<i128>,
    swap_fee: i128,
) -> Address {
    let contract_id = env.register(CometPoolContract, ());
    let client = CometPoolContractClient::new(&env, &contract_id);

    client.init(&controller, &tokens, &weights, &balances, &swap_fee);
    contract_id
}

pub fn create_stellar_token(env: &Env, admin: &Address) -> Address {
    env.register_stellar_asset_contract_v2(admin.clone())
        .address()
}

pub fn event_from_end(env: &Env, offset: usize) -> (Address, Vec<Val>, Val) {
    let events = env.events().all();
    let event = &events.events()[events.events().len() - offset];
    let contract_id = event.contract_id.clone().unwrap();
    let contract =
        Address::try_from_val(env, &ScVal::Address(ScAddress::Contract(contract_id))).unwrap();
    let ContractEventBody::V0(body) = &event.body;
    let mut topics = Vec::new(env);
    for topic in body.topics.iter() {
        topics.push_back(Val::try_from_val(env, topic).unwrap());
    }
    let data = Val::try_from_val(env, &body.data).unwrap();
    (contract, topics, data)
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
