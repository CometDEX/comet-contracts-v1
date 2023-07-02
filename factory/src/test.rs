#![cfg(test)]

extern crate std;
use std::println;

use crate::{Factory, FactoryClient};
use soroban_sdk::{testutils::Address, Bytes, Env, IntoVal, Symbol};

// The contract that will be deployed by the deployer contract.
mod contract {
    soroban_sdk::contractimport!(file = "../target/wasm32-unknown-unknown/release/contracts.wasm");
}

#[test]
fn test_factory() {
    let env = Env::default();
    let client = FactoryClient::new(&env, &env.register_contract(None, Factory));
    let user = soroban_sdk::Address::random(&env);
    client.init(&user);
    let wasm_hash = env.install_contract_wasm(contract::WASM);
    let salt = Bytes::from_array(&env, &[0; 32]);
    let init_fn = Symbol::short("init");
    let init_fn_args = (5u32,).into_val(&env);
    let pool_controller = soroban_sdk::Address::random(&env);
    let contract_id = client.new_c_pool(&init_fn, &init_fn_args, &wasm_hash, &pool_controller);
    assert_eq!(
        client.is_c_pool(&soroban_sdk::Address::from_contract_id(&env, &contract_id)),
        true
    );
    let new_admin = soroban_sdk::Address::random(&env);
    client.set_c_admin(&user, &new_admin);
    assert_eq!(client.get_c_admin(), new_admin);

    //Exit Fee is 0 so this wont do anything
    client.collect(
        &new_admin,
        &soroban_sdk::Address::from_contract_id(&env, &contract_id),
    );
}
