#![cfg(test)]

extern crate std;
use std::println;

use crate::{Factory, FactoryClient};
use soroban_sdk::{testutils::Address, Bytes, Env, IntoVal, Symbol, BytesN};

// The contract that will be deployed by the deployer contract.
mod contract {
    soroban_sdk::contractimport!(file = "../target/wasm32-unknown-unknown/optimized/comet.wasm");
}

#[test]
fn test_factory() {
    let env = Env::default();
    env.mock_all_auths();
    let client = FactoryClient::new(&env, &env.register_contract(None, Factory));
    let user = soroban_sdk::Address::random(&env);
    env.budget().reset_unlimited();
    let wasm_hash = env.deployer().upload_contract_wasm(contract::WASM);

    client.init(&user, &wasm_hash);

    let pool_controller = soroban_sdk::Address::random(&env);
    let salt = BytesN::from_array(&env, &[0; 32]);
    let contract_id = client.new_c_pool(&salt, &pool_controller);
    assert_eq!(client.is_c_pool(&contract_id.clone()), true);
    let new_admin = soroban_sdk::Address::random(&env);
    client.set_c_admin(&user, &new_admin);
    assert_eq!(client.get_c_admin(), new_admin);

    //Exit Fee is 0 so this wont do anything
    client.collect(&new_admin, &contract_id);
}
