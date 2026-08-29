#![cfg(test)]

extern crate std;

use crate::{Factory, FactoryClient};
use soroban_sdk::{testutils::Address as _, token::StellarAssetClient, vec, Address, BytesN, Env};

// The contract that will be deployed by the deployer contract.
mod contract {
    soroban_sdk::contractimport!(file = "../target/wasm32v1-none/optimized/comet.wasm");
}

mod factory_wasm {
    soroban_sdk::contractimport!(file = "../target/wasm32v1-none/optimized/comet_factory.wasm");
}

#[test]
fn test_factory() {
    let env = Env::default();
    env.mock_all_auths();
    env.cost_estimate().budget().reset_unlimited();

    let wasm_hash = env.deployer().upload_contract_wasm(contract::WASM);
    let controller = Address::generate(&env);
    let salt = BytesN::from_array(&env, &[0; 32]);
    let factory_id = env
        .deployer()
        .with_address(controller.clone(), salt.clone())
        .deployed_address();
    env.register_at(&factory_id, Factory, ());
    let client = FactoryClient::new(&env, &factory_id);
    client.init(&controller, &salt, &wasm_hash);

    let token_1 = env
        .register_stellar_asset_contract_v2(controller.clone())
        .address();
    let token_1_client = StellarAssetClient::new(&env, &token_1);
    let token_2 = env
        .register_stellar_asset_contract_v2(controller.clone())
        .address();
    let token_2_client = StellarAssetClient::new(&env, &token_2);
    token_1_client.mint(&controller, &1_0000000);
    token_2_client.mint(&controller, &1_0000000);

    let tokens = vec![&env, token_1.clone(), token_2.clone()];
    let weights = vec![&env, 0_5000000, 0_5000000];
    let balances = vec![&env, 1_0000000, 1_0000000];
    let swap_fee = 0_0030000;

    let pool_salt = BytesN::from_array(&env, &[0; 32]);
    let contract_id = client.new_c_pool(
        &pool_salt,
        &controller,
        &tokens,
        &weights,
        &balances,
        &swap_fee,
    );

    let pool_client = contract::Client::new(&env, &contract_id);
    assert_eq!(client.is_c_pool(&contract_id.clone()), true);
    assert_eq!(pool_client.get_controller(), controller);
    assert_eq!(pool_client.get_tokens(), tokens);
    assert_eq!(pool_client.get_swap_fee(), swap_fee);
    assert_eq!(pool_client.get_total_supply(), 100 * 1_0000000);
}

#[test]
fn test_init_requires_contract_deployer() {
    let env = Env::default();
    env.mock_all_auths();
    let deployer = Address::generate(&env);
    let attacker = Address::generate(&env);
    let salt = BytesN::from_array(&env, &[1; 32]);
    let wrong_salt = BytesN::from_array(&env, &[2; 32]);
    let pool_wasm_hash = env.deployer().upload_contract_wasm(contract::WASM);
    let factory_wasm_hash = env.deployer().upload_contract_wasm(factory_wasm::WASM);
    let factory_id = env
        .deployer()
        .with_address(deployer.clone(), salt.clone())
        .deploy_v2(factory_wasm_hash, ());
    let client = FactoryClient::new(&env, &factory_id);

    // Knowing the deployment address and salt is insufficient without the
    // deployer's authorization.
    env.set_auths(&[]);
    assert!(client.try_init(&deployer, &salt, &pool_wasm_hash).is_err());

    env.mock_all_auths();

    // An authenticated caller cannot claim a factory deployed by another
    // address or provide a salt that does not reproduce the factory ID.
    assert!(client.try_init(&attacker, &salt, &pool_wasm_hash).is_err());
    assert!(client
        .try_init(&deployer, &wrong_salt, &pool_wasm_hash)
        .is_err());

    client.init(&deployer, &salt, &pool_wasm_hash);
    assert!(client.try_init(&deployer, &salt, &pool_wasm_hash).is_err());
}
