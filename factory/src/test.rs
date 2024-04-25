#![cfg(test)]

extern crate std;

use crate::{Factory, FactoryClient};
use soroban_sdk::{testutils::Address as _, token::StellarAssetClient, vec, Address, BytesN, Env};

// The contract that will be deployed by the deployer contract.
mod contract {
    soroban_sdk::contractimport!(file = "../target/wasm32-unknown-unknown/optimized/comet.wasm");
}

#[test]
fn test_factory() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let wasm_hash = env.deployer().upload_contract_wasm(contract::WASM);

    let client = FactoryClient::new(&env, &env.register_contract(None, Factory));
    client.init(&wasm_hash);

    let controller = Address::generate(&env);
    let token_1 = env.register_stellar_asset_contract(controller.clone());
    let token_1_client = StellarAssetClient::new(&env, &token_1);
    let token_2 = env.register_stellar_asset_contract(controller.clone());
    let token_2_client = StellarAssetClient::new(&env, &token_2);
    token_1_client.mint(&controller, &1_0000000);
    token_2_client.mint(&controller, &1_0000000);

    let tokens = vec![&env, token_1.clone(), token_2.clone()];
    let weights = vec![&env, 0_5000000, 0_5000000];
    let balances = vec![&env, 1_0000000, 1_0000000];
    let swap_fee = 0_0030000;

    let salt = BytesN::from_array(&env, &[0; 32]);
    let contract_id =
        client.new_c_pool(&salt, &controller, &tokens, &weights, &balances, &swap_fee);

    let pool_client = contract::Client::new(&env, &contract_id);
    assert_eq!(client.is_c_pool(&contract_id.clone()), true);
    assert_eq!(pool_client.get_controller(), controller);
    assert_eq!(pool_client.get_tokens(), tokens);
    assert_eq!(pool_client.get_swap_fee(), swap_fee);
    assert_eq!(pool_client.get_total_supply(), 100 * 1_0000000);
}
