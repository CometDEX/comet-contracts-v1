#![cfg(test)]

extern crate std;

use crate::{Factory, FactoryClient};
use soroban_sdk::{
    contract, contractimpl, contracttype,
    testutils::Address as _,
    token::{StellarAssetClient, TokenClient},
    vec, Address, BytesN, Env, Error,
};

// The contract that will be deployed by the deployer contract.
mod contract {
    soroban_sdk::contractimport!(file = "../target/wasm32-unknown-unknown/optimized/comet.wasm");
}

#[derive(Clone)]
#[contracttype]
enum FeeTokenKey {
    Balance(Address),
    Fee,
}

#[contract]
struct FeeToken;

#[contractimpl]
impl FeeToken {
    pub fn mint(e: Env, to: Address, amount: i128) {
        write_balance(&e, &to, read_balance(&e, &to) + amount);
    }

    pub fn set_fee(e: Env, fee: i128) {
        e.storage().instance().set(&FeeTokenKey::Fee, &fee);
    }

    pub fn balance(e: Env, id: Address) -> i128 {
        read_balance(&e, &id)
    }

    pub fn transfer(e: Env, from: Address, to: Address, amount: i128) {
        let fee = e
            .storage()
            .instance()
            .get(&FeeTokenKey::Fee)
            .unwrap_or(0i128);
        write_balance(&e, &from, read_balance(&e, &from) - amount);
        write_balance(&e, &to, read_balance(&e, &to) + amount - fee);
    }

    pub fn decimals(_e: Env) -> u32 {
        7
    }
}

fn read_balance(e: &Env, address: &Address) -> i128 {
    e.storage()
        .instance()
        .get(&FeeTokenKey::Balance(address.clone()))
        .unwrap_or(0)
}

fn write_balance(e: &Env, address: &Address, amount: i128) {
    e.storage()
        .instance()
        .set(&FeeTokenKey::Balance(address.clone()), &amount);
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

#[test]
fn test_compiled_pool_rejects_inexact_initial_transfer() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let controller = Address::generate(&env);
    let standard_token = env.register_stellar_asset_contract(controller.clone());
    let standard_client = StellarAssetClient::new(&env, &standard_token);
    let standard_token_client = TokenClient::new(&env, &standard_token);
    let fee_token = env.register_contract(None, FeeToken);
    let fee_client = FeeTokenClient::new(&env, &fee_token);
    standard_client.mint(&controller, &1_0000000);
    fee_client.mint(&controller, &1_0000000);
    fee_client.set_fee(&1);

    let pool = env.register_contract_wasm(None, contract::WASM);
    let pool_client = contract::Client::new(&env, &pool);
    let result = pool_client.try_init(
        &controller,
        &vec![&env, standard_token.clone(), fee_token.clone()],
        &vec![&env, 0_5000000, 0_5000000],
        &vec![&env, 1_0000000, 1_0000000],
        &0_0030000,
    );

    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            contract::Error::ErrBalanceMismatch as u32
        )))
    );
    assert_eq!(standard_token_client.balance(&controller), 1_0000000);
    assert_eq!(standard_token_client.balance(&pool), 0);
    assert_eq!(fee_client.balance(&controller), 1_0000000);
    assert_eq!(fee_client.balance(&pool), 0);
}
