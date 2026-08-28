#![cfg(test)]

extern crate std;

use crate::{
    call_logic::factory::{DAY_IN_LEDGERS, INSTANCE_BUMP_AMOUNT},
    DataKeyFactory, Factory, FactoryClient,
};
use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::StellarAssetClient,
    vec, xdr, Address, BytesN, Env,
};

fn instance_live_until(e: &Env, contract_id: &Address) -> u32 {
    let contract_address: xdr::ScAddress = contract_id.clone().try_into().unwrap();
    e.to_ledger_snapshot()
        .ledger_entries
        .iter()
        .find_map(|(key, (_, live_until))| match key.as_ref() {
            xdr::LedgerKey::ContractData(entry)
                if entry.contract == contract_address
                    && entry.key == xdr::ScVal::LedgerKeyContractInstance =>
            {
                *live_until
            }
            _ => None,
        })
        .unwrap()
}

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

#[test]
fn test_is_c_pool_extends_factory_instance_ttl() {
    let env = Env::default();
    let factory_id = env.register_contract(None, Factory);
    let client = FactoryClient::new(&env, &factory_id);
    let wasm_hash = BytesN::from_array(&env, &[0; 32]);

    let initial_live_until = instance_live_until(&env, &factory_id);
    client.init(&wasm_hash);
    let initialized_live_until = instance_live_until(&env, &factory_id);
    assert!(initialized_live_until > initial_live_until);

    env.ledger().with_mut(|ledger| {
        ledger.sequence_number += DAY_IN_LEDGERS + 1;
    });

    let unknown_pool = Address::generate(&env);
    assert!(!client.is_c_pool(&unknown_pool));
    assert!(!env.as_contract(&factory_id, || {
        env.storage()
            .persistent()
            .has(&DataKeyFactory::IsCpool(unknown_pool.clone()))
    }));

    let refreshed_live_until = instance_live_until(&env, &factory_id);
    assert!(refreshed_live_until > initialized_live_until);
    assert_eq!(
        refreshed_live_until,
        env.ledger().sequence() + INSTANCE_BUMP_AMOUNT
    );
}
