#![cfg(test)]

use soroban_sdk::{testutils::Address as _, vec, Address, Env, Error, Executable};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::{CometPoolContract, CometPoolContractClient},
        error::Error as CometError,
    },
    tests::utils::MockTokenClient,
};

#[test]
fn test_init_rejects_wasm_token_contract() {
    let env = Env::default();
    env.mock_all_auths();

    let controller = Address::generate(&env);
    let pool = env.register(CometPoolContract, ());
    let comet = CometPoolContractClient::new(&env, &pool);

    let stellar_asset = env
        .register_stellar_asset_contract_v2(controller.clone())
        .address();
    let stellar_asset_client = MockTokenClient::new(&env, &stellar_asset);
    stellar_asset_client.mint(&controller, &STROOP);

    let wasm_contract = env.register(CometPoolContract, ());

    assert_eq!(stellar_asset.executable(), Some(Executable::StellarAsset));
    assert!(matches!(
        wasm_contract.executable(),
        Some(Executable::Wasm(_))
    ));

    let result = comet.try_init(
        &controller,
        &vec![&env, stellar_asset.clone(), wasm_contract],
        &vec![&env, 5 * STROOP / 10, 5 * STROOP / 10],
        &vec![&env, STROOP, STROOP],
        &0_0030000,
    );

    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrTokenInvalid as u32
        )))
    );
    assert_eq!(stellar_asset_client.balance(&controller), STROOP);
    assert_eq!(stellar_asset_client.balance(&pool), 0);
}
