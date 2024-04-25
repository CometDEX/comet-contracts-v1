#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    testutils::{Address as _, MockAuth, MockAuthInvoke},
    vec, Address, Env, Error, IntoVal,
};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::{CometPoolContract, CometPoolContractClient},
        error::Error as CometError,
    },
};

#[test]
fn test_init() {
    let env = Env::default();
    env.mock_all_auths();

    let contract_id = env.register_contract(None, CometPoolContract);
    let comet = CometPoolContractClient::new(&env, &contract_id);

    let controller = Address::generate(&env);
    let token_1 = env.register_stellar_asset_contract(controller.clone());
    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2 = env.register_stellar_asset_contract(controller.clone());
    let token_2_client = MockTokenClient::new(&env, &token_2);
    token_1_client.mint(&controller, &STROOP);
    token_2_client.mint(&controller, &STROOP);

    let tokens = vec![&env, token_1.clone(), token_2.clone()];
    let weights = vec![&env, 0_4000000, 0_6000000];
    let balances = vec![&env, STROOP, STROOP];
    let swap_fee = 0_0030000;

    // validates not enough tokens
    let result = comet.try_init(
        &controller,
        &vec![&env, token_1.clone()],
        &vec![&env, 0_5000000],
        &vec![&env, STROOP],
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMinTokens as u32
        )))
    );

    // validates all vecs are same len
    let result = comet.try_init(
        &controller,
        &tokens,
        &vec![&env, 0_5000000],
        &balances,
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInvalidVectorLen as u32
        )))
    );
    let result = comet.try_init(
        &controller,
        &tokens,
        &weights,
        &vec![&env, STROOP],
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInvalidVectorLen as u32
        )))
    );

    // validates total weight is 1 STROOP
    let result = comet.try_init(
        &controller,
        &tokens,
        &vec![&env, 0_5000000, 0_5000001],
        &balances,
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrTotalWeight as u32
        )))
    );

    // validates individual weights
    let result = comet.try_init(
        &controller,
        &tokens,
        &vec![&env, 0_9100000, 0_1000000],
        &balances,
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxWeight as u32
        )))
    );
    let result = comet.try_init(
        &controller,
        &tokens,
        &vec![&env, 0_0900000, 0_9100000],
        &balances,
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMinWeight as u32
        )))
    );

    // validates balances over min
    let result = comet.try_init(
        &controller,
        &tokens,
        &weights,
        &vec![&env, STROOP, 99],
        &swap_fee,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInsufficientBalance as u32
        )))
    );

    // validates swap fee
    let result = comet.try_init(&controller, &tokens, &weights, &balances, &0_1000001);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrSwapFee as u32
        )))
    );
    let result = comet.try_init(&controller, &tokens, &weights, &balances, &0_0000009);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrSwapFee as u32
        )))
    );

    // do init
    env.set_auths(&[]);
    comet
        .mock_auths(&[MockAuth {
            address: &controller,
            invoke: &MockAuthInvoke {
                contract: &contract_id,
                fn_name: &"init",
                args: vec![
                    &env,
                    controller.into_val(&env),
                    tokens.into_val(&env),
                    weights.into_val(&env),
                    balances.into_val(&env),
                    swap_fee.into_val(&env),
                ],
                sub_invokes: &[
                    MockAuthInvoke {
                        contract: &token_1,
                        fn_name: &"transfer",
                        args: vec![
                            &env,
                            controller.into_val(&env),
                            contract_id.into_val(&env),
                            STROOP.into_val(&env),
                        ],
                        sub_invokes: &[],
                    },
                    MockAuthInvoke {
                        contract: &token_2,
                        fn_name: &"transfer",
                        args: vec![
                            &env,
                            controller.into_val(&env),
                            contract_id.into_val(&env),
                            STROOP.into_val(&env),
                        ],
                        sub_invokes: &[],
                    },
                ],
            },
        }])
        .init(&controller, &tokens, &weights, &balances, &swap_fee);

    assert_eq!(comet.get_swap_fee(), swap_fee);
    assert_eq!(comet.get_controller(), controller);
    assert_eq!(comet.get_tokens(), tokens);
    assert_eq!(comet.get_normalized_weight(&token_1), 0_4000000);
    assert_eq!(comet.get_normalized_weight(&token_2), 0_6000000);
    assert_eq!(comet.get_balance(&token_1), STROOP);
    assert_eq!(comet.get_balance(&token_2), STROOP);
    assert_eq!(comet.get_total_supply(), 100 * STROOP);
    assert_eq!(comet.balance(&controller), 100 * STROOP);
    assert_eq!(token_1_client.balance(&controller), 0);
    assert_eq!(token_2_client.balance(&controller), 0);
    assert_eq!(token_1_client.balance(&contract_id), STROOP);
    assert_eq!(token_2_client.balance(&contract_id), STROOP);

    // verify init cannot be called again
    env.mock_all_auths();
    let result = comet.try_init(&controller, &tokens, &weights, &balances, &swap_fee);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::AlreadyInitialized as u32
        )))
    );
}
