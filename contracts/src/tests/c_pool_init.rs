#![cfg(test)]

extern crate std;
use std::println;

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    contract, contractimpl, testutils::{Address as _, BytesN as _, Events as _, MockAuth, MockAuthInvoke}, vec, Address, BytesN, Env, Error, FromVal, IntoVal, Val, Vec
};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::{CometPoolContract, CometPoolContractArgs, CometPoolContractClient},
        error::Error as CometError,
    },
};

mod comet {
    soroban_sdk::contractimport!(file = "../target/wasm32v1-none/optimized/comet.wasm");
}

#[contract]
struct DeployHelper;

#[contractimpl]
impl DeployHelper {
    pub fn deploy(env: Env, salt: BytesN<32>, wasm_hash: BytesN<32>, constructor_args: Vec<Val>) -> Address {
        Address::from_val(&env, &constructor_args.first().unwrap()).require_auth();
        env.deployer().with_current_contract(salt).deploy_v2(wasm_hash, constructor_args)
    }
}

#[ignore = "Cannot try __constructor calls"]
#[test]
fn test_init() {
    let env = Env::default();
    env.mock_all_auths();

    let controller = Address::generate(&env);
    let token_1 = env.register_stellar_asset_contract_v2(controller.clone());
    let token_1_address = token_1.address();
    let token_1_client = MockTokenClient::new(&env, &token_1_address);
    let token_2 = env.register_stellar_asset_contract_v2(controller.clone());
    let token_2_address = token_2.address();
    let token_2_client = MockTokenClient::new(&env, &token_2_address);
    token_1_client.mint(&controller, &STROOP);
    token_2_client.mint(&controller, &STROOP);

    let tokens = vec![&env, token_1_address.clone(), token_2_address.clone()];
    let weights = vec![&env, 0_4000000, 0_6000000];
    let balances = vec![&env, STROOP, STROOP];
    let min_fee = 0_0010000;
    let max_fee = 0_0030000;
    let low_util_balance = STROOP;
    let high_util_balance = STROOP + 1000;
    
    let wasm_hash = env.deployer().upload_contract_wasm(comet::WASM);

    let deploy_helper_address = env.register(DeployHelper, ());
    let deploy_helper_client = DeployHelperClient::new(&env, &deploy_helper_address);

    let result = deploy_helper_client.try_deploy(
        &BytesN::random(&env),
        &wasm_hash,
        &CometPoolContractArgs::__constructor(
            &controller,
            &vec![&env, token_1_address.clone()],
            &vec![&env, 0_5000000],
            &vec![&env, STROOP], 
            &min_fee,
            &max_fee,
            &token_2_address,
            &low_util_balance,
            &high_util_balance,
        ).into_val(&env)
    );

    println!("events: {:?}", env.events().all());

    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMinTokens as u32
        )))
    );
    
    // validates not enough tokens
    // let result = comet.try_init(
    //     &controller,
    //     &vec![&env, token_1_address.clone()],
    //     &vec![&env, 0_5000000],
    //     &vec![&env, STROOP],
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrMinTokens as u32
    //     )))
    // );

    // // validates all vecs are same len
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &vec![&env, 0_5000000],
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrInvalidVectorLen as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &vec![&env, STROOP],
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrInvalidVectorLen as u32
    //     )))
    // );

    // // validates total weight is 1 STROOP
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &vec![&env, 0_5000000, 0_5000001],
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrTotalWeight as u32
    //     )))
    // );

    // // validates individual weights
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &vec![&env, 0_9100000, 0_1000000],
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrMaxWeight as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &vec![&env, 0_0900000, 0_9100000],
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrMinWeight as u32
    //     )))
    // );

    // // validates balances over min
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &vec![&env, STROOP, 99],
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrInsufficientBalance as u32
    //     )))
    // );

    // // validates swap fee bounds and configuration
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &min_fee,
    //     &0_9999991,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrSwapFee as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &0_0000009,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrSwapFee as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &max_fee,
    //     &min_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrSwapFee as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &Address::generate(&env),
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrNotBound as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &high_util_balance,
    //     &low_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrSwapFee as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &(low_util_balance + 1),
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrSwapFee as u32
    //     )))
    // );
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &(low_util_balance - 10),
    //     &(low_util_balance - 1),
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::ErrSwapFee as u32
    //     )))
    // );

    // // do init
    // env.set_auths(&[]);
    // comet
    //     .mock_auths(&[MockAuth {
    //         address: &controller,
    //         invoke: &MockAuthInvoke {
    //             contract: &contract_id,
    //             fn_name: &"init",
    //             args: vec![
    //                 &env,
    //                 controller.into_val(&env),
    //                 tokens.clone().into_val(&env),
    //                 weights.clone().into_val(&env),
    //                 balances.clone().into_val(&env),
    //                 min_fee.into_val(&env),
    //                 max_fee.into_val(&env),
    //                 token_2_address.clone().into_val(&env),
    //                 low_util_balance.into_val(&env),
    //                 high_util_balance.into_val(&env),
    //             ],
    //             sub_invokes: &[
    //                 MockAuthInvoke {
    //                     contract: &token_1_address,
    //                     fn_name: &"transfer",
    //                     args: vec![
    //                         &env,
    //                         controller.into_val(&env),
    //                         contract_id.into_val(&env),
    //                         STROOP.into_val(&env),
    //                     ],
    //                     sub_invokes: &[],
    //                 },
    //                 MockAuthInvoke {
    //                     contract: &token_2_address,
    //                     fn_name: &"transfer",
    //                     args: vec![
    //                         &env,
    //                         controller.into_val(&env),
    //                         contract_id.into_val(&env),
    //                         STROOP.into_val(&env),
    //                     ],
    //                     sub_invokes: &[],
    //                 },
    //             ],
    //         },
    //     }])
    //     .init(
    //         &controller,
    //         &tokens,
    //         &weights,
    //         &balances,
    //         &min_fee,
    //         &max_fee,
    //         &token_2_address,
    //         &low_util_balance,
    //         &high_util_balance,
    //     );

    // assert_eq!(comet.get_swap_fee(), max_fee);
    // assert_eq!(comet.get_controller(), controller);
    // assert_eq!(comet.get_tokens(), tokens);
    // assert_eq!(comet.get_normalized_weight(&token_1_address), 0_4000000);
    // assert_eq!(comet.get_normalized_weight(&token_2_address), 0_6000000);
    // assert_eq!(comet.get_balance(&token_1_address), STROOP);
    // assert_eq!(comet.get_balance(&token_2_address), STROOP);
    // assert_eq!(comet.get_total_supply(), 100 * STROOP);
    // assert_eq!(comet.balance(&controller), 100 * STROOP);
    // assert_eq!(token_1_client.balance(&controller), 0);
    // assert_eq!(token_2_client.balance(&controller), 0);
    // assert_eq!(token_1_client.balance(&contract_id), STROOP);
    // assert_eq!(token_2_client.balance(&contract_id), STROOP);

    // verify init cannot be called again
    // env.mock_all_auths();
    // let result = comet.try_init(
    //     &controller,
    //     &tokens,
    //     &weights,
    //     &balances,
    //     &min_fee,
    //     &max_fee,
    //     &token_2_address,
    //     &low_util_balance,
    //     &high_util_balance,
    // );
    // assert_eq!(
    //     result.err(),
    //     Some(Ok(Error::from_contract_error(
    //         CometError::AlreadyInitialized as u32
    //     )))
    // );
}
