#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    testutils::{Address as _, MockAuth, MockAuthInvoke},
    vec, Address, Env, Error, IntoVal, Vec,
};
use std::vec as std_vec;

use crate::{
    c_consts::STROOP,
    c_pool::{comet::CometPoolContractClient, error::Error as CometError},
    tests::{balancer::F64Utils, utils::assert_approx_eq_rel},
};

use super::{
    balancer::BalancerPool,
    utils::{create_comet_pool, create_stellar_token},
};

#[test]
fn test_join_exit() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);
    let token_3 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let token_3_client = MockTokenClient::new(&env, &token_3);

    let balances: Vec<i128> = vec![&env, 100 * STROOP, 150 * STROOP, 50 * STROOP];
    let weights: Vec<i128> = vec![&env, 2 * STROOP, 5 * STROOP, 3 * STROOP];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    token_3_client.mint(&admin, &balances.get_unchecked(2));
    let starting_bal: i128 = 100_000 * STROOP;
    token_1_client.mint(&user, &starting_bal);
    token_2_client.mint(&user, &starting_bal);
    token_3_client.mint(&user, &starting_bal);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone(), token_3.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);
    let mut balancer = BalancerPool::new(
        std_vec![100.0, 150.0, 50.0],
        std_vec![0.20, 0.50, 0.30],
        0.003,
    );
    let starting_supply = comet.get_total_supply();

    let join_amount = 5.0;
    let join_amount_fixed = join_amount.to_i128(&7);
    let in_float = balancer.join_pool(join_amount);
    let mut in_float_fixed: Vec<i128> = vec![&env];
    let mut above_in_fixed: Vec<i128> = vec![&env];
    for x in in_float.iter() {
        let as_fixed = x.to_i128(&7);
        in_float_fixed.push_back(as_fixed);
        above_in_fixed.push_back(as_fixed + 1000);
    }

    //***** Join Pool *****//

    // verify negative check
    let result = comet.try_join_pool(&-1, &above_in_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify 0 check
    let result = comet.try_join_pool(&0, &above_in_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify limit in
    let mut below_in_fixed = above_in_fixed.clone();
    below_in_fixed.set(2, below_in_fixed.get_unchecked(2) - 1001);
    let result = comet.try_join_pool(&join_amount_fixed, &below_in_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitIn as u32
        )))
    );

    // -> do join
    let approval_ledger = (env.ledger().sequence() / 100000 + 1) * 100000;
    env.set_auths(&[]);
    comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"join_pool",
                args: vec![
                    &env,
                    join_amount_fixed.into_val(&env),
                    above_in_fixed.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[
                    MockAuthInvoke {
                        contract: &token_1,
                        fn_name: &"approve",
                        args: vec![
                            &env,
                            user.into_val(&env),
                            comet_id.into_val(&env),
                            above_in_fixed.get_unchecked(0).into_val(&env),
                            approval_ledger.into_val(&env),
                        ],
                        sub_invokes: &[],
                    },
                    MockAuthInvoke {
                        contract: &token_2,
                        fn_name: &"approve",
                        args: vec![
                            &env,
                            user.into_val(&env),
                            comet_id.into_val(&env),
                            above_in_fixed.get_unchecked(1).into_val(&env),
                            approval_ledger.into_val(&env),
                        ],
                        sub_invokes: &[],
                    },
                    MockAuthInvoke {
                        contract: &token_3,
                        fn_name: &"approve",
                        args: vec![
                            &env,
                            user.into_val(&env),
                            comet_id.into_val(&env),
                            above_in_fixed.get_unchecked(2).into_val(&env),
                            approval_ledger.into_val(&env),
                        ],
                        sub_invokes: &[],
                    },
                ],
            },
        }])
        .join_pool(&join_amount_fixed, &above_in_fixed, &user);

    assert_eq!(comet.balance(&user), join_amount_fixed);
    assert_eq!(
        comet.get_total_supply(),
        starting_supply + join_amount_fixed
    );
    // in-bound tokens rounded up
    let post_join_bal_1 = token_1_client.balance(&user);
    let post_join_bal_2 = token_2_client.balance(&user);
    let post_join_bal_3 = token_3_client.balance(&user);
    let post_join_comet_bal_1 = token_1_client.balance(&comet_id);
    let post_join_comet_bal_2 = token_2_client.balance(&comet_id);
    let post_join_comet_bal_3 = token_3_client.balance(&comet_id);
    assert!(post_join_bal_1 <= starting_bal - in_float_fixed.get_unchecked(0));
    assert!(post_join_bal_2 <= starting_bal - in_float_fixed.get_unchecked(1));
    assert!(post_join_bal_3 <= starting_bal - in_float_fixed.get_unchecked(2));
    assert!(post_join_comet_bal_1 >= balances.get_unchecked(0) + in_float_fixed.get_unchecked(0));
    assert!(post_join_comet_bal_2 >= balances.get_unchecked(1) + in_float_fixed.get_unchecked(1));
    assert!(post_join_comet_bal_3 >= balances.get_unchecked(2) + in_float_fixed.get_unchecked(2));
    assert_approx_eq_rel(
        starting_bal - post_join_bal_1,
        in_float_fixed.get_unchecked(0),
        0_0001000,
    );
    assert_approx_eq_rel(
        starting_bal - post_join_bal_2,
        in_float_fixed.get_unchecked(1),
        0_0001000,
    );
    assert_approx_eq_rel(
        starting_bal - post_join_bal_3,
        in_float_fixed.get_unchecked(2),
        0_0001000,
    );

    //***** Exit Pool *****//

    env.mock_all_auths();
    let exit_amount = 3.0;
    let exit_amount_fixed = exit_amount.to_i128(&7);
    let out_float = balancer.exit_pool(exit_amount);
    let mut out_float_fixed: Vec<i128> = vec![&env];
    let mut below_out_fixed: Vec<i128> = vec![&env];
    for x in out_float.iter() {
        let as_fixed = x.to_i128(&7);
        out_float_fixed.push_back(as_fixed);
        below_out_fixed.push_back(as_fixed - 1000);
    }

    // verify negative check
    let result = comet.try_exit_pool(&-1, &below_out_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify zero check
    let result = comet.try_exit_pool(&0, &below_out_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify ratio zero
    let result = comet.try_exit_pool(&1, &below_out_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMathApprox as u32
        )))
    );

    // verify burn too large
    let result = comet.try_exit_pool(&(join_amount_fixed + 1), &below_out_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInsufficientBalance as u32
        )))
    );

    // verify limit out
    let mut above_out_fixed = below_out_fixed.clone();
    above_out_fixed.set(2, above_out_fixed.get_unchecked(2) + 100000);
    let result = comet.try_exit_pool(&exit_amount_fixed, &above_out_fixed, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitOut as u32
        )))
    );

    // -> do exit
    env.set_auths(&[]);
    comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"exit_pool",
                args: vec![
                    &env,
                    exit_amount_fixed.into_val(&env),
                    below_out_fixed.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[],
            },
        }])
        .exit_pool(&exit_amount_fixed, &below_out_fixed, &user);
    assert_eq!(comet.balance(&user), join_amount_fixed - exit_amount_fixed);
    assert_eq!(
        comet.get_total_supply(),
        starting_supply + join_amount_fixed - exit_amount_fixed
    );
    assert!(token_1_client.balance(&user) <= post_join_bal_1 + out_float_fixed.get_unchecked(0));
    assert!(token_2_client.balance(&user) <= post_join_bal_2 + out_float_fixed.get_unchecked(1));
    assert!(token_3_client.balance(&user) <= post_join_bal_3 + out_float_fixed.get_unchecked(2));
    assert!(
        token_1_client.balance(&comet_id)
            >= post_join_comet_bal_1 - out_float_fixed.get_unchecked(0)
    );
    assert!(
        token_2_client.balance(&comet_id)
            >= post_join_comet_bal_2 - out_float_fixed.get_unchecked(1)
    );
    assert!(
        token_3_client.balance(&comet_id)
            >= post_join_comet_bal_3 - out_float_fixed.get_unchecked(2)
    );
    assert_approx_eq_rel(
        token_1_client.balance(&user) - post_join_bal_1,
        out_float_fixed.get_unchecked(0),
        0_0001000,
    );
    assert_approx_eq_rel(
        token_2_client.balance(&user) - post_join_bal_2,
        out_float_fixed.get_unchecked(1),
        0_0001000,
    );
    assert_approx_eq_rel(
        token_3_client.balance(&user) - post_join_bal_3,
        out_float_fixed.get_unchecked(2),
        0_0001000,
    );
}
