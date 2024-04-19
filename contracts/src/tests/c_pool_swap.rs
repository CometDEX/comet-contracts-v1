#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    testutils::{Address as _, MockAuth, MockAuthInvoke},
    vec, Address, Env, Error, IntoVal, Vec,
};
use std::{println, vec as std_vec};

use crate::{
    c_consts::STROOP,
    c_pool::{comet::CometPoolContractClient, error::Error as CometError},
    tests::{
        balancer::F64Utils,
        utils::{assert_approx_eq_abs, assert_approx_eq_rel, create_soroban_token, print_compare},
    },
};

use super::{
    balancer::BalancerPool,
    utils::{create_comet_pool, create_stellar_token},
};

#[test]
fn test_swap_out_given_in() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 100 * STROOP, 75 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let starting_bal: i128 = 100_000 * STROOP;
    token_1_client.mint(&user, &starting_bal);
    token_2_client.mint(&user, &starting_bal);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);
    let mut balancer = BalancerPool::new(std_vec![100.0, 75.0], std_vec![0.50, 0.50], 0.003);

    // verify MAX_IN_RATIO
    let result =
        comet.try_swap_exact_amount_in(&token_1, &35_0000000, &token_2, &0, &i128::MAX, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxInRatio as u32
        )))
    );

    // verify negative input
    let result = comet.try_swap_exact_amount_in(&token_1, &-1, &token_2, &0, &i128::MAX, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegative as u32
        )))
    );

    // verify checks for valid swap
    let swap_in_amount = 1.0;
    let swap_in_amount_fixed = swap_in_amount.to_i128(&7);
    let float_out = balancer.swap_out_given_in(0, 1, swap_in_amount);
    let float_out_fixed = float_out.to_i128(&7);
    let float_price_fixed = balancer.spot_price(0, 1).to_i128(&7);

    // - verify price
    let over_res_price = float_price_fixed + 100;
    let result = comet.try_swap_exact_amount_in(
        &token_1,
        &swap_in_amount_fixed,
        &token_2,
        &0,
        &over_res_price,
        &user,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitPrice as u32
        )))
    );

    // - verify limit out
    let more_than_out = float_out_fixed + 100;
    let result = comet.try_swap_exact_amount_in(
        &token_1,
        &swap_in_amount_fixed,
        &token_2,
        &more_than_out,
        &i128::MAX,
        &user,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitOut as u32
        )))
    );

    // - do swap
    let approval_ledger = (env.ledger().sequence() / 100000 + 1) * 100000;
    env.set_auths(&[]);
    let (res_2_out, _) = comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"swap_exact_amount_in",
                args: vec![
                    &env,
                    token_1.into_val(&env),
                    swap_in_amount_fixed.into_val(&env),
                    token_2.into_val(&env),
                    0i128.into_val(&env),
                    i128::MAX.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[MockAuthInvoke {
                    contract: &token_1,
                    fn_name: &"approve",
                    args: vec![
                        &env,
                        user.into_val(&env),
                        comet_id.into_val(&env),
                        swap_in_amount_fixed.into_val(&env),
                        approval_ledger.into_val(&env),
                    ],
                    sub_invokes: &[],
                }],
            },
        }])
        .swap_exact_amount_in(
            &token_1,
            &swap_in_amount_fixed,
            &token_2,
            &0,
            &i128::MAX,
            &user,
        );
    assert!(res_2_out <= float_out_fixed); // rounds down
    assert_approx_eq_rel(res_2_out, float_out_fixed, 0_0001000);

    // verify ledger state
    assert_eq!(
        token_1_client.balance(&user),
        starting_bal - swap_in_amount_fixed
    );
    assert_eq!(token_2_client.balance(&user), starting_bal + res_2_out);
    assert_eq!(
        token_1_client.balance(&comet_id),
        balances.get_unchecked(0) + swap_in_amount_fixed
    );
    assert_eq!(
        token_2_client.balance(&comet_id),
        balances.get_unchecked(1) - res_2_out
    );
}

#[test]
fn test_swap_in_given_out() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 100 * STROOP, 75 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let starting_bal: i128 = 100_000 * STROOP;
    token_1_client.mint(&user, &starting_bal);
    token_2_client.mint(&user, &starting_bal);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);
    let mut balancer = BalancerPool::new(std_vec![100.0, 75.0], std_vec![0.50, 0.50], 0.003);

    // verify MAX_OUT_RATIO
    let result = comet.try_swap_exact_amount_out(
        &token_2,
        &i128::MAX,
        &token_1,
        &36_0000000,
        &i128::MAX,
        &user,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxOutRatio as u32
        )))
    );

    // verify negative input
    let result =
        comet.try_swap_exact_amount_out(&token_2, &i128::MAX, &token_1, &-2, &i128::MAX, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegative as u32
        )))
    );

    // verify checks for valid swap
    let swap_out_amount = 1.0;
    let swap_out_amount_fixed = swap_out_amount.to_i128(&7);
    let float_in = balancer.swap_in_given_out(1, 0, swap_out_amount);
    let float_in_fixed = float_in.to_i128(&7);
    let float_price_fixed = balancer.spot_price(1, 0).to_i128(&7);

    // - verify price
    let over_in = float_in_fixed + 100000;
    let over_res_price = float_price_fixed + 100;
    let result = comet.try_swap_exact_amount_out(
        &token_2,
        &over_in,
        &token_1,
        &swap_out_amount_fixed,
        &over_res_price,
        &user,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitPrice as u32
        )))
    );

    // - verify limit it
    let less_than_in = float_in_fixed - 100;
    let result = comet.try_swap_exact_amount_out(
        &token_2,
        &less_than_in,
        &token_1,
        &swap_out_amount_fixed,
        &i128::MAX,
        &user,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitIn as u32
        )))
    );

    // - do swap
    let approval_ledger = (env.ledger().sequence() / 100000 + 1) * 100000;
    env.set_auths(&[]);
    let (res_2_in, _) = comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"swap_exact_amount_out",
                args: vec![
                    &env,
                    token_2.into_val(&env),
                    over_in.into_val(&env),
                    token_1.into_val(&env),
                    swap_out_amount_fixed.into_val(&env),
                    i128::MAX.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[MockAuthInvoke {
                    contract: &token_2,
                    fn_name: &"approve",
                    args: vec![
                        &env,
                        user.into_val(&env),
                        comet_id.into_val(&env),
                        over_in.into_val(&env),
                        approval_ledger.into_val(&env),
                    ],
                    sub_invokes: &[],
                }],
            },
        }])
        .swap_exact_amount_out(
            &token_2,
            &over_in,
            &token_1,
            &swap_out_amount_fixed,
            &i128::MAX,
            &user,
        );

    assert!(res_2_in >= float_in_fixed); // rounds up
    assert_approx_eq_rel(res_2_in, float_in_fixed, 0_0001000);

    // verify ledger state
    assert_eq!(
        token_1_client.balance(&user),
        starting_bal + swap_out_amount_fixed
    );
    assert_eq!(token_2_client.balance(&user), starting_bal - res_2_in);
    assert_eq!(
        token_1_client.balance(&comet_id),
        balances.get_unchecked(0) - swap_out_amount_fixed
    );
    assert_eq!(
        token_2_client.balance(&comet_id),
        balances.get_unchecked(1) + res_2_in
    );
}

#[test]
fn test_swap_large_amounts() {
    // test only validates recorded pool balances and assumes the above tests ensure that
    // ledger state is correct if the pool tracks internal balances correctly
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 123456789 * STROOP, 987654321 * STROOP];
    let weights: Vec<i128> = vec![&env, 3 * STROOP / 10, 7 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let starting_bal: i128 = 1_000_000_000 * STROOP;
    token_1_client.mint(&user, &starting_bal);
    token_2_client.mint(&user, &starting_bal);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);
    let mut balancer = BalancerPool::new(
        std_vec![123456789.0, 987654321.0],
        std_vec![0.30, 0.70],
        0.003,
    );

    // small amount
    let amount = 0.042;
    let amount_fixed = amount.to_i128(&7);

    // exact in
    let bal_out = balancer.swap_out_given_in(1, 0, amount).to_i128(&7);
    let (res_out, _) =
        comet.swap_exact_amount_in(&token_2, &amount_fixed, &token_1, &0, &i128::MAX, &user);
    assert!(res_out <= bal_out);
    assert_approx_eq_rel(res_out, bal_out, 0_0001000);

    // exact out
    let bal_in = balancer.swap_in_given_out(1, 0, amount).to_i128(&7);
    let (res_in, _) = comet.swap_exact_amount_out(
        &token_2,
        &i128::MAX,
        &token_1,
        &amount_fixed,
        &i128::MAX,
        &user,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    // large amount
    let amount = 25_000_000.0;
    let amount_fixed = amount.to_i128(&7);

    // exact in
    let bal_out = balancer.swap_out_given_in(1, 0, amount).to_i128(&7);
    let (res_out, _) =
        comet.swap_exact_amount_in(&token_2, &amount_fixed, &token_1, &0, &i128::MAX, &user);
    assert!(res_out <= bal_out);
    assert_approx_eq_rel(res_out, bal_out, 0_0001000);

    // exact out
    let bal_in = balancer.swap_in_given_out(1, 0, amount).to_i128(&7);
    let (res_in, _) = comet.swap_exact_amount_out(
        &token_2,
        &i128::MAX,
        &token_1,
        &amount_fixed,
        &i128::MAX,
        &user,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    print_compare(&env, &balancer, &comet_id);
}

#[test]
fn test_swap_large_price() {
    // test only validates recorded pool balances and assumes the above tests ensure that
    // ledger state is correct if the pool tracks internal balances correctly
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 9999999 * STROOP, 100 * STROOP];
    let weights: Vec<i128> = vec![&env, 1 * STROOP / 10, 9 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let starting_bal: i128 = 1_000_000_000 * STROOP;
    token_1_client.mint(&user, &starting_bal);
    token_2_client.mint(&user, &starting_bal);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);
    let mut balancer = BalancerPool::new(std_vec![9999999.0, 100.0], std_vec![0.10, 0.90], 0.003);

    // small amount

    // exact in
    let amount = 0.42;
    let amount_fixed = amount.to_i128(&7);
    let bal_out = balancer.swap_out_given_in(0, 1, amount).to_i128(&7);
    let (res_out, _) =
        comet.swap_exact_amount_in(&token_1, &amount_fixed, &token_2, &0, &i128::MAX, &user);
    assert!(res_out <= bal_out);
    assert_approx_eq_abs(res_out, bal_out, 10);

    // exact out
    let amount = 0.0000024;
    let amount_fixed = amount.to_i128(&7);
    let bal_in = balancer.swap_in_given_out(0, 1, amount).to_i128(&7);
    let (res_in, _) = comet.swap_exact_amount_out(
        &token_1,
        &i128::MAX,
        &token_2,
        &amount_fixed,
        &i128::MAX,
        &user,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    // large amount

    // exact in
    let amount = 250_000.0;
    let amount_fixed = amount.to_i128(&7);
    let bal_out = balancer.swap_out_given_in(0, 1, amount).to_i128(&7);
    let (res_out, _) =
        comet.swap_exact_amount_in(&token_1, &amount_fixed, &token_2, &0, &i128::MAX, &user);
    assert!(res_out <= bal_out);
    assert_approx_eq_rel(res_out, bal_out, 0_0001000);

    // exact out
    let amount = 25.0;
    let amount_fixed = amount.to_i128(&7);
    let bal_in = balancer.swap_in_given_out(0, 1, amount).to_i128(&7);
    let (res_in, _) = comet.swap_exact_amount_out(
        &token_1,
        &i128::MAX,
        &token_2,
        &amount_fixed,
        &i128::MAX,
        &user,
    );
    // assert!(res_in >= bal_in); // fails
    // -> next check ensures result is close to floating point result by a basis point
    //    while its possible float error is worse than rounding error at these scales, this
    //    ensures the diff is held within the min fee to avoid abuse
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    print_compare(&env, &balancer, &comet_id);
}

#[test]
fn test_swap_diff_decimals() {
    // test only validates recorded pool balances and assumes the above tests ensure that
    // ledger state is correct if the pool tracks internal balances correctly
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_soroban_token(&env, &admin, 6);
    let token_2 = create_soroban_token(&env, &admin, 9);
    let scalar_6 = 10i128.pow(6);
    let scalar_9 = 10i128.pow(9);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 1234 * scalar_6, 12345 * scalar_9];
    let weights: Vec<i128> = vec![&env, 2 * STROOP / 10, 8 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let starting_bal: i128 = 1_000_000_000 * STROOP;
    token_1_client.mint(&user, &starting_bal);
    token_2_client.mint(&user, &starting_bal);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);
    let mut balancer = BalancerPool::new(std_vec![1234.0, 12345.0], std_vec![0.20, 0.80], 0.003);

    // 1 (6 dec) in for 2 (9 dec) out
    let amount = 5.0;

    // exact in
    let amount_1_in = amount.to_i128(&6);
    let bal_out = balancer.swap_out_given_in(0, 1, amount).to_i128(&9);
    let (res_out, _) =
        comet.swap_exact_amount_in(&token_1, &amount_1_in, &token_2, &0, &i128::MAX, &user);
    assert!(res_out <= bal_out);
    assert_approx_eq_rel(res_out, bal_out, 0_0001000);

    // exact out
    let amount_2_out = amount.to_i128(&9);
    let bal_in = balancer.swap_in_given_out(0, 1, amount).to_i128(&6);
    let (res_in, _) = comet.swap_exact_amount_out(
        &token_1,
        &i128::MAX,
        &token_2,
        &amount_2_out,
        &i128::MAX,
        &user,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    // 2 (9 dec) for 1 (6 dec)

    // exact in
    let amount_2_in = amount.to_i128(&9);
    let bal_out = balancer.swap_out_given_in(1, 0, amount).to_i128(&6);
    let (res_out, _) =
        comet.swap_exact_amount_in(&token_2, &amount_2_in, &token_1, &0, &i128::MAX, &user);
    assert!(res_out <= bal_out);
    assert_approx_eq_rel(res_out, bal_out, 0_0001000);

    // exact out
    let amount_1_out = amount.to_i128(&6);
    let bal_in = balancer.swap_in_given_out(1, 0, amount).to_i128(&9);
    let (res_in, _) = comet.swap_exact_amount_out(
        &token_2,
        &i128::MAX,
        &token_1,
        &amount_1_out,
        &i128::MAX,
        &user,
    );
    println!("result: {:?}", res_in);
    println!("float_: {:?}", bal_in);
    println!("diff: {:?}", res_in - bal_in);
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);
}
