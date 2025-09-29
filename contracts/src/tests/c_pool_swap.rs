#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    testutils::{Address as _, MockAuth, MockAuthInvoke},
    vec, Address, Env, Error, IntoVal, Vec,
};
use std::{println, vec as std_vec};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::CometPoolContractClient,
        error::Error as CometError,
        storage_types::{FeeRecipient, FeeRule},
    },
    tests::{
        balancer::F64Utils,
        utils::{assert_approx_eq_abs, assert_approx_eq_rel, create_soroban_token, print_compare},
    },
};

use super::{
    balancer::BalancerPool,
    utils::{create_comet_pool, create_stellar_token},
};

fn compute_expected_payouts(percents: &[i128], fee_total: i128) -> std::vec::Vec<i128> {
    let mut remaining = fee_total;
    let mut payouts = std::vec::Vec::new();
    for percent in percents.iter() {
        if remaining <= 0 {
            payouts.push(0);
            continue;
        }
        let desired = percent.checked_mul(fee_total).expect("fee_total overflow") / STROOP;
        let payout = desired.min(remaining);
        payouts.push(payout);
        remaining -= payout;
    }
    payouts
}

#[test]
fn test_swap_out_given_in() {
    let env = Env::default();
    env.mock_all_auths();
    env.cost_estimate().budget().reset_unlimited();

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
    let result = comet.try_swap_exact_amount_in(
        &token_1,
        &35_0000000,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxInRatio as u32
        )))
    );

    // verify negative input
    let result =
        comet.try_swap_exact_amount_in(&token_1, &-1, &token_2, &0, &i128::MAX, &user, &None);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify zero input
    let result =
        comet.try_swap_exact_amount_in(&token_1, &0, &token_2, &0, &i128::MAX, &user, &None);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
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
        &None,
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
        &None,
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
                    Option::<Vec<FeeRecipient>>::None.into_val(&env),
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
            &None,
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
    env.cost_estimate().budget().reset_unlimited();

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
        &None,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxOutRatio as u32
        )))
    );

    // verify negative input
    let result = comet.try_swap_exact_amount_out(
        &token_2,
        &i128::MAX,
        &token_1,
        &-2,
        &i128::MAX,
        &user,
        &None,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify zero input
    let result = comet.try_swap_exact_amount_out(
        &token_2,
        &i128::MAX,
        &token_1,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );
    let result =
        comet.try_swap_exact_amount_out(&token_2, &0, &token_1, &1, &i128::MAX, &user, &None);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
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
        &None,
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
        &None,
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
                    Option::<Vec<FeeRecipient>>::None.into_val(&env),
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
            &None,
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
    env.cost_estimate().budget().reset_unlimited();

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
    let (res_out, _) = comet.swap_exact_amount_in(
        &token_2,
        &amount_fixed,
        &token_1,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
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
        &None,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    // large amount
    let amount = 25_000_000.0;
    let amount_fixed = amount.to_i128(&7);

    // exact in
    let bal_out = balancer.swap_out_given_in(1, 0, amount).to_i128(&7);
    let (res_out, _) = comet.swap_exact_amount_in(
        &token_2,
        &amount_fixed,
        &token_1,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
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
        &None,
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
    env.cost_estimate().budget().reset_unlimited();

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
    let (res_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &amount_fixed,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
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
        &None,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    // large amount

    // exact in
    let amount = 250_000.0;
    let amount_fixed = amount.to_i128(&7);
    let bal_out = balancer.swap_out_given_in(0, 1, amount).to_i128(&7);
    let (res_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &amount_fixed,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
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
        &None,
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
    env.cost_estimate().budget().reset_unlimited();

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
    let (res_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &amount_1_in,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
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
        &None,
    );
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);

    // 2 (9 dec) for 1 (6 dec)

    // exact in
    let amount_2_in = amount.to_i128(&9);
    let bal_out = balancer.swap_out_given_in(1, 0, amount).to_i128(&6);
    let (res_out, _) = comet.swap_exact_amount_in(
        &token_2,
        &amount_2_in,
        &token_1,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
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
        &None,
    );
    println!("result: {:?}", res_in);
    println!("float_: {:?}", bal_in);
    println!("diff: {:?}", res_in - bal_in);
    assert!(res_in >= bal_in);
    assert_approx_eq_rel(res_in, bal_in, 0_0001000);
}

#[test]
fn test_fee_distribution_pool_recipients_exact_in() {
    let env = Env::default();
    env.mock_all_auths();
    env.cost_estimate().budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);
    let recipient_a = Address::generate(&env);
    let recipient_b = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);
    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);

    let balances: Vec<i128> = vec![&env, 100 * STROOP, 75 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let user_funding = 1000 * STROOP;
    token_1_client.mint(&user, &user_funding);
    token_2_client.mint(&user, &user_funding);

    let swap_fee = 1_000000; // 10%
    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        swap_fee,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let pool_recipients = vec![
        &env,
        FeeRecipient {
            recipient: recipient_a.clone(),
            percent: 6_000000,
        },
        FeeRecipient {
            recipient: recipient_b.clone(),
            percent: 3_000000,
        },
    ];
    let rule = FeeRule {
        fee_asset: token_1.clone(),
        recipients: pool_recipients,
    };
    comet.replace_fee_rule(&rule);

    let pool_balance_before = comet.get_balance(&token_1);

    let token_amount_in = 10 * STROOP;
    let (_token_amount_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &token_amount_in,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );

    let fee_total = swap_fee * token_amount_in / STROOP;
    let percents = [6_000000, 3_000000];
    let expected = compute_expected_payouts(&percents, fee_total);
    let distributed_total: i128 = expected.iter().copied().sum();

    assert_eq!(token_1_client.balance(&recipient_a), expected[0]);
    assert_eq!(token_1_client.balance(&recipient_b), expected[1]);

    let pool_balance_after = comet.get_balance(&token_1);
    assert_eq!(
        pool_balance_after,
        pool_balance_before + token_amount_in - distributed_total
    );
    assert_eq!(
        token_1_client.balance(&comet_id),
        balances.get_unchecked(0) + token_amount_in - distributed_total
    );

    let leftover = fee_total - distributed_total;
    assert!(leftover >= 0);
    assert_eq!(token_1_client.balance(&comet_id) - pool_balance_after, 0);
}

#[test]
fn test_fee_distribution_trade_recipients_share_remainder() {
    let env = Env::default();
    env.mock_all_auths();
    env.cost_estimate().budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);
    let pool_recipient = Address::generate(&env);
    let pool_recipient_b = Address::generate(&env);
    let trade_recipient_a = Address::generate(&env);
    let trade_recipient_b = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);
    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);

    let balances: Vec<i128> = vec![&env, 90 * STROOP, 110 * STROOP];
    let weights: Vec<i128> = vec![&env, 4 * STROOP / 10, 6 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let user_funding = 1000 * STROOP;
    token_1_client.mint(&user, &user_funding);
    token_2_client.mint(&user, &user_funding);

    let swap_fee = 1_000000; // 10%
    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        swap_fee,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let rule = FeeRule {
        fee_asset: token_1.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: pool_recipient.clone(),
                percent: 4_000000,
            },
            FeeRecipient {
                recipient: pool_recipient_b.clone(),
                percent: 1_000000,
            },
        ],
    };
    comet.replace_fee_rule(&rule);

    let pool_balance_before = comet.get_balance(&token_1);

    let trade_recipients_vec = vec![
        &env,
        FeeRecipient {
            recipient: trade_recipient_a.clone(),
            percent: 3_000000,
        },
        FeeRecipient {
            recipient: trade_recipient_b.clone(),
            percent: 2_000000,
        },
    ];
    let trade_option = Some(trade_recipients_vec);

    let token_amount_in = 10 * STROOP;
    let (_token_amount_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &token_amount_in,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &trade_option,
    );

    let fee_total = swap_fee * token_amount_in / STROOP;
    let combined_percents = [4_000000, 1_000000, 3_000000, 2_000000];
    let payouts = compute_expected_payouts(&combined_percents, fee_total);
    let distributed_total: i128 = payouts.iter().copied().sum();

    assert_eq!(token_1_client.balance(&pool_recipient), payouts[0]);
    assert_eq!(token_1_client.balance(&pool_recipient_b), payouts[1]);
    assert_eq!(token_1_client.balance(&trade_recipient_a), payouts[2]);
    assert_eq!(token_1_client.balance(&trade_recipient_b), payouts[3]);

    assert_eq!(distributed_total, fee_total);

    let pool_balance_after = comet.get_balance(&token_1);
    assert_eq!(
        pool_balance_after,
        pool_balance_before + token_amount_in - distributed_total
    );
}

#[test]
fn test_fee_distribution_fee_asset_token_out_exact_out() {
    let env = Env::default();
    env.mock_all_auths();
    env.cost_estimate().budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);
    let recipient_a = Address::generate(&env);
    let recipient_b = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);
    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);

    let balances: Vec<i128> = vec![&env, 120 * STROOP, 80 * STROOP];
    let weights: Vec<i128> = vec![&env, 6 * STROOP / 10, 4 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let user_funding = 1_000 * STROOP;
    token_1_client.mint(&user, &user_funding);
    token_2_client.mint(&user, &user_funding);

    let swap_fee = 1_000000; // 10%
    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        swap_fee,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let rule = FeeRule {
        fee_asset: token_2.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: recipient_a.clone(),
                percent: 5_000000,
            },
            FeeRecipient {
                recipient: recipient_b.clone(),
                percent: 3_000000,
            },
        ],
    };
    comet.replace_fee_rule(&rule);

    let pool_balance_before = comet.get_balance(&token_2);

    let token_amount_out = 5 * STROOP;
    let (token_amount_in, _) = comet.swap_exact_amount_out(
        &token_1,
        &i128::MAX,
        &token_2,
        &token_amount_out,
        &i128::MAX,
        &user,
        &None,
    );
    assert!(token_amount_in > 0);

    let fee_total = swap_fee * token_amount_out / STROOP;
    let percents = [5_000000, 3_000000];
    let payouts = compute_expected_payouts(&percents, fee_total);
    let distributed_total: i128 = payouts.iter().copied().sum();

    assert_eq!(token_2_client.balance(&recipient_a), payouts[0]);
    assert_eq!(token_2_client.balance(&recipient_b), payouts[1]);

    let pool_balance_after = comet.get_balance(&token_2);
    assert_eq!(
        pool_balance_after,
        pool_balance_before - token_amount_out - distributed_total
    );

    assert_eq!(
        token_2_client.balance(&comet_id),
        balances.get_unchecked(1) - token_amount_out - distributed_total
    );

    let leftover = fee_total - distributed_total;
    assert!(leftover >= 0);
}

#[test]
fn test_replace_fee_rule_validation_errors() {
    let env = Env::default();
    env.mock_all_auths();

    let admin = Address::generate(&env);
    let new_recipient = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 50 * STROOP, 50 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let unattached_asset_rule = FeeRule {
        fee_asset: Address::generate(&env),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: new_recipient.clone(),
                percent: 5_000000,
            },
        ],
    };
    let result = comet.try_replace_fee_rule(&unattached_asset_rule);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrFeeAssetNotBound as u32
        )))
    );

    let duplicate_rule = FeeRule {
        fee_asset: token_1.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: new_recipient.clone(),
                percent: 3_000000,
            },
            FeeRecipient {
                recipient: new_recipient.clone(),
                percent: 2_000000,
            },
        ],
    };
    let result = comet.try_replace_fee_rule(&duplicate_rule);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrFeeRecipientDuplicate as u32
        )))
    );

    let oversubscribed_rule = FeeRule {
        fee_asset: token_1.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: Address::generate(&env),
                percent: 7_000000,
            },
            FeeRecipient {
                recipient: Address::generate(&env),
                percent: 6_000000,
            },
        ],
    };
    let result = comet.try_replace_fee_rule(&oversubscribed_rule);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrFeeRecipientSum as u32
        )))
    );

    let self_rule = FeeRule {
        fee_asset: token_1.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: comet_id.clone(),
                percent: 2_000000,
            },
        ],
    };
    let result = comet.try_replace_fee_rule(&self_rule);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInvalidFeeRecipient as u32
        )))
    );
}

#[test]
fn test_trade_recipient_validation_failures() {
    let env = Env::default();
    env.mock_all_auths();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 80 * STROOP, 80 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let user_funding = 80 * STROOP;
    token_1_client.mint(&user, &user_funding);
    token_2_client.mint(&user, &user_funding);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let over_sum = vec![
        &env,
        FeeRecipient {
            recipient: Address::generate(&env),
            percent: 7_000000,
        },
        FeeRecipient {
            recipient: Address::generate(&env),
            percent: 6_000000,
        },
    ];
    let trade_amount = STROOP;
    let result = comet.try_swap_exact_amount_in(
        &token_1,
        &trade_amount,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &Some(over_sum),
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrFeeRecipientSum as u32
        )))
    );

    let dup_recipient = Address::generate(&env);
    let duplicates = vec![
        &env,
        FeeRecipient {
            recipient: dup_recipient.clone(),
            percent: 3_000000,
        },
        FeeRecipient {
            recipient: dup_recipient,
            percent: 1_000000,
        },
    ];
    let result = comet.try_swap_exact_amount_in(
        &token_1,
        &trade_amount,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &Some(duplicates),
    );
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrFeeRecipientDuplicate as u32
        )))
    );
}

#[test]
fn test_fee_rule_skips_when_asset_not_involved() {
    let env = Env::default();
    env.mock_all_auths();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);
    let token_3 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let token_3_client = MockTokenClient::new(&env, &token_3);
    let balances: Vec<i128> = vec![&env, 90 * STROOP, 90 * STROOP, 90 * STROOP];
    let weights: Vec<i128> = vec![&env, 3 * STROOP / 10, 3 * STROOP / 10, 4 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    token_3_client.mint(&admin, &balances.get_unchecked(2));
    let user_funding = 100 * STROOP;
    token_1_client.mint(&user, &user_funding);
    token_2_client.mint(&user, &user_funding);
    token_3_client.mint(&user, &user_funding);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone(), token_3.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let skip_recipient = Address::generate(&env);
    let rule = FeeRule {
        fee_asset: token_3.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: skip_recipient.clone(),
                percent: 5_000000,
            },
        ],
    };
    comet.replace_fee_rule(&rule);

    let pool_balance_before = comet.get_balance(&token_3);
    let recipient_balance_before = token_3_client.balance(&skip_recipient);

    let trade_amount = 5 * STROOP;
    let (token_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &trade_amount,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );
    assert!(token_out > 0);

    let pool_balance_after = comet.get_balance(&token_3);
    assert_eq!(pool_balance_after, pool_balance_before);
    assert_eq!(token_3_client.balance(&skip_recipient), recipient_balance_before);
}

#[test]
fn test_fee_distribution_refunds_failed_transfers() {
    let env = Env::default();
    env.mock_all_auths();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 100 * STROOP, 100 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));
    let user_funding = 100 * STROOP;
    token_1_client.mint(&user, &user_funding);
    token_2_client.mint(&user, &user_funding);

    let comet_id = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1.clone(), token_2.clone()],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &comet_id);

    let failing_recipient = Address::from_str(
        &env,
        "GCEDG23LK46PHGXIY63E3ELQGBX6VHQ4EWLYT7FMLOOCIS3ZY2ITHDXB",
    );
    let successful_recipient = Address::generate(&env);

    let rule = FeeRule {
        fee_asset: token_1.clone(),
        recipients: vec![
            &env,
            FeeRecipient {
                recipient: failing_recipient.clone(),
                percent: 5_000000,
            },
            FeeRecipient {
                recipient: successful_recipient.clone(),
                percent: 3_000000,
            },
        ],
    };
    comet.replace_fee_rule(&rule);

    let pool_balance_before = comet.get_balance(&token_1);

    let token_amount_in = 10 * STROOP;
    let (_token_amount_out, _) = comet.swap_exact_amount_in(
        &token_1,
        &token_amount_in,
        &token_2,
        &0,
        &i128::MAX,
        &user,
        &None,
    );

    let successful_amount = token_1_client.balance(&successful_recipient);

    let pool_balance_after = comet.get_balance(&token_1);
    let fee_total = (0_0030000 * token_amount_in) / STROOP;
    let allocations = compute_expected_payouts(&[5_000000, 3_000000], fee_total);
    let all_success_balance = pool_balance_before + token_amount_in
        - allocations.iter().copied().sum::<i128>();
    assert_eq!(successful_amount, allocations[1]);
    assert_eq!(
        pool_balance_after,
        all_success_balance + allocations[0]
    );
}
