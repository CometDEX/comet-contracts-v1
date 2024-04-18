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
fn test_single_sided_dep() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 100 * STROOP, 50 * STROOP];
    let weights: Vec<i128> = vec![&env, 8 * STROOP, 2 * STROOP];
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
    let mut balancer = BalancerPool::new(std_vec![100.0, 50.0], std_vec![0.80, 0.20], 0.003);

    let starting_supply = comet.get_total_supply();

    //***** single sided dep given token in ******//

    let dep_amount = 1.0;
    let dep_amount_fixed = dep_amount.to_i128(&7);
    let bal_pool_mint = balancer.single_sided_dep_given_in(0, dep_amount);
    let bal_pool_mint_fixed = bal_pool_mint.to_i128(&7);

    // verify MAX_IN_RATIO
    let result = comet.try_dep_tokn_amt_in_get_lp_tokns_out(&token_1, &350_0000000, &0, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxInRatio as u32
        )))
    );

    // verify invalid input
    let result = comet.try_dep_tokn_amt_in_get_lp_tokns_out(&token_1, &0, &0, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify limit out
    let more_than_out = bal_pool_mint_fixed + 1000;
    let result = comet.try_dep_tokn_amt_in_get_lp_tokns_out(
        &token_1,
        &dep_amount_fixed,
        &more_than_out,
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
    let pool_mint = comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"dep_tokn_amt_in_get_lp_tokns_out",
                args: vec![
                    &env,
                    token_1.into_val(&env),
                    dep_amount_fixed.into_val(&env),
                    0i128.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[MockAuthInvoke {
                    contract: &token_1,
                    fn_name: &"approve",
                    args: vec![
                        &env,
                        user.into_val(&env),
                        comet_id.into_val(&env),
                        dep_amount_fixed.into_val(&env),
                        approval_ledger.into_val(&env),
                    ],
                    sub_invokes: &[],
                }],
            },
        }])
        .dep_tokn_amt_in_get_lp_tokns_out(&token_1, &dep_amount_fixed, &0, &user);
    assert!(pool_mint <= bal_pool_mint_fixed); // rounds down
    assert_approx_eq_rel(pool_mint, bal_pool_mint_fixed, 0_0001000);

    // verify ledger state
    assert_eq!(
        token_1_client.balance(&user),
        starting_bal - dep_amount_fixed
    );
    assert_eq!(comet.balance(&user), pool_mint);
    assert_eq!(
        token_1_client.balance(&comet_id),
        balances.get_unchecked(0) + dep_amount_fixed
    );
    assert_eq!(comet.get_total_supply(), starting_supply + pool_mint);

    //***** single sided dep given pool mint ******//

    env.mock_all_auths();
    let mint_amount = 1.0;
    let mint_amount_fixed = mint_amount.to_i128(&7);
    let bal_token_in = balancer.single_sided_dep_given_out(1, mint_amount);
    let bal_token_in_fixed = bal_token_in.to_i128(&7);
    let over_token_in = bal_token_in_fixed + 1000;

    // verify MAX_IN_RATIO
    let result =
        comet.try_dep_lp_tokn_amt_out_get_tokn_in(&token_2, &35_0000000, &i128::MAX, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxInRatio as u32
        )))
    );

    // verify invalid input
    let result = comet.try_dep_lp_tokn_amt_out_get_tokn_in(&token_2, &0, &over_token_in, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify limit out
    let under_token_in = bal_token_in_fixed - 1000;
    let result = comet.try_dep_lp_tokn_amt_out_get_tokn_in(
        &token_2,
        &mint_amount_fixed,
        &under_token_in,
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
    let token_in = comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"dep_lp_tokn_amt_out_get_tokn_in",
                args: vec![
                    &env,
                    token_2.into_val(&env),
                    mint_amount_fixed.into_val(&env),
                    over_token_in.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[MockAuthInvoke {
                    contract: &token_2,
                    fn_name: &"approve",
                    args: vec![
                        &env,
                        user.into_val(&env),
                        comet_id.into_val(&env),
                        over_token_in.into_val(&env),
                        approval_ledger.into_val(&env),
                    ],
                    sub_invokes: &[],
                }],
            },
        }])
        .dep_lp_tokn_amt_out_get_tokn_in(&token_2, &mint_amount_fixed, &over_token_in, &user);
    assert!(token_in >= bal_token_in_fixed); // rounds up
    assert_approx_eq_rel(token_in, bal_token_in_fixed, 0_0001000);

    // verify ledger state
    assert_eq!(token_2_client.balance(&user), starting_bal - token_in);
    assert_eq!(comet.balance(&user), pool_mint + mint_amount_fixed);
    assert_eq!(
        token_2_client.balance(&comet_id),
        balances.get_unchecked(1) + token_in
    );
    assert_eq!(
        comet.get_total_supply(),
        starting_supply + pool_mint + mint_amount_fixed
    );
}

#[test]
fn test_single_sided_wdr() {
    let env = Env::default();
    env.mock_all_auths();
    env.budget().reset_unlimited();

    let admin = Address::generate(&env);
    let user = Address::generate(&env);

    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);

    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 100 * STROOP, 50 * STROOP];
    let weights: Vec<i128> = vec![&env, 6 * STROOP, 4 * STROOP];
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
    let mut balancer = BalancerPool::new(std_vec![100.0, 50.0], std_vec![0.60, 0.40], 0.003);

    // join pool w/ user to have some tokens to withdrawal
    let starting_bal_comet = 10 * STROOP;
    comet.join_pool(
        &starting_bal_comet,
        &vec![&env, starting_bal, starting_bal],
        &user,
    );
    balancer.join_pool(10.0);

    let starting_supply = comet.get_total_supply();
    let starting_comet_bal_1 = token_1_client.balance(&comet_id);
    let starting_comet_bal_2 = token_2_client.balance(&comet_id);
    let starting_bal_1 = token_1_client.balance(&user);
    let starting_bal_2 = token_2_client.balance(&user);

    //***** single sided wdr given shares in ******//

    let burn_amount = 1.0;
    let burn_amount_fixed = burn_amount.to_i128(&7);
    let bal_token_out = balancer.single_sided_wd_given_in(0, burn_amount);
    let bal_token_out_fixed = bal_token_out.to_i128(&7);
    let under_out = bal_token_out_fixed - 1000;

    // verify MAX_IN_RATIO
    let result = comet.try_wdr_tokn_amt_in_get_lp_tokns_out(&token_1, &99_9999999, &0, &admin);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxInRatio as u32
        )))
    );

    // verify invalid input
    let result = comet.try_wdr_tokn_amt_in_get_lp_tokns_out(&token_1, &0, &0, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify over wdr
    let result =
        comet.try_wdr_tokn_amt_in_get_lp_tokns_out(&token_1, &(starting_bal_comet + 1), &0, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInsufficientBalance as u32
        )))
    );

    // verify limit out
    let over_out = bal_token_out_fixed + 1000;
    let result =
        comet.try_wdr_tokn_amt_in_get_lp_tokns_out(&token_1, &burn_amount_fixed, &over_out, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitOut as u32
        )))
    );

    // - do swap
    env.set_auths(&[]);
    let token_out = comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"wdr_tokn_amt_in_get_lp_tokns_out",
                args: vec![
                    &env,
                    token_1.into_val(&env),
                    burn_amount_fixed.into_val(&env),
                    under_out.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[],
            },
        }])
        .wdr_tokn_amt_in_get_lp_tokns_out(&token_1, &burn_amount_fixed, &under_out, &user);
    assert!(token_out <= bal_token_out_fixed); // rounds down
    assert_approx_eq_rel(token_out, bal_token_out_fixed, 0_0001000);

    // verify ledger state
    assert_eq!(token_1_client.balance(&user), starting_bal_1 + token_out);
    assert_eq!(comet.balance(&user), starting_bal_comet - burn_amount_fixed);
    assert_eq!(
        token_1_client.balance(&comet_id),
        starting_comet_bal_1 - token_out
    );
    assert_eq!(
        comet.get_total_supply(),
        starting_supply - burn_amount_fixed
    );

    //***** single sided wdr given token out ******//

    env.mock_all_auths();
    let bal_token_out = 1.0;
    let token_out_fixed = bal_token_out.to_i128(&7);
    let bal_burn = balancer.single_sided_wd_given_out(1, bal_token_out);
    let bal_burn_fixed = bal_burn.to_i128(&7);
    let over_burn = bal_burn_fixed + 1000;

    // verify MAX_OUT_RATIO
    let result =
        comet.try_wdr_tokn_amt_out_get_lp_tokns_in(&token_2, &20_0000000, &i128::MAX, &admin);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrMaxOutRatio as u32
        )))
    );

    // verify invalid input
    let result = comet.try_wdr_tokn_amt_out_get_lp_tokns_in(&token_2, &0, &over_burn, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrNegativeOrZero as u32
        )))
    );

    // verify over wdr
    let result =
        comet.try_wdr_tokn_amt_out_get_lp_tokns_in(&token_2, &14_0000000, &i128::MAX, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrInsufficientBalance as u32
        )))
    );

    // verify limit out
    let under_burn = bal_burn_fixed - 1000;
    let result =
        comet.try_wdr_tokn_amt_out_get_lp_tokns_in(&token_2, &token_out_fixed, &under_burn, &user);
    assert_eq!(
        result.err(),
        Some(Ok(Error::from_contract_error(
            CometError::ErrLimitIn as u32
        )))
    );

    // - do swap
    env.set_auths(&[]);
    let pool_burn = comet
        .mock_auths(&[MockAuth {
            address: &user,
            invoke: &MockAuthInvoke {
                contract: &comet_id,
                fn_name: &"wdr_tokn_amt_out_get_lp_tokns_in",
                args: vec![
                    &env,
                    token_2.into_val(&env),
                    burn_amount_fixed.into_val(&env),
                    under_out.into_val(&env),
                    user.into_val(&env),
                ],
                sub_invokes: &[],
            },
        }])
        .wdr_tokn_amt_out_get_lp_tokns_in(&token_2, &token_out_fixed, &under_out, &user);
    assert!(pool_burn >= bal_burn_fixed); // rounds up
    assert_approx_eq_rel(pool_burn, bal_burn_fixed, 0_0001000);

    // verify ledger state
    assert_eq!(
        token_2_client.balance(&user),
        starting_bal_2 + token_out_fixed
    );
    assert_eq!(
        comet.balance(&user),
        starting_bal_comet - burn_amount_fixed - pool_burn
    );
    assert_eq!(
        token_2_client.balance(&comet_id),
        starting_comet_bal_2 - token_out_fixed
    );
    assert_eq!(
        comet.get_total_supply(),
        starting_supply - burn_amount_fixed - pool_burn
    );
}
