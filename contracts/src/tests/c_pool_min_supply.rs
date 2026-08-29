#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{testutils::Address as _, vec, Address, Env, Vec};

use crate::{
    c_consts::{INIT_POOL_SUPPLY, MIN_POOL_SUPPLY, STROOP},
    c_pool::comet::CometPoolContractClient,
    tests::utils::{create_comet_pool, create_stellar_token},
};

fn create_pool(e: &Env) -> (Address, Address, Vec<Address>) {
    e.mock_all_auths();
    e.cost_estimate().budget().reset_unlimited();

    let controller = Address::generate(e);
    let token_1 = create_stellar_token(e, &controller);
    let token_2 = create_stellar_token(e, &controller);
    let balances = vec![e, 100 * STROOP, 100 * STROOP];

    MockTokenClient::new(e, &token_1).mint(&controller, &balances.get_unchecked(0));
    MockTokenClient::new(e, &token_2).mint(&controller, &balances.get_unchecked(1));

    let tokens = vec![e, token_1, token_2];
    let pool = create_comet_pool(
        e,
        &controller,
        &tokens,
        &vec![e, 5 * STROOP / 10, 5 * STROOP / 10],
        &balances,
        0_0030000,
    );

    (pool, controller, tokens)
}

#[test]
fn test_initialization_locks_minimum_pool_supply() {
    let e = Env::default();
    let (pool, controller, _) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);

    assert_eq!(comet.get_total_supply(), INIT_POOL_SUPPLY);
    assert_eq!(
        comet.balance(&controller),
        INIT_POOL_SUPPLY - MIN_POOL_SUPPLY
    );
    assert_eq!(comet.balance(&pool), MIN_POOL_SUPPLY);
}

#[test]
fn test_exit_all_user_shares_preserves_usable_pool() {
    let e = Env::default();
    let (pool, controller, tokens) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);

    comet.exit_pool(
        &(INIT_POOL_SUPPLY - MIN_POOL_SUPPLY),
        &vec![&e, 0, 0],
        &controller,
    );

    assert_eq!(comet.get_total_supply(), MIN_POOL_SUPPLY);
    assert_eq!(comet.balance(&controller), 0);
    assert_eq!(comet.balance(&pool), MIN_POOL_SUPPLY);
    assert_eq!(comet.get_balance(&tokens.get_unchecked(0)), 1);
    assert_eq!(comet.get_balance(&tokens.get_unchecked(1)), 1);

    comet.join_pool(&1, &vec![&e, 1, 1], &controller);

    assert_eq!(comet.get_total_supply(), MIN_POOL_SUPPLY + 1);
    assert_eq!(comet.get_balance(&tokens.get_unchecked(0)), 2);
    assert_eq!(comet.get_balance(&tokens.get_unchecked(1)), 2);
}

#[test]
fn test_burn_all_user_shares_preserves_minimum_supply() {
    let e = Env::default();
    let (pool, controller, _) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);

    comet.burn(&controller, &(INIT_POOL_SUPPLY - MIN_POOL_SUPPLY));

    assert_eq!(comet.get_total_supply(), MIN_POOL_SUPPLY);
    assert_eq!(comet.balance(&controller), 0);
    assert_eq!(comet.balance(&pool), MIN_POOL_SUPPLY);
}

#[test]
fn test_burn_from_all_user_shares_preserves_minimum_supply() {
    let e = Env::default();
    let (pool, controller, _) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);
    let spender = Address::generate(&e);
    let burn_amount = INIT_POOL_SUPPLY - MIN_POOL_SUPPLY;

    comet.approve(&controller, &spender, &burn_amount, &100);
    comet.burn_from(&spender, &controller, &burn_amount);

    assert_eq!(comet.get_total_supply(), MIN_POOL_SUPPLY);
    assert_eq!(comet.balance(&controller), 0);
    assert_eq!(comet.balance(&pool), MIN_POOL_SUPPLY);
    assert_eq!(comet.allowance(&controller, &spender), 0);
}
