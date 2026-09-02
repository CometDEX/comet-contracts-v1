#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    symbol_short,
    testutils::{Address as _, Events as _},
    vec, Address, Env, Symbol, TryFromVal, Vec,
};

use crate::{
    c_consts::{INIT_POOL_SUPPLY, STROOP},
    c_pool::comet::CometPoolContractClient,
    tests::utils::{create_comet_pool, create_stellar_token},
};

fn assert_last_mint_event(e: &Env, pool: &Address, to: &Address, amount: i128) {
    let events = e.events().all();
    let (contract, topics, data) = events.last().unwrap();
    assert_eq!(contract, pool.clone());
    assert_eq!(topics.len(), 3);
    assert_eq!(
        Symbol::try_from_val(e, &topics.get_unchecked(0)).unwrap(),
        symbol_short!("mint")
    );
    assert_eq!(
        Address::try_from_val(e, &topics.get_unchecked(1)).unwrap(),
        pool.clone()
    );
    assert_eq!(
        Address::try_from_val(e, &topics.get_unchecked(2)).unwrap(),
        to.clone()
    );
    assert_eq!(i128::try_from_val(e, &data).unwrap(), amount);
}

#[test]
fn test_lp_issuance_emits_mint_events() {
    let e = Env::default();
    e.mock_all_auths();
    e.budget().reset_unlimited();

    let controller = Address::generate(&e);
    let user = Address::generate(&e);
    let token_1 = create_stellar_token(&e, &controller);
    let token_2 = create_stellar_token(&e, &controller);
    let token_1_client = MockTokenClient::new(&e, &token_1);
    let token_2_client = MockTokenClient::new(&e, &token_2);
    let balances: Vec<i128> = vec![&e, 100 * STROOP, 100 * STROOP];

    token_1_client.mint(&controller, &balances.get_unchecked(0));
    token_2_client.mint(&controller, &balances.get_unchecked(1));
    token_1_client.mint(&user, &(1_000 * STROOP));
    token_2_client.mint(&user, &(1_000 * STROOP));

    let pool = create_comet_pool(
        &e,
        &controller,
        &vec![&e, token_1.clone(), token_2.clone()],
        &vec![&e, 5 * STROOP / 10, 5 * STROOP / 10],
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&e, &pool);

    assert_last_mint_event(&e, &pool, &controller, INIT_POOL_SUPPLY);

    let join_amount = 10 * STROOP;
    comet.join_pool(&join_amount, &vec![&e, i128::MAX, i128::MAX], &user);
    assert_last_mint_event(&e, &pool, &user, join_amount);

    let pool_amount_out = comet.dep_tokn_amt_in_get_lp_tokns_out(&token_1, &STROOP, &0, &user);
    assert_last_mint_event(&e, &pool, &user, pool_amount_out);

    let exact_pool_amount_out = STROOP;
    comet.dep_lp_tokn_amt_out_get_tokn_in(&token_2, &exact_pool_amount_out, &i128::MAX, &user);
    assert_last_mint_event(&e, &pool, &user, exact_pool_amount_out);
}
