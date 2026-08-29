#![cfg(test)]

use crate::tests::utils::MockTokenClient;
use soroban_sdk::{
    symbol_short, testutils::Address as _, vec, Address, Env, Map, Symbol, TryFromVal, Val, Vec,
};

use crate::{
    c_consts::STROOP,
    c_pool::comet::CometPoolContractClient,
    tests::utils::{create_comet_pool, create_stellar_token, event_from_end},
};

fn assert_pool_event(e: &Env, pool: &Address, name: Symbol) -> soroban_sdk::Val {
    let (contract, topics, data) = event_from_end(e, 1);
    assert_eq!(contract, pool.clone());
    assert_eq!(topics.len(), 2);
    assert_eq!(
        Symbol::try_from_val(e, &topics.get_unchecked(0)).unwrap(),
        symbol_short!("POOL")
    );
    assert_eq!(
        Symbol::try_from_val(e, &topics.get_unchecked(1)).unwrap(),
        name
    );
    data
}

fn event_data_map(e: &Env, data: &Val) -> Map<Symbol, Val> {
    Map::try_from_val(e, data).unwrap()
}

fn create_pool(e: &Env) -> (Address, Address, Address) {
    let controller = Address::generate(e);
    let token_1 = create_stellar_token(e, &controller);
    let token_2 = create_stellar_token(e, &controller);
    let token_1_client = MockTokenClient::new(e, &token_1);
    let token_2_client = MockTokenClient::new(e, &token_2);
    let balances: Vec<i128> = vec![e, 100 * STROOP, 100 * STROOP];

    token_1_client.mint(&controller, &balances.get_unchecked(0));
    token_2_client.mint(&controller, &balances.get_unchecked(1));

    let pool = create_comet_pool(
        e,
        &controller,
        &vec![e, token_1.clone(), token_2],
        &vec![e, 5 * STROOP / 10, 5 * STROOP / 10],
        &balances,
        0_0030000,
    );

    (pool, controller, token_1)
}

#[test]
fn test_set_freeze_status_emits_event() {
    let e = Env::default();
    e.mock_all_auths();
    e.cost_estimate().budget().reset_unlimited();

    let (pool, controller, _) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);

    comet.set_freeze_status(&true);
    let data = assert_pool_event(&e, &pool, symbol_short!("freeze"));
    let data = event_data_map(&e, &data);
    assert_eq!(
        Address::try_from_val(&e, &data.get(Symbol::new(&e, "controller")).unwrap()).unwrap(),
        controller.clone()
    );
    assert!(bool::try_from_val(&e, &data.get(symbol_short!("frozen")).unwrap()).unwrap());

    comet.set_freeze_status(&false);
    let data = assert_pool_event(&e, &pool, symbol_short!("freeze"));
    let data = event_data_map(&e, &data);
    assert_eq!(
        Address::try_from_val(&e, &data.get(Symbol::new(&e, "controller")).unwrap()).unwrap(),
        controller
    );
    assert!(!bool::try_from_val(&e, &data.get(symbol_short!("frozen")).unwrap()).unwrap());
}

#[test]
fn test_gulp_emits_reserve_transition() {
    let e = Env::default();
    e.mock_all_auths();
    e.cost_estimate().budget().reset_unlimited();

    let (pool, _, token) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);
    let token_client = MockTokenClient::new(&e, &token);
    let previous_balance = comet.get_balance(&token);
    let donation = 7 * STROOP;
    token_client.mint(&pool, &donation);

    comet.gulp(&token);

    let new_balance = previous_balance + donation;
    let data = assert_pool_event(&e, &pool, symbol_short!("gulp"));
    let data = event_data_map(&e, &data);
    assert_eq!(
        Address::try_from_val(&e, &data.get(symbol_short!("token")).unwrap()).unwrap(),
        token.clone()
    );
    assert_eq!(
        i128::try_from_val(&e, &data.get(Symbol::new(&e, "previous_balance")).unwrap()).unwrap(),
        previous_balance
    );
    assert_eq!(
        i128::try_from_val(&e, &data.get(Symbol::new(&e, "new_balance")).unwrap()).unwrap(),
        new_balance
    );
    assert_eq!(comet.get_balance(&token), new_balance);
}
