#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    symbol_short,
    testutils::{Address as _, Events as _},
    vec, Address, Env, Symbol, TryFromVal, Vec,
};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::CometPoolContractClient,
        event::{FreezeEvent, GulpEvent},
    },
    tests::utils::{create_comet_pool, create_stellar_token},
};

fn assert_pool_event(e: &Env, pool: &Address, name: Symbol) -> soroban_sdk::Val {
    let events = e.events().all();
    let (contract, topics, data) = events.last().unwrap();
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
    e.budget().reset_unlimited();

    let (pool, controller, _) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);

    comet.set_freeze_status(&true);
    let data = assert_pool_event(&e, &pool, symbol_short!("freeze"));
    assert_eq!(
        FreezeEvent::try_from_val(&e, &data).unwrap(),
        FreezeEvent {
            controller: controller.clone(),
            frozen: true,
        }
    );

    comet.set_freeze_status(&false);
    let data = assert_pool_event(&e, &pool, symbol_short!("freeze"));
    assert_eq!(
        FreezeEvent::try_from_val(&e, &data).unwrap(),
        FreezeEvent {
            controller,
            frozen: false,
        }
    );
}

#[test]
fn test_gulp_emits_reserve_transition() {
    let e = Env::default();
    e.mock_all_auths();
    e.budget().reset_unlimited();

    let (pool, _, token) = create_pool(&e);
    let comet = CometPoolContractClient::new(&e, &pool);
    let token_client = MockTokenClient::new(&e, &token);
    let previous_balance = comet.get_balance(&token);
    let donation = 7 * STROOP;
    token_client.mint(&pool, &donation);

    comet.gulp(&token);

    let new_balance = previous_balance + donation;
    assert_eq!(comet.get_balance(&token), new_balance);
    let data = assert_pool_event(&e, &pool, symbol_short!("gulp"));
    assert_eq!(
        GulpEvent::try_from_val(&e, &data).unwrap(),
        GulpEvent {
            token,
            previous_balance,
            new_balance,
        }
    );
}
