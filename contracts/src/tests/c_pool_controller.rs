use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::{pending_controller_or_error, CometPoolContractClient},
        error::Error as CometError,
        metadata::read_pending_controller,
    },
    tests::utils::{create_comet_pool, create_stellar_token},
};
use soroban_sdk::{
    symbol_short,
    testutils::{Address as _, Events as _, MockAuth, MockAuthInvoke},
    token::StellarAssetClient,
    vec, Address, Env, IntoVal,
};

fn pending_controller(e: &Env, pool: &Address) -> Option<Address> {
    e.as_contract(pool, || read_pending_controller(e))
}

fn create_pool(e: &Env, controller: &Address) -> Address {
    let token_1 = create_stellar_token(e, controller);
    let token_2 = create_stellar_token(e, controller);
    StellarAssetClient::new(e, &token_1).mint(controller, &STROOP);
    StellarAssetClient::new(e, &token_2).mint(controller, &STROOP);
    let tokens = vec![e, token_1, token_2];
    let weights = vec![e, 5_000_000, 5_000_000];
    let balances = vec![e, STROOP, STROOP];
    create_comet_pool(e, controller, &tokens, &weights, &balances, 10_000)
}

fn set_controller(e: &Env, client: &CometPoolContractClient, controller: &Address, next: &Address) {
    client
        .mock_auths(&[MockAuth {
            address: controller,
            invoke: &MockAuthInvoke {
                contract: &client.address,
                fn_name: &"set_controller",
                args: vec![e, next.into_val(e)],
                sub_invokes: &[],
            },
        }])
        .set_controller(next);
    assert_eq!(e.auths().len(), 1);
    assert_eq!(e.auths()[0].0, *controller);
}

fn accept_controller(e: &Env, client: &CometPoolContractClient, controller: &Address) {
    client
        .mock_auths(&[MockAuth {
            address: controller,
            invoke: &MockAuthInvoke {
                contract: &client.address,
                fn_name: &"accept_controller",
                args: vec![e],
                sub_invokes: &[],
            },
        }])
        .accept_controller();
    assert_eq!(e.auths().len(), 1);
    assert_eq!(e.auths()[0].0, *controller);
}

#[test]
fn test_two_step_controller_transfer() {
    let e = Env::default();
    e.mock_all_auths();
    let controller = Address::generate(&e);
    let first_candidate = Address::generate(&e);
    let second_candidate = Address::generate(&e);
    let third_candidate = Address::generate(&e);
    let pool = create_pool(&e, &controller);
    let client = CometPoolContractClient::new(&e, &pool);
    e.set_auths(&[]);

    set_controller(&e, &client, &controller, &first_candidate);
    assert_eq!(client.get_controller(), controller);
    assert_eq!(pending_controller(&e, &pool), Some(first_candidate));

    set_controller(&e, &client, &controller, &second_candidate);
    assert_eq!(client.get_controller(), controller);
    assert_eq!(
        pending_controller(&e, &pool),
        Some(second_candidate.clone())
    );

    accept_controller(&e, &client, &second_candidate);
    assert_eq!(client.get_controller(), second_candidate.clone());
    assert_eq!(pending_controller(&e, &pool), None);

    set_controller(&e, &client, &second_candidate, &third_candidate);
    assert_eq!(client.get_controller(), second_candidate);
    assert_eq!(pending_controller(&e, &pool), Some(third_candidate));
}

#[test]
fn test_set_controller_to_current_controller_cancels_transfer() {
    let e = Env::default();
    e.mock_all_auths();
    let controller = Address::generate(&e);
    let candidate = Address::generate(&e);
    let pool = create_pool(&e, &controller);
    let client = CometPoolContractClient::new(&e, &pool);
    e.set_auths(&[]);

    set_controller(&e, &client, &controller, &candidate);
    assert_eq!(pending_controller(&e, &pool), Some(candidate));

    set_controller(&e, &client, &controller, &controller);
    assert_eq!(client.get_controller(), controller);
    assert_eq!(pending_controller(&e, &pool), None);
    let event = vec![&e, e.events().all().last_unchecked()];
    assert_eq!(
        event,
        vec![
            &e,
            (
                pool,
                (
                    symbol_short!("POOL"),
                    symbol_short!("set_ctrl"),
                    controller.clone()
                )
                    .into_val(&e),
                controller.into_val(&e)
            )
        ]
    );
}

#[test]
fn test_accept_controller_requires_pending_transfer() {
    let e = Env::default();
    let candidate = Address::generate(&e);

    assert_eq!(
        pending_controller_or_error(None),
        Err(CometError::ErrNoPendingController)
    );
    assert_eq!(
        pending_controller_or_error(Some(candidate.clone())),
        Ok(candidate)
    );
}
