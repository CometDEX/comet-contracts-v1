#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{testutils::Address as _, vec, Address, Env, Error, MuxedAddress, Vec};

use crate::{
    c_consts::STROOP,
    c_pool::{comet::CometPoolContractClient, error::Error as CometError},
    tests::utils::{create_comet_pool, create_stellar_token},
};

#[test]
fn test_negative_token_amounts_return_contract_error() {
    let e = Env::default();
    e.mock_all_auths();
    e.cost_estimate().budget().reset_unlimited();

    let controller = Address::generate(&e);
    let spender = Address::generate(&e);
    let recipient = Address::generate(&e);
    let token_1 = create_stellar_token(&e, &controller);
    let token_2 = create_stellar_token(&e, &controller);
    let token_1_client = MockTokenClient::new(&e, &token_1);
    let token_2_client = MockTokenClient::new(&e, &token_2);
    let balances: Vec<i128> = vec![&e, 100 * STROOP, 100 * STROOP];

    token_1_client.mint(&controller, &balances.get_unchecked(0));
    token_2_client.mint(&controller, &balances.get_unchecked(1));

    let pool = create_comet_pool(
        &e,
        &controller,
        &vec![&e, token_1, token_2],
        &vec![&e, 5 * STROOP / 10, 5 * STROOP / 10],
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&e, &pool);
    let muxed_recipient = MuxedAddress::from(recipient.clone());
    let negative_amount = -1;
    let expected_error = Error::from_contract_error(CometError::ErrTokenAmountIsNegative as u32);

    assert_eq!(
        comet
            .try_approve(&controller, &spender, &negative_amount, &100)
            .err(),
        Some(Ok(expected_error.clone()))
    );
    assert_eq!(
        comet
            .try_transfer(&controller, &muxed_recipient, &negative_amount)
            .err(),
        Some(Ok(expected_error.clone()))
    );
    assert_eq!(
        comet
            .try_transfer_from(&spender, &controller, &recipient, &negative_amount)
            .err(),
        Some(Ok(expected_error.clone()))
    );
    assert_eq!(
        comet.try_burn(&controller, &negative_amount).err(),
        Some(Ok(expected_error.clone()))
    );
    assert_eq!(
        comet
            .try_burn_from(&spender, &controller, &negative_amount)
            .err(),
        Some(Ok(expected_error))
    );
}
