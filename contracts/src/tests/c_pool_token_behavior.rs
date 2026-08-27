#![cfg(test)]

use sep_41_token::testutils::MockTokenClient;
use soroban_sdk::{
    contract, contractimpl, contracttype, testutils::Address as _, vec, Address, Env, Error, String,
};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::{CometPoolContract, CometPoolContractClient},
        error::Error as CometError,
    },
};

#[derive(Clone)]
#[contracttype]
enum FeeTokenKey {
    Balance(Address),
    Fee,
}

#[contract]
struct FeeToken;

#[contractimpl]
impl FeeToken {
    pub fn init(e: Env) {
        e.storage().instance().set(&FeeTokenKey::Fee, &0i128);
    }

    pub fn mint(e: Env, to: Address, amount: i128) {
        write_balance(&e, &to, read_balance(&e, &to) + amount);
    }

    pub fn set_fee(e: Env, fee: i128) {
        e.storage().instance().set(&FeeTokenKey::Fee, &fee);
    }

    pub fn approve(
        _e: Env,
        _from: Address,
        _spender: Address,
        _amount: i128,
        _expiration_ledger: u32,
    ) {
    }

    pub fn balance(e: Env, id: Address) -> i128 {
        read_balance(&e, &id)
    }

    pub fn transfer(e: Env, from: Address, to: Address, amount: i128) {
        transfer(&e, &from, &to, amount);
    }

    pub fn transfer_from(e: Env, _spender: Address, from: Address, to: Address, amount: i128) {
        transfer(&e, &from, &to, amount);
    }

    pub fn decimals(_e: Env) -> u32 {
        7
    }

    pub fn name(e: Env) -> String {
        String::from_str(&e, "Fee Token")
    }

    pub fn symbol(e: Env) -> String {
        String::from_str(&e, "FEE")
    }
}

fn read_balance(e: &Env, address: &Address) -> i128 {
    e.storage()
        .instance()
        .get(&FeeTokenKey::Balance(address.clone()))
        .unwrap_or(0)
}

fn write_balance(e: &Env, address: &Address, amount: i128) {
    e.storage()
        .instance()
        .set(&FeeTokenKey::Balance(address.clone()), &amount);
}

fn transfer(e: &Env, from: &Address, to: &Address, amount: i128) {
    let fee = e
        .storage()
        .instance()
        .get(&FeeTokenKey::Fee)
        .unwrap_or(0i128);
    write_balance(e, from, read_balance(e, from) - amount);
    write_balance(e, to, read_balance(e, to) + amount - fee);
}

fn register_fee_token(e: &Env) -> Address {
    let token = e.register_contract(None, FeeToken);
    FeeTokenClient::new(e, &token).init();
    token
}

fn assert_balance_mismatch<T, E>(result: Result<T, Result<Error, E>>) {
    assert_eq!(
        result.err().map(|error| error.map_err(|_| ())),
        Some(Ok(Error::from_contract_error(
            CometError::ErrBalanceMismatch as u32
        )))
    );
}

#[test]
fn init_rejects_inexact_token_transfer_and_rolls_back() {
    let e = Env::default();
    e.mock_all_auths();

    let controller = Address::generate(&e);
    let standard_token = e.register_stellar_asset_contract(controller.clone());
    let standard_client = MockTokenClient::new(&e, &standard_token);
    let fee_token = register_fee_token(&e);
    let fee_client = FeeTokenClient::new(&e, &fee_token);

    standard_client.mint(&controller, &STROOP);
    fee_client.mint(&controller, &STROOP);
    fee_client.set_fee(&1);

    let pool = e.register_contract(None, CometPoolContract);
    let client = CometPoolContractClient::new(&e, &pool);
    let result = client.try_init(
        &controller,
        &vec![&e, standard_token.clone(), fee_token.clone()],
        &vec![&e, STROOP / 2, STROOP / 2],
        &vec![&e, STROOP, STROOP],
        &0_0030000,
    );

    assert_balance_mismatch(result);
    assert_eq!(standard_client.balance(&controller), STROOP);
    assert_eq!(standard_client.balance(&pool), 0);
    assert_eq!(fee_client.balance(&controller), STROOP);
    assert_eq!(fee_client.balance(&pool), 0);
}

#[test]
fn swaps_reject_inexact_input_and_output_transfers_and_roll_back() {
    let e = Env::default();
    e.mock_all_auths();
    e.budget().reset_unlimited();

    let controller = Address::generate(&e);
    let user = Address::generate(&e);
    let standard_token = e.register_stellar_asset_contract(controller.clone());
    let standard_client = MockTokenClient::new(&e, &standard_token);
    let fee_token = register_fee_token(&e);
    let fee_client = FeeTokenClient::new(&e, &fee_token);
    let reserve = 100 * STROOP;
    let user_balance = 10 * STROOP;

    standard_client.mint(&controller, &reserve);
    standard_client.mint(&user, &user_balance);
    fee_client.mint(&controller, &reserve);
    fee_client.mint(&user, &user_balance);

    let pool = e.register_contract(None, CometPoolContract);
    let client = CometPoolContractClient::new(&e, &pool);
    client.init(
        &controller,
        &vec![&e, standard_token.clone(), fee_token.clone()],
        &vec![&e, STROOP / 2, STROOP / 2],
        &vec![&e, reserve, reserve],
        &0_0030000,
    );
    fee_client.set_fee(&1);

    let result = client.try_swap_exact_amount_in(
        &fee_token,
        &STROOP,
        &standard_token,
        &0,
        &i128::MAX,
        &user,
    );
    assert_balance_mismatch(result);

    assert_eq!(fee_client.balance(&user), user_balance);
    assert_eq!(fee_client.balance(&pool), reserve);
    assert_eq!(standard_client.balance(&user), user_balance);
    assert_eq!(standard_client.balance(&pool), reserve);
    assert_eq!(client.get_balance(&fee_token), reserve);
    assert_eq!(client.get_balance(&standard_token), reserve);

    let result = client.try_swap_exact_amount_in(
        &standard_token,
        &STROOP,
        &fee_token,
        &0,
        &i128::MAX,
        &user,
    );
    assert_balance_mismatch(result);

    assert_eq!(fee_client.balance(&user), user_balance);
    assert_eq!(fee_client.balance(&pool), reserve);
    assert_eq!(standard_client.balance(&user), user_balance);
    assert_eq!(standard_client.balance(&pool), reserve);
    assert_eq!(client.get_balance(&fee_token), reserve);
    assert_eq!(client.get_balance(&standard_token), reserve);
}
