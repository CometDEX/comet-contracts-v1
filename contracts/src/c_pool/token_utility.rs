//! Utilities for the LP Token
use soroban_sdk::{assert_with_error, Address, Env};
use soroban_token_sdk::TokenUtils;

use super::{
    balance::{receive_balance, spend_balance},
    error::Error,
    metadata::{get_total_shares, put_total_shares},
};

use soroban_sdk::token::Client;

fn transfer_balances(e: &Env, client: &Client, from: &Address, to: &Address) -> (i128, i128) {
    assert_with_error!(e, from != to, Error::ErrBalanceMismatch);
    (client.balance(from), client.balance(to))
}

fn require_exact_transfer(
    e: &Env,
    client: &Client,
    from: &Address,
    to: &Address,
    amount: i128,
    balances_before: (i128, i128),
) {
    let expected_from = balances_before.0.checked_sub(amount);
    let expected_to = balances_before.1.checked_add(amount);
    assert_with_error!(
        e,
        expected_from == Some(client.balance(from)) && expected_to == Some(client.balance(to)),
        Error::ErrBalanceMismatch
    );
}

/// Transfer an exact amount between two addresses.
pub fn transfer_underlying(e: &Env, token: &Address, from: &Address, to: &Address, amount: i128) {
    let client = Client::new(e, token);
    let balances_before = transfer_balances(e, &client, from, to);
    client.transfer(from, to, &amount);
    require_exact_transfer(e, &client, from, to, amount, balances_before);
}

// Transfers the Specific Token from the User’s Address to the Contract’s Address
pub fn pull_underlying(e: &Env, token: &Address, from: &Address, amount: i128, max_amount: i128) {
    // @DEV - This rounds the sequence number to the nearest 100000 to avoid simulation -> execution sequence number mismatch
    let ledger = (e.ledger().sequence() / 100000 + 1) * 100000;
    let client = Client::new(e, token);
    let contract = e.current_contract_address();
    client.approve(from, &contract, &max_amount, &ledger);
    let balances_before = transfer_balances(e, &client, from, &contract);
    client.transfer_from(&contract, from, &contract, &amount);
    require_exact_transfer(e, &client, from, &contract, amount, balances_before);
}

// Transfers the Specific Token from the Contract’s Address to the given 'to' Address
pub fn push_underlying(e: &Env, token: &Address, to: &Address, amount: i128) {
    transfer_underlying(e, token, &e.current_contract_address(), to, amount);
}

// Mint the given amount of LP Tokens
pub fn mint_shares(e: &Env, to: &Address, amount: i128) {
    let total = get_total_shares(e);
    put_total_shares(e, total + amount);
    check_nonnegative_amount(amount);
    receive_balance(e, to.clone(), amount);
}

// Transfer the LP Tokens from the given 'from' Address to the contract Address
pub fn pull_shares(e: &Env, from: &Address, amount: i128) {
    let contract_address = e.current_contract_address();
    check_nonnegative_amount(amount);
    spend_balance(e, from.clone(), amount);
    receive_balance(e, contract_address.clone(), amount);
    TokenUtils::new(e)
        .events()
        .transfer(from.clone(), contract_address, amount);
}

// Burn the LP Tokens
pub fn burn_shares(e: &Env, amount: i128) {
    let total = get_total_shares(e);
    let contract_address = e.current_contract_address();
    check_nonnegative_amount(amount);
    spend_balance(e, contract_address.clone(), amount);
    TokenUtils::new(e).events().burn(contract_address, amount);
    put_total_shares(e, total - amount);
}

// Check if the given amount is negative
pub fn check_nonnegative_amount(amount: i128) {
    if amount < 0 {
        panic!("negative amount is not allowed: {}", amount)
    }
}
