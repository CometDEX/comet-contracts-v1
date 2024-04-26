//! Utilities for the LP Token
use soroban_sdk::{Address, Env};
use soroban_token_sdk::TokenUtils;

use super::{
    balance::{receive_balance, spend_balance},
    metadata::{get_total_shares, put_total_shares},
};

use soroban_sdk::token::Client;

// Transfers the Specific Token from the User’s Address to the Contract’s Address
pub fn pull_underlying(e: &Env, token: &Address, from: &Address, amount: i128, max_amount: i128) {
    // @DEV - This rounds the sequence number to the nearest 100000 to avoid simulation -> execution sequence number mismatch
    let ledger = (e.ledger().sequence() / 100000 + 1) * 100000;
    Client::new(e, token).approve(&from, &e.current_contract_address(), &max_amount, &ledger);
    Client::new(e, token).transfer_from(
        &e.current_contract_address(),
        &from,
        &e.current_contract_address(),
        &amount,
    );
}

// Transfers the Specific Token from the Contract’s Address to the given 'to' Address
pub fn push_underlying(e: &Env, token: &Address, to: &Address, amount: i128) {
    Client::new(e, token).transfer(&e.current_contract_address(), &to, &amount);
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
