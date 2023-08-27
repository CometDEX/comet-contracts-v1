//! Utilities for the LP Token
use soroban_sdk::{panic_with_error, Address, Env};

use crate::c_pool::error::Error;

use super::{
    balance::{receive_balance, spend_balance},
    comet::{self, CometPoolContract, CometPoolTrait},
    event::{burn, transfer},
    metadata::{get_token_share, get_total_shares, put_total_shares}, storage_types::SHARED_BUMP_AMOUNT,
};

use soroban_sdk::token::Client;

// Transfers the Specific Token from the User’s Address to the Contract’s Address
pub fn pull_underlying(e: &Env, token: &Address, from: Address, amount: i128) {
    // Client::new(e, token).transfer_from(
    //     &e.current_contract_address(),
    //     &from,
    //     &e.current_contract_address(),
    //     &amount,
    // );
    Client::new(e, token).transfer(&from, &e.current_contract_address(), &amount)
}

// Transfers the Specific Token from the Contract’s Address to the given 'to' Address
pub fn push_underlying(e: &Env, token: &Address, to: Address, amount: i128) {
    Client::new(e, token).transfer(&e.current_contract_address(), &to, &amount);
}

// Mint the given amount of LP Tokens
pub fn mint_shares(e: Env, to: Address, amount: i128) {
    let total = get_total_shares(&e);
    put_total_shares(&e, total + amount);
    let contract_address = e.current_contract_address();
    // CometPoolContract::mint(e, to, amount);
    check_nonnegative_amount(amount);
    e.storage().instance().bump(SHARED_BUMP_AMOUNT);
    receive_balance(&e, to.clone(), amount);
    // event::mint(&e, admin, to, amount);

}

// Transfer the LP Tokens from the given 'from' Address to the contract Address
pub fn pull_shares(e: &Env, from: Address, amount: i128) {
    let contract_address = e.current_contract_address();
    check_nonnegative_amount(amount);
    spend_balance(e, from.clone(), amount);
    receive_balance(e, contract_address.clone(), amount);
    transfer(e, from, contract_address, amount);
}

// Burn the LP Tokens
pub fn burn_shares(e: &Env, amount: i128) {
    let total = get_total_shares(e);
    let contract_address = e.current_contract_address();
    let share_contract_id = get_token_share(e);
    check_nonnegative_amount(amount);
    spend_balance(e, contract_address.clone(), amount);
    burn(e, contract_address, amount);
    put_total_shares(e, total - amount);
}

// Transfer the LP tokens from Contract to the given 'to' Address
pub fn push_shares(e: &Env, to: Address, amount: i128) {
    let share_contract_id = get_token_share(e);
    let contract_address = e.current_contract_address();

    check_nonnegative_amount(amount);
    spend_balance(e, contract_address.clone(), amount);
    receive_balance(e, to.clone(), amount);
    transfer(e, contract_address, to, amount);
}

// Check if the given amount is negative
pub fn check_nonnegative_amount(amount: i128) {
    if amount < 0 {
        panic!("negative amount is not allowed: {}", amount)
    }
}