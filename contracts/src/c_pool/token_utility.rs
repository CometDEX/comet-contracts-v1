//! Utilities for the LP Token
use soroban_sdk::{panic_with_error, Address, Env};
use soroban_token_sdk::events::{Burn, Transfer};

use super::{
    balance::{receive_balance, spend_balance},
    error::Error,
    metadata::{get_total_shares, put_total_shares},
};

use soroban_sdk::token::Client;

// Transfers the Specific Token from the User's Address to the Contract's Address
pub fn pull_underlying(e: &Env, token: &Address, from: &Address, amount: i128) {
    // Direct transfer using Soroban's authorization framework
    // The user's require_auth() at the contract entry point authorizes this sub-contract call
    Client::new(e, token).transfer(from, &e.current_contract_address(), &amount);
}

// Transfers the Specific Token from the Contract’s Address to the given 'to' Address
pub fn push_underlying(e: &Env, token: &Address, to: &Address, amount: i128) {
    Client::new(e, token).transfer(&e.current_contract_address(), &*to, &amount);
}

// Mint the given amount of LP Tokens
pub fn mint_shares(e: &Env, to: &Address, amount: i128) {
    let total = get_total_shares(e);
    put_total_shares(
        e,
        total
            .checked_add(amount)
            .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox)),
    );
    check_nonnegative_amount(e, amount);
    receive_balance(e, to.clone(), amount);
}

// Transfer the LP Tokens from the given 'from' Address to the contract Address
pub fn pull_shares(e: &Env, from: &Address, amount: i128) {
    let contract_address = e.current_contract_address();
    check_nonnegative_amount(e, amount);
    spend_balance(e, from.clone(), amount);
    receive_balance(e, contract_address.clone(), amount);
    Transfer {
        from: from.clone(),
        to: contract_address,
        to_muxed_id: None,
        amount,
    }
    .publish(e);
}

// Burn the LP Tokens
pub fn burn_shares(e: &Env, amount: i128) {
    let total = get_total_shares(e);
    let contract_address = e.current_contract_address();
    check_nonnegative_amount(e, amount);
    spend_balance(e, contract_address.clone(), amount);
    Burn {
        from: contract_address,
        amount,
    }
    .publish(e);
    put_total_shares(
        e,
        total
            .checked_sub(amount)
            .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox)),
    );
}

// Check if the given amount is negative
pub fn check_nonnegative_amount(e: &Env, amount: i128) {
    if amount < 0 {
        panic_with_error!(e, Error::ErrNegative);
    }
}
