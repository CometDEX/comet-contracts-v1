//! Utilities for the LP Token
use soroban_sdk::{assert_with_error, Address, Env};
use soroban_token_sdk::events::{Burn, MintWithAmountOnly, TransferWithAmountOnly};

use crate::c_consts::MIN_POOL_SUPPLY;

use super::{
    balance::{receive_balance, spend_balance},
    error::Error,
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
    Client::new(e, token).transfer(&e.current_contract_address(), to, &amount);
}

// Mint the given amount of LP Tokens
pub fn mint_shares(e: &Env, to: &Address, amount: i128) {
    check_nonnegative_amount(e, amount);
    let total = get_total_shares(e);
    put_total_shares(e, total + amount);
    receive_balance(e, to.clone(), amount);
    MintWithAmountOnly {
        to: to.clone(),
        amount,
    }
    .publish(e);
}

// Transfer the LP Tokens from the given 'from' Address to the contract Address
pub fn pull_shares(e: &Env, from: &Address, amount: i128) {
    let contract_address = e.current_contract_address();
    check_nonnegative_amount(e, amount);
    spend_balance(e, from.clone(), amount);
    receive_balance(e, contract_address.clone(), amount);
    TransferWithAmountOnly {
        from: from.clone(),
        to: contract_address,
        amount,
    }
    .publish(e);
}

// Burn the LP Tokens
pub fn burn_shares(e: &Env, amount: i128) {
    let contract_address = e.current_contract_address();
    burn_shares_from(e, &contract_address, amount);
}

// Burn LP Tokens from an address while preserving the minimum pool supply.
pub fn burn_shares_from(e: &Env, from: &Address, amount: i128) {
    check_nonnegative_amount(e, amount);
    let total = get_total_shares(e);
    assert_with_error!(
        e,
        preserves_minimum_supply(total, amount),
        Error::ErrMinPoolSupply
    );
    spend_balance(e, from.clone(), amount);
    Burn {
        from: from.clone(),
        amount,
    }
    .publish(e);
    put_total_shares(e, total - amount);
}

// Check if the given amount is negative
pub fn check_nonnegative_amount(e: &Env, amount: i128) {
    assert_with_error!(e, amount >= 0, Error::ErrTokenAmountIsNegative);
}

fn preserves_minimum_supply(total: i128, amount: i128) -> bool {
    amount <= total - MIN_POOL_SUPPLY
}

#[cfg(test)]
mod tests {
    use super::preserves_minimum_supply;
    use crate::c_consts::{INIT_POOL_SUPPLY, MIN_POOL_SUPPLY};

    #[test]
    fn test_preserves_minimum_supply() {
        assert!(preserves_minimum_supply(
            INIT_POOL_SUPPLY,
            INIT_POOL_SUPPLY - MIN_POOL_SUPPLY
        ));
        assert!(!preserves_minimum_supply(
            INIT_POOL_SUPPLY,
            INIT_POOL_SUPPLY
        ));
        assert!(!preserves_minimum_supply(MIN_POOL_SUPPLY, 1));
    }
}
