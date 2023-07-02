//! Balance Utilities for the LP Token

use crate::c_pool::error::Error;

use super::storage_types::DataKeyToken;
use soroban_sdk::{panic_with_error, Address, Env};

// Read the balance of the LP Token of the given 'addr' Address
pub fn read_balance(e: &Env, addr: Address) -> i128 {
    let key = DataKeyToken::Balance(addr);
    if let Some(balance) = e.storage().get(&key) {
        balance.unwrap()
    } else {
        0
    }
}

// Write the balance of the LP Token of the given 'addr' Address with the given 'amount'
fn write_balance(e: &Env, addr: Address, amount: i128) {
    let key = DataKeyToken::Balance(addr);
    e.storage().set(&key, &amount);
}

// After you receive the LP Token for the given 'addr' Address
pub fn receive_balance(e: &Env, addr: Address, amount: i128) {
    let balance = read_balance(e, addr.clone());
    if !is_authorized(e, addr.clone()) {
        panic_with_error!(e, Error::ErrDeauthorized);
    }
    write_balance(e, addr, balance + amount);
}

// When you spend the LP token, decrease the balance of the given user 'addr' Address
pub fn spend_balance(e: &Env, addr: Address, amount: i128) {
    let balance = read_balance(e, addr.clone());
    if !is_authorized(e, addr.clone()) {
        panic_with_error!(e, Error::ErrDeauthorized);
    }
    if balance < amount {
        panic_with_error!(e, Error::ErrInsufficientBalance);
    }
    write_balance(e, addr, balance - amount);
}

// Check if the address is authorized
pub fn is_authorized(e: &Env, addr: Address) -> bool {
    let key = DataKeyToken::State(addr);
    if let Some(state) = e.storage().get(&key) {
        state.unwrap()
    } else {
        true
    }
}

// Write if the given address is authorized or not to the contract's state
pub fn write_authorization(e: &Env, addr: Address, is_authorized: bool) {
    let key = DataKeyToken::State(addr);
    e.storage().set(&key, &is_authorized);
}
