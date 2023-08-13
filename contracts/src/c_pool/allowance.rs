//! Allowance Utilities for the LP Token

use soroban_sdk::{panic_with_error, Address, Env};

use crate::c_pool::error::Error;

use super::storage_types::{AllowanceDataKey, DataKeyToken};

// Read the Allowance of the LP Token of the spender approved by 'from' address
pub fn read_allowance(e: &Env, from: Address, spender: Address) -> i128 {
    let key = DataKeyToken::Allowance(AllowanceDataKey { from, spender });
    if let Some(allowance) = e.storage().persistent().get::<DataKeyToken, i128>(&key) {
        allowance
    } else {
        0
    }
}

// Write the Allowance of the LP Token of the spender approved by 'from' address
pub fn write_allowance(e: &Env, from: Address, spender: Address, amount: i128) {
    let key = DataKeyToken::Allowance(AllowanceDataKey { from, spender });
    e.storage().persistent().set(&key, &amount);
}

// Spend the Allowance of the LP Token by the spender
pub fn spend_allowance(e: &Env, from: Address, spender: Address, amount: i128) {
    let allowance = read_allowance(e, from.clone(), spender.clone());
    if allowance < amount {
        panic_with_error!(e, Error::ErrInsufficientAllowance);
    }
    write_allowance(e, from, spender, allowance - amount);
}
