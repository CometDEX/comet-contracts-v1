//! Allowance Utilities for the LP Token

use crate::c_pool::error::Error;
use crate::c_pool::storage_types::{AllowanceDataKey, AllowanceValue, DataKeyToken};
use soroban_sdk::{panic_with_error, Address, Env};

pub fn read_allowance(e: &Env, from: Address, spender: Address) -> AllowanceValue {
    let key = DataKeyToken::Allowance(AllowanceDataKey { from, spender });
    if let Some(allowance) = e.storage().temporary().get::<_, AllowanceValue>(&key) {
        if allowance.expiration_ledger < e.ledger().sequence() {
            AllowanceValue {
                amount: 0,
                expiration_ledger: allowance.expiration_ledger,
            }
        } else {
            allowance
        }
    } else {
        AllowanceValue {
            amount: 0,
            expiration_ledger: 0,
        }
    }
}

pub fn write_allowance(
    e: &Env,
    from: Address,
    spender: Address,
    amount: i128,
    expiration_ledger: u32,
) {
    let allowance = AllowanceValue {
        amount,
        expiration_ledger,
    };

    if amount > 0 && expiration_ledger < e.ledger().sequence() {
        panic_with_error!(&e, Error::ErrInvalidExpirationLedger)
    }

    let key = DataKeyToken::Allowance(AllowanceDataKey { from, spender });
    e.storage().temporary().set(&key.clone(), &allowance);

    if amount > 0 {
        let new_expiration_ledger = expiration_ledger
            .checked_sub(e.ledger().sequence())
            .unwrap();
        e.storage()
            .temporary()
            .extend_ttl(&key, new_expiration_ledger, new_expiration_ledger)
    }
}

pub fn spend_allowance(e: &Env, from: Address, spender: Address, amount: i128) {
    let allowance = read_allowance(e, from.clone(), spender.clone());
    if allowance.amount < amount {
        panic_with_error!(&e, Error::ErrInsufficientAllowance);
    }
    if amount > 0 {
        write_allowance(
            e,
            from,
            spender,
            allowance.amount - amount,
            allowance.expiration_ledger,
        );
    }
}
