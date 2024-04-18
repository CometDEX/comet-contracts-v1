use crate::c_pool::{error::Error, storage_types::{DataKeyToken, BALANCE_BUMP_AMOUNT}};
use soroban_sdk::{assert_with_error, Address, Env};

use super::storage_types::BALANCE_LIFETIME_THRESHOLD;

pub fn read_balance(e: &Env, addr: Address) -> i128 {
    let key = DataKeyToken::Balance(addr);
    if let Some(balance) = e.storage().persistent().get::<DataKeyToken, i128>(&key) {
        e.storage()
            .persistent()
            .extend_ttl(&key, BALANCE_LIFETIME_THRESHOLD, BALANCE_BUMP_AMOUNT);
        balance
    } else {
        0
    }
}

fn write_balance(e: &Env, addr: Address, amount: i128) {
    let key = DataKeyToken::Balance(addr);
    e.storage().persistent().set(&key, &amount);
    e.storage()
        .persistent()
        .extend_ttl(&key, BALANCE_LIFETIME_THRESHOLD, BALANCE_BUMP_AMOUNT);
}

pub fn receive_balance(e: &Env, addr: Address, amount: i128) {
    let balance = read_balance(e, addr.clone());
    write_balance(e, addr, balance + amount);
}

pub fn spend_balance(e: &Env, addr: Address, amount: i128) {
    let balance = read_balance(e, addr.clone());
    assert_with_error!(e, balance >= amount, Error::ErrInsufficientBalance);
    write_balance(e, addr, balance - amount);
}
