//! Admin Utilities for the LP Token

use crate::c_pool::error::Error;

use super::storage_types::DataKeyToken;
use soroban_sdk::{panic_with_error, Address, Env};

// Return true if the Admin of the LP token is set, else false
pub fn has_administrator(e: &Env) -> bool {
    let key = DataKeyToken::Admin;
    e.storage().persistent().has(&key)
}

// Read the Administrator of the LP Token
fn read_administrator(e: &Env) -> Address {
    let key = DataKeyToken::Admin;
    e.storage().persistent().get::<DataKeyToken, Address>(&key).unwrap()
}

// Write the Administrator of the LP Token
pub fn write_administrator(e: &Env, id: &Address) {
    let key = DataKeyToken::Admin;
    e.storage().persistent().set(&key, id);
}

// Check if the provided address matches the actual admin
pub fn check_admin(e: &Env, admin: &Address) {
    if admin != &read_administrator(e) {
        panic_with_error!(e, Error::ErrNotAuthorizedByAdmin)
    }
}
