//! Utilities to read and write contract's storage

use crate::c_pool::storage_types::DataKey;
use soroban_sdk::{unwrap::UnwrapOptimized, Address, Env, Map, String, Vec};
use soroban_token_sdk::{metadata::TokenMetadata, TokenUtils};

use super::storage_types::{
    Record, POOL_BUMP_AMOUNT, POOL_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT,
    SHARED_LIFETIME_THRESHOLD,
};

// Keep all state required to account for and redeem LP balances live together.
// Public entrypoints that access LP balances call this once before doing so.
pub fn extend_pool_ttl(e: &Env) {
    e.storage()
        .instance()
        .extend_ttl(POOL_LIFETIME_THRESHOLD, POOL_BUMP_AMOUNT);

    let persistent = e.storage().persistent();
    let token_key = DataKey::AllTokenVec;
    let record_key = DataKey::AllRecordData;
    let supply_key = DataKey::TotalShares;

    // Preserve pre-initialization token behavior while avoiding an existence
    // check for every key. Initialization creates all three entries atomically.
    if !persistent.has(&token_key) {
        return;
    }
    persistent.extend_ttl(&token_key, POOL_LIFETIME_THRESHOLD, POOL_BUMP_AMOUNT);
    persistent.extend_ttl(&record_key, POOL_LIFETIME_THRESHOLD, POOL_BUMP_AMOUNT);
    persistent.extend_ttl(&supply_key, POOL_LIFETIME_THRESHOLD, POOL_BUMP_AMOUNT);
}

// Read all Token Addresses in the pool
pub fn read_tokens(e: &Env) -> Vec<Address> {
    let key = DataKey::AllTokenVec;
    e.storage()
        .persistent()
        .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, Vec<Address>>(&key)
        .unwrap_optimized()
}

// Write All Tokens Addresses to the Vector
pub fn write_tokens(e: &Env, new: Vec<Address>) {
    let key = DataKey::AllTokenVec;
    e.storage().persistent().set(&key, &new);
    e.storage()
        .persistent()
        .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
}

// Read Record
pub fn read_record(e: &Env) -> Map<Address, Record> {
    let key_rec = DataKey::AllRecordData;
    e.storage()
        .persistent()
        .extend_ttl(&key_rec, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
        .unwrap_optimized()
}

// Write Record
pub fn write_record(e: &Env, new_map: Map<Address, Record>) {
    let key_rec = DataKey::AllRecordData;
    e.storage().persistent().set(&key_rec, &new_map);
    e.storage()
        .persistent()
        .extend_ttl(&key_rec, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
}

// Read Factory
pub fn read_factory(e: &Env) -> Address {
    let key = DataKey::Factory;
    e.storage()
        .instance()
        .get::<DataKey, Address>(&key)
        .unwrap_optimized()
}

// Write Factory
pub fn write_factory(e: &Env, d: Address) {
    let key = DataKey::Factory;
    e.storage().instance().set(&key, &d)
}

// Read Controller
pub fn read_controller(e: &Env) -> Address {
    let key = DataKey::Controller;
    e.storage()
        .instance()
        .get::<DataKey, Address>(&key)
        .unwrap_optimized()
}

// Write Controller
pub fn write_controller(e: &Env, d: Address) {
    let key = DataKey::Controller;
    e.storage().instance().set(&key, &d);
}

// Read Swap Fee
pub fn read_swap_fee(e: &Env) -> i128 {
    let key = DataKey::SwapFee;
    e.storage()
        .instance()
        .get::<DataKey, i128>(&key)
        .unwrap_or(0)
}

// Write Swap Fee
pub fn write_swap_fee(e: &Env, d: i128) {
    let key = DataKey::SwapFee;
    e.storage().instance().set(&key, &d)
}

// Read Total Shares
pub fn get_total_shares(e: &Env) -> i128 {
    let key = DataKey::TotalShares;
    if let Some(supply) = e.storage().persistent().get::<DataKey, i128>(&key) {
        e.storage()
            .persistent()
            .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        supply
    } else {
        0
    }
}

// Update Total Shares
pub fn put_total_shares(e: &Env, amount: i128) {
    e.storage().persistent().set(&DataKey::TotalShares, &amount);
    e.storage().persistent().extend_ttl(
        &DataKey::TotalShares,
        SHARED_LIFETIME_THRESHOLD,
        SHARED_BUMP_AMOUNT,
    );
}

// Read Finalize
pub fn read_finalize(e: &Env) -> bool {
    e.storage()
        .instance()
        .get::<DataKey, bool>(&DataKey::Finalize)
        .unwrap_optimized()
}

// Write Finalize
pub fn write_finalize(e: &Env, val: bool) {
    e.storage().instance().set(&DataKey::Finalize, &val)
}

// Read Public Swap
pub fn read_public_swap(e: &Env) -> bool {
    e.storage()
        .instance()
        .get::<DataKey, bool>(&DataKey::PublicSwap)
        .unwrap_optimized()
}

// Write Public Swap
pub fn write_public_swap(e: &Env, val: bool) {
    e.storage().instance().set(&DataKey::PublicSwap, &val)
}

// Read status of the pool
pub fn read_freeze(e: &Env) -> bool {
    let key = DataKey::Freeze;
    e.storage()
        .instance()
        .get::<DataKey, bool>(&key)
        .unwrap_or(false)
}

// Write status of the pool
pub fn write_freeze(e: &Env, d: bool) {
    let key = DataKey::Freeze;
    e.storage().instance().set(&key, &d)
}

pub fn read_decimal(e: &Env) -> u32 {
    let util = TokenUtils::new(e);
    util.metadata().get_metadata().decimal
}

pub fn read_name(e: &Env) -> String {
    let util = TokenUtils::new(e);
    util.metadata().get_metadata().name
}

pub fn read_symbol(e: &Env) -> String {
    let util = TokenUtils::new(e);
    util.metadata().get_metadata().symbol
}

pub fn write_metadata(e: &Env, metadata: TokenMetadata) {
    let util = TokenUtils::new(e);
    util.metadata().set_metadata(&metadata);
}
