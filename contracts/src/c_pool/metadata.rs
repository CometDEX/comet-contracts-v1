//! Utilities to read and write contract's storage

use crate::c_pool::storage_types::DataKey;
use soroban_sdk::{unwrap::UnwrapOptimized, Address, Env, Map, String, Vec};
use soroban_token_sdk::{metadata::TokenMetadata, TokenUtils};

use super::storage_types::{Record, POOL_BUMP_AMOUNT, POOL_LIFETIME_THRESHOLD};

// Pool accounting state lives in the contract instance and shares its TTL.
// Public entrypoints that access this state call this once before doing so.
pub fn extend_pool_ttl(e: &Env) {
    e.storage()
        .instance()
        .extend_ttl(POOL_LIFETIME_THRESHOLD, POOL_BUMP_AMOUNT);
}

// Read all Token Addresses in the pool
pub fn read_tokens(e: &Env) -> Vec<Address> {
    let key = DataKey::AllTokenVec;
    e.storage()
        .instance()
        .get::<DataKey, Vec<Address>>(&key)
        .unwrap_optimized()
}

// Write All Tokens Addresses to the Vector
pub fn write_tokens(e: &Env, new: Vec<Address>) {
    let key = DataKey::AllTokenVec;
    e.storage().instance().set(&key, &new);
}

// Read Record
pub fn read_record(e: &Env) -> Map<Address, Record> {
    let key_rec = DataKey::AllRecordData;
    e.storage()
        .instance()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
        .unwrap_optimized()
}

// Write Record
pub fn write_record(e: &Env, new_map: Map<Address, Record>) {
    let key_rec = DataKey::AllRecordData;
    e.storage().instance().set(&key_rec, &new_map);
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
    e.storage()
        .instance()
        .get::<DataKey, i128>(&key)
        .unwrap_or(0)
}

// Update Total Shares
pub fn put_total_shares(e: &Env, amount: i128) {
    e.storage().instance().set(&DataKey::TotalShares, &amount);
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
