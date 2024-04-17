//! Utilities to read and write contract's storage

use crate::c_pool::storage_types::DataKey;
use soroban_sdk::{unwrap::UnwrapOptimized, vec, Address, Env, Map, String, Vec};
use soroban_token_sdk::{metadata::TokenMetadata, TokenUtils};

use super::storage_types::{Record, SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD};

// Read all Token Addresses in the pool
pub fn read_tokens(e: &Env) -> Vec<Address> {
    let key = DataKey::AllTokenVec;
    if let Some(arr) = e.storage().persistent().get::<DataKey, Vec<Address>>(&key) {
        e.storage()
            .persistent()
            .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        arr
    } else {
        vec![e]
    }
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
    if let Some(rec) = e
        .storage()
        .persistent()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
    {
        e.storage().persistent().extend_ttl(
            &key_rec,
            SHARED_LIFETIME_THRESHOLD,
            SHARED_BUMP_AMOUNT,
        );
        rec
    } else {
        Map::<Address, Record>::new(e)
    }
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

// TODO: Tests fail during bundle_bind on second `controller.require_auth` call during
//       rebind when set to instance storage. Setting to persistent storage as workaround.
// Read Controller
pub fn read_controller(e: &Env) -> Address {
    let key = DataKey::Controller;
    e.storage()
        .persistent()
        .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, Address>(&key)
        .unwrap_optimized()
}

// Write Controller
pub fn write_controller(e: &Env, d: Address) {
    let key = DataKey::Controller;
    e.storage().persistent().set(&key, &d);
    e.storage()
        .persistent()
        .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
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

// Read Total Weight
pub fn read_total_weight(e: &Env) -> i128 {
    let key = DataKey::TotalWeight;
    e.storage()
        .instance()
        .get::<DataKey, i128>(&key)
        .unwrap_or(0_i128)
}

// Write Total Weight
pub fn write_total_weight(e: &Env, d: i128) {
    let key = DataKey::TotalWeight;
    e.storage().instance().set(&key, &d)
}

// Read Total Shares
pub fn get_total_shares(e: &Env) -> i128 {
    e.storage().persistent().extend_ttl(
        &DataKey::TotalShares,
        SHARED_LIFETIME_THRESHOLD,
        SHARED_BUMP_AMOUNT,
    );
    e.storage()
        .persistent()
        .get::<DataKey, i128>(&DataKey::TotalShares)
        .unwrap_optimized()
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
