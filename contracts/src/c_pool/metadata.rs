//! Utilities to read and write contract's storage

use crate::c_pool::storage_types::DataKey;
use soroban_sdk::{unwrap::UnwrapOptimized, vec, Address, Bytes, BytesN, Env, Map, Vec};

use super::storage_types::{DataKeyToken, Record, SHARED_BUMP_AMOUNT};

// Read all Token Addresses in the pool
pub fn read_tokens(e: &Env) -> Vec<Address> {
    let key = DataKey::AllTokenVec;
    if let Some(arr) = e.storage().persistent().get::<DataKey, Vec<Address>>(&key) {
        e.storage().persistent().bump(&key, SHARED_BUMP_AMOUNT);
        arr
    } else {
        vec![e]
    }
}

// Write All Tokens Addresses to the Vector
pub fn write_tokens(e: &Env, new: Vec<Address>) {
    let key = DataKey::AllTokenVec;
    e.storage().persistent().set(&key, &new);
    e.storage().persistent().bump(&key, SHARED_BUMP_AMOUNT);
}

// Read Record
pub fn read_record(e: &Env) -> Map<Address, Record> {
    let key_rec = DataKey::AllRecordData;
    if let Some(rec) = e
        .storage()
        .persistent()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
    {
        e.storage().persistent().bump(&key_rec, SHARED_BUMP_AMOUNT);
        rec
    } else {
        Map::<Address, Record>::new(e)
    }
}

// Write Record
pub fn write_record(e: &Env, new_map: Map<Address, Record>) {
    let key_rec = DataKey::AllRecordData;
    e.storage().persistent().set(&key_rec, &new_map);
    e.storage().persistent().bump(&key_rec, SHARED_BUMP_AMOUNT);
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

//Read Token Share
pub fn get_token_share(e: &Env) -> Address {
    e.storage()
        .persistent()
        .bump(&DataKey::TokenShare, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, Address>(&DataKey::TokenShare)
        .unwrap_optimized()
}

// Update Token Share
pub fn put_token_share(e: &Env, contract_id: Address) {
    e.storage()
        .persistent()
        .set(&DataKey::TokenShare, &contract_id);
    e.storage()
        .persistent()
        .bump(&DataKey::TokenShare, SHARED_BUMP_AMOUNT);
}

// Read Total Shares
pub fn get_total_shares(e: &Env) -> i128 {
    e.storage()
        .persistent()
        .bump(&DataKey::TotalShares, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, i128>(&DataKey::TotalShares)
        .unwrap_optimized()
}

// Update Total Shares
pub fn put_total_shares(e: &Env, amount: i128) {
    e.storage().persistent().set(&DataKey::TotalShares, &amount);
    e.storage()
        .persistent()
        .bump(&DataKey::TotalShares, SHARED_BUMP_AMOUNT);
}

// Read LP Token Decimals
pub fn read_decimal(e: &Env) -> u32 {
    let key = DataKeyToken::Decimals;
    e.storage()
        .instance()
        .get::<DataKeyToken, u32>(&key)
        .unwrap_optimized()
}

// Write LP Token Decimals
pub fn write_decimal(e: &Env, d: u8) {
    let key = DataKeyToken::Decimals;
    e.storage().instance().set(&key, &u32::from(d))
}

// Read Name of the LP Token
pub fn read_name(e: &Env) -> Bytes {
    let key = DataKeyToken::Name;
    e.storage()
        .instance()
        .get::<DataKeyToken, Bytes>(&key)
        .unwrap_optimized()
}

// Write Name of the LP Token
pub fn write_name(e: &Env, d: Bytes) {
    let key = DataKeyToken::Name;
    e.storage().instance().set(&key, &d)
}

// Read Symbol of the LP Token
pub fn read_symbol(e: &Env) -> Bytes {
    let key = DataKeyToken::Symbol;
    e.storage()
        .instance()
        .get::<DataKeyToken, Bytes>(&key)
        .unwrap_optimized()
}

// Write Symbol of the LP Token
pub fn write_symbol(e: &Env, d: Bytes) {
    let key = DataKeyToken::Symbol;
    e.storage().instance().set(&key, &d)
}
