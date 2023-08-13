//! Utilities to read and write contract's storage

use crate::c_pool::storage_types::DataKey;
use soroban_sdk::{vec, Address, Bytes, BytesN, Env, Map, Vec};

use super::storage_types::{DataKeyToken, Record};

// Read all Token Addresses in the pool
pub fn read_tokens(e: &Env) -> Vec<Address> {
    let key = DataKey::AllTokenVec;
    let arr: Vec<Address> = e
        .storage()
        .persistent()
        .get::<DataKey, Vec<Address>>(&key)
        .unwrap_or(vec![e]); // if no members on vector
    arr
}

// Write All Tokens Addresses to the Vector
pub fn write_tokens(e: &Env, new: Vec<Address>) {
    let key = DataKey::AllTokenVec;
    e.storage().persistent().set(&key, &new);
}

// Read Record
pub fn read_record(e: &Env) -> Map<Address, Record> {
    let key_rec = DataKey::AllRecordData;
        e.storage()
        .persistent()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
        .unwrap_or(Map::<Address, Record>::new(e)) // if no members on vector
}

// Write Record
pub fn write_record(e: &Env, new_map: Map<Address, Record>) {
    let key_rec = DataKey::AllRecordData;
    e.storage().persistent().set(&key_rec, &new_map);
}
// Read Factory
pub fn read_factory(e: &Env) -> Address {
    let key = DataKey::Factory;
    e.storage().persistent().get::<DataKey, Address>(&key).unwrap()
}
// Write Factory
pub fn write_factory(e: &Env, d: Address) {
    let key = DataKey::Factory;
    e.storage().persistent().set(&key, &d)
}
// Read Controller
pub fn read_controller(e: &Env) -> Address {
    let key = DataKey::Controller;
    e.storage().persistent().get::<DataKey, Address>(&key).unwrap()
}

// Write Controller
pub fn write_controller(e: &Env, d: Address) {
    let key = DataKey::Controller;
    e.storage().persistent().set(&key, &d)
}

// Read Swap Fee
pub fn read_swap_fee(e: &Env) -> i128 {
    let key = DataKey::SwapFee;
    e.storage()
        .persistent()
        .get::<DataKey, i128>(&key)
        .unwrap_or(0) // if no members on vector
}

// Write Swap Fee
pub fn write_swap_fee(e: &Env, d: i128) {
    let key = DataKey::SwapFee;
    e.storage().persistent().set(&key, &d)
}

// Read Total Weight
pub fn read_total_weight(e: &Env) -> i128 {
    let key = DataKey::TotalWeight;
    e.storage().
        persistent()
        .get::<DataKey, i128>(&DataKey::TotalWeight)
        .unwrap_or(0_i128)
        
}

// Write Total Weight
pub fn write_total_weight(e: &Env, d: i128) {
    let key = DataKey::TotalWeight;
    e.storage().persistent().set(&key, &d)
}

//Read Token Share
pub fn get_token_share(e: &Env) -> Address {
    e.storage().persistent().get::<DataKey, Address>(&DataKey::TokenShare).unwrap()
}

// Update Token Share
pub fn put_token_share(e: &Env, contract_id: Address) {
    e.storage().persistent().set(&DataKey::TokenShare, &contract_id);
}

// Read Total Shares
pub fn get_total_shares(e: &Env) -> i128 {
    e.storage().persistent().get::<DataKey, i128>(&DataKey::TotalShares).unwrap()
}

// Update Total Shares
pub fn put_total_shares(e: &Env, amount: i128) {
    e.storage().persistent().set(&DataKey::TotalShares, &amount)
}

// Read Finalize
pub fn read_finalize(e: &Env) -> bool {
    e.storage().persistent().get::<DataKey, bool>(&DataKey::Finalize).unwrap()
}

// Write Finalize
pub fn write_finalize(e: &Env, val: bool) {
    e.storage().persistent().set(&DataKey::Finalize, &val)
}

// Read Public Swap
pub fn read_public_swap(e: &Env) -> bool {
    e.storage().persistent().get::<DataKey, bool>(&DataKey::PublicSwap).unwrap()
}

// Write Public Swap
pub fn write_public_swap(e: &Env, val: bool) {
    e.storage().persistent().set(&DataKey::PublicSwap, &val)
}

// Check if the token Address is bound to the pool
pub fn check_record_bound(e: &Env, token: Address) -> bool {
    let key_rec = DataKey::AllRecordData;

    let mut val = e
        .storage()
        .persistent()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
        .unwrap_or(Map::<Address, Record>::new(e)); // if no members on vector

    let key_existence = val.contains_key(token.clone());
    if key_existence {
        val.get(token).unwrap().bound
    } else {
        false
    }
}

// Read Name of the LP Token
pub fn read_freeze(e: &Env) -> bool {
    let key = DataKey::Freeze;
    e.storage().persistent().get::<DataKey, bool>(&key).unwrap_or(false)
}

// Write Name of the LP Token
pub fn write_freeze(e: &Env, d: bool) {
    let key = DataKey::Freeze;
    e.storage().persistent().set(&key, &d)
}

// Read LP Token Decimals
pub fn read_decimal(e: &Env) -> u32 {
    let key = DataKeyToken::Decimals;
    e.storage().persistent().get::<DataKeyToken, u32>(&key).unwrap()
}

// Write LP Token Decimals
pub fn write_decimal(e: &Env, d: u8) {
    let key = DataKeyToken::Decimals;
    e.storage().persistent().set(&key, &u32::from(d))
}

// Read Name of the LP Token
pub fn read_name(e: &Env) -> Bytes {
    let key = DataKeyToken::Name;
    e.storage().persistent().get::<DataKeyToken, Bytes>(&key).unwrap()
}

// Write Name of the LP Token
pub fn write_name(e: &Env, d: Bytes) {
    let key = DataKeyToken::Name;
    e.storage().persistent().set(&key, &d)
}

// Read Symbol of the LP Token
pub fn read_symbol(e: &Env) -> Bytes {
    let key = DataKeyToken::Symbol;
    e.storage().persistent().get::<DataKeyToken, Bytes>(&key).unwrap()
}

// Write Symbol of the LP Token
pub fn write_symbol(e: &Env, d: Bytes) {
    let key = DataKeyToken::Symbol;
    e.storage().persistent().set(&key, &d)
}
