//! Utilities to read and write contract's storage

use crate::{c_consts::STROOP, c_pool::{error::Error, storage_types::DataKey}};
use soroban_fixed_point_math::FixedPoint;
use soroban_sdk::{panic_with_error, unwrap::UnwrapOptimized, Address, Env, Map, String, Vec};
use soroban_token_sdk::{metadata::TokenMetadata, TokenUtils};

use super::storage_types::{
    FeeRule, Record, SwapFeeConfig, SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD,
};

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

// Read Swap Fee Config
pub fn read_swap_fee_config(e: &Env) -> SwapFeeConfig {
    let key = DataKey::SwapFeeConfig;
    e.storage()
        .instance()
        .get::<DataKey, SwapFeeConfig>(&key)
        .unwrap_optimized()
}

// Write Swap Fee Config
pub fn write_swap_fee_config(e: &Env, config: &SwapFeeConfig) {
    let key = DataKey::SwapFeeConfig;
    e.storage().instance().set(&key, config)
}

pub fn read_fee_rule(e: &Env) -> Option<FeeRule> {
    let key = DataKey::FeeRule;
    e.storage().instance().get::<DataKey, FeeRule>(&key)
}

pub fn write_fee_rule(e: &Env, rule: &FeeRule) {
    let key = DataKey::FeeRule;
    e.storage().instance().set(&key, rule);
}

pub fn clear_fee_rule(e: &Env) {
    let key = DataKey::FeeRule;
    e.storage().instance().remove(&key);
}

/// Calculates the dynamic swap fee based on tracked token utilization.
///
/// The fee varies linearly between min_fee and max_fee based on the current balance
/// of the tracked token relative to configured low and high utilization thresholds.
///
/// # Fee Calculation
/// - Below low_util_balance: max_fee (incentivize adding this token)
/// - Above high_util_balance: min_fee (incentivize removing this token)
/// - Between thresholds: Linear interpolation from max_fee to min_fee
///
/// # Overflow Protection
/// The multiplication of balances by scalar is protected by:
/// 1. checked_mul() operations that panic on overflow
/// 2. Validation at initialization that low_util_balance and high_util_balance
///    are capped at MAX_UTIL_BALANCE (i128::MAX / 10^18 ≈ 1.7e20)
/// 3. This ensures balance * scalar never overflows i128, even for 0-decimal tokens
///
/// # Returns
/// The calculated swap fee in stroop units (1e-7)
pub fn read_swap_fee(e: &Env) -> i128 {
    let config = read_swap_fee_config(e);
    // Fallback to max_fee if configuration is degenerate.
    if config.max_fee <= config.min_fee || config.high_util_balance <= config.low_util_balance {
        return config.max_fee;
    }

    let records = read_record(e);
    let tracked = records.get(config.tracked_token.clone()).unwrap_optimized();

    // Convert balances to 18-decimal fixed precision using the stored scalar.
    // These multiplications are safe from overflow due to MAX_UTIL_BALANCE validation at init.
    let scalar = tracked.scalar;
    let current_balance = tracked.balance.checked_mul(scalar)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox));
    let low_balance = config.low_util_balance.checked_mul(scalar)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox));
    let high_balance = config.high_util_balance.checked_mul(scalar)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox));

    let clamped = current_balance.max(low_balance).min(high_balance);

    let span = high_balance.checked_sub(low_balance)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox));
    if span <= 0 {
        return config.max_fee;
    }

    let utilization = (clamped.checked_sub(low_balance)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox)))
        .fixed_div_floor(span, STROOP)
        .unwrap_optimized();

    let fee_delta = (config.max_fee.checked_sub(config.min_fee)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox)))
        .fixed_mul_floor(utilization, STROOP)
        .unwrap_optimized();

    config.max_fee.checked_sub(fee_delta)
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrMathApprox))
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
