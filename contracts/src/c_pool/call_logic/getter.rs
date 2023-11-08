use soroban_sdk::{
    assert_with_error, panic_with_error, unwrap::UnwrapOptimized, Address, Env, Vec,
};

use crate::{
    c_math::calc_spot_price,
    c_num::c_div,
    c_pool::{
        error::Error,
        metadata::{
            get_total_shares, read_controller, read_finalize, read_public_swap, read_record,
            read_swap_fee, read_tokens, read_total_weight,
        },
        storage_types::Record,
    },
};

// Get the denormalized weight of the token
pub fn execute_get_denormalized_weight(e: Env, token: Address) -> i128 {
    let records = read_record(&e);
    let val = records
        .get(token.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, val.bound, Error::ErrNotBound);
    val.denorm
}

// Get the normalized weight of the token
pub fn execute_get_normalized_weight(e: Env, token: Address) -> i128 {
    let records = read_record(&e);
    let val = records
        .get(token.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, val.bound, Error::ErrNotBound);
    c_div(&e, val.denorm, read_total_weight(&e)).unwrap_optimized()
}

// Calculate the spot considering the swap fee
pub fn execute_get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
    let record = read_record(&e);
    let in_record = record.get(token_in).unwrap_optimized();
    let out_record = record.get(token_out).unwrap_optimized();
    calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        read_swap_fee(&e),
    )
}

// Get the spot price without considering the swap fee
pub fn execute_get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
    let record = read_record(&e);
    let in_record = record.get(token_in).unwrap_optimized();
    let out_record = record.get(token_out).unwrap_optimized();
    calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        0,
    )
}
