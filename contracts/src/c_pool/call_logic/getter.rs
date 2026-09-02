use soroban_sdk::{assert_with_error, unwrap::UnwrapOptimized, Address, Env};

use crate::{
    c_math::calc_spot_price,
    c_pool::{
        error::Error,
        metadata::{read_record, read_swap_fee},
    },
};

// Calculate the spot considering the swap fee
pub fn execute_get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
    assert_with_error!(&e, token_in != token_out, Error::ErrSameToken);
    let record = read_record(&e);
    let in_record = record.get(token_in).unwrap_optimized();
    let out_record = record.get(token_out).unwrap_optimized();
    let swap_fee = read_swap_fee(&e);
    calc_spot_price(&in_record, &out_record, swap_fee)
}

// Get the spot price without considering the swap fee
pub fn execute_get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
    assert_with_error!(&e, token_in != token_out, Error::ErrSameToken);
    let record = read_record(&e);
    let in_record = record.get(token_in).unwrap_optimized();
    let out_record = record.get(token_out).unwrap_optimized();
    calc_spot_price(&in_record, &out_record, 0)
}
