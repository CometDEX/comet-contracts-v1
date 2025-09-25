use soroban_sdk::{unwrap::UnwrapOptimized, Address, Env};

use crate::{
    c_math::calc_spot_price,
    c_pool::metadata::{read_record, read_swap_fee, read_swap_fee_config},
    c_pool::storage_types::SwapFeeConfig,
};

// Calculate the spot considering the swap fee
pub fn execute_get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
    let record = read_record(&e);
    let in_record = record.get(token_in).unwrap_optimized();
    let out_record = record.get(token_out).unwrap_optimized();
    let swap_fee = read_swap_fee(&e);
    calc_spot_price(&in_record, &out_record, swap_fee)
}

// Get the spot price without considering the swap fee
pub fn execute_get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
    let record = read_record(&e);
    let in_record = record.get(token_in).unwrap_optimized();
    let out_record = record.get(token_out).unwrap_optimized();
    calc_spot_price(&in_record, &out_record, 0)
}

// Read the stored swap fee configuration
pub fn execute_get_swap_fee_config(e: Env) -> SwapFeeConfig {
    read_swap_fee_config(&e)
}
