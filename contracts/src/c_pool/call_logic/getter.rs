use soroban_sdk::{assert_with_error, unwrap::UnwrapOptimized, Address, Env, Vec};

use crate::{
    c_math::calc_spot_price,
    c_num::c_div,
    c_pool::{
        error::Error,
        metadata::{
            check_record_bound, get_token_share, get_total_shares, read_controller, read_finalize,
            read_public_swap, read_record, read_swap_fee, read_tokens, read_total_weight,
        },
        storage_types::Record,
    },
};

pub fn execute_get_total_supply(e: Env) -> i128 {
    get_total_shares(&e)
}

// Get the Controller Address
pub fn execute_get_controller(e: Env) -> Address {
    read_controller(&e)
}

// Get the total dernormalized weight
pub fn execute_get_total_denormalized_weight(e: Env) -> i128 {
    read_total_weight(&e)
}

// Get the number of tokens in the pool
pub fn execute_get_num_tokens(e: Env) -> u32 {
    let token_vec = read_tokens(&e);
    token_vec.len()
}

// Get the Current Tokens in the Pool
pub fn execute_get_current_tokens(e: Env) -> Vec<Address> {
    read_tokens(&e)
}

// Get the finalized tokens in the pool
pub fn execute_get_final_tokens(e: Env) -> Vec<Address> {
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    read_tokens(&e)
}

// Get the balance of the Token
pub fn execute_get_balance(e: Env, token: Address) -> i128 {
    let val = read_record(&e).get(token).unwrap_optimized();
    assert_with_error!(&e, val.bound, Error::ErrNotBound);
    val.balance
}

// Get the denormalized weight of the token
pub fn execute_get_denormalized_weight(e: Env, token: Address) -> i128 {
    assert_with_error!(
        &e,
        check_record_bound(&e, token.clone()),
        Error::ErrNotBound
    );
    let val = read_record(&e).get(token).unwrap_optimized();
    val.denorm
}

// Get the normalized weight of the token
pub fn execute_get_normalized_weight(e: Env, token: Address) -> i128 {
    assert_with_error!(
        &e,
        check_record_bound(&e, token.clone()),
        Error::ErrNotBound
    );
    let val = read_record(&e).get(token).unwrap_optimized();
    c_div(&e, val.denorm, read_total_weight(&e)).unwrap_optimized()
}

// Calculate the spot considering the swap fee
pub fn execute_get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
    let in_record = read_record(&e).get(token_in).unwrap_optimized();
    let out_record: Record = read_record(&e).get(token_out).unwrap_optimized();
    calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        read_swap_fee(&e),
    )
}

// Get the Swap Fee of the Contract
pub fn execute_get_swap_fee(e: Env) -> i128 {
    read_swap_fee(&e)
}

// Get the spot price without considering the swap fee
pub fn execute_get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
    let in_record = read_record(&e).get(token_in).unwrap_optimized();
    let out_record = read_record(&e).get(token_out).unwrap_optimized();
    calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        0,
    )
}

// Get LP Token Address
pub fn execute_share_id(e: Env) -> Address {
    get_token_share(&e)
}

// Check if the Pool can be used for swapping by normal users
pub fn execute_is_public_swap(e: Env) -> bool {
    read_public_swap(&e)
}

// Check if the Pool is finalized by the Controller
pub fn execute_is_finalized(e: Env) -> bool {
    read_finalize(&e)
}

// Check if the token Address is bound to the pool
pub fn execute_is_bound(e: Env, t: Address) -> bool {
    read_record(&e).get(t).unwrap_optimized().bound
}
