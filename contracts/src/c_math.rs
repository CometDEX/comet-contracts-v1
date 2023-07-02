//! Comet Pool Math Utilities
use soroban_sdk::Env;

use crate::{
    c_consts::{BONE, EXIT_FEE},
    c_num::{c_add, c_div, c_mul, c_pow, c_sub},
    c_pool::error::Error,
};

// Calculates the spot price for a token pair
// based on weights and balances for that pair of tokens,
// accounting for fees
pub fn calc_spot_price(
    e: &Env,
    token_balance_in: i128,
    token_weight_in: i128,
    token_balance_out: i128,
    token_weight_out: i128,
    swap_fee: i128,
) -> i128 {
    let numer = c_div(e, token_balance_in, token_weight_in).unwrap();
    let denom = c_div(e, token_balance_out, token_weight_out).unwrap();
    let ratio = c_div(e, numer, denom).unwrap();
    let scale = c_div(e, BONE, c_sub(e, BONE, swap_fee).unwrap()).unwrap();
    c_mul(e, ratio, scale).unwrap()
}

// Calculates the amount of token B you get after a swap,
// given amount of token A are you swapping
pub fn calc_token_out_given_token_in(
    e: &Env,
    token_balance_in: i128,
    token_weight_in: i128,
    token_balance_out: i128,
    token_weight_out: i128,
    token_amount_in: i128,
    swap_fee: i128,
) -> i128 {
    let weight_ratio = c_div(e, token_weight_in, token_weight_out).unwrap();
    let mut adjusted_in = c_sub(e, BONE, swap_fee).unwrap();
    adjusted_in = c_mul(e, token_amount_in, adjusted_in).unwrap();
    let y = c_div(
        e,
        token_balance_in,
        c_add(e, token_balance_in, adjusted_in).unwrap(),
    )
    .unwrap();
    let f = c_pow(e, y, weight_ratio).unwrap();
    let b = c_sub(e, BONE, f).unwrap();

    c_mul(e, token_balance_out, b).unwrap()
}

// Calculates the amount of token A you need to have,
// given amount of token B you want to get
pub fn calc_token_in_given_token_out(
    e: &Env,
    token_balance_in: i128,
    token_weight_in: i128,
    token_balance_out: i128,
    token_weight_out: i128,
    token_amount_out: i128,
    swap_fee: i128,
) -> i128 {
    let weight_ratio = c_div(e, token_weight_out, token_weight_in).unwrap();
    let diff = c_sub(e, token_balance_out, token_amount_out).unwrap();
    let y = c_div(e, token_balance_out, diff).unwrap();
    let mut f = c_pow(e, y, weight_ratio).unwrap();
    f = c_sub(e, f, BONE).unwrap();
    let mut token_amount_in = c_sub(e, BONE, swap_fee).unwrap();
    token_amount_in = c_div(e, c_mul(e, token_balance_in, f).unwrap(), token_amount_in).unwrap();
    token_amount_in
}

// Calculates the amount of LP tokens being minted to user,
// given how many deposit tokens a user deposits
pub fn calc_lp_token_amount_given_token_deposits_in(
    e: &Env,
    token_balance_in: i128,
    token_weight_in: i128,
    pool_supply: i128,
    total_weight: i128,
    token_amount_in: i128,
    swap_fee: i128,
) -> i128 {
    let normalized_weight = c_div(e, token_weight_in, total_weight).unwrap();
    let zaz = c_mul(e, c_sub(e, BONE, normalized_weight).unwrap(), swap_fee).unwrap();
    let token_amount_in_after_fee =
        c_mul(e, token_amount_in, c_sub(e, BONE, zaz).unwrap()).unwrap();

    let new_token_balance_in = c_add(e, token_balance_in, token_amount_in_after_fee).unwrap();
    let token_in_ratio = c_div(e, new_token_balance_in, token_balance_in).unwrap();

    let pool_ratio = c_pow(e, token_in_ratio, normalized_weight).unwrap();
    let new_pool_supply = c_mul(e, pool_ratio, pool_supply).unwrap();

    c_sub(e, new_pool_supply, pool_supply).unwrap()
}

// If a user wants some amount of LP tokens,
// this is how many tokens to deposit into the pool
pub fn calc_token_deposits_in_given_lp_token_amount(
    e: &Env,
    token_balance_in: i128,
    token_weight_in: i128,
    pool_supply: i128,
    total_weight: i128,
    pool_amount_out: i128,
    swap_fee: i128,
) -> i128 {
    let normalized_weight = c_div(e, token_weight_in, total_weight).unwrap();
    let new_pool_supply = c_add(e, pool_supply, pool_amount_out).unwrap();
    let pool_ratio = c_div(e, new_pool_supply, pool_supply).unwrap();

    let boo = c_div(e, BONE, normalized_weight).unwrap();
    let token_in_ratio = c_pow(e, pool_ratio, boo).unwrap();
    let new_token_balance_in = c_mul(e, token_in_ratio, token_balance_in).unwrap();
    let token_amount_in_after_fee = c_sub(e, new_token_balance_in, token_balance_in).unwrap();

    let zar = c_mul(e, c_sub(e, BONE, normalized_weight).unwrap(), swap_fee).unwrap();

    c_div(e, token_amount_in_after_fee, c_sub(e, BONE, zar).unwrap()).unwrap()
}

// Calculating the amount of LP tokens a user needs to burn,
// given how many deposit tokens they want to receive
pub fn calc_lp_token_amount_given_token_withdrawal_amount(
    e: &Env,
    token_balance_out: i128,
    token_weight_out: i128,
    pool_supply: i128,
    total_weight: i128,
    token_amount_out: i128,
    swap_fee: i128,
) -> i128 {
    let normalized_weight = c_div(e, token_weight_out, total_weight).unwrap();
    let zoo = c_sub(e, BONE, normalized_weight).unwrap();
    let zar = c_mul(e, zoo, swap_fee).unwrap();
    let token_amount_out_before_swap_fee =
        c_div(e, token_amount_out, c_sub(e, BONE, zar).unwrap()).unwrap();

    let new_token_balance_out =
        c_sub(e, token_balance_out, token_amount_out_before_swap_fee).unwrap();
    let token_out_ratio = c_div(e, new_token_balance_out, token_balance_out).unwrap();

    let pool_ratio = c_pow(e, token_out_ratio, normalized_weight).unwrap();
    let new_pool_supply = c_mul(e, pool_ratio, pool_supply).unwrap();
    let pool_amount_in_after_exit_fee = c_sub(e, pool_supply, new_pool_supply).unwrap();

    c_div(
        e,
        pool_amount_in_after_exit_fee,
        c_sub(e, BONE, EXIT_FEE).unwrap(),
    )
    .unwrap()
}

// Calculating the amount of deposit token returned,
// given how many LP tokens the user wants to burn
pub fn calc_token_withdrawal_amount_given_lp_token_amount(
    e: &Env,
    token_balance_out: i128,
    token_weight_out: i128,
    pool_supply: i128,
    total_weight: i128,
    pool_amount_in: i128,
    swap_fee: i128,
) -> i128 {
    let normalized_weight = c_div(e, token_weight_out, total_weight).unwrap();

    let pool_amount_in_after_exit_fee =
        c_mul(e, pool_amount_in, c_sub(e, BONE, EXIT_FEE).unwrap()).unwrap();
    let new_pool_supply = c_sub(e, pool_supply, pool_amount_in_after_exit_fee).unwrap();
    let pool_ratio = c_div(e, new_pool_supply, pool_supply).unwrap();

    let token_out_ratio = c_pow(e, pool_ratio, c_div(e, BONE, normalized_weight).unwrap()).unwrap();
    let new_token_balance_out = c_mul(e, token_out_ratio, token_balance_out).unwrap();

    let token_amount_out_before_swap_fee =
        c_sub(e, token_balance_out, new_token_balance_out).unwrap();

    let zaz = c_mul(e, c_sub(e, BONE, normalized_weight).unwrap(), swap_fee).unwrap();

    c_mul(
        e,
        token_amount_out_before_swap_fee,
        c_sub(e, BONE, zaz).unwrap(),
    )
    .unwrap()
}
