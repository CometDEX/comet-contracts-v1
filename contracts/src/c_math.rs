//! Comet Pool Math Utilities
use soroban_fixed_point_math::{FixedPoint, SorobanFixedPoint};
use soroban_sdk::{assert_with_error, unwrap::UnwrapOptimized, Env, I256};

use crate::{
    c_consts::{BONE, STROOP, STROOP_SCALAR},
    c_num::{c_pow, sub_no_negative},
    c_pool::{error::Error, storage_types::Record},
};

// Calculates the spot price for a token pair
// based on weights and balances for that pair of tokens,
// accounting for fees
pub fn calc_spot_price(in_record: &Record, out_record: &Record, swap_fee: i128) -> i128 {
    // don't upscale to preserve "token in" / "token out" precision
    let numer = in_record
        .balance
        .fixed_div_floor(in_record.denorm, STROOP)
        .unwrap_optimized();
    let denom = out_record
        .balance
        .fixed_div_floor(out_record.denorm, STROOP)
        .unwrap_optimized();
    let ratio = numer.fixed_div_floor(denom, STROOP).unwrap_optimized();
    ratio
        .fixed_div_floor(STROOP - swap_fee, STROOP)
        .unwrap_optimized()
}

/// Calculates the amount of token out sent to user,
/// for a given amount of token in
///
/// Rounds down to benefit the pool
pub fn calc_token_out_given_token_in(
    e: &Env,
    in_record: &Record,
    out_record: &Record,
    amount_in: i128,
    swap_fee: i128,
) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_in = upscale(e, in_record.balance, in_record.scalar);
    let token_balance_out = upscale(e, out_record.balance, out_record.scalar);
    let token_amount_in = upscale(e, amount_in, in_record.scalar);

    let fee_adjust_ratio = upscale(e, STROOP - swap_fee, STROOP_SCALAR);
    let weight_ratio = upscale(
        e,
        in_record
            .denorm
            .fixed_div_floor(out_record.denorm, STROOP)
            .unwrap_optimized(),
        STROOP_SCALAR,
    );

    let adjusted_in = token_amount_in.fixed_mul_floor(&e, &fee_adjust_ratio, &bone);

    let base = token_balance_in.fixed_div_floor(&e, &token_balance_in.add(&adjusted_in), &bone);
    let power = c_pow(e, &base, &weight_ratio, true);
    let balance_ratio = sub_no_negative(e, &bone, &power);
    let result = token_balance_out.fixed_mul_floor(&e, &balance_ratio, &bone);

    downscale_floor(e, &result, out_record.scalar)
}

/// Calculates the amount of token in required by pool,
/// for a given amount of token out
///
/// Rounds up to benefit the pool
pub fn calc_token_in_given_token_out(
    e: &Env,
    in_record: &Record,
    out_record: &Record,
    amount_out: i128,
    swap_fee: i128,
) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_in = upscale(e, in_record.balance, in_record.scalar);
    let token_balance_out = upscale(e, out_record.balance, out_record.scalar);
    let token_amount_out = upscale(e, amount_out, out_record.scalar);

    let fee_adjust_ratio = upscale(e, STROOP - swap_fee, STROOP_SCALAR);
    let weight_ratio = upscale(
        e,
        out_record
            .denorm
            .fixed_div_ceil(in_record.denorm, STROOP)
            .unwrap_optimized(),
        STROOP_SCALAR,
    );

    let base =
        token_balance_out.fixed_div_ceil(&e, &token_balance_out.sub(&token_amount_out), &bone);
    let power = c_pow(e, &base, &weight_ratio, true);
    let balance_ratio = sub_no_negative(e, &power, &bone);

    let token_amount_in = token_balance_in.fixed_mul_ceil(&e, &balance_ratio, &bone);
    let adjusted_in = token_amount_in.fixed_div_ceil(&e, &fee_adjust_ratio, &bone);
    downscale_ceil(e, &adjusted_in, in_record.scalar)
}

/// Calculates the amount of LP tokens being minted to user,
/// for a given amount of deposited tokens
///
/// Rounds down to benefit the pool
pub fn calc_lp_token_amount_given_token_deposits_in(
    e: &Env,
    in_record: &Record,
    pool_supply: i128,
    total_weight: i128,
    token_amount_in: i128,
    swap_fee: i128,
) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_in = upscale(e, in_record.balance, in_record.scalar);
    let token_amount_in = upscale(e, token_amount_in, in_record.scalar);
    let pool_supply = upscale(e, pool_supply, STROOP_SCALAR);
    let fee = upscale(e, swap_fee, STROOP_SCALAR);

    let normalized_weight = upscale(
        e,
        in_record
            .denorm
            .fixed_div_floor(total_weight, STROOP)
            .unwrap_optimized(),
        STROOP_SCALAR,
    );
    let zaz = bone.sub(&normalized_weight).fixed_mul_floor(e, &fee, &bone);
    let token_amount_in_after_fee = token_amount_in.fixed_mul_floor(&e, &bone.sub(&zaz), &bone);

    let new_token_balance_in = token_balance_in.add(&token_amount_in_after_fee);
    let balance_ratio = new_token_balance_in.fixed_div_floor(&e, &token_balance_in, &bone);

    let pool_ratio = c_pow(e, &balance_ratio, &normalized_weight, false);
    let new_pool_supply = pool_ratio.fixed_mul_floor(&e, &pool_supply, &bone);

    downscale_floor(e, &sub_no_negative(e, &new_pool_supply, &pool_supply), STROOP_SCALAR)
}

/// Calculates the amount of deposited tokens required by pool,
/// for a given amount of LP tokens being minted
///
/// Rounds up to benefit the pool
pub fn calc_token_deposits_in_given_lp_token_amount(
    e: &Env,
    in_record: &Record,
    pool_supply: i128,
    total_weight: i128,
    pool_amount_out: i128,
    swap_fee: i128,
) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_in = upscale(e, in_record.balance, in_record.scalar);
    let pool_amount_out = upscale(e, pool_amount_out, STROOP_SCALAR);
    let pool_supply = upscale(e, pool_supply, STROOP_SCALAR);
    let fee = upscale(e, swap_fee, STROOP_SCALAR);

    let normalized_weight = upscale(
        e,
        in_record
            .denorm
            .fixed_div_ceil(total_weight, STROOP)
            .unwrap_optimized(),
        STROOP_SCALAR,
    );

    let new_pool_supply = pool_supply.add(&pool_amount_out);
    let pool_ratio = new_pool_supply.fixed_div_ceil(&e, &pool_supply, &bone);

    let boo = bone.fixed_div_ceil(e, &normalized_weight, &bone);
    let token_in_ratio = c_pow(e, &pool_ratio, &boo, false);
    let new_token_balance_in = token_balance_in.fixed_mul_ceil(&e, &token_in_ratio, &bone);

    let token_amount_in_after_fee = sub_no_negative(e, &new_token_balance_in, &token_balance_in);
    let zar = bone.sub(&normalized_weight).fixed_mul_floor(e, &fee, &bone);
    let result = token_amount_in_after_fee.fixed_div_ceil(&e, &bone.sub(&zar), &bone);

    downscale_ceil(e, &result, in_record.scalar)
}

/// Calculating the amount of LP tokens a user needs to burn,
/// for a given amount of tokens being withdrawn.
///
/// Rounds up to benefit the pool
pub fn calc_lp_token_amount_given_token_withdrawal_amount(
    e: &Env,
    out_record: &Record,
    pool_supply: i128,
    total_weight: i128,
    token_amount_out: i128,
    swap_fee: i128,
) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_out = upscale(e, out_record.balance, out_record.scalar);
    let token_amount_out = upscale(e, token_amount_out, out_record.scalar);
    let pool_supply = upscale(e, pool_supply, STROOP_SCALAR);
    let fee = upscale(e, swap_fee, STROOP_SCALAR);

    let normalized_weight = upscale(
        e,
        out_record
            .denorm
            .fixed_div_ceil(total_weight, STROOP)
            .unwrap_optimized(),
        STROOP_SCALAR,
    );

    let zoo = bone.sub(&normalized_weight);
    let zar = zoo.fixed_mul_floor(e, &fee, &bone);

    let token_amount_out_before_fee = token_amount_out.fixed_div_ceil(&e, &bone.sub(&zar), &bone);
    let new_token_balance_out = token_balance_out.sub(&token_amount_out_before_fee);
    let balance_ratio = new_token_balance_out.fixed_div_ceil(&e, &token_balance_out, &bone);

    let pool_ratio = c_pow(e, &balance_ratio, &normalized_weight, true);
    let new_pool_supply = pool_ratio.fixed_mul_ceil(&e, &pool_supply, &bone);
    let result = sub_no_negative(&e, &pool_supply, &new_pool_supply);

    downscale_ceil(e, &result, STROOP_SCALAR)
}

/// Calculating the amount of tokens being withdrawn,
/// given how many LP tokens the user wants to burn.
///
/// Rounds down to benefit the pool
pub fn calc_token_withdrawal_amount_given_lp_token_amount(
    e: &Env,
    out_record: &Record,
    pool_supply: i128,
    total_weight: i128,
    pool_amount_in: i128,
    swap_fee: i128,
) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_out = upscale(e, out_record.balance, out_record.scalar);
    let pool_amount_in = upscale(e, pool_amount_in, STROOP_SCALAR);
    let pool_supply = upscale(e, pool_supply, STROOP_SCALAR);
    let fee = upscale(e, swap_fee, STROOP_SCALAR);

    let normalized_weight = upscale(
        e,
        out_record
            .denorm
            .fixed_div_floor(total_weight, STROOP)
            .unwrap_optimized(),
        STROOP_SCALAR,
    );

    let new_pool_supply = pool_supply.sub(&pool_amount_in);
    let pool_ratio = new_pool_supply.fixed_div_floor(&e, &pool_supply, &bone);

    let exp = bone.fixed_div_floor(e, &normalized_weight, &bone);
    let token_out_ratio = c_pow(e, &pool_ratio, &exp, false);
    let new_token_balance_out = token_balance_out.fixed_mul_floor(&e, &token_out_ratio, &bone);

    let token_amount_out_before_fee = sub_no_negative(e, &token_balance_out, &new_token_balance_out);

    let zaz = bone.sub(&normalized_weight).fixed_mul_floor(e, &fee, &bone);
    let result = token_amount_out_before_fee.fixed_mul_floor(&e, &bone.sub(&zaz), &bone);

    downscale_floor(e, &result, out_record.scalar)
}

/// Calculate the join balance ratio
///
/// Rounds up to benefit the pool
pub fn calc_join_ratio(e: &Env, pool_supply: i128, pool_amount_out: i128) -> I256 {
    let bone = I256::from_i128(e, BONE);
    let pool_supply = upscale(e, pool_supply, STROOP_SCALAR);
    let pool_amount_out = upscale(e, pool_amount_out, STROOP_SCALAR);

    pool_amount_out.fixed_div_ceil(&e, &pool_supply, &bone)
}

/// Calculate the join deposit amount given the join balance ratio
///
/// Rounds up to benefit the pool
pub fn calc_join_deposit_amount(e: &Env, in_record: &Record, join_ratio: &I256) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_in = upscale(e, in_record.balance, in_record.scalar);

    let result = token_balance_in.fixed_mul_ceil(&e, join_ratio, &bone);
    downscale_ceil(e, &result, in_record.scalar)
}

/// Calculate the exit balance ratio
///
/// Rounds down to benefit the pool
pub fn calc_exit_ratio(e: &Env, pool_supply: i128, pool_amount_in: i128) -> I256 {
    let bone = I256::from_i128(e, BONE);
    let pool_supply = upscale(e, pool_supply, STROOP_SCALAR);
    let pool_amount_in = upscale(e, pool_amount_in, STROOP_SCALAR);

    pool_amount_in.fixed_div_floor(&e, &pool_supply, &bone)
}

/// Calculate the exit withdrawal amount given the exit balance ratio
///
/// Rounds down to benefit the pool
pub fn calc_exit_withdrawal_amount(e: &Env, out_record: &Record, exit_ratio: &I256) -> i128 {
    let bone = I256::from_i128(e, BONE);
    let token_balance_out = upscale(e, out_record.balance, out_record.scalar);

    let result = token_balance_out.fixed_mul_floor(&e, exit_ratio, &bone);
    downscale_floor(e, &result, out_record.scalar)
}

/********** Scaling Utils **********/

/// Upscale a number to 18 decimals and 256 bits for use in pool math
///
/// Requires that "amount" is less that 1.7e19 * scalar
///
/// Will fail if `amount` is greater than 1e18 * scalar
fn upscale(e: &Env, amount: i128, scalar: i128) -> I256 {
    I256::from_i128(e, amount * scalar)
}

/// Downscale a number from 18 decimals and 256 bits to i128 to represent a token amount.
///
/// Rounds floor if there is any remainder.
fn downscale_floor(e: &Env, amount: &I256, scalar: i128) -> i128 {
    let scale_256 = I256::from_i128(e, scalar);
    let one = I256::from_i32(e, 1);
    let result = amount.fixed_div_floor(&e, &scale_256, &one).to_i128();
    assert_with_error!(&e, result.is_some(), Error::ErrMathApprox);
    result.unwrap_optimized()
}

/// Descale a number from 18 decimals and 256 bits to i128 to represent a token amount.
///
/// Rounds up if there is any remainder.
fn downscale_ceil(e: &Env, amount: &I256, scalar: i128) -> i128 {
    let scale_256 = I256::from_i128(e, scalar);
    let one = I256::from_i32(e, 1);
    let result = amount.fixed_div_ceil(&e, &scale_256, &one).to_i128();
    assert_with_error!(&e, result.is_some(), Error::ErrMathApprox);
    result.unwrap_optimized()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scale_stroop() {
        let env = Env::default();
        let x: i128 = 12345_1234567i128;

        let mut scaled = upscale(&env, x, STROOP_SCALAR);
        let expected = I256::from_i128(&env, 12345_1234567_00_000_000_000i128);
        assert_eq!(scaled, expected);

        // takes floor
        scaled = scaled.add(&I256::from_i128(&env, STROOP_SCALAR / 10));
        let floor = downscale_floor(&env, &scaled, STROOP_SCALAR);
        assert_eq!(x, floor);

        // takes ceil
        let ceil = downscale_ceil(&env, &scaled, STROOP_SCALAR);
        assert_eq!(x + 1, ceil);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #18)")]
    fn test_downscale_floor_too_large_panics() {
        let env = Env::default();
        let x = I256::from_i128(&env, i128::MAX);
        let too_large = x.mul(&I256::from_i128(&env, STROOP_SCALAR)).add(&x);
        downscale_floor(&env, &too_large, STROOP_SCALAR);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #18)")]
    fn test_downscale_ceil_too_large_panics() {
        let env = Env::default();
        let x = I256::from_i128(&env, i128::MAX);
        let too_large = x.mul(&I256::from_i128(&env, STROOP_SCALAR)).add(&x);
        downscale_ceil(&env, &too_large, STROOP_SCALAR);
    }

    #[test]
    fn test_calc_stroop_inputs_round_correctly() {
        let env = Env::default();
        let swap_fee = 0_0030000;
        let supply = 55 * STROOP / 10; // 5.5 * STROOP

        // price: 1.94 in to 1 out
        let record_1 = Record {
            balance: 5 * STROOP,
            denorm: 3 * STROOP,
            scalar: STROOP_SCALAR,
            index: 0,
            bound: true,
        };
        let record_2 = Record {
            balance: 6 * STROOP,
            denorm: 7 * STROOP,
            scalar: STROOP_SCALAR,
            index: 0,
            bound: true,
        };

        // swap
        let result = calc_token_in_given_token_out(&env, &record_1, &record_2, 1, swap_fee);
        assert_eq!(result, 2);
        let result = calc_token_in_given_token_out(&env, &record_2, &record_1, 1, swap_fee);
        assert_eq!(result, 1);

        let result = calc_token_out_given_token_in(&env, &record_1, &record_2, 1, swap_fee);
        assert_eq!(result, 0);
        let result = calc_token_out_given_token_in(&env, &record_2, &record_1, 1, swap_fee);
        assert_eq!(result, 1);

        // exit
        let result = calc_exit_ratio(&env, 10 * STROOP, 1);
        assert_eq!(result, I256::from_i128(&env, STROOP_SCALAR / 10));

        let result = calc_exit_withdrawal_amount(
            &env,
            &record_2,
            &I256::from_i128(&env, STROOP_SCALAR / 10),
        );
        assert_eq!(result, 0);

        // join
        let result = calc_join_ratio(&env, BONE, 1);
        assert_eq!(result, I256::from_i32(&env, 1));

        let result = calc_join_deposit_amount(&env, &record_1, &I256::from_i32(&env, 1));
        assert_eq!(result, 1);

        // deposit
        let result = calc_lp_token_amount_given_token_deposits_in(
            &env,
            &record_1,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 0);

        let result = calc_token_deposits_in_given_lp_token_amount(
            &env,
            &record_1,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 4);

        let result = calc_lp_token_amount_given_token_deposits_in(
            &env,
            &record_2,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 0);

        let result = calc_token_deposits_in_given_lp_token_amount(
            &env,
            &record_2,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 2);

        // withdraw
        let result = calc_lp_token_amount_given_token_withdrawal_amount(
            &env,
            &record_1,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 1);

        let result = calc_token_withdrawal_amount_given_lp_token_amount(
            &env,
            &record_1,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 3);

        let result = calc_lp_token_amount_given_token_withdrawal_amount(
            &env,
            &record_2,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 1);

        let result = calc_token_withdrawal_amount_given_lp_token_amount(
            &env,
            &record_2,
            supply,
            10 * STROOP,
            1,
            swap_fee,
        );
        assert_eq!(result, 1);
    }
}
