use soroban_fixed_point_math::FixedPoint;
use soroban_sdk::I256;
use soroban_sdk::{
    assert_with_error, panic_with_error, symbol_short,
    token,
    unwrap::UnwrapOptimized,
    Address, Env, Symbol, Vec,
};

use crate::c_consts::STROOP;
use crate::{
    c_consts::{MAX_IN_RATIO, MAX_OUT_RATIO},
    c_math,
    c_pool::{
        error::Error,
        event::{DepositEvent, ExitEvent, JoinEvent, SwapEvent, WithdrawEvent},
        metadata::{
            get_total_shares, read_finalize, read_freeze, read_public_swap,
            read_record, read_swap_fee, read_tokens, read_total_weight, write_record,
        },
        storage_types::{SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD},
        token_utility::{
            burn_shares, mint_shares, pull_shares, pull_underlying, push_underlying,
        },
    },
};
const POOL: Symbol = symbol_short!("POOL");

// Absorbing tokens into the pool directly sent to the current contract
pub fn execute_gulp(e: Env, t: Address) {
    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    let mut records = read_record(&e);
    let mut rec = records
        .get(t.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, rec.bound, Error::ErrNotBound);

    rec.balance = token::Client::new(&e, &t).balance(&e.current_contract_address());
    records.set(t, rec);
    write_record(&e, records);
}

pub fn execute_join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address) {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);
    assert_with_error!(&e, pool_amount_out > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let pool_total = get_total_shares(&e);
    let zero = I256::from_i32(&e, 0);
    let ratio = c_math::calc_join_ratio(&e, pool_total, pool_amount_out);
    assert_with_error!(&e, ratio > zero, Error::ErrMathApprox);

    let tokens = read_tokens(&e);
    let mut records = read_record(&e);
    for i in 0..tokens.len() {
        let t = tokens.get_unchecked(i);
        let mut rec = records.get_unchecked(t.clone());

        let token_amount_in = c_math::calc_join_deposit_amount(&e, &rec, &ratio);
        assert_with_error!(&e, token_amount_in > 0, Error::ErrMathApprox);
        let max_amount_in = max_amounts_in.get_unchecked(i);
        assert_with_error!(&e, max_amount_in > 0, Error::ErrNegative);
        assert_with_error!(&e, token_amount_in <= max_amount_in, Error::ErrLimitIn);
        rec.balance = rec.balance.checked_add(token_amount_in).unwrap_optimized();
        records.set(t.clone(), rec);
        let event: JoinEvent = JoinEvent {
            caller: user.clone(),
            token_in: t.clone(),
            token_amount_in,
        };
        e.events()
            .publish((POOL, symbol_short!("join_pool")), event);
        pull_underlying(&e, &t, user.clone(), token_amount_in, max_amount_in);
    }

    write_record(&e, records);
    mint_shares(e, user, pool_amount_out);
}

// Helps a user exit the pool
pub fn execute_exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
    assert_with_error!(&e, pool_amount_in > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let pool_total = get_total_shares(&e);
    let zero = I256::from_i32(&e, 0);
    let ratio = c_math::calc_exit_ratio(&e, pool_total, pool_amount_in);
    assert_with_error!(&e, ratio > zero, Error::ErrMathApprox);
    pull_shares(&e, user.clone(), pool_amount_in);
    burn_shares(&e, pool_amount_in);

    let tokens = read_tokens(&e);
    let mut records = read_record(&e);
    for i in 0..tokens.len() {
        let t = tokens.get_unchecked(i);
        let mut rec = records.get_unchecked(t.clone());
        let token_amount_out = c_math::calc_exit_withdrawal_amount(&e, &rec, &ratio);
        assert_with_error!(&e, token_amount_out > 0, Error::ErrMathApprox);
        let min_amount_out = min_amounts_out.get_unchecked(i);
        assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);
        assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);
        assert_with_error!(
            &e,
            token_amount_out <= rec.balance,
            Error::ErrInsufficientBalance
        );
        rec.balance = rec.balance - token_amount_out;
        records.set(t.clone(), rec);
        let event: ExitEvent = ExitEvent {
            caller: user.clone(),
            token_out: t.clone(),
            token_amount_out,
        };
        e.events()
            .publish((POOL, symbol_short!("exit_pool")), event);
        push_underlying(&e, &t, user.clone(), token_amount_out)
    }

    write_record(&e, records);
}

pub fn execute_swap_exact_amount_in(
    e: Env,
    token_in: Address,
    token_amount_in: i128,
    token_out: Address,
    min_amount_out: i128,
    max_price: i128,
    user: Address,
) -> (i128, i128) {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);

    assert_with_error!(&e, token_amount_in >= 0, Error::ErrNegative);
    assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);
    assert_with_error!(&e, max_price >= 0, Error::ErrNegative);

    assert_with_error!(&e, read_public_swap(&e), Error::ErrSwapNotPublic);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    let swap_fee = read_swap_fee(&e);
    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, in_record.bound, Error::ErrNotBound);
    assert_with_error!(&e, out_record.bound, Error::ErrNotBound);
    assert_with_error!(
        &e,
        token_amount_in
            <= in_record
                .balance
                .fixed_mul_ceil(MAX_IN_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let spot_price_before = c_math::calc_spot_price(&in_record, &out_record, swap_fee);

    assert_with_error!(&e, spot_price_before <= max_price, Error::ErrBadLimitPrice);
    let token_amount_out = c_math::calc_token_out_given_token_in(
        &e,
        &in_record,
        &out_record,
        token_amount_in,
        swap_fee,
    );
    assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);

    in_record.balance = in_record
        .balance
        .checked_add(token_amount_in)
        .unwrap_optimized();
    assert_with_error!(
        &e,
        out_record.balance >= token_amount_out,
        Error::ErrInsufficientBalance
    );
    out_record.balance = out_record.balance - token_amount_out;

    let spot_price_after = c_math::calc_spot_price(&in_record, &out_record, swap_fee);

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= max_price, Error::ErrLimitPrice);
    // TODO: Check if this works for different token_in and token_out decimals
    assert_with_error!(
        &e,
        spot_price_before
            <= token_amount_in
                .fixed_div_floor(token_amount_out, STROOP)
                .unwrap_optimized(),
        Error::ErrMathApprox
    );

    let event: SwapEvent = SwapEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_out: token_out.clone(),
        token_amount_in,
        token_amount_out,
    };
    e.events().publish((POOL, symbol_short!("swap")), event);

    pull_underlying(
        &e,
        &token_in,
        user.clone(),
        token_amount_in,
        token_amount_in.clone(),
    );
    push_underlying(&e, &token_out, user, token_amount_out);

    record_map.set(token_in, in_record);
    record_map.set(token_out, out_record);

    write_record(&e, record_map);

    (token_amount_out, spot_price_after)
}

pub fn execute_swap_exact_amount_out(
    e: Env,
    token_in: Address,
    max_amount_in: i128,
    token_out: Address,
    token_amount_out: i128,
    max_price: i128,
    user: Address,
) -> (i128, i128) {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);
    assert_with_error!(&e, token_amount_out >= 0, Error::ErrNegative);
    assert_with_error!(&e, max_amount_in >= 0, Error::ErrNegative);
    assert_with_error!(&e, max_price >= 0, Error::ErrNegative);
    assert_with_error!(&e, read_public_swap(&e), Error::ErrSwapNotPublic);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let swap_fee = read_swap_fee(&e);
    let record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, in_record.bound, Error::ErrNotBound);
    assert_with_error!(&e, out_record.bound, Error::ErrNotBound);
    assert_with_error!(
        &e,
        token_amount_out
            <= out_record
                .balance
                .fixed_mul_ceil(MAX_OUT_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxOutRatio
    );

    let spot_price_before = c_math::calc_spot_price(&in_record, &out_record, swap_fee);
    assert_with_error!(&e, spot_price_before <= max_price, Error::ErrBadLimitPrice);
    let token_amount_in = c_math::calc_token_in_given_token_out(
        &e,
        &in_record,
        &out_record,
        token_amount_out,
        swap_fee,
    );

    assert_with_error!(&e, token_amount_in > 0, Error::ErrMathApprox);
    assert_with_error!(&e, token_amount_in <= max_amount_in, Error::ErrLimitIn);

    in_record.balance = in_record
        .balance
        .checked_add(token_amount_in)
        .unwrap_optimized();
    assert_with_error!(
        &e,
        out_record.balance >= token_amount_out,
        Error::ErrInsufficientBalance
    );
    out_record.balance = out_record.balance - token_amount_out;

    let spot_price_after = c_math::calc_spot_price(&in_record, &out_record, swap_fee);

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= max_price, Error::ErrLimitPrice);
    // TODO: Check if this works for different token_in and token_out decimals
    assert_with_error!(
        &e,
        spot_price_before
            <= token_amount_in
                .fixed_div_floor(token_amount_out, STROOP)
                .unwrap_optimized(),
        Error::ErrMathApprox
    );

    let event: SwapEvent = SwapEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_out: token_out.clone(),
        token_amount_in,
        token_amount_out,
    };
    e.events().publish((POOL, symbol_short!("swap")), event);
    pull_underlying(&e, &token_in, user.clone(), token_amount_in, max_amount_in);
    push_underlying(&e, &token_out, user, token_amount_out);

    let mut record_map = read_record(&e);
    record_map.set(token_in, in_record);
    record_map.set(token_out, out_record);

    write_record(&e, record_map);

    (token_amount_in, spot_price_after)
}

pub fn execute_dep_tokn_amt_in_get_lp_tokns_out(
    e: Env,
    token_in: Address,
    token_amount_in: i128,
    min_pool_amount_out: i128,
    user: Address,
) -> i128 {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);
    assert_with_error!(&e, token_amount_in > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, min_pool_amount_out >= 0, Error::ErrNegative);

    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    assert_with_error!(&e, read_public_swap(&e), Error::ErrSwapNotPublic);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let swap_fee = read_swap_fee(&e);
    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, in_record.bound, Error::ErrNotBound);
    assert_with_error!(
        &e,
        token_amount_in
            <= in_record
                .balance
                .fixed_mul_ceil(MAX_IN_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let total_shares = get_total_shares(&e);
    let total_weight = read_total_weight(&e);
    let pool_amount_out = c_math::calc_lp_token_amount_given_token_deposits_in(
        &e,
        &in_record,
        total_shares,
        total_weight,
        token_amount_in,
        swap_fee,
    );
    assert_with_error!(
        &e,
        pool_amount_out >= min_pool_amount_out,
        Error::ErrLimitOut
    );

    in_record.balance = in_record
        .balance
        .checked_add(token_amount_in)
        .unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    let event: DepositEvent = DepositEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    };
    e.events().publish((POOL, symbol_short!("deposit")), event);
    pull_underlying(
        &e,
        &token_in,
        user.clone(),
        token_amount_in,
        token_amount_in,
    );
    mint_shares(e, user, pool_amount_out);

    pool_amount_out
}

pub fn execute_dep_lp_tokn_amt_out_get_tokn_in(
    e: Env,
    token_in: Address,
    pool_amount_out: i128,
    max_amount_in: i128,
    user: Address,
) -> i128 {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);

    assert_with_error!(&e, pool_amount_out > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, max_amount_in > 0, Error::ErrNegativeOrZero);

    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    assert_with_error!(&e, read_public_swap(&e), Error::ErrSwapNotPublic);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, in_record.bound, Error::ErrNotBound);

    let swap_fee = read_swap_fee(&e);
    let total_shares = get_total_shares(&e);
    let total_weight = read_total_weight(&e);
    let token_amount_in = c_math::calc_token_deposits_in_given_lp_token_amount(
        &e,
        &in_record,
        total_shares,
        total_weight,
        pool_amount_out,
        swap_fee,
    );
    assert_with_error!(&e, token_amount_in != 0, Error::ErrMathApprox);
    assert_with_error!(&e, token_amount_in <= max_amount_in, Error::ErrLimitIn);
    assert_with_error!(
        &e,
        token_amount_in
            <= in_record
                .balance
                .fixed_mul_ceil(MAX_IN_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxInRatio
    );
    in_record.balance = in_record
        .balance
        .checked_add(token_amount_in)
        .unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    let event: DepositEvent = DepositEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    };
    e.events().publish((POOL, symbol_short!("deposit")), event);
    pull_underlying(&e, &token_in, user.clone(), token_amount_in, max_amount_in);
    mint_shares(e, user, pool_amount_out);

    token_amount_in
}

pub fn execute_wdr_tokn_amt_in_get_lp_tokns_out(
    e: Env,
    token_out: Address,
    pool_amount_in: i128,
    min_amount_out: i128,
    user: Address,
) -> i128 {
    assert_with_error!(&e, pool_amount_in > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    assert_with_error!(&e, read_public_swap(&e), Error::ErrSwapNotPublic);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let mut record_map = read_record(&e);
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, out_record.bound, Error::ErrNotBound);

    let swap_fee = read_swap_fee(&e);
    let total_shares = get_total_shares(&e);
    let total_weight = read_total_weight(&e);
    let token_amount_out = c_math::calc_token_withdrawal_amount_given_lp_token_amount(
        &e,
        &out_record,
        total_shares,
        total_weight,
        pool_amount_in,
        swap_fee,
    );

    assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);
    assert_with_error!(
        &e,
        token_amount_out
            <= out_record
                .balance
                .fixed_mul_ceil(MAX_OUT_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxInRatio
    );
    assert_with_error!(
        &e,
        token_amount_out <= out_record.balance,
        Error::ErrInsufficientBalance
    );
    out_record.balance = out_record.balance - token_amount_out;

    let event: WithdrawEvent = WithdrawEvent {
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in,
    };
    e.events().publish((POOL, symbol_short!("withdraw")), event);

    pull_shares(&e, user.clone(), pool_amount_in);
    burn_shares(&e, pool_amount_in);
    push_underlying(&e, &token_out, user, token_amount_out);

    record_map.set(token_out, out_record);
    write_record(&e, record_map);

    token_amount_out
}

pub fn execute_wdr_tokn_amt_out_get_lp_tokns_in(
    e: Env,
    token_out: Address,
    token_amount_out: i128,
    max_pool_amount_in: i128,
    user: Address,
) -> i128 {
    assert_with_error!(&e, token_amount_out > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, max_pool_amount_in > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    assert_with_error!(&e, read_public_swap(&e), Error::ErrSwapNotPublic);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let mut record_map = read_record(&e);
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, out_record.bound, Error::ErrNotBound);
    assert_with_error!(
        &e,
        token_amount_out
            <= out_record
                .balance
                .fixed_mul_ceil(MAX_OUT_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxOutRatio
    );

    let swap_fee = read_swap_fee(&e);
    let total_shares = get_total_shares(&e);
    let total_weight = read_total_weight(&e);
    let pool_amount_in = c_math::calc_lp_token_amount_given_token_withdrawal_amount(
        &e,
        &out_record,
        total_shares,
        total_weight,
        token_amount_out,
        swap_fee,
    );

    assert_with_error!(&e, pool_amount_in != 0, Error::ErrMathApprox);
    assert_with_error!(&e, pool_amount_in <= max_pool_amount_in, Error::ErrLimitIn);
    assert_with_error!(
        &e,
        token_amount_out <= out_record.balance,
        Error::ErrInsufficientBalance
    );
    out_record.balance = out_record.balance - token_amount_out;
    let event: WithdrawEvent = WithdrawEvent {
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in,
    };
    e.events().publish((POOL, symbol_short!("withdraw")), event);

    pull_shares(&e, user.clone(), pool_amount_in);
    burn_shares(&e, pool_amount_in);
    push_underlying(&e, &token_out, user, token_amount_out);

    record_map.set(token_out, out_record);
    write_record(&e, record_map);

    pool_amount_in
}
