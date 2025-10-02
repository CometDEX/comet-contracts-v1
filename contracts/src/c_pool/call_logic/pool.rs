use soroban_fixed_point_math::FixedPoint;
use soroban_sdk::{
    assert_with_error, panic_with_error, token, unwrap::UnwrapOptimized, Address, Env, Vec,
};
use soroban_sdk::{symbol_short, I256};

use crate::c_consts::{POOL, STROOP};
use crate::{
    c_consts::{MAX_IN_RATIO, MAX_OUT_RATIO},
    c_math,
    c_pool::{
        call_logic::fee::{apply_fee_distribution, validate_fee_recipients, SwapLeg},
        error::Error,
        event::{DepositEvent, ExitEvent, JoinEvent, SwapEvent, WithdrawEvent},
        metadata::{
            get_total_shares, read_fee_rule, read_freeze, read_record, read_swap_fee, read_tokens,
            write_record,
        },
        storage_types::FeeRecipient,
        token_utility::{burn_shares, mint_shares, pull_shares, pull_underlying, push_underlying},
    },
};

// Absorbing tokens into the pool directly sent to the current contract
pub fn execute_gulp(e: Env, t: Address) {
    let mut records = read_record(&e);
    let mut rec = records
        .get(t.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));

    rec.balance = token::Client::new(&e, &t).balance(&e.current_contract_address());
    records.set(t, rec);
    write_record(&e, records);
}

pub fn execute_join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address) {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);
    assert_with_error!(&e, pool_amount_out > 0, Error::ErrNegativeOrZero);

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
        JoinEvent {
            tag: POOL,
            event: symbol_short!("join_pool"),
            caller: user.clone(),
            token_in: t.clone(),
            token_amount_in,
        }
        .publish(&e);
        pull_underlying(&e, &t, &user, token_amount_in);
    }

    write_record(&e, records);
    mint_shares(&e, &user, pool_amount_out);
}

// Helps a user exit the pool
pub fn execute_exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
    assert_with_error!(&e, pool_amount_in > 0, Error::ErrNegativeOrZero);

    let pool_total = get_total_shares(&e);
    let zero = I256::from_i32(&e, 0);
    let ratio = c_math::calc_exit_ratio(&e, pool_total, pool_amount_in);
    assert_with_error!(&e, ratio > zero, Error::ErrMathApprox);
    pull_shares(&e, &user, pool_amount_in);
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
        rec.balance = rec.balance.checked_sub(token_amount_out)
            .unwrap_or_else(|| panic_with_error!(&e, Error::ErrMathApprox));
        records.set(t.clone(), rec);
        ExitEvent {
            tag: POOL,
            event: symbol_short!("exit_pool"),
            caller: user.clone(),
            token_out: t.clone(),
            token_amount_out,
        }
        .publish(&e);
        push_underlying(&e, &t, &user, token_amount_out)
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
    trade_recipients: Option<&Vec<FeeRecipient>>,
) -> (i128, i128) {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);
    assert_with_error!(&e, token_amount_in > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);
    assert_with_error!(&e, max_price >= 0, Error::ErrNegative);

    if let Some(recipients) = trade_recipients {
        validate_fee_recipients(&e, recipients);
    }

    let swap_fee = read_swap_fee(&e);

    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(
        &e,
        token_amount_in
            <= in_record
                .balance
                .fixed_mul_floor(MAX_IN_RATIO, STROOP)
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
    out_record.balance = out_record.balance.checked_sub(token_amount_out)
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrMathApprox));

    let spot_price_after = c_math::calc_spot_price(&in_record, &out_record, swap_fee);

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= max_price, Error::ErrLimitPrice);
    assert_with_error!(
        &e,
        spot_price_before
            <= token_amount_in
                .fixed_div_floor(token_amount_out, STROOP)
                .unwrap_optimized(),
        Error::ErrMathApprox
    );

    SwapEvent {
        tag: POOL,
        event: symbol_short!("swap"),
        caller: user.clone(),
        token_in: token_in.clone(),
        token_out: token_out.clone(),
        token_amount_in,
        token_amount_out,
    }
    .publish(&e);

    pull_underlying(&e, &token_in, &user, token_amount_in);
    push_underlying(&e, &token_out, &user, token_amount_out);

    record_map.set(token_in.clone(), in_record);
    record_map.set(token_out.clone(), out_record);

    if let Some(rule) = read_fee_rule(&e) {
        if rule.fee_asset == token_in {
            apply_fee_distribution(
                &e,
                &mut record_map,
                SwapLeg::In,
                token_amount_in,
                &rule,
                trade_recipients,
            );
        } else if rule.fee_asset == token_out {
            apply_fee_distribution(
                &e,
                &mut record_map,
                SwapLeg::Out,
                token_amount_out,
                &rule,
                trade_recipients,
            );
        }
    }

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
    trade_recipients: Option<&Vec<FeeRecipient>>,
) -> (i128, i128) {
    assert_with_error!(&e, !read_freeze(&e), Error::ErrFreezeOnlyWithdrawals);
    assert_with_error!(&e, token_amount_out > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, max_amount_in > 0, Error::ErrNegativeOrZero);
    assert_with_error!(&e, max_price >= 0, Error::ErrNegative);

    if let Some(recipients) = trade_recipients {
        validate_fee_recipients(&e, recipients);
    }

    let swap_fee = read_swap_fee(&e);
    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(
        &e,
        token_amount_out
            <= out_record
                .balance
                .fixed_mul_floor(MAX_OUT_RATIO, STROOP)
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
    out_record.balance = out_record.balance.checked_sub(token_amount_out)
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrMathApprox));

    let spot_price_after = c_math::calc_spot_price(&in_record, &out_record, swap_fee);

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= max_price, Error::ErrLimitPrice);
    assert_with_error!(
        &e,
        spot_price_before
            <= token_amount_in
                .fixed_div_floor(token_amount_out, STROOP)
                .unwrap_optimized(),
        Error::ErrMathApprox
    );

    SwapEvent {
        tag: POOL,
        event: symbol_short!("swap"),
        caller: user.clone(),
        token_in: token_in.clone(),
        token_out: token_out.clone(),
        token_amount_in,
        token_amount_out,
    }
    .publish(&e);
    pull_underlying(&e, &token_in, &user, token_amount_in);
    push_underlying(&e, &token_out, &user, token_amount_out);

    record_map.set(token_in.clone(), in_record);
    record_map.set(token_out.clone(), out_record);

    if let Some(rule) = read_fee_rule(&e) {
        if rule.fee_asset == token_in {
            apply_fee_distribution(
                &e,
                &mut record_map,
                SwapLeg::In,
                token_amount_in,
                &rule,
                trade_recipients,
            );
        } else if rule.fee_asset == token_out {
            apply_fee_distribution(
                &e,
                &mut record_map,
                SwapLeg::Out,
                token_amount_out,
                &rule,
                trade_recipients,
            );
        }
    }

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

    let swap_fee = read_swap_fee(&e);
    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(
        &e,
        token_amount_in
            <= in_record
                .balance
                .fixed_mul_floor(MAX_IN_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let total_shares = get_total_shares(&e);
    let pool_amount_out = c_math::calc_lp_token_amount_given_token_deposits_in(
        &e,
        &in_record,
        total_shares,
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

    DepositEvent {
        tag: POOL,
        event: symbol_short!("deposit"),
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    }
    .publish(&e);
    pull_underlying(&e, &token_in, &user, token_amount_in);
    mint_shares(&e, &user, pool_amount_out);

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

    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));

    let swap_fee = read_swap_fee(&e);
    let total_shares = get_total_shares(&e);
    let token_amount_in = c_math::calc_token_deposits_in_given_lp_token_amount(
        &e,
        &in_record,
        total_shares,
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
                .fixed_mul_floor(MAX_IN_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxInRatio
    );
    in_record.balance = in_record
        .balance
        .checked_add(token_amount_in)
        .unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    DepositEvent {
        tag: POOL,
        event: symbol_short!("deposit"),
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    }
    .publish(&e);
    pull_underlying(&e, &token_in, &user, token_amount_in);
    mint_shares(&e, &user, pool_amount_out);

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

    let mut record_map = read_record(&e);
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));

    let swap_fee = read_swap_fee(&e);
    let total_shares = get_total_shares(&e);
    let token_amount_out = c_math::calc_token_withdrawal_amount_given_lp_token_amount(
        &e,
        &out_record,
        total_shares,
        pool_amount_in,
        swap_fee,
    );

    assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);
    assert_with_error!(
        &e,
        token_amount_out
            <= out_record
                .balance
                .fixed_mul_floor(MAX_OUT_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxOutRatio
    );
    assert_with_error!(
        &e,
        token_amount_out <= out_record.balance,
        Error::ErrInsufficientBalance
    );
    out_record.balance = out_record.balance.checked_sub(token_amount_out)
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrMathApprox));

    WithdrawEvent {
        tag: POOL,
        event: symbol_short!("withdraw"),
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in,
    }
    .publish(&e);

    pull_shares(&e, &user, pool_amount_in);
    burn_shares(&e, pool_amount_in);
    push_underlying(&e, &token_out, &user, token_amount_out);

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

    let mut record_map = read_record(&e);
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(
        &e,
        token_amount_out
            <= out_record
                .balance
                .fixed_mul_floor(MAX_OUT_RATIO, STROOP)
                .unwrap_optimized(),
        Error::ErrMaxOutRatio
    );

    let swap_fee = read_swap_fee(&e);
    let total_shares = get_total_shares(&e);
    let pool_amount_in = c_math::calc_lp_token_amount_given_token_withdrawal_amount(
        &e,
        &out_record,
        total_shares,
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
    out_record.balance = out_record.balance.checked_sub(token_amount_out)
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrMathApprox));
    WithdrawEvent {
        tag: POOL,
        event: symbol_short!("withdraw"),
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in,
    }
    .publish(&e);

    pull_shares(&e, &user, pool_amount_in);
    burn_shares(&e, pool_amount_in);
    push_underlying(&e, &token_out, &user, token_amount_out);

    record_map.set(token_out, out_record);
    write_record(&e, record_map);

    pool_amount_in
}
