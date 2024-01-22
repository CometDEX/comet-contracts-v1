use soroban_sdk::{
    assert_with_error, panic_with_error, symbol_short, token, unwrap::UnwrapOptimized, Address,
    Env, Symbol, Vec,
};

use crate::{
    c_consts::{EXIT_FEE, MAX_IN_RATIO, MAX_OUT_RATIO},
    c_math::{
        calc_lp_token_amount_given_token_deposits_in,
        calc_lp_token_amount_given_token_withdrawal_amount, calc_spot_price,
        calc_token_deposits_in_given_lp_token_amount, calc_token_in_given_token_out,
        calc_token_out_given_token_in, calc_token_withdrawal_amount_given_lp_token_amount,
    },
    c_num::{c_add, c_div, c_mul, c_sub},
    c_pool::{
        error::Error,
        event::{DepositEvent, ExitEvent, JoinEvent, SwapEvent, WithdrawEvent},
        metadata::{
            get_total_shares, read_factory, read_finalize, read_freeze, read_public_swap,
            read_record, read_swap_fee, read_tokens, read_total_weight, write_record,
        },
        storage_types::{Record, SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD},
        token_utility::{
            burn_shares, mint_shares, pull_shares, pull_underlying, push_shares, push_underlying,
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
    let ratio = c_add(
        &e,
        c_div(&e, pool_amount_out, pool_total).unwrap_optimized(),
        1,
    )
    .unwrap_optimized();

    if ratio == 0 {
        panic_with_error!(&e, Error::ErrMathApprox)
    }
    let tokens = read_tokens(&e);
    let mut records = read_record(&e);
    for i in 0..tokens.len() {
        let t = tokens.get(i).unwrap_optimized();
        let mut rec = records.get(t.clone()).unwrap_optimized();
        let token_amount_in =
            c_add(&e, c_mul(&e, ratio, rec.balance).unwrap_optimized(), 1).unwrap_optimized();
        if token_amount_in == 0 {
            panic_with_error!(&e, Error::ErrMathApprox);
        }

        assert_with_error!(
            &e,
            max_amounts_in.get(i).unwrap_optimized() > 0,
            Error::ErrNegative
        );

        if token_amount_in > max_amounts_in.get(i).unwrap_optimized() {
            panic_with_error!(&e, Error::ErrLimitIn);
        }
        rec.balance = c_add(&e, rec.balance, token_amount_in).unwrap_optimized();
        records.set(t.clone(), rec);
        let event: JoinEvent = JoinEvent {
            caller: user.clone(),
            token_in: t.clone(),
            token_amount_in,
        };
        e.events()
            .publish((POOL, symbol_short!("join_pool")), event);
        pull_underlying(&e, &t, user.clone(), token_amount_in);
    }

    write_record(&e, records);
    mint_shares(e, user, pool_amount_out);
}

// Helps a user exit the pool
pub fn execute_exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
    assert_with_error!(&e, pool_amount_in >= 0, Error::ErrNegative);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);
    let pool_total = get_total_shares(&e);
    let exit_fee = c_mul(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();
    let pai_after_exit_fee = c_sub(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();
    let ratio: i128 = c_div(&e, pai_after_exit_fee, pool_total).unwrap_optimized();
    assert_with_error!(&e, ratio != 0, Error::ErrMathApprox);
    pull_shares(&e, user.clone(), pool_amount_in);

    let share_contract_id = e.current_contract_address();
    push_shares(&e, share_contract_id, EXIT_FEE);
    burn_shares(&e, pai_after_exit_fee);
    let tokens = read_tokens(&e);
    let mut records = read_record(&e);
    for i in 0..tokens.len() {
        let t = tokens.get(i).unwrap_optimized();
        let mut rec = records.get(t.clone()).unwrap_optimized();
        let token_amount_out = c_mul(&e, ratio, rec.balance).unwrap_optimized();
        assert_with_error!(&e, token_amount_out != 0, Error::ErrMathApprox);
        assert_with_error!(
            &e,
            min_amounts_out.get(i).unwrap_optimized() >= 0,
            Error::ErrNegative
        );
        assert_with_error!(
            &e,
            token_amount_out >= min_amounts_out.get(i).unwrap_optimized(),
            Error::ErrLimitOut
        );
        rec.balance = c_sub(&e, rec.balance, token_amount_out).unwrap_optimized();
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
        token_amount_in <= c_mul(&e, in_record.balance, MAX_IN_RATIO).unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let spot_price_before = calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        read_swap_fee(&e),
    );

    assert_with_error!(&e, spot_price_before <= max_price, Error::ErrBadLimitPrice);
    let token_amount_out = calc_token_out_given_token_in(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        token_amount_in,
        read_swap_fee(&e),
    );
    assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);

    in_record.balance = c_add(&e, in_record.balance, token_amount_in).unwrap_optimized();
    out_record.balance = c_sub(&e, out_record.balance, token_amount_out).unwrap_optimized();

    let spot_price_after = calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        read_swap_fee(&e),
    );

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= max_price, Error::ErrLimitPrice);
    assert_with_error!(
        &e,
        spot_price_before <= c_div(&e, token_amount_in, token_amount_out).unwrap_optimized(),
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

    pull_underlying(&e, &token_in, user.clone(), token_amount_in);
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
        token_amount_out <= c_mul(&e, out_record.balance, MAX_OUT_RATIO).unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let spot_price_before = calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        read_swap_fee(&e),
    );

    assert_with_error!(&e, spot_price_before <= max_price, Error::ErrBadLimitPrice);
    let token_amount_in = calc_token_in_given_token_out(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        token_amount_out,
        read_swap_fee(&e),
    );

    assert_with_error!(&e, token_amount_in <= max_amount_in, Error::ErrLimitIn);

    in_record.balance = c_add(&e, in_record.balance, token_amount_in).unwrap_optimized();
    out_record.balance = c_sub(&e, out_record.balance, token_amount_out).unwrap_optimized();

    let spot_price_after = calc_spot_price(
        &e,
        in_record.balance,
        in_record.denorm,
        out_record.balance,
        out_record.denorm,
        read_swap_fee(&e),
    );

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= max_price, Error::ErrLimitPrice);
    assert_with_error!(
        &e,
        spot_price_before <= c_div(&e, token_amount_in, token_amount_out).unwrap_optimized(),
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

    pull_underlying(&e, &token_in, user.clone(), token_amount_in);
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
    assert_with_error!(&e, token_amount_in >= 0, Error::ErrNegative);
    assert_with_error!(&e, min_pool_amount_out >= 0, Error::ErrNegative);

    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, in_record.bound, Error::ErrNotBound);
    assert_with_error!(
        &e,
        token_amount_in <= c_mul(&e, in_record.balance, MAX_IN_RATIO).unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let pool_amount_out = calc_lp_token_amount_given_token_deposits_in(
        &e,
        in_record.balance,
        in_record.denorm,
        get_total_shares(&e),
        read_total_weight(&e),
        token_amount_in,
        read_swap_fee(&e),
    );
    assert_with_error!(
        &e,
        pool_amount_out >= min_pool_amount_out,
        Error::ErrLimitOut
    );
    in_record.balance = c_add(&e, in_record.balance, token_amount_in).unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    let event: DepositEvent = DepositEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    };
    e.events().publish((POOL, symbol_short!("deposit")), event);

    pull_underlying(&e, &token_in, user.clone(), token_amount_in);
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

    assert_with_error!(&e, pool_amount_out >= 0, Error::ErrNegative);
    assert_with_error!(&e, max_amount_in >= 0, Error::ErrNegative);

    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let mut record_map = read_record(&e);
    let mut in_record = record_map
        .get(token_in.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, in_record.bound, Error::ErrNotBound);

    let token_amount_in = calc_token_deposits_in_given_lp_token_amount(
        &e,
        in_record.balance,
        in_record.denorm,
        get_total_shares(&e),
        read_total_weight(&e),
        pool_amount_out,
        read_swap_fee(&e),
    );
    assert_with_error!(&e, token_amount_in != 0, Error::ErrMathApprox);
    assert_with_error!(&e, token_amount_in <= max_amount_in, Error::ErrLimitIn);
    assert_with_error!(
        &e,
        token_amount_in <= c_mul(&e, in_record.balance, MAX_IN_RATIO).unwrap_optimized(),
        Error::ErrMaxInRatio
    );
    in_record.balance = c_add(&e, in_record.balance, token_amount_in).unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    let event: DepositEvent = DepositEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    };
    e.events().publish((POOL, symbol_short!("deposit")), event);

    pull_underlying(&e, &token_in, user.clone(), token_amount_in);
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
    assert_with_error!(&e, pool_amount_in >= 0, Error::ErrNegative);
    assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);

    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let mut record_map = read_record(&e);
    let mut out_record = record_map
        .get(token_out.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, out_record.bound, Error::ErrNotBound);

    let token_amount_out = calc_token_withdrawal_amount_given_lp_token_amount(
        &e,
        out_record.balance,
        out_record.denorm,
        get_total_shares(&e),
        read_total_weight(&e),
        pool_amount_in,
        read_swap_fee(&e),
    );

    assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);
    assert_with_error!(
        &e,
        token_amount_out <= c_mul(&e, out_record.balance, MAX_OUT_RATIO).unwrap_optimized(),
        Error::ErrMaxOutRatio
    );
    out_record.balance = c_sub(&e, out_record.balance, token_amount_out).unwrap_optimized();
    let exit_fee = c_mul(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();

    let event: WithdrawEvent = WithdrawEvent {
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in,
    };
    e.events().publish((POOL, symbol_short!("withdraw")), event);

    pull_shares(&e, user.clone(), pool_amount_in);
    burn_shares(&e, c_sub(&e, pool_amount_in, EXIT_FEE).unwrap_optimized());
    let factory = read_factory(&e);
    push_shares(&e, factory, EXIT_FEE);
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
    assert_with_error!(&e, read_finalize(&e), Error::ErrNotFinalized);

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
        token_amount_out <= c_mul(&e, out_record.balance, MAX_OUT_RATIO).unwrap_optimized(),
        Error::ErrMaxOutRatio
    );

    let pool_amount_in = calc_lp_token_amount_given_token_withdrawal_amount(
        &e,
        out_record.balance,
        out_record.denorm,
        get_total_shares(&e),
        read_total_weight(&e),
        token_amount_out,
        read_swap_fee(&e),
    );

    assert_with_error!(&e, pool_amount_in != 0, Error::ErrMathApprox);
    assert_with_error!(&e, pool_amount_in <= max_pool_amount_in, Error::ErrLimitIn);
    out_record.balance = c_sub(&e, out_record.balance, token_amount_out).unwrap_optimized();
    let exit_fee = c_mul(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();
    let event: WithdrawEvent = WithdrawEvent {
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in,
    };
    e.events().publish((POOL, symbol_short!("withdraw")), event);

    pull_shares(&e, user.clone(), pool_amount_in);
    burn_shares(&e, c_sub(&e, pool_amount_in, EXIT_FEE).unwrap_optimized());
    let factory = read_factory(&e);
    push_shares(&e, factory, EXIT_FEE);
    push_underlying(&e, &token_out, user, token_amount_out);

    record_map.set(token_out, out_record);
    write_record(&e, record_map);

    pool_amount_in
}
