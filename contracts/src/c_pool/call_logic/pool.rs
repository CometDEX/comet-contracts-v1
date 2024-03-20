use soroban_sdk::{
    assert_with_error, panic_with_error, symbol_short, token, unwrap::UnwrapOptimized, Address,
    Env, Symbol, Vec, I256,
};
use soroban_sdk::token::Client;

use crate::{
    c_consts_256::{get_exit_fee, get_max_in_ratio, get_max_out_ratio},
    c_math_256::{
        calc_lp_token_amount_given_token_deposits_in,
        calc_lp_token_amount_given_token_withdrawal_amount, calc_spot_price,
        calc_token_deposits_in_given_lp_token_amount, calc_token_in_given_token_out,
        calc_token_out_given_token_in, calc_token_withdrawal_amount_given_lp_token_amount,
    },
    c_num_256::{c_add, c_div, c_mul, c_sub},
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
        c_div(&e, I256::from_i128(&e, pool_amount_out), I256::from_i128(&e, pool_total)).unwrap_optimized(),
        I256::from_i128(&e,1)
    )
    .unwrap_optimized();

    if ratio == I256::from_i128(&e, 0) {
        panic_with_error!(&e, Error::ErrMathApprox)
    }
    let tokens = read_tokens(&e);
    let mut records = read_record(&e);
    for i in 0..tokens.len() {
        let t = tokens.get(i).unwrap_optimized();
        let mut rec = records.get(t.clone()).unwrap_optimized();
        let token_amount_in =
            c_add(&e, c_mul(&e, ratio.clone(), I256::from_i128(&e,rec.balance)).unwrap_optimized(), I256::from_i128(&e, 1)).unwrap_optimized();
        if token_amount_in == I256::from_i128(&e, 0) {
            panic_with_error!(&e, Error::ErrMathApprox);
        }

        assert_with_error!(
            &e,
            max_amounts_in.get(i).unwrap_optimized() > 0,
            Error::ErrNegative
        );

        if token_amount_in > I256::from_i128(&e, max_amounts_in.get(i).unwrap_optimized()) {
            panic_with_error!(&e, Error::ErrLimitIn);
        }
        rec.balance = c_add(&e, I256::from_i128(&e, rec.balance), token_amount_in.clone()).unwrap_optimized().to_i128().unwrap_optimized();
        records.set(t.clone(), rec);
        let event: JoinEvent = JoinEvent {
            caller: user.clone(),
            token_in: t.clone(),
            token_amount_in: token_amount_in.to_i128().unwrap_optimized(),
        };
        e.events()
            .publish((POOL, symbol_short!("join_pool")), event);
        pull_underlying(&e, &t, user.clone(),  token_amount_in.to_i128().unwrap_optimized(), max_amounts_in.get(i).unwrap_optimized());
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
    let exit_fee = c_mul(&e, I256::from_i128(&e,pool_amount_in), get_exit_fee(&e)).unwrap_optimized();
    let pai_after_exit_fee = c_sub(&e, I256::from_i128(&e, pool_amount_in), exit_fee.clone()).unwrap_optimized();
    let ratio = c_div(&e, pai_after_exit_fee.clone(), I256::from_i128(&e,pool_total)).unwrap_optimized();
    assert_with_error!(&e, ratio != I256::from_i128(&e, 0), Error::ErrMathApprox);
    pull_shares(&e, user.clone(), pool_amount_in);

    let factory = read_factory(&e);
    push_shares(&e, factory, exit_fee.to_i128().unwrap_optimized());

    burn_shares(&e, pai_after_exit_fee.to_i128().unwrap_optimized());
    let tokens = read_tokens(&e);
    let mut records = read_record(&e);
    for i in 0..tokens.len() {
        let t = tokens.get(i).unwrap_optimized();
        let mut rec = records.get(t.clone()).unwrap_optimized();
        let token_amount_out = c_mul(&e, ratio.clone(), I256::from_i128(&e,rec.balance)).unwrap_optimized();
        assert_with_error!(&e, token_amount_out != I256::from_i128(&e, 0), Error::ErrMathApprox);
        assert_with_error!(
            &e,
            min_amounts_out.get(i).unwrap_optimized() >= 0,
            Error::ErrNegative
        );
        assert_with_error!(
            &e,
            token_amount_out >= I256::from_i128(&e,min_amounts_out.get(i).unwrap_optimized()),
            Error::ErrLimitOut
        );
        rec.balance = c_sub(&e, I256::from_i128(&e,rec.balance), token_amount_out.clone()).unwrap_optimized().to_i128().unwrap_optimized();
        records.set(t.clone(), rec);
        let event: ExitEvent = ExitEvent {
            caller: user.clone(),
            token_out: t.clone(),
            token_amount_out: token_amount_out.to_i128().unwrap_optimized(),
        };
        e.events()
            .publish((POOL, symbol_short!("exit_pool")), event);
        push_underlying(&e, &t, user.clone(), token_amount_out.to_i128().unwrap_optimized())
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
        I256::from_i128(&e,token_amount_in) <= c_mul(&e, I256::from_i128(&e,in_record.balance), get_max_in_ratio(&e)).unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let spot_price_before = calc_spot_price(
        &e,
        I256::from_i128(&e,in_record.balance),
        I256::from_i128(&e,in_record.denorm),
        I256::from_i128(&e,out_record.balance),
        I256::from_i128(&e,out_record.denorm),
        I256::from_i128(&e,read_swap_fee(&e)),
    );

    assert_with_error!(&e, spot_price_before <=  I256::from_i128(&e,max_price), Error::ErrBadLimitPrice);
    let token_amount_out = calc_token_out_given_token_in(
        &e,
        I256::from_i128(&e,in_record.balance),
        I256::from_i128(&e,in_record.denorm),
        I256::from_i128(&e,out_record.balance),
        I256::from_i128(&e,out_record.denorm),
        I256::from_i128(&e,token_amount_in),
        I256::from_i128(&e,read_swap_fee(&e)),
    );
    assert_with_error!(&e, token_amount_out >=  I256::from_i128(&e,min_amount_out), Error::ErrLimitOut);

    in_record.balance = c_add(&e,  I256::from_i128(&e,in_record.balance),  I256::from_i128(&e,token_amount_in)).unwrap_optimized().to_i128().unwrap_optimized();
    out_record.balance = c_sub(&e,  I256::from_i128(&e,out_record.balance), token_amount_out.clone()).unwrap_optimized().to_i128().unwrap_optimized();

    let spot_price_after = calc_spot_price(
        &e,
        I256::from_i128(&e, in_record.balance),
        I256::from_i128(&e, in_record.denorm),
        I256::from_i128(&e, out_record.balance),
        I256::from_i128(&e, out_record.denorm),
        I256::from_i128(&e, read_swap_fee(&e)),
    );

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= I256::from_i128(&e, max_price), Error::ErrLimitPrice);
    assert_with_error!(
        &e,
        spot_price_before <= c_div(&e, I256::from_i128(&e, token_amount_in), token_amount_out.clone()).unwrap_optimized(),
        Error::ErrMathApprox
    );

    let event: SwapEvent = SwapEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_out: token_out.clone(),
        token_amount_in,
        token_amount_out:token_amount_out.to_i128().unwrap_optimized(),
    };
    e.events().publish((POOL, symbol_short!("swap")), event);

    pull_underlying(&e, &token_in, user.clone(), token_amount_in, token_amount_in.clone());
    push_underlying(&e, &token_out, user, token_amount_out.to_i128().unwrap_optimized());

    record_map.set(token_in, in_record);
    record_map.set(token_out, out_record);

    write_record(&e, record_map);

    (token_amount_out.to_i128().unwrap_optimized(), spot_price_after.to_i128().unwrap_optimized())
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
        I256::from_i128(&e, token_amount_out) <= c_mul(&e, I256::from_i128(&e, out_record.balance), get_max_out_ratio(&e)).unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let spot_price_before = calc_spot_price(
        &e,
        I256::from_i128(&e,in_record.balance),
        I256::from_i128(&e,in_record.denorm),
        I256::from_i128(&e,out_record.balance),
        I256::from_i128(&e,out_record.denorm),
        I256::from_i128(&e,read_swap_fee(&e)),
    );

    assert_with_error!(&e, spot_price_before <= I256::from_i128(&e, max_price), Error::ErrBadLimitPrice);
    let token_amount_in = calc_token_in_given_token_out(
        &e,
        I256::from_i128(&e, in_record.balance),
        I256::from_i128(&e,in_record.denorm), 
        I256::from_i128(&e,out_record.balance),
        I256::from_i128(&e,out_record.denorm),
        I256::from_i128(&e,token_amount_out),
        I256::from_i128(&e,read_swap_fee(&e)),
    );

    assert_with_error!(&e, token_amount_in > I256::from_i128(&e,0), Error::ErrMathApprox);
    assert_with_error!(&e, token_amount_in <=  I256::from_i128(&e,max_amount_in), Error::ErrLimitIn);

    in_record.balance = c_add(&e, I256::from_i128(&e,in_record.balance), token_amount_in.clone()).unwrap_optimized().to_i128().unwrap_optimized();
    out_record.balance = c_sub(&e, I256::from_i128(&e,out_record.balance), I256::from_i128(&e,token_amount_out)).unwrap_optimized().to_i128().unwrap_optimized();

    let spot_price_after = calc_spot_price(
        &e,
        I256::from_i128(&e,in_record.balance),
        I256::from_i128(&e,in_record.denorm),
        I256::from_i128(&e,out_record.balance),
        I256::from_i128(&e,out_record.denorm),
        I256::from_i128(&e,read_swap_fee(&e)),
    );

    assert_with_error!(
        &e,
        spot_price_after >= spot_price_before,
        Error::ErrMathApprox
    );
    assert_with_error!(&e, spot_price_after <= I256::from_i128(&e,max_price), Error::ErrLimitPrice);
    assert_with_error!(
        &e,
        spot_price_before <= c_div(&e, token_amount_in.clone(), I256::from_i128(&e,token_amount_out)).unwrap_optimized(),
        Error::ErrMathApprox
    );

    let event: SwapEvent = SwapEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        token_amount_in: token_amount_in.to_i128().unwrap_optimized(),
    };
    e.events().publish((POOL, symbol_short!("swap")), event);

    pull_underlying(&e, &token_in, user.clone(), token_amount_in.to_i128().unwrap_optimized(),max_amount_in);
    push_underlying(&e, &token_out, user, token_amount_out);

    let mut record_map = read_record(&e);
    record_map.set(token_in, in_record);
    record_map.set(token_out, out_record);

    write_record(&e, record_map);

    (token_amount_in.to_i128().unwrap_optimized(), spot_price_after.to_i128().unwrap_optimized())
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
        I256::from_i128(&e, token_amount_in) <= c_mul(&e, I256::from_i128(&e, in_record.balance), get_max_in_ratio(&e)).unwrap_optimized(),
        Error::ErrMaxInRatio
    );

    let pool_amount_out = calc_lp_token_amount_given_token_deposits_in(
        &e,
        I256::from_i128(&e,in_record.balance),
        I256::from_i128(&e,in_record.denorm),
        I256::from_i128(&e,get_total_shares(&e)),
        I256::from_i128(&e,read_total_weight(&e)),
        I256::from_i128(&e, token_amount_in),
        I256::from_i128(&e,read_swap_fee(&e)),
    );
    assert_with_error!(
        &e,
        pool_amount_out >= I256::from_i128(&e,min_pool_amount_out),
        Error::ErrLimitOut
    );
    in_record.balance = c_add(&e, I256::from_i128(&e,in_record.balance), I256::from_i128(&e,token_amount_in)).unwrap_optimized().to_i128().unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    let event: DepositEvent = DepositEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in,
    };
    e.events().publish((POOL, symbol_short!("deposit")), event);

    pull_underlying(&e, &token_in, user.clone(), token_amount_in, token_amount_in);
    mint_shares(e, user, pool_amount_out.to_i128().unwrap_optimized());

    pool_amount_out.to_i128().unwrap_optimized()
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
        I256::from_i128(&e,in_record.balance),
        I256::from_i128(&e, in_record.denorm),
        I256::from_i128(&e, get_total_shares(&e)),
        I256::from_i128(&e, read_total_weight(&e)),
        I256::from_i128(&e, pool_amount_out),
        I256::from_i128(&e, read_swap_fee(&e)),
    );
    assert_with_error!(&e, token_amount_in != I256::from_i128(&e, 0), Error::ErrMathApprox);
    assert_with_error!(&e, token_amount_in <= I256::from_i128(&e, max_amount_in), Error::ErrLimitIn);
    assert_with_error!(
        &e,
        token_amount_in <= c_mul(&e, I256::from_i128(&e, in_record.balance), get_max_in_ratio(&e)).unwrap_optimized(),
        Error::ErrMaxInRatio
    );
    in_record.balance = c_add(&e, I256::from_i128(&e, in_record.balance), token_amount_in.clone()).unwrap_optimized().to_i128().unwrap_optimized();

    record_map.set(token_in.clone(), in_record);
    write_record(&e, record_map);

    let event: DepositEvent = DepositEvent {
        caller: user.clone(),
        token_in: token_in.clone(),
        token_amount_in: token_amount_in.to_i128().unwrap_optimized(),
    };
    e.events().publish((POOL, symbol_short!("deposit")), event);

    pull_underlying(&e, &token_in, user.clone(), token_amount_in.to_i128().unwrap_optimized(), max_amount_in);
    mint_shares(e, user, pool_amount_out);

    token_amount_in.to_i128().unwrap_optimized()
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
        I256::from_i128(&e, out_record.balance),
        I256::from_i128(&e, out_record.denorm),
        I256::from_i128(&e, get_total_shares(&e)),
        I256::from_i128(&e, read_total_weight(&e)),
        I256::from_i128(&e, pool_amount_in),
        I256::from_i128(&e, read_swap_fee(&e)),
    );

    assert_with_error!(&e, token_amount_out >= I256::from_i128(&e, min_amount_out), Error::ErrLimitOut);
    assert_with_error!(
        &e,
        token_amount_out <= c_mul(&e, I256::from_i128(&e, out_record.balance), get_max_out_ratio(&e)).unwrap_optimized(),
        Error::ErrMaxOutRatio
    );
    out_record.balance = c_sub(&e, I256::from_i128(&e, out_record.balance), token_amount_out.clone()).unwrap_optimized().to_i128().unwrap_optimized();
    let exit_fee = c_mul(&e, I256::from_i128(&e, pool_amount_in), get_exit_fee(&e)).unwrap_optimized();

    let event: WithdrawEvent = WithdrawEvent {
        caller: user.clone(),
        token_out: token_out.clone(),      
        pool_amount_in,
        token_amount_out: token_amount_out.to_i128().unwrap_optimized(),
    };
    e.events().publish((POOL, symbol_short!("withdraw")), event);

    pull_shares(&e, user.clone(), pool_amount_in);
    burn_shares(&e, c_sub(&e, I256::from_i128(&e,pool_amount_in), exit_fee.clone()).unwrap_optimized().to_i128().unwrap_optimized());
    let factory = read_factory(&e);
    push_shares(&e, factory, exit_fee.to_i128().unwrap_optimized());
    push_underlying(&e, &token_out, user, token_amount_out.to_i128().unwrap_optimized());

    record_map.set(token_out, out_record);
    write_record(&e, record_map);

    token_amount_out.to_i128().unwrap_optimized()
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
        I256::from_i128(&e, token_amount_out) <= c_mul(&e, I256::from_i128(&e, out_record.balance), get_max_out_ratio(&e)).unwrap_optimized(),
        Error::ErrMaxOutRatio
    );

    let pool_amount_in = calc_lp_token_amount_given_token_withdrawal_amount(
        &e,
        I256::from_i128(&e, out_record.balance),
        I256::from_i128(&e, out_record.denorm),
        I256::from_i128(&e,  get_total_shares(&e)),
        I256::from_i128(&e, read_total_weight(&e)),
        I256::from_i128(&e, token_amount_out),
        I256::from_i128(&e, read_swap_fee(&e)),
    );

    assert_with_error!(&e, pool_amount_in !=I256::from_i128(&e, 0), Error::ErrMathApprox);
    assert_with_error!(&e, pool_amount_in <= I256::from_i128(&e,max_pool_amount_in), Error::ErrLimitIn);
    out_record.balance = c_sub(&e, I256::from_i128(&e, out_record.balance), I256::from_i128(&e,token_amount_out)).unwrap_optimized().to_i128().unwrap_optimized();
    let exit_fee = c_mul(&e, pool_amount_in.clone(), get_exit_fee(&e)).unwrap_optimized();
    let event: WithdrawEvent = WithdrawEvent {
        caller: user.clone(),
        token_out: token_out.clone(),
        token_amount_out,
        pool_amount_in: pool_amount_in.to_i128().unwrap_optimized(),
    };
    e.events().publish((POOL, symbol_short!("withdraw")), event);

    pull_shares(&e, user.clone(), pool_amount_in.to_i128().unwrap_optimized());
    burn_shares(&e, c_sub(&e, pool_amount_in.clone(), exit_fee.clone()).unwrap_optimized().to_i128().unwrap_optimized());
    let factory = read_factory(&e);
    push_shares(&e, factory, exit_fee.to_i128().unwrap_optimized());
    push_underlying(&e, &token_out, user, token_amount_out);

    record_map.set(token_out, out_record);
    write_record(&e, record_map);

    pool_amount_in.to_i128().unwrap_optimized()
}
