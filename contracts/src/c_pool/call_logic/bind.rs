use soroban_sdk::{
    assert_with_error, panic_with_error, token::TokenClient, unwrap::UnwrapOptimized, Address, Env,
    Map,
};

use crate::{
    c_consts::{EXIT_FEE, MAX_BOUND_TOKENS, MAX_TOTAL_WEIGHT, MAX_WEIGHT, MIN_BALANCE, MIN_WEIGHT},
    c_num::{c_add, c_mul, c_sub},
    c_pool::{
        error::Error,
        metadata::{
            read_factory, read_finalize, read_record, read_tokens,
            read_total_weight, write_record, write_tokens, write_total_weight,
        },
        storage_types::Record,
        token_utility::{pull_underlying, push_underlying},
    },
};

// Binds tokens to the Pool
pub fn execute_bind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address) {
    assert_with_error!(&e, denorm >= 0, Error::ErrNegative);
    assert_with_error!(&e, balance >= 0, Error::ErrNegative);
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);

    let index = read_tokens(&e).len();
    assert_with_error!(&e, index < MAX_BOUND_TOKENS, Error::ErrMaxTokens);

    let mut tokens_arr = read_tokens(&e);
    let mut record_map = read_record(&e);
    if record_map.contains_key(token.clone()) {
        let record = record_map.get(token.clone()).unwrap_optimized();
        assert_with_error!(&e, record.bound == false, Error::ErrIsBound);
    }

    let decimals = TokenClient::new(&e, &token).decimals();
    assert_with_error!(&e, decimals <= 18, Error::ErrTokenInvalid);
    let scalar = 10i128.pow(18 - decimals);

    let record = Record {
        balance: 0,
        denorm: 0,
        scalar,
        index,
        bound: true,
    };
    record_map.set(token.clone(), record);
    write_record(&e, record_map);
    tokens_arr.push_back(token.clone());
    write_tokens(&e, tokens_arr);
    execute_rebind(e, token, balance, denorm, admin);
}

// If you you want to adjust values of the token which was already called using bind
pub fn execute_rebind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address) {
    assert_with_error!(&e, denorm >= 0, Error::ErrNegative);
    assert_with_error!(&e, balance >= 0, Error::ErrNegative);
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);

    assert_with_error!(&e, denorm >= MIN_WEIGHT, Error::ErrMinWeight);
    assert_with_error!(&e, denorm <= MAX_WEIGHT, Error::ErrMaxWeight);
    assert_with_error!(&e, balance >= MIN_BALANCE, Error::ErrMinBalance);

    let mut record_map: Map<Address, Record> = read_record(&e);
    let mut record = record_map
        .get(token.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, record.bound, Error::ErrNotBound);
    let old_weight = record.denorm;
    let mut total_weight = read_total_weight(&e);

    #[allow(clippy::comparison_chain)]
    if denorm > old_weight {
        total_weight = c_add(
            total_weight,
            c_sub(denorm, old_weight).unwrap_optimized(),
        )
        .unwrap_optimized();
        write_total_weight(&e, total_weight);
        if total_weight > MAX_TOTAL_WEIGHT {
            panic_with_error!(&e, Error::ErrMaxTotalWeight);
        }
    } else if denorm < old_weight {
        total_weight = c_sub(
            total_weight,
            c_sub(old_weight, denorm).unwrap_optimized(),
        )
        .unwrap_optimized();
        write_total_weight(&e, total_weight);
    }

    record.denorm = denorm;

    let old_balance = record.balance;
    record.balance = balance;

    #[allow(clippy::comparison_chain)]
    if balance > old_balance {
        pull_underlying(
            &e,
            &token,
            admin,
            c_sub(balance, old_balance).unwrap_optimized(),
            balance,
        );
    } else if balance < old_balance {
        let token_balance_withdrawn = c_sub(old_balance, balance).unwrap_optimized();
        let token_exit_fee = c_mul(token_balance_withdrawn, EXIT_FEE).unwrap_optimized();
        push_underlying(
            &e,
            &token,
            admin,
            c_sub(token_balance_withdrawn, token_exit_fee).unwrap_optimized(),
        );
        let factory = read_factory(&e);
        push_underlying(&e, &token, factory, token_exit_fee)
    }

    record_map.set(token, record);
    write_record(&e, record_map);
}

// Removes a specific token from the Liquidity Pool
pub fn execute_unbind(e: Env, token: Address, user: Address) {
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);

    let mut record_map: Map<Address, Record> = read_record(&e);
    let record = record_map
        .get(token.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, record.bound, Error::ErrNotBound);

    let token_balance = record.balance;
    let token_exit_fee = c_mul(token_balance, EXIT_FEE).unwrap_optimized();
    let curr_weight = read_total_weight(&e);
    write_total_weight(&e, c_sub(curr_weight, record.denorm).unwrap_optimized());
    let index = record.index;
    let mut tokens = read_tokens(&e);
    let last = tokens.len() - 1;
    let last_token = tokens.get(last).unwrap_optimized();
    tokens.set(index, last_token.clone());
    tokens.pop_back();
    write_tokens(&e, tokens);
    let mut record_current = record_map.get(last_token.clone()).unwrap_optimized();
    record_current.index = index;
    record_map.set(last_token, record_current);
    record_map.remove(token.clone());

    write_record(&e, record_map);

    push_underlying(
        &e,
        &token,
        user,
        c_sub(token_balance, token_exit_fee).unwrap_optimized(),
    );
    let factory = read_factory(&e);
    push_underlying(&e, &token, factory, token_exit_fee);
}
