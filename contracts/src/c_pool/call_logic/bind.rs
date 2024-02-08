use soroban_sdk::{
    assert_with_error, panic_with_error, unwrap::UnwrapOptimized, Address, Env, Map, I256,
};

use crate::{
    c_num_256::{c_add, c_mul, c_sub},
    c_pool::{
        error::Error,
        metadata::{
            read_controller, read_factory, read_finalize, read_record, read_tokens,
            read_total_weight, write_record, write_tokens, write_total_weight,
        },
        storage_types::{DataKey, Record},
        token_utility::{pull_underlying, push_underlying},
    }, c_consts_256::{get_max_bound_tokens, get_min_weight, get_max_weight, get_min_balance, get_max_total_weight, get_exit_fee, get_bone},
};

// Binds tokens to the Pool
pub fn execute_bind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address) {
    assert_with_error!(&e, denorm >= 0, Error::ErrNegative);
    assert_with_error!(&e, balance >= 0, Error::ErrNegative);
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);

    let index = read_tokens(&e).len();
    assert_with_error!(&e, index < get_max_bound_tokens(&e), Error::ErrMaxTokens);

    let mut tokens_arr = read_tokens(&e);
    let mut record_map = read_record(&e);
    if record_map.contains_key(token.clone()) {
        let record = record_map.get(token.clone()).unwrap_optimized();
        assert_with_error!(&e, record.bound == false, Error::ErrIsBound);
    }

    let record = Record {
        bound: true,
        index,
        denorm: 0,
        balance: 0,
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
    let denorm_256 = I256::from_i128(&e, denorm).mul(&I256::from_i128(&e, 1e11 as i128));
    let balance_256 = I256::from_i128(&e, balance).mul(&I256::from_i128(&e, 1e11 as i128));
    assert_with_error!(&e,  denorm_256 >= get_min_weight(&e), Error::ErrMinWeight);
    assert_with_error!(&e, denorm_256 <=  get_max_weight(&e), Error::ErrMaxWeight);
    assert_with_error!(&e, balance_256 >= get_min_balance(&e), Error::ErrMinBalance);

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
            &e,
            I256::from_i128(&e, total_weight),
            c_sub(&e, I256::from_i128(&e, denorm), I256::from_i128(&e, old_weight)).unwrap_optimized(),
        )
        .unwrap_optimized().to_i128().unwrap();
        write_total_weight(&e, total_weight);
        if I256::from_i128(&e, total_weight) > get_max_total_weight(&e) {
            panic_with_error!(&e, Error::ErrMaxTotalWeight);
        }
    } else if denorm < old_weight {
        total_weight = c_sub(
            &e,
            I256::from_i128(&e, total_weight),
            c_sub(&e, I256::from_i128(&e, old_weight), I256::from_i128(&e, denorm)).unwrap_optimized(),
        )
        .unwrap_optimized().to_i128().unwrap();
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
            c_sub(&e, I256::from_i128(&e, balance), I256::from_i128(&e, old_balance)).unwrap_optimized().to_i128().unwrap(),
        );
    } else if balance < old_balance {
        let token_balance_withdrawn = c_sub(&e, I256::from_i128(&e, old_balance), I256::from_i128(&e, balance)).unwrap_optimized();
        let token_exit_fee = c_mul(&e, token_balance_withdrawn.clone(), get_exit_fee(&e)).unwrap_optimized();
        push_underlying(
            &e,
            &token,
            admin,
            c_sub(&e,token_balance_withdrawn, token_exit_fee.clone()).unwrap_optimized().to_i128().unwrap(),
        );
        let factory = read_factory(&e);
        push_underlying(&e, &token, factory, token_exit_fee.to_i128().unwrap())
    }

    record_map.set(token, record);
    write_record(&e, record_map);
}

// Removes a specific token from the Liquidity Pool
pub fn execute_unbind(e: Env, token: Address, user: Address) {
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);

    let mut record_map: Map<Address, Record> = read_record(&e);
    let mut record = record_map
        .get(token.clone())
        .unwrap_or_else(|| panic_with_error!(&e, Error::ErrNotBound));
    assert_with_error!(&e, record.bound, Error::ErrNotBound);

    let token_balance = record.balance;
    let token_exit_fee = c_mul(&e, I256::from_i128(&e, token_balance), get_exit_fee(&e)).unwrap_optimized();
    let curr_weight = read_total_weight(&e);
    write_total_weight(&e, c_sub(&e, I256::from_i128(&e, curr_weight), I256::from_i128(&e, record.denorm)).unwrap_optimized().to_i128().unwrap());
    let index = record.index;
    let mut tokens = read_tokens(&e);
    let last = tokens.len() - 1;
    let index_token = tokens.get(index).unwrap_optimized();
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
        c_sub(&e, I256::from_i128(&e,token_balance), token_exit_fee.clone()).unwrap_optimized().to_i128().unwrap(),
    );
    let factory = read_factory(&e);
    push_underlying(&e, &token, factory, token_exit_fee.to_i128().unwrap());
}
