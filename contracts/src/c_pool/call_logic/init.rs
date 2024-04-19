use soroban_sdk::{
    assert_with_error, token::TokenClient, unwrap::UnwrapOptimized, Address, Env, Map, String, Vec,
};
use soroban_token_sdk::metadata::TokenMetadata;

use crate::{
    c_consts::{INIT_POOL_SUPPLY, MAX_FEE, MAX_WEIGHT, MIN_BALANCE, MIN_FEE, MIN_WEIGHT, STROOP},
    c_pool::{
        error::Error,
        metadata::{write_controller, write_metadata, write_record, write_swap_fee, write_tokens},
        storage_types::{DataKey, Record},
        token_utility::mint_shares,
    },
};

pub fn execute_init(
    e: &Env,
    controller: Address,
    tokens: Vec<Address>,
    weights: Vec<i128>,
    balances: Vec<i128>,
    swap_fee: i128,
) {
    assert_with_error!(
        &e,
        !e.storage().instance().has(&DataKey::Controller),
        Error::AlreadyInitialized
    );

    // valiate and store the records of the tokens
    assert_with_error!(&e, tokens.len() >= 2, Error::ErrMinTokens);
    assert_with_error!(&e, tokens.len() <= 8, Error::ErrMaxTokens);
    assert_with_error!(
        &e,
        weights.len() == tokens.len() && tokens.len() == balances.len(),
        Error::ErrInvalidVectorLen
    );
    assert_with_error!(
        &e,
        swap_fee >= MIN_FEE && swap_fee <= MAX_FEE,
        Error::ErrSwapFee
    );

    let mut records = Map::<Address, Record>::new(&e);
    let mut total_weight: i128 = 0;
    for i in 0..tokens.len() {
        let token = tokens.get(i).unwrap_optimized();
        let weight = weights.get(i).unwrap_optimized();
        let balance = balances.get(i).unwrap_optimized();

        assert_with_error!(&e, !records.contains_key(token.clone()), Error::ErrIsBound);

        assert_with_error!(&e, weight >= MIN_WEIGHT, Error::ErrMinWeight);
        assert_with_error!(&e, weight <= MAX_WEIGHT, Error::ErrMaxWeight);
        assert_with_error!(&e, balance >= MIN_BALANCE, Error::ErrInsufficientBalance);

        let token_client = TokenClient::new(&e, &token);
        let decimals = token_client.decimals();
        assert_with_error!(&e, decimals <= 18, Error::ErrTokenInvalid);
        let scalar = 10i128.pow(18 - decimals);

        total_weight += weight;

        // transfer starting balance to the pool
        token_client.transfer(&controller, &e.current_contract_address(), &balance);

        let record = Record {
            balance,
            weight,
            scalar,
            index: i,
        };
        records.set(token.clone(), record);
    }
    assert_with_error!(&e, total_weight == STROOP, Error::ErrTotalWeight);
    mint_shares(&e, &controller, INIT_POOL_SUPPLY);
    write_swap_fee(&e, swap_fee);

    write_record(e, records);
    write_tokens(e, tokens);

    // Name of the LP Token
    let name = String::from_str(&e, "Comet Pool Token");
    // Symbol of the LP Token
    let symbol = String::from_str(&e, "CPAL");
    write_metadata(
        &e,
        TokenMetadata {
            name,
            symbol,
            decimal: 7u32,
        },
    );

    // Store the Controller Address (Pool Admin)
    write_controller(&e, controller);
}
