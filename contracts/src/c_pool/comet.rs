//! Liquidity Pool and Token Implementation
use super::{
    admin::{check_admin, has_administrator, write_administrator},
    allowance::{read_allowance, spend_allowance, write_allowance},
    balance::{is_authorized, read_balance, receive_balance, spend_balance, write_authorization},
    events::{
        burn_event, clawback_event, decr_allow_event, incr_allow_event, mint_event,
        set_admin_event, set_auth_event, transfer_event,
    },
    metadata::{read_decimal, read_name, read_symbol, write_decimal, write_name, write_symbol},
};
use super::{
    metadata::{
        get_token_share, get_total_shares, put_total_shares, read_factory, read_record,
        read_swap_fee, read_tokens, write_record, write_tokens,
    },
    storage_types::{DataKey, Record, BALANCE_BUMP_AMOUNT, SHARED_BUMP_AMOUNT},
    token_utility::{self, check_nonnegative_amount},
};

use crate::{
    c_consts::{
        EXIT_FEE, INIT_POOL_SUPPLY, MAX_BOUND_TOKENS, MAX_FEE, MAX_IN_RATIO, MAX_OUT_RATIO,
        MAX_WEIGHT, MIN_BALANCE, MIN_BOUND_TOKENS, MIN_FEE, MIN_WEIGHT, TOTAL_WEIGHT,
    },
    c_math::{
        self, calc_lp_token_amount_given_token_deposits_in,
        calc_lp_token_amount_given_token_withdrawal_amount, calc_spot_price,
        calc_token_deposits_in_given_lp_token_amount, calc_token_in_given_token_out,
        calc_token_out_given_token_in, calc_token_withdrawal_amount_given_lp_token_amount,
    },
    c_num::{c_add, c_div, c_mul, c_sub},
    c_pool::{
        comet,
        error::Error,
        events::{ExitEvent, JoinEvent, SwapEvent},
        metadata::{put_token_share, write_factory, write_swap_fee},
        token_utility::{
            burn_shares, mint_shares, pull_shares, pull_underlying, push_shares, push_underlying,
        },
    },
};
use soroban_sdk::token::Client;
use soroban_sdk::{
    assert_with_error, contract, contractimpl, log, panic_with_error, symbol_short, token,
    unwrap::UnwrapOptimized, vec, xdr::SurveyMessageResponseType, Address, Bytes, BytesN, Env, Map,
    Symbol, Vec,
};

#[contract]
pub struct CometPoolContract;

pub trait CometPoolTrait {
    fn initialize(e: Env, admin: Address, decimal: u32, name: Bytes, symbol: Bytes);

    fn allowance(e: Env, from: Address, spender: Address) -> i128;

    fn incr_allow(e: Env, from: Address, spender: Address, amount: i128);

    fn decr_allow(e: Env, from: Address, spender: Address, amount: i128);

    fn balance(e: Env, id: Address) -> i128;

    fn spendable(e: Env, id: Address) -> i128;

    fn authorized(e: Env, id: Address) -> bool;

    fn xfer(e: Env, from: Address, to: Address, amount: i128);

    fn xfer_from(e: Env, spender: Address, from: Address, to: Address, amount: i128);

    fn burn(e: Env, from: Address, amount: i128);

    fn burn_from(e: Env, spender: Address, from: Address, amount: i128);

    fn clawback(e: Env, admin: Address, from: Address, amount: i128);

    fn set_auth(e: Env, admin: Address, id: Address, authorize: bool);

    fn mint(e: Env, admin: Address, to: Address, amount: i128);

    fn set_admin(e: Env, admin: Address, new_admin: Address);

    fn decimals(e: Env) -> u32;

    fn name(e: Env) -> Bytes;

    fn symbol(e: Env) -> Bytes;

    fn get_total_supply(e: Env) -> i128;

    fn get_num_tokens(e: Env) -> u32;

    fn get_current_tokens(e: Env) -> Vec<Address>;

    fn get_balance(e: Env, token: Address) -> i128;

    fn get_denormalized_weight(e: Env, token: Address) -> i128;

    fn get_normalized_weight(e: Env, token: Address) -> i128;

    fn get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128;

    fn get_swap_fee(e: Env) -> i128;

    fn share_id(e: Env) -> Address;

    fn get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128;

    fn init(
        e: Env,
        factory: Address,
        swap_fee: i128,
        token: Vec<Address>,
        balance: Vec<i128>,
        denorm: Vec<i128>,
        from: Address,
    );

    fn gulp(e: Env, token: Address);

    fn join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address);

    fn exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address);

    fn swap_exact_amount_in(
        e: Env,
        token_in: Address,
        token_amount_in: i128,
        token_out: Address,
        min_amount_out: i128,
        max_price: i128,
        user: Address,
    ) -> (i128, i128);

    fn swap_exact_amount_out(
        e: Env,
        token_in: Address,
        max_amount_in: i128,
        token_out: Address,
        token_amount_out: i128,
        max_price: i128,
        user: Address,
    ) -> (i128, i128);

    fn dep_lp_tokn_amt_out_get_tokn_in(
        e: Env,
        token_in: Address,
        pool_amount_out: i128,
        max_amount_in: i128,
        user: Address,
    ) -> i128;

    fn dep_tokn_amt_in_get_lp_tokns_out(
        e: Env,
        token_in: Address,
        token_amount_in: i128,
        min_pool_amount_out: i128,
        user: Address,
    ) -> i128;

    fn wdr_tokn_amt_in_get_lp_tokns_out(
        e: Env,
        token_out: Address,
        pool_amount_in: i128,
        min_amount_out: i128,
        user: Address,
    ) -> i128;

    fn wdr_tokn_amt_out_get_lp_tokns_in(
        e: Env,
        token_out: Address,
        token_amount_out: i128,
        max_pool_amount_in: i128,
        user: Address,
    ) -> i128;
}

#[contractimpl]
impl CometPoolTrait for CometPoolContract {
    // Initialize the Pool and the LP Token
    fn init(
        e: Env,
        factory: Address,
        swap_fee: i128,
        token: Vec<Address>,
        balance: Vec<i128>,
        denorm: Vec<i128>,
        from: Address,
    ) {
        // Check if the Contract Storage is already initialized
        assert_with_error!(
            &e,
            !e.storage().instance().has(&DataKey::Factory),
            Error::AlreadyInitialized
        );

        // Store the factory Address
        write_factory(&e, factory);

        // Get the Current Contract Address
        let val: &Address = &e.current_contract_address();

        // Name of the LP Token
        let name = Bytes::from_slice(&e, b"Comet Pool Token");
        // Symbol of the LP Token
        let symbol = Bytes::from_slice(&e, b"CPAL");

        // Current Contract is the LP Token as well
        put_token_share(&e, val.clone());

        // Set the Total Supply of the LP Token as 0
        put_total_shares(&e, 0);

        // Store the Swap Fee
        if swap_fee < MIN_FEE || swap_fee > MAX_FEE {
            assert_with_error!(
                &e,
                !e.storage().instance().has(&DataKey::Factory),
                Error::ErrMinFee
            );
        }
        write_swap_fee(&e, swap_fee);

        // Bind tokens
        assert_with_error!(
            &e,
            read_tokens(&e).len() >= MIN_BOUND_TOKENS,
            Error::ErrMinTokens
        );
        bundle_bind(
            e.clone(),
            token.clone(),
            balance.clone(),
            denorm.clone(),
            from.clone(),
        );

        // Initialize the LP Token
        Self::initialize(e.clone(), val.clone(), 7u32, name, symbol);

        //mint initial shares
        mint_shares(e, from, INIT_POOL_SUPPLY);
    }

    // Absorbing tokens into the pool directly sent to the current contract
    fn gulp(e: Env, t: Address) {
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        let mut records = read_record(&e);

        let mut rec = records.get(t.clone()).unwrap_optimized();
        // log!(&e, "Earlier {}", rec.balance);
        rec.balance = token::Client::new(&e, &t).balance(&e.current_contract_address());
        // log!(&e, "Later {}", rec.balance);
        records.set(t, rec);
        write_record(&e, records);
    }

    // Helps a users join the pool
    fn join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address) {
        assert_with_error!(&e, pool_amount_out >= 0, Error::ErrNegative);

        user.require_auth();

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
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
                .publish((symbol_short!("LOG"), symbol_short!("JOIN")), event);
            pull_underlying(&e, &t, user.clone(), token_amount_in);
        }

        write_record(&e, records);
        mint_shares(e, user, pool_amount_out);
    }

    // Helps a user exit the pool
    fn exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
        assert_with_error!(&e, pool_amount_in >= 0, Error::ErrNegative);

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        user.require_auth();
        let pool_total = get_total_shares(&e);
        let exit_fee = c_mul(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();
        let pai_after_exit_fee = c_sub(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();
        let ratio: i128 = c_div(&e, pai_after_exit_fee, pool_total).unwrap_optimized();
        assert_with_error!(&e, ratio != 0, Error::ErrMathApprox);
        pull_shares(&e, user.clone(), pool_amount_in);
        let share_contract_id = get_token_share(&e);
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
                .publish((symbol_short!("LOG"), symbol_short!("EXIT")), event);
            push_underlying(&e, &t, user.clone(), token_amount_out)
        }

        write_record(&e, records);
    }

    // User wants to swap X amount of Token A
    // for Y amount of Token B
    fn swap_exact_amount_in(
        e: Env,
        token_in: Address,
        token_amount_in: i128,
        token_out: Address,
        min_amount_out: i128,
        max_price: i128,
        user: Address,
    ) -> (i128, i128) {
        assert_with_error!(&e, token_amount_in >= 0, Error::ErrNegative);
        assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);
        assert_with_error!(&e, max_price >= 0, Error::ErrNegative);

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        user.require_auth();
        let mut in_record = read_record(&e).get(token_in.clone()).unwrap_optimized();
        let mut out_record = read_record(&e).get(token_out.clone()).unwrap_optimized();
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
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("SWAP")), event);

        pull_underlying(&e, &token_in, user.clone(), token_amount_in);
        push_underlying(&e, &token_out, user, token_amount_out);

        let mut record_map = read_record(&e);
        record_map.set(token_in, in_record);
        record_map.set(token_out, out_record);

        write_record(&e, record_map);

        (token_amount_out, spot_price_after)
    }

    // User wants to get Y amount of Token B,
    // he has X amount of Token A
    fn swap_exact_amount_out(
        e: Env,
        token_in: Address,
        max_amount_in: i128,
        token_out: Address,
        token_amount_out: i128,
        max_price: i128,
        user: Address,
    ) -> (i128, i128) {
        assert_with_error!(&e, token_amount_out >= 0, Error::ErrNegative);
        assert_with_error!(&e, max_amount_in >= 0, Error::ErrNegative);
        assert_with_error!(&e, max_price >= 0, Error::ErrNegative);

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        user.require_auth();
        let mut in_record = read_record(&e).get(token_in.clone()).unwrap_optimized();
        let mut out_record = read_record(&e).get(token_out.clone()).unwrap_optimized();
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
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("SWAP")), event);

        pull_underlying(&e, &token_in, user.clone(), token_amount_in);
        push_underlying(&e, &token_out, user, token_amount_out);

        let mut record_map = read_record(&e);
        record_map.set(token_in, in_record);
        record_map.set(token_out, out_record);

        write_record(&e, record_map);

        (token_amount_in, spot_price_after)
    }

    // Deposit X amount of Token A to get LP Token
    // Function Mints the LP Tokens to the user's wallet
    fn dep_tokn_amt_in_get_lp_tokns_out(
        e: Env,
        token_in: Address,
        token_amount_in: i128,
        min_pool_amount_out: i128,
        user: Address,
    ) -> i128 {
        assert_with_error!(&e, token_amount_in >= 0, Error::ErrNegative);
        assert_with_error!(&e, min_pool_amount_out >= 0, Error::ErrNegative);

        assert_with_error!(
            &e,
            token_amount_in
                <= c_mul(
                    &e,
                    read_record(&e)
                        .get(token_in.clone())
                        .unwrap_optimized()
                        .balance,
                    MAX_IN_RATIO
                )
                .unwrap_optimized(),
            Error::ErrMaxInRatio
        );

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        let mut in_record = read_record(&e).get(token_in.clone()).unwrap_optimized();
        let pool_amount_out = calc_lp_token_amount_given_token_deposits_in(
            &e,
            in_record.balance,
            in_record.denorm,
            get_total_shares(&e),
            TOTAL_WEIGHT,
            token_amount_in,
            read_swap_fee(&e),
        );
        assert_with_error!(
            &e,
            pool_amount_out >= min_pool_amount_out,
            Error::ErrLimitOut
        );
        in_record.balance = c_add(&e, in_record.balance, token_amount_in).unwrap_optimized();

        let mut record_map = read_record(&e);
        record_map.set(token_in.clone(), in_record);
        write_record(&e, record_map);

        let event: JoinEvent = JoinEvent {
            caller: user.clone(),
            token_in: token_in.clone(),
            token_amount_in,
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("JOIN")), event);

        pull_underlying(&e, &token_in, user.clone(), token_amount_in);
        mint_shares(e, user, pool_amount_out);

        pool_amount_out
    }

    // To get Y amount of LP tokens, how much of token will be required
    fn dep_lp_tokn_amt_out_get_tokn_in(
        e: Env,
        token_in: Address,
        pool_amount_out: i128,
        max_amount_in: i128,
        user: Address,
    ) -> i128 {
        assert_with_error!(&e, pool_amount_out >= 0, Error::ErrNegative);
        assert_with_error!(&e, max_amount_in >= 0, Error::ErrNegative);

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        let mut in_record: Record = read_record(&e).get(token_in.clone()).unwrap_optimized();

        let token_amount_in = calc_token_deposits_in_given_lp_token_amount(
            &e,
            in_record.balance,
            in_record.denorm,
            get_total_shares(&e),
            TOTAL_WEIGHT,
            pool_amount_out,
            read_swap_fee(&e),
        );
        assert_with_error!(&e, token_amount_in != 0, Error::ErrMathApprox);
        assert_with_error!(&e, token_amount_in <= max_amount_in, Error::ErrLimitIn);
        assert_with_error!(
            &e,
            token_amount_in
                <= c_mul(
                    &e,
                    read_record(&e)
                        .get(token_in.clone())
                        .unwrap_optimized()
                        .balance,
                    MAX_IN_RATIO
                )
                .unwrap_optimized(),
            Error::ErrMaxInRatio
        );
        in_record.balance = c_add(&e, in_record.balance, token_amount_in).unwrap_optimized();

        let mut record_map = read_record(&e);
        record_map.set(token_in.clone(), in_record);
        write_record(&e, record_map);

        let event: JoinEvent = JoinEvent {
            caller: user.clone(),
            token_in: token_in.clone(),
            token_amount_in,
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("JOIN")), event);

        pull_underlying(&e, &token_in, user.clone(), token_amount_in);
        mint_shares(e, user, pool_amount_out);

        token_amount_in
    }

    // Burns LP tokens and gives back the deposit tokens
    // Given: Y amount of Pool Token
    // Result: X Amount of Token A
    fn wdr_tokn_amt_in_get_lp_tokns_out(
        e: Env,
        token_out: Address,
        pool_amount_in: i128,
        min_amount_out: i128,
        user: Address,
    ) -> i128 {
        assert_with_error!(&e, pool_amount_in >= 0, Error::ErrNegative);
        assert_with_error!(&e, min_amount_out >= 0, Error::ErrNegative);

        user.require_auth();

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        let mut out_record: Record = read_record(&e).get(token_out.clone()).unwrap_optimized();

        let token_amount_out = calc_token_withdrawal_amount_given_lp_token_amount(
            &e,
            out_record.balance,
            out_record.denorm,
            get_total_shares(&e),
            TOTAL_WEIGHT,
            pool_amount_in,
            read_swap_fee(&e),
        );

        assert_with_error!(&e, token_amount_out >= min_amount_out, Error::ErrLimitOut);
        assert_with_error!(
            &e,
            token_amount_out
                <= c_mul(
                    &e,
                    read_record(&e)
                        .get(token_out.clone())
                        .unwrap_optimized()
                        .balance,
                    MAX_OUT_RATIO
                )
                .unwrap_optimized(),
            Error::ErrMaxOutRatio
        );
        out_record.balance = c_sub(&e, out_record.balance, token_amount_out).unwrap_optimized();
        let exit_fee = c_mul(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();

        let event: ExitEvent = ExitEvent {
            caller: user.clone(),
            token_out: token_out.clone(),
            token_amount_out,
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("EXIT")), event);

        pull_shares(&e, user.clone(), pool_amount_in);
        burn_shares(&e, c_sub(&e, pool_amount_in, EXIT_FEE).unwrap_optimized());
        let factory = read_factory(&e);
        push_shares(&e, factory, EXIT_FEE);
        push_underlying(&e, &token_out, user, token_amount_out);

        let mut record_map = read_record(&e);
        record_map.set(token_out, out_record);
        write_record(&e, record_map);

        token_amount_out
    }

    // Burns LP tokens and gives back the deposit tokens
    // Given: X amount of Token A
    // Result: Y amount of Pool Token
    fn wdr_tokn_amt_out_get_lp_tokns_in(
        e: Env,
        token_out: Address,
        token_amount_out: i128,
        max_pool_amount_in: i128,
        user: Address,
    ) -> i128 {
        user.require_auth();

        assert_with_error!(
            &e,
            token_amount_out
                <= c_mul(
                    &e,
                    read_record(&e)
                        .get(token_out.clone())
                        .unwrap_optimized()
                        .balance,
                    MAX_OUT_RATIO
                )
                .unwrap_optimized(),
            Error::ErrMaxOutRatio
        );

        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        let mut out_record: Record = read_record(&e).get(token_out.clone()).unwrap_optimized();
        let pool_amount_in = calc_lp_token_amount_given_token_withdrawal_amount(
            &e,
            out_record.balance,
            out_record.denorm,
            get_total_shares(&e),
            TOTAL_WEIGHT,
            token_amount_out,
            read_swap_fee(&e),
        );

        assert_with_error!(&e, pool_amount_in != 0, Error::ErrMathApprox);
        assert_with_error!(&e, pool_amount_in <= max_pool_amount_in, Error::ErrLimitIn);
        out_record.balance = c_sub(&e, out_record.balance, token_amount_out).unwrap_optimized();
        let exit_fee = c_mul(&e, pool_amount_in, EXIT_FEE).unwrap_optimized();
        let event: ExitEvent = ExitEvent {
            caller: user.clone(),
            token_out: token_out.clone(),
            token_amount_out,
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("EXIT")), event);

        pull_shares(&e, user.clone(), pool_amount_in);
        burn_shares(&e, c_sub(&e, pool_amount_in, EXIT_FEE).unwrap_optimized());
        let factory = read_factory(&e);
        push_shares(&e, factory, EXIT_FEE);
        push_underlying(&e, &token_out, user, token_amount_out);

        pool_amount_in
    }

    // Get the Controller Address
    fn get_total_supply(e: Env) -> i128 {
        get_total_shares(&e)
    }

    // Get the number of tokens in the pool
    fn get_num_tokens(e: Env) -> u32 {
        let token_vec = read_tokens(&e);
        token_vec.len()
    }

    // Get the Current Tokens in the Pool
    fn get_current_tokens(e: Env) -> Vec<Address> {
        read_tokens(&e)
    }

    // Get the balance of the Token
    fn get_balance(e: Env, token: Address) -> i128 {
        let val = read_record(&e).get(token).unwrap_optimized();
        assert_with_error!(&e, val.bound, Error::ErrNotBound);
        val.balance
    }

    // Get the denormalized weight of the token
    fn get_denormalized_weight(e: Env, token: Address) -> i128 {
        let val = read_record(&e).get(token).unwrap_optimized();
        val.denorm
    }

    // Get the normalized weight of the token
    fn get_normalized_weight(e: Env, token: Address) -> i128 {
        let val = read_record(&e).get(token).unwrap_optimized();
        c_div(&e, val.denorm, TOTAL_WEIGHT).unwrap_optimized()
    }

    // Calculate the spot considering the swap fee
    fn get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
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
    fn get_swap_fee(e: Env) -> i128 {
        read_swap_fee(&e)
    }

    // Get the spot price without considering the swap fee
    fn get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
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
    fn share_id(e: Env) -> Address {
        get_token_share(&e)
    }

    // Initialize the LP Token
    fn initialize(e: Env, admin: Address, decimal: u32, name: Bytes, symbol: Bytes) {
        if has_administrator(&e) {
            panic!("already initialized")
        }
        write_administrator(&e, &admin);

        write_decimal(&e, u8::try_from(decimal).expect("Decimal must fit in a u8"));
        write_name(&e, name);
        write_symbol(&e, symbol);
    }

    // TODO: Update allowance, incr_allow, and decr_allow to new token interface
    // Check the allowance of the spender approved by the 'from' address
    fn allowance(e: Env, from: Address, spender: Address) -> i128 {
        read_allowance(&e, from, spender).amount
    }

    // Increment the allowance for the spender approved by the 'from' address
    fn incr_allow(e: Env, from: Address, spender: Address, amount: i128) {
        from.require_auth();
        check_nonnegative_amount(&e, amount);
        let allowance = read_allowance(&e, from.clone(), spender.clone()).amount;
        let new_allowance = allowance
            .checked_add(amount)
            .expect("Updated allowance doesn't fit in an i128");

        write_allowance(
            &e,
            from.clone(),
            spender.clone(),
            new_allowance,
            BALANCE_BUMP_AMOUNT,
        );
        incr_allow_event(&e, from, spender, amount);
    }

    // Increment the allowance for the spender approved by the 'from' address
    fn decr_allow(e: Env, from: Address, spender: Address, amount: i128) {
        from.require_auth();

        check_nonnegative_amount(&e, amount);

        let allowance = read_allowance(&e, from.clone(), spender.clone());
        if amount >= allowance.amount {
            write_allowance(
                &e,
                from.clone(),
                spender.clone(),
                0,
                allowance.expiration_ledger,
            );
        } else {
            write_allowance(
                &e,
                from.clone(),
                spender.clone(),
                allowance.amount - amount,
                allowance.expiration_ledger,
            );
        }
        decr_allow_event(&e, from, spender, amount);
    }

    // Read the balanace of the user
    fn balance(e: Env, id: Address) -> i128 {
        read_balance(&e, id)
    }

    // Read the spendable balance of the user
    fn spendable(e: Env, id: Address) -> i128 {
        read_balance(&e, id)
    }

    // Return whether the address is authorized or deauthorized
    fn authorized(e: Env, id: Address) -> bool {
        is_authorized(&e, id)
    }

    // Tranfer the LP Token
    fn xfer(e: Env, from: Address, to: Address, amount: i128) {
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        from.require_auth();
        check_nonnegative_amount(&e, amount);
        spend_balance(&e, from.clone(), amount);
        receive_balance(&e, to.clone(), amount);
        transfer_event(&e, from, to, amount);
    }

    // Transfrom 'from' address to 'to' address by the 'spender' address
    fn xfer_from(e: Env, spender: Address, from: Address, to: Address, amount: i128) {
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        spender.require_auth();
        check_nonnegative_amount(&e, amount);
        spend_allowance(&e, from.clone(), spender, amount);
        spend_balance(&e, from.clone(), amount);
        receive_balance(&e, to.clone(), amount);
        transfer_event(&e, from, to, amount)
    }

    // Burn the LP Token from the wallet
    fn burn(e: Env, from: Address, amount: i128) {
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        from.require_auth();
        check_nonnegative_amount(&e, amount);
        spend_balance(&e, from.clone(), amount);
        burn_event(&e, from, amount);
    }

    // Helps the spender burn the LP Token from 'from' Address
    fn burn_from(e: Env, spender: Address, from: Address, amount: i128) {
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        spender.require_auth();
        check_nonnegative_amount(&e, amount);
        spend_allowance(&e, from.clone(), spender, amount);
        spend_balance(&e, from.clone(), amount);
        burn_event(&e, from, amount)
    }

    // Help Admin burns LP Tokens from Deauthorized balances
    fn clawback(e: Env, admin: Address, from: Address, amount: i128) {
        check_nonnegative_amount(&e, amount);
        check_admin(&e, &admin);
        admin.require_auth();
        spend_balance(&e, from.clone(), amount);
        clawback_event(&e, admin, from, amount);
    }

    // Set authorization for a address
    fn set_auth(e: Env, admin: Address, id: Address, authorize: bool) {
        check_admin(&e, &admin);
        admin.require_auth();
        write_authorization(&e, id.clone(), authorize);
        set_auth_event(&e, admin, id, authorize);
    }

    // Admin Mints the LP Token to the given address
    fn mint(e: Env, admin: Address, to: Address, amount: i128) {
        check_nonnegative_amount(&e, amount);
        check_admin(&e, &admin);
        admin.require_auth();
        receive_balance(&e, to.clone(), amount);
        mint_event(&e, admin, to, amount);
    }

    // Current Admin is able to set new Admin using this function
    fn set_admin(e: Env, admin: Address, new_admin: Address) {
        check_admin(&e, &admin);
        admin.require_auth();
        write_administrator(&e, &new_admin);
        set_admin_event(&e, admin, new_admin);
    }

    // Get the number of decimals of the LP Token
    fn decimals(e: Env) -> u32 {
        read_decimal(&e)
    }

    // Get the name of the LP Token
    fn name(e: Env) -> Bytes {
        read_name(&e)
    }

    // Get the symbol of the LP Token
    fn symbol(e: Env) -> Bytes {
        read_symbol(&e)
    }
}
fn bundle_bind(e: Env, token: Vec<Address>, balance: Vec<i128>, denorm: Vec<i128>, from: Address) {
    // token::Client::approve()
    let mut total_weight = 0;
    for i in 0..token.len() {
        // Client::new(e, token)
        token::Client::new(&e, &token.get(i).unwrap_optimized()).approve(
            &(from.clone()),
            &e.current_contract_address(),
            &balance.get(i).unwrap_optimized(),
            &1000,
        );
        total_weight = c_add(&e, total_weight, denorm.get(i).unwrap_optimized()).unwrap_optimized();
        if total_weight != TOTAL_WEIGHT {
            panic_with_error!(&e, Error::ErrMaxTotalWeight);
        }
        bind(
            e.clone(),
            token.get(i).unwrap_optimized(),
            balance.get(i).unwrap_optimized(),
            denorm.get(i).unwrap_optimized(),
            from.clone(),
        );
    }
}

// Binds tokens to the Pool
fn bind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address) {
    assert_with_error!(&e, denorm >= 0, Error::ErrNegative);
    assert_with_error!(&e, balance >= 0, Error::ErrNegative);
    assert_with_error!(&e, denorm >= MIN_WEIGHT, Error::ErrMinWeight);
    assert_with_error!(&e, denorm <= MAX_WEIGHT, Error::ErrMaxWeight);
    assert_with_error!(&e, balance >= MIN_BALANCE, Error::ErrMinBalance);
    assert_with_error!(
        &e,
        read_tokens(&e).len() < MAX_BOUND_TOKENS,
        Error::ErrMaxTokens
    );
    let key = DataKey::AllTokenVec;
    let key_rec = DataKey::AllRecordData;
    assert_with_error!(
        &e,
        read_record(&e).contains_key(token.clone()),
        Error::ErrIsBound
    );
    let index = read_tokens(&e).len();
    let mut tokens_arr = read_tokens(&e);
    let mut record_map = e
        .storage()
        .persistent()
        .get(&key_rec)
        .unwrap_or(Map::<Address, Record>::new(&e)); // if no members on vector

    let record = Record {
        bound: true,
        index,
        denorm,
        balance,
    };
    pull_underlying(&e, &token, admin, balance);
    record_map.set(token.clone(), record);
    write_record(&e, record_map);
    tokens_arr.push_back(token.clone());
    write_tokens(&e, tokens_arr);
}
