//! Liquidity Pool and Token Implementation
use crate::{
    c_consts::{
        EXIT_FEE, INIT_POOL_SUPPLY, MAX_BOUND_TOKENS, MAX_FEE, MAX_IN_RATIO, MAX_OUT_RATIO,
        MAX_TOTAL_WEIGHT, MAX_WEIGHT, MIN_BALANCE, MIN_BOUND_TOKENS, MIN_FEE, MIN_WEIGHT,
    },
    c_math::{
        self, calc_lp_token_amount_given_token_deposits_in,
        calc_lp_token_amount_given_token_withdrawal_amount, calc_spot_price,
        calc_token_deposits_in_given_lp_token_amount, calc_token_in_given_token_out,
        calc_token_out_given_token_in, calc_token_withdrawal_amount_given_lp_token_amount,
    },
    c_num::{c_add, c_div, c_mul, c_sub},
    c_pool::{
        allowance::{read_allowance, spend_allowance, write_allowance},
        balance::{read_balance, receive_balance, spend_balance},
        call_logic::{
            bind::{execute_bind, execute_rebind, execute_unbind},
            finalize::execute_finalize,
            getter::{
                execute_get_denormalized_weight, execute_get_normalized_weight,
                execute_get_spot_price, execute_get_spot_price_sans_fee,
            },
            init::execute_init,
            pool::{
                execute_dep_lp_tokn_amt_out_get_tokn_in, execute_dep_tokn_amt_in_get_lp_tokns_out,
                execute_exit_pool, execute_gulp, execute_join_pool, execute_swap_exact_amount_in,
                execute_swap_exact_amount_out, execute_wdr_tokn_amt_in_get_lp_tokns_out,
                execute_wdr_tokn_amt_out_get_lp_tokns_in,
            },
            setter::{
                execute_set_controller, execute_set_freeze_status, execute_set_public_swap,
                execute_set_swap_fee,
            },
        },
        error::Error,
        event,
        metadata::{
            get_total_shares, read_controller, read_decimal, read_finalize, read_name,
            read_public_swap, read_record, read_swap_fee, read_symbol, read_tokens,
            read_total_weight,
        },
        storage_types::{SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD},
        token_utility::check_nonnegative_amount,
    },
};
use soroban_sdk::{
    assert_with_error, contract, contractimpl, log, panic_with_error, symbol_short, token,
    unwrap::UnwrapOptimized, vec, Address, Bytes, BytesN, Env, Map, String, Symbol, Vec,
};
use soroban_token_sdk::metadata::TokenMetadata;
use soroban_token_sdk::TokenUtils;

use super::metadata::put_total_shares;

#[contract]
pub struct CometPoolContract;

pub trait CometPoolTrait {
    fn get_total_supply(e: Env) -> i128;

    fn get_tokens(e: Env) -> Vec<Address>;

    fn get_balance(e: Env, token: Address) -> i128;

    fn get_total_denormalized_weight(e: Env) -> i128;

    fn get_denormalized_weight(e: Env, token: Address) -> i128;

    fn get_normalized_weight(e: Env, token: Address) -> i128;

    fn get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128;

    fn get_swap_fee(e: Env) -> i128;

    fn is_bound(e: Env, t: Address) -> bool;

    fn is_public_swap(e: Env) -> bool;

    fn is_finalized(e: Env) -> bool;

    fn get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128;

    fn set_swap_fee(e: Env, fee: i128, caller: Address);

    fn set_controller(e: Env, caller: Address, manager: Address);

    fn set_public_swap(e: Env, caller: Address, val: bool);

    fn set_freeze_status(e: Env, caller: Address, val: bool);

    fn init(e: Env, factory: Address, controller: Address);

    fn bundle_bind(e: Env, token: Vec<Address>, balance: Vec<i128>, denorm: Vec<i128>);

    fn get_controller(e: Env) -> Address;

    fn bind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address);

    fn rebind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address);

    fn unbind(e: Env, token: Address, user: Address);

    fn finalize(e: Env);

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
    fn init(e: Env, factory: Address, controller: Address) {
        // Check if the Contract Storage is already initialized

        execute_init(e, factory, controller);
    }

    fn bundle_bind(e: Env, token: Vec<Address>, balance: Vec<i128>, denorm: Vec<i128>) {
        // token::Client::approve()
        let controller: Address = read_controller(&e);
        controller.require_auth();

        for i in 0..token.len() {
            execute_bind(
                e.clone(),
                token.get(i).unwrap_optimized(),
                balance.get(i).unwrap_optimized(),
                denorm.get(i).unwrap_optimized(),
                controller.clone(),
            );
        }
    }

    // Binds tokens to the Pool
    fn bind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address) {
        let controller = read_controller(&e);
        controller.require_auth();
        execute_bind(e, token, balance, denorm, admin);
    }

    // If you you want to adjust values of the token which was already called using bind
    fn rebind(e: Env, token: Address, balance: i128, denorm: i128, admin: Address) {
        let controller = read_controller(&e);
        controller.require_auth();
        execute_rebind(e, token, balance, denorm, admin);
    }

    // Removes a specific token from the Liquidity Pool
    fn unbind(e: Env, token: Address, user: Address) {
        let controller = read_controller(&e);
        assert_with_error!(&e, user == controller, Error::ErrNotController);
        controller.require_auth();
        execute_unbind(e, token, user);
    }

    // Finalizes the Pool
    // Set true for Public Swap
    // Mint Pool Tokens to the controller Address
    fn finalize(e: Env) {
        let controller = read_controller(&e);
        controller.require_auth();
        execute_finalize(e, controller);
    }

    // Absorbing tokens into the pool directly sent to the current contract
    fn gulp(e: Env, t: Address) {
        execute_gulp(e, t);
    }

    // Helps a users join the pool
    fn join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address) {
        user.require_auth();
        execute_join_pool(e, pool_amount_out, max_amounts_in, user);
    }

    // Helps a user exit the pool
    fn exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
        user.require_auth();
        execute_exit_pool(e, pool_amount_in, min_amounts_out, user);
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
        user.require_auth();

        execute_swap_exact_amount_in(
            e,
            token_in,
            token_amount_in,
            token_out,
            min_amount_out,
            max_price,
            user,
        )
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
        user.require_auth();
        execute_swap_exact_amount_out(
            e,
            token_in,
            max_amount_in,
            token_out,
            token_amount_out,
            max_price,
            user,
        )
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
        user.require_auth();

        execute_dep_tokn_amt_in_get_lp_tokns_out(
            e,
            token_in,
            token_amount_in,
            min_pool_amount_out,
            user,
        )
    }

    // To get Y amount of LP tokens, how much of token will be required
    fn dep_lp_tokn_amt_out_get_tokn_in(
        e: Env,
        token_in: Address,
        pool_amount_out: i128,
        max_amount_in: i128,
        user: Address,
    ) -> i128 {
        user.require_auth();

        execute_dep_lp_tokn_amt_out_get_tokn_in(e, token_in, pool_amount_out, max_amount_in, user)
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
        user.require_auth();

        execute_wdr_tokn_amt_in_get_lp_tokns_out(e, token_out, pool_amount_in, min_amount_out, user)
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
        execute_wdr_tokn_amt_out_get_lp_tokns_in(
            e,
            token_out,
            token_amount_out,
            max_pool_amount_in,
            user,
        )
    }

    // Sets the swap fee, can only be set by the controller (pool admin)
    fn set_swap_fee(e: Env, fee: i128, caller: Address) {
        assert_with_error!(&e, caller == read_controller(&e), Error::ErrNotController);
        caller.require_auth();
        execute_set_swap_fee(e, fee, caller);
    }

    // Sets the value of the controller address, only can be set by the current controller
    fn set_controller(e: Env, caller: Address, manager: Address) {
        assert_with_error!(&e, caller == read_controller(&e), Error::ErrNotController);
        caller.require_auth();
        execute_set_controller(e, caller, manager);
    }

    // Set the value of the Public Swap
    fn set_public_swap(e: Env, caller: Address, val: bool) {
        assert_with_error!(&e, caller == read_controller(&e), Error::ErrNotController);
        caller.require_auth();
        execute_set_public_swap(e, caller, val);
    }

    // Only Callable by the Pool Admin
    // Freezes Functions and only allows withdrawals
    fn set_freeze_status(e: Env, caller: Address, val: bool) {
        assert_with_error!(&e, caller == read_controller(&e), Error::ErrNotController);
        caller.require_auth();
        execute_set_freeze_status(e, caller, val);
    }

    // GETTER FUNCTIONS

    // Get the Controller Address
    fn get_total_supply(e: Env) -> i128 {
        get_total_shares(&e)
    }

    // Get the Controller Address
    fn get_controller(e: Env) -> Address {
        read_controller(&e)
    }

    // Get the total dernormalized weight
    fn get_total_denormalized_weight(e: Env) -> i128 {
        read_total_weight(&e)
    }

    // Get the Current Tokens in the Pool
    fn get_tokens(e: Env) -> Vec<Address> {
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
        execute_get_denormalized_weight(e, token)
    }

    // Get the normalized weight of the token
    fn get_normalized_weight(e: Env, token: Address) -> i128 {
        execute_get_normalized_weight(e, token)
    }

    // Calculate the spot considering the swap fee
    fn get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
        execute_get_spot_price(e, token_in, token_out)
    }

    // Get the Swap Fee of the Contract
    fn get_swap_fee(e: Env) -> i128 {
        read_swap_fee(&e)
    }

    // Get the spot price without considering the swap fee
    fn get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
        execute_get_spot_price_sans_fee(e, token_in, token_out)
    }

    // Check if the Pool can be used for swapping by normal users
    fn is_public_swap(e: Env) -> bool {
        read_public_swap(&e)
    }

    // Check if the Pool is finalized by the Controller
    fn is_finalized(e: Env) -> bool {
        read_finalize(&e)
    }

    // Check if the token Address is bound to the pool
    fn is_bound(e: Env, t: Address) -> bool {
        read_record(&e).get(t).unwrap_optimized().bound
    }
}

pub trait TokenInterface {
    /// Returns the allowance for `spender` to transfer from `from`.
    ///
    /// # Arguments
    ///
    /// - `from` - The address holding the balance of tokens to be drawn from.
    /// - `spender` - The address spending the tokens held by `from`.
    fn allowance(env: Env, from: Address, spender: Address) -> i128;

    /// Set the allowance by `amount` for `spender` to transfer/burn from
    /// `from`.
    ///
    /// # Arguments
    ///
    /// - `from` - The address holding the balance of tokens to be drawn from.
    /// - `spender` - The address being authorized to spend the tokens held by
    /// `from`.
    /// - `amount` - The tokens to be made available to `spender`.
    /// - `live_until_ledger` - The ledger number where this allowance expires.
    /// Cannot be less than the current ledger number unless the amount is being
    /// set to 0.  An expired entry (where live_until_ledger < the current
    /// ledger number) should be treated as a 0 amount allowance.
    ///
    /// # Events
    ///
    /// Emits an event with topics `["approve", from: Address,
    /// spender: Address], data = [amount: i128, live_until_ledger: u32]`
    ///
    /// Emits an event with:
    /// - topics - `["approve", from: Address, spender: Address]`
    /// - data - `[amount: i128, live_until_ledger: u32]`
    fn approve(env: Env, from: Address, spender: Address, amount: i128, live_until_ledger: u32);

    /// Returns the balance of `id`.
    ///
    /// # Arguments
    ///
    /// - `id` - The address for which a balance is being queried. If the
    /// address has no existing balance, returns 0.
    fn balance(env: Env, id: Address) -> i128;

    /// Transfer `amount` from `from` to `to`.
    ///
    /// # Arguments
    ///
    /// - `from` - The address holding the balance of tokens which will be
    /// withdrawn from.
    /// - `to` - The address which will receive the transferred tokens.
    /// - `amount` - The amount of tokens to be transferred.
    ///
    /// # Events
    ///
    /// Emits an event with:
    /// - topics - `["transfer", from: Address, to: Address]`
    /// - data - `[amount: i128]`
    fn transfer(env: Env, from: Address, to: Address, amount: i128);

    /// Transfer `amount` from `from` to `to`, consuming the allowance of
    /// `spender`. Authorized by spender (`spender.require_auth()`).
    ///
    /// # Arguments
    ///
    /// - `spender` - The address authorizing the transfer, and having its
    /// allowance consumed during the transfer.
    /// - `from` - The address holding the balance of tokens which will be
    /// withdrawn from.
    /// - `to` - The address which will receive the transferred tokens.
    /// - `amount` - The amount of tokens to be transferred.
    ///
    /// # Events
    ///
    /// Emits an event with:
    /// - topics - `["transfer", from: Address, to: Address]`
    /// - data - `[amount: i128]`
    fn transfer_from(env: Env, spender: Address, from: Address, to: Address, amount: i128);

    /// Burn `amount` from `from`.
    ///
    /// # Arguments
    ///
    /// - `from` - The address holding the balance of tokens which will be
    /// burned from.
    /// - `amount` - The amount of tokens to be burned.
    ///
    /// # Events
    ///
    /// Emits an event with:
    /// - topics - `["burn", from: Address]`
    /// - data - `[amount: i128]`
    fn burn(env: Env, from: Address, amount: i128);

    /// Burn `amount` from `from`, consuming the allowance of `spender`.
    ///
    /// # Arguments
    ///
    /// - `spender` - The address authorizing the burn, and having its allowance
    /// consumed during the burn.
    /// - `from` - The address holding the balance of tokens which will be
    /// burned from.
    /// - `amount` - The amount of tokens to be burned.
    ///
    /// # Events
    ///
    /// Emits an event with:
    /// - topics - `["burn", from: Address]`
    /// - data - `[amount: i128]`
    fn burn_from(env: Env, spender: Address, from: Address, amount: i128);

    /// Returns the number of decimals used to represent amounts of this token.
    fn decimals(env: Env) -> u32;

    /// Returns the name for this token.
    fn name(env: Env) -> String;

    /// Returns the symbol for this token.
    fn symbol(env: Env) -> String;
}

// SEP-0041 Token Implementation
#[contractimpl]
impl TokenInterface for CometPoolContract {
    fn allowance(e: Env, from: Address, spender: Address) -> i128 {
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        read_allowance(&e, from, spender).amount
    }

    fn approve(e: Env, from: Address, spender: Address, amount: i128, expiration_ledger: u32) {
        from.require_auth();

        check_nonnegative_amount(amount);

        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

        write_allowance(&e, from.clone(), spender.clone(), amount, expiration_ledger);

        TokenUtils::new(&e)
            .events()
            .approve(from, spender, amount, expiration_ledger);
    }

    fn balance(e: Env, id: Address) -> i128 {
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        read_balance(&e, id)
    }

    fn transfer(e: Env, from: Address, to: Address, amount: i128) {
        from.require_auth();

        check_nonnegative_amount(amount);

        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

        spend_balance(&e, from.clone(), amount);
        receive_balance(&e, to.clone(), amount);
        TokenUtils::new(&e).events().transfer(from, to, amount);
    }

    fn transfer_from(e: Env, spender: Address, from: Address, to: Address, amount: i128) {
        spender.require_auth();

        check_nonnegative_amount(amount);

        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

        spend_allowance(&e, from.clone(), spender, amount);
        spend_balance(&e, from.clone(), amount);
        receive_balance(&e, to.clone(), amount);
        TokenUtils::new(&e).events().transfer(from, to, amount)
    }

    fn burn(e: Env, from: Address, amount: i128) {
        from.require_auth();
        let total = get_total_shares(&e);
        check_nonnegative_amount(amount);

        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

        spend_balance(&e, from.clone(), amount);
        TokenUtils::new(&e).events().burn(from, amount);
        put_total_shares(&e, total - amount);
    }

    fn burn_from(e: Env, spender: Address, from: Address, amount: i128) {
        spender.require_auth();
        let total = get_total_shares(&e);
        check_nonnegative_amount(amount);

        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

        spend_allowance(&e, from.clone(), spender, amount);
        spend_balance(&e, from.clone(), amount);
        TokenUtils::new(&e).events().burn(from, amount);
        put_total_shares(&e, total - amount);

    }

    fn decimals(e: Env) -> u32 {
        read_decimal(&e)
    }

    fn name(e: Env) -> String {
        read_name(&e)
    }

    fn symbol(e: Env) -> String {
        read_symbol(&e)
    }
}
