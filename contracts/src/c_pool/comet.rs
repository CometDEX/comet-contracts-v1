//! Liquidity Pool and Token Implementation
use crate::c_pool::{
    allowance::{read_allowance, spend_allowance, write_allowance},
    balance::{read_balance, receive_balance, spend_balance},
    call_logic::{
        getter::{execute_get_spot_price, execute_get_spot_price_sans_fee},
        init::execute_init,
        pool::{
            execute_dep_lp_tokn_amt_out_get_tokn_in, execute_dep_tokn_amt_in_get_lp_tokns_out,
            execute_exit_pool, execute_gulp, execute_join_pool, execute_swap_exact_amount_in,
            execute_swap_exact_amount_out, execute_wdr_tokn_amt_in_get_lp_tokns_out,
            execute_wdr_tokn_amt_out_get_lp_tokns_in,
        },
    },
    metadata::{
        get_total_shares, read_controller, read_decimal, read_name, read_record, read_swap_fee,
        read_symbol, read_tokens,
    },
    storage_types::{SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD},
    token_utility::check_nonnegative_amount,
};
use soroban_sdk::{
    contract, contractimpl, token::TokenInterface, unwrap::UnwrapOptimized, Address, Env, String,
    Vec,
};
use soroban_token_sdk::TokenUtils;

use super::metadata::{put_total_shares, write_controller, write_freeze};

#[contract]
pub struct CometPoolContract;

#[contractimpl]
impl CometPoolContract {
    // Initialize the Pool and the LP Token
    pub fn init(
        e: Env,
        controller: Address,
        tokens: Vec<Address>,
        weights: Vec<i128>,
        balances: Vec<i128>,
        swap_fee: i128,
    ) {
        controller.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_init(&e, controller, tokens, weights, balances, swap_fee);
    }

    // Absorbing tokens into the pool directly sent to the current contract
    pub fn gulp(e: Env, t: Address) {
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_gulp(e, t);
    }

    // Helps a users join the pool
    pub fn join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address) {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

        execute_join_pool(e, pool_amount_out, max_amounts_in, user);
    }

    // Helps a user exit the pool
    pub fn exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_exit_pool(e, pool_amount_in, min_amounts_out, user);
    }

    // User wants to swap X amount of Token A
    // for Y amount of Token B
    pub fn swap_exact_amount_in(
        e: Env,
        token_in: Address,
        token_amount_in: i128,
        token_out: Address,
        min_amount_out: i128,
        max_price: i128,
        user: Address,
    ) -> (i128, i128) {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
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
    pub fn swap_exact_amount_out(
        e: Env,
        token_in: Address,
        max_amount_in: i128,
        token_out: Address,
        token_amount_out: i128,
        max_price: i128,
        user: Address,
    ) -> (i128, i128) {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
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
    pub fn dep_tokn_amt_in_get_lp_tokns_out(
        e: Env,
        token_in: Address,
        token_amount_in: i128,
        min_pool_amount_out: i128,
        user: Address,
    ) -> i128 {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_dep_tokn_amt_in_get_lp_tokns_out(
            e,
            token_in,
            token_amount_in,
            min_pool_amount_out,
            user,
        )
    }

    // To get Y amount of LP tokens, how much of token will be required
    pub fn dep_lp_tokn_amt_out_get_tokn_in(
        e: Env,
        token_in: Address,
        pool_amount_out: i128,
        max_amount_in: i128,
        user: Address,
    ) -> i128 {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_dep_lp_tokn_amt_out_get_tokn_in(e, token_in, pool_amount_out, max_amount_in, user)
    }

    // Burns LP tokens and gives back the deposit tokens
    // Given: Y amount of Pool Token
    // Result: X Amount of Token A
    pub fn wdr_tokn_amt_in_get_lp_tokns_out(
        e: Env,
        token_out: Address,
        pool_amount_in: i128,
        min_amount_out: i128,
        user: Address,
    ) -> i128 {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_wdr_tokn_amt_in_get_lp_tokns_out(e, token_out, pool_amount_in, min_amount_out, user)
    }

    // Burns LP tokens and gives back the deposit tokens
    // Given: X amount of Token A
    // Result: Y amount of Pool Token
    pub fn wdr_tokn_amt_out_get_lp_tokns_in(
        e: Env,
        token_out: Address,
        token_amount_out: i128,
        max_pool_amount_in: i128,
        user: Address,
    ) -> i128 {
        user.require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        execute_wdr_tokn_amt_out_get_lp_tokns_in(
            e,
            token_out,
            token_amount_out,
            max_pool_amount_in,
            user,
        )
    }

    // Sets the value of the controller address, only can be set by the current controller
    pub fn set_controller(e: Env, manager: Address) {
        read_controller(&e).require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        write_controller(&e, manager);
    }

    // Only Callable by the Pool Admin
    // Freezes Functions and only allows withdrawals
    pub fn set_freeze_status(e: Env, val: bool) {
        read_controller(&e).require_auth();
        e.storage()
            .instance()
            .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        write_freeze(&e, val);
    }

    // GETTER FUNCTIONS

    // Get the Controller Address
    pub fn get_total_supply(e: Env) -> i128 {
        get_total_shares(&e)
    }

    // Get the Controller Address
    pub fn get_controller(e: Env) -> Address {
        read_controller(&e)
    }

    // Get the Current Tokens in the Pool
    pub fn get_tokens(e: Env) -> Vec<Address> {
        read_tokens(&e)
    }

    // Get the balance of the Token
    pub fn get_balance(e: Env, token: Address) -> i128 {
        let val = read_record(&e).get(token).unwrap_optimized();
        val.balance
    }

    // Get the weight of the token in decimal form with 7 decimals
    pub fn get_normalized_weight(e: Env, token: Address) -> i128 {
        let val = read_record(&e).get(token).unwrap_optimized();
        val.weight
    }

    // Calculate the spot considering the swap fee
    pub fn get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
        execute_get_spot_price(e, token_in, token_out)
    }

    // Get the Swap Fee of the Contract
    pub fn get_swap_fee(e: Env) -> i128 {
        read_swap_fee(&e)
    }

    // Get the spot price without considering the swap fee
    pub fn get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
        execute_get_spot_price_sans_fee(e, token_in, token_out)
    }
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
