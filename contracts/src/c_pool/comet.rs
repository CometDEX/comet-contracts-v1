//! Liquidity Pool and Token Implementation
use crate::c_pool::{
    allowance::{read_allowance, spend_allowance, write_allowance},
    balance::{read_balance, receive_balance, spend_balance},
    call_logic::{
        getter::{
            execute_get_balance, execute_get_normalized_weight, execute_get_spot_price,
            execute_get_spot_price_sans_fee,
        },
        init::execute_init,
        pool::{
            execute_dep_lp_tokn_amt_out_get_tokn_in, execute_dep_tokn_amt_in_get_lp_tokns_out,
            execute_exit_pool, execute_gulp, execute_join_pool, execute_swap_exact_amount_in,
            execute_swap_exact_amount_out, execute_wdr_tokn_amt_in_get_lp_tokns_out,
            execute_wdr_tokn_amt_out_get_lp_tokns_in,
        },
    },
    error::Error,
    metadata::{
        extend_pool_ttl, get_total_shares, read_controller, read_decimal, read_name, read_swap_fee,
        read_pending_controller, read_symbol, read_tokens, remove_pending_controller,
        write_pending_controller,
    },
    token_utility::{burn_shares_from, check_nonnegative_amount},
};
use soroban_sdk::{
    contract, contractimpl, panic_with_error, symbol_short, token::TokenInterface, Address, Env,
    MuxedAddress, String, Vec,
};
use soroban_token_sdk::events::{Approve, Transfer, TransferWithAmountOnly};

use super::metadata::{write_controller, write_freeze};

pub(crate) fn pending_controller_or_error(
    pending_controller: Option<Address>,
) -> Result<Address, Error> {
    pending_controller.ok_or(Error::ErrNoPendingController)
}

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
        execute_init(&e, controller, tokens, weights, balances, swap_fee);
        extend_pool_ttl(&e);
    }

    // Absorbing tokens into the pool directly sent to the current contract
    pub fn gulp(e: Env, t: Address) {
        extend_pool_ttl(&e);
        execute_gulp(e, t);
    }

    // Helps a users join the pool
    pub fn join_pool(e: Env, pool_amount_out: i128, max_amounts_in: Vec<i128>, user: Address) {
        user.require_auth();
        extend_pool_ttl(&e);

        execute_join_pool(e, pool_amount_out, max_amounts_in, user);
    }

    // Helps a user exit the pool
    pub fn exit_pool(e: Env, pool_amount_in: i128, min_amounts_out: Vec<i128>, user: Address) {
        user.require_auth();
        extend_pool_ttl(&e);
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
        extend_pool_ttl(&e);
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
        extend_pool_ttl(&e);
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
        extend_pool_ttl(&e);
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
        extend_pool_ttl(&e);
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
        extend_pool_ttl(&e);
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
        extend_pool_ttl(&e);
        execute_wdr_tokn_amt_out_get_lp_tokns_in(
            e,
            token_out,
            token_amount_out,
            max_pool_amount_in,
            user,
        )
    }

    // Proposes a new controller, replacing any existing proposal. Passing the current controller
    // cancels the pending transfer. The proposed controller must accept before the change applies.
    pub fn set_controller(e: Env, manager: Address) {
        let controller = read_controller(&e);
        controller.require_auth();
        extend_pool_ttl(&e);

        if manager == controller {
            remove_pending_controller(&e);
        } else {
            write_pending_controller(&e, manager.clone());
        }
        e.events().publish(
            (symbol_short!("POOL"), symbol_short!("set_ctrl"), controller),
            manager,
        );
    }

    // Accepts a pending controller transfer. Only the pending controller can authorize acceptance.
    pub fn accept_controller(e: Env) {
        extend_pool_ttl(&e);
        let new_controller = pending_controller_or_error(read_pending_controller(&e))
            .unwrap_or_else(|error| panic_with_error!(&e, error));
        new_controller.require_auth();

        let previous_controller = read_controller(&e);
        write_controller(&e, new_controller.clone());
        remove_pending_controller(&e);
        e.events().publish(
            (
                symbol_short!("POOL"),
                symbol_short!("acpt_ctrl"),
                previous_controller,
            ),
            new_controller,
        );
    }

    // Only Callable by the Pool Admin
    // Freezes Functions and only allows withdrawals
    pub fn set_freeze_status(e: Env, val: bool) {
        read_controller(&e).require_auth();
        extend_pool_ttl(&e);
        write_freeze(&e, val);
    }

    // GETTER FUNCTIONS

    // Get the Controller Address
    pub fn get_total_supply(e: Env) -> i128 {
        extend_pool_ttl(&e);
        get_total_shares(&e)
    }

    // Get the Controller Address
    pub fn get_controller(e: Env) -> Address {
        read_controller(&e)
    }

    // Get the Current Tokens in the Pool
    pub fn get_tokens(e: Env) -> Vec<Address> {
        extend_pool_ttl(&e);
        read_tokens(&e)
    }

    // Get the balance of the Token
    pub fn get_balance(e: Env, token: Address) -> i128 {
        extend_pool_ttl(&e);
        execute_get_balance(e, token)
    }

    // Get the weight of the token in decimal form with 7 decimals
    pub fn get_normalized_weight(e: Env, token: Address) -> i128 {
        extend_pool_ttl(&e);
        execute_get_normalized_weight(e, token)
    }

    // Calculate the spot considering the swap fee
    pub fn get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
        extend_pool_ttl(&e);
        execute_get_spot_price(e, token_in, token_out)
    }

    // Get the Swap Fee of the Contract
    pub fn get_swap_fee(e: Env) -> i128 {
        read_swap_fee(&e)
    }

    // Get the spot price without considering the swap fee
    pub fn get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
        extend_pool_ttl(&e);
        execute_get_spot_price_sans_fee(e, token_in, token_out)
    }
}

// SEP-0041 Token Implementation
#[contractimpl]
impl TokenInterface for CometPoolContract {
    fn allowance(e: Env, from: Address, spender: Address) -> i128 {
        extend_pool_ttl(&e);
        read_allowance(&e, from, spender).amount
    }

    fn approve(e: Env, from: Address, spender: Address, amount: i128, expiration_ledger: u32) {
        from.require_auth();

        check_nonnegative_amount(amount);

        extend_pool_ttl(&e);

        write_allowance(&e, from.clone(), spender.clone(), amount, expiration_ledger);

        Approve {
            from,
            spender,
            amount,
            expiration_ledger,
        }
        .publish(&e);
    }

    fn balance(e: Env, id: Address) -> i128 {
        extend_pool_ttl(&e);
        read_balance(&e, id)
    }

    fn transfer(e: Env, from: Address, to: MuxedAddress, amount: i128) {
        from.require_auth();

        check_nonnegative_amount(amount);

        extend_pool_ttl(&e);

        let to_address = to.address();
        spend_balance(&e, from.clone(), amount);
        receive_balance(&e, to_address.clone(), amount);
        Transfer {
            from,
            to: to_address,
            to_muxed_id: to.id(),
            amount,
        }
        .publish(&e);
    }

    fn transfer_from(e: Env, spender: Address, from: Address, to: Address, amount: i128) {
        spender.require_auth();

        check_nonnegative_amount(amount);

        extend_pool_ttl(&e);

        spend_allowance(&e, from.clone(), spender, amount);
        spend_balance(&e, from.clone(), amount);
        receive_balance(&e, to.clone(), amount);
        TransferWithAmountOnly { from, to, amount }.publish(&e);
    }

    fn burn(e: Env, from: Address, amount: i128) {
        from.require_auth();

        extend_pool_ttl(&e);

        burn_shares_from(&e, &from, amount);
    }

    fn burn_from(e: Env, spender: Address, from: Address, amount: i128) {
        spender.require_auth();
        check_nonnegative_amount(amount);

        extend_pool_ttl(&e);

        spend_allowance(&e, from.clone(), spender, amount);
        burn_shares_from(&e, &from, amount);
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
