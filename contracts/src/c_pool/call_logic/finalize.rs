use soroban_sdk::{assert_with_error, Address, Env};

use crate::{
    c_consts::{INIT_POOL_SUPPLY, MIN_BOUND_TOKENS},
    c_pool::{
        error::Error,
        metadata::{read_finalize, read_tokens, write_finalize, write_public_swap},
        token_utility::mint_shares,
    }, c_consts_256::get_min_bound_tokens,
};

pub fn execute_finalize(e: Env, controller: Address) {
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);
    assert_with_error!(
        &e,
        read_tokens(&e).len() >= get_min_bound_tokens(&e),
        Error::ErrMinTokens
    );
    write_finalize(&e, true);
    write_public_swap(&e, true);
    mint_shares(e, controller, INIT_POOL_SUPPLY);
}
