use soroban_sdk::{assert_with_error, Address, Env, String};
use soroban_token_sdk::metadata::TokenMetadata;

use crate::{
    c_consts_256::get_min_fee,
    c_pool::{
        error::Error,
        metadata::{
            put_total_shares, write_controller, write_factory, write_finalize, write_metadata,
            write_public_swap, write_swap_fee,
        },
        storage_types::DataKey,
    },
};

pub fn execute_init(e: Env, factory: Address, controller: Address) {
    // Check if the Contract Storage is already initialized
    assert_with_error!(
        &e,
        !e.storage().instance().has(&DataKey::Factory),
        Error::AlreadyInitialized
    );

    // Store the factory Address
    write_factory(&e, factory);
    // Store the Controller Address (Pool Admin)
    write_controller(&e, controller);

    // Get the Current Contract Address
    let val: &Address = &e.current_contract_address();

    // Name of the LP Token
    let name = String::from_str(&e, "Comet Pool Token");
    // Symbol of the LP Token
    let symbol = String::from_str(&e, "CPAL");

    // Set the Total Supply of the LP Token as 0
    put_total_shares(&e, 0);

    // Store the Swap Fee
    write_swap_fee(&e, get_min_fee(&e).to_i128().unwrap());

    // Initialize Public Swap and Finalize as false
    write_finalize(&e, false);
    write_public_swap(&e, false);

    write_metadata(
        &e,
        TokenMetadata {
            name,
            symbol,
            decimal: 7u32,
        },
    )
}
