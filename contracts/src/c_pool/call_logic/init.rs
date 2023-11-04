use soroban_sdk::{assert_with_error, Address, Env, String};
use soroban_token_sdk::metadata::TokenMetadata;

use crate::{
    c_consts::MIN_FEE,
    c_pool::{
        admin::{has_administrator, write_administrator},
        error::Error,
        metadata::{
            put_token_share, put_total_shares, write_controller, write_factory, write_finalize,
            write_metadata, write_public_swap, write_swap_fee,
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
    let name = String::from_slice(&e, "Comet Pool Token");
    // Symbol of the LP Token
    let symbol = String::from_slice(&e, "CPAL");

    // Current Contract is the LP Token as well
    put_token_share(&e, val.clone());

    // Set the Total Supply of the LP Token as 0
    put_total_shares(&e, 0);

    // Store the Swap Fee
    write_swap_fee(&e, MIN_FEE);

    // Initialize Public Swap and Finalize as false
    write_finalize(&e, false);
    write_public_swap(&e, false);

    // Initialize the LP Token

    if has_administrator(&e) {
        panic!("already initialized")
    }
    write_administrator(&e, val);
    if 7u32 > u8::MAX.into() {
        panic!("Decimal must fit in a u8");
    }

    write_metadata(
        &e,
        TokenMetadata {
            name,
            symbol,
            decimal: 7u32,
        },
    )
}
