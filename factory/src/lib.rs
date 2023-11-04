#![no_std]
#![allow(unused)]
use call_logic::factory::{execute_is_c_pool, execute_new_c_pool};
use soroban_sdk::{
    assert_with_error, contract, contractimpl, contracttype, symbol_short, unwrap::UnwrapOptimized,
    vec, Address, Bytes, BytesN, Env, IntoVal, Symbol, Val, Vec,
};

// Errors Listed
pub mod call_logic;
pub mod error;
use crate::{
    call_logic::factory::{execute_collect, execute_init, execute_set_c_admin},
    error::Error,
};

pub(crate) const DAY_IN_LEDGERS: u32 = 17280;
pub(crate) const SHARED_BUMP_AMOUNT: u32 = 69120; // 4 days
pub(crate) const SHARED_LIFETIME_THRESHOLD: u32 = SHARED_BUMP_AMOUNT - DAY_IN_LEDGERS;
pub(crate) const LARGE_BUMP_AMOUNT: u32 = 518400; // 30 days
pub(crate) const LARGE_LIFETIME_THRESHOLD: u32 = LARGE_BUMP_AMOUNT - DAY_IN_LEDGERS;

// Keys which will give access to the corresponding data
#[derive(Clone)]
#[contracttype]
pub enum DataKeyFactory {
    IsCpool(Address),
    Admin,
    WasmHash,
}

// Event to signal a new pool has been created
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NewPoolEvent {
    pub caller: Address,
    pub pool: Address,
}

// Event to signal the admin for the factory contract has been changed.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SetAdminEvent {
    pub caller: Address,
    pub admin: Address,
}
#[contract]
pub struct Factory;

#[contractimpl]
impl Factory {
    // Initialize the Admin for the Factory Contract
    pub fn init(e: Env, user: Address, pool_wasm_hash: BytesN<32>) {
        assert_with_error!(
            &e,
            !e.storage().instance().has(&DataKeyFactory::Admin),
            Error::AlreadyInitialized
        );
        user.require_auth();
        execute_init(e, user, pool_wasm_hash);
    }

    // Create a new Comet Pool
    pub fn new_c_pool(e: Env, salt: BytesN<32>, user: Address) -> Address {
        user.require_auth();
        execute_new_c_pool(e, salt, user)
    }

    // Set a new admin for the factory contract
    pub fn set_c_admin(e: Env, caller: Address, user: Address) {
        assert_with_error!(
            &e,
            caller
                == e.storage()
                    .instance()
                    .get::<DataKeyFactory, Address>(&DataKeyFactory::Admin)
                    .unwrap_optimized(),
            Error::ErrNotController
        );
        caller.require_auth();
        execute_set_c_admin(e, caller, user);
    }

    pub fn collect(e: Env, caller: Address, addr: Address) {
        assert_with_error!(
            &e,
            caller
                == e.storage()
                    .instance()
                    .get::<DataKeyFactory, Address>(&DataKeyFactory::Admin)
                    .unwrap_optimized(),
            Error::ErrNotController
        );
        caller.require_auth();
        execute_collect(e, caller, addr)
    }

    // Returns true if the passed Address is a valid Pool
    pub fn is_c_pool(e: Env, addr: Address) -> bool {
        execute_is_c_pool(e, addr)
    }
    // Get the Current Admin of the Factory Contract
    pub fn get_c_admin(e: Env) -> Address {
        e.storage()
            .instance()
            .get::<DataKeyFactory, Address>(&DataKeyFactory::Admin)
            .unwrap_optimized()
    }
}

mod test;
