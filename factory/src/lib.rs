#![no_std]

use call_logic::factory::{execute_is_c_pool, execute_new_c_pool};
use soroban_sdk::{
    assert_with_error, contract, contractimpl, contracttype, Address, BytesN, Env, Vec,
};

// Errors Listed
pub mod call_logic;
pub mod error;
use crate::{call_logic::factory::execute_init, error::Error};

// Keys which will give access to the corresponding data
#[derive(Clone)]
#[contracttype]
pub enum DataKeyFactory {
    IsCpool(Address),
    WasmHash,
}

// Event to signal a new pool has been created
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NewPoolEvent {
    pub caller: Address,
    pub pool: Address,
}

#[contract]
pub struct Factory;

#[contractimpl]
impl Factory {
    // Initialize the Admin for the Factory Contract
    pub fn init(e: Env, pool_wasm_hash: BytesN<32>) {
        assert_with_error!(
            &e,
            !e.storage().instance().has(&DataKeyFactory::WasmHash),
            Error::AlreadyInitialized
        );
        execute_init(e, pool_wasm_hash);
    }

    // Create a new Comet Pool
    pub fn new_c_pool(
        e: Env,
        salt: BytesN<32>,
        controller: Address,
        tokens: Vec<Address>,
        weights: Vec<i128>,
        balances: Vec<i128>,
        swap_fee: i128,
    ) -> Address {
        controller.require_auth();
        execute_new_c_pool(e, salt, controller, tokens, weights, balances, swap_fee)
    }

    // Returns true if the passed Address is a valid Pool
    pub fn is_c_pool(e: Env, addr: Address) -> bool {
        execute_is_c_pool(e, addr)
    }
}

mod test;
