#![no_std]
#![allow(unused)]
use soroban_sdk::{contractimpl, contracttype, Address, Bytes, BytesN, Env, Symbol, Vec, contract, symbol_short, vec, IntoVal, Val, unwrap::UnwrapOptimized, assert_with_error};

// Errors Listed
pub mod error;
use crate::error::Error;

pub(crate) const SHARED_BUMP_AMOUNT: u32 = 69120; // 4 days
pub(crate) const LARGE_BUMP_AMOUNT: u32 = 518400; // 30 days

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
        e.storage().instance().set(&DataKeyFactory::Admin, &user);
        e.storage().instance().set(&DataKeyFactory::WasmHash, &pool_wasm_hash);
    }

    // Create a new Comet Pool
    pub fn new_c_pool(e: Env, salt: BytesN<32>, user: Address) -> Address {
        user.require_auth();
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        // let mut salt = Bytes::new(&e);
        // let salt = e.crypto().sha256(&salt);
        // let id = e.deployer().with_current_contract(salt).deploy(wasm_hash);
        let wasm_hash = e.storage()
            .instance()
            .get::<DataKeyFactory, BytesN<32>>(&DataKeyFactory::WasmHash)
            .unwrap_optimized();
        let id = e.deployer()
            .with_address(user.clone(), salt)
            .deploy(wasm_hash);
        // let x: Vec<Val> = Vec::new(&e);
        let val = e.current_contract_address().clone();

        let init_args: Vec<Val> = (
            val.clone(),
            user.clone()
        ).into_val(&e);
        
        e.invoke_contract::<()>(&id, &symbol_short!("init"), init_args);

        let key = DataKeyFactory::IsCpool(id.clone());
        e.storage().persistent().set(&key, &true);
        e.storage().persistent().bump(&key, LARGE_BUMP_AMOUNT);
        let event: NewPoolEvent = NewPoolEvent {
            caller: user,
            pool: id.clone(),
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("NEW_POOL")), event);
        id
    }

    // Set a new admin for the factory contract
    pub fn set_c_admin(e: Env, caller: Address, user: Address) {
        assert_with_error!(
            &e,
            caller == e.storage()
                .instance()
                .get::<DataKeyFactory, Address>(&DataKeyFactory::Admin)
                .unwrap_optimized(),
            Error::ErrNotController
        );
        caller.require_auth();
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);
        e.storage().instance().set(&DataKeyFactory::Admin, &user);
        let event: SetAdminEvent = SetAdminEvent {
            caller,
            admin: user,
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("SET_ADMIN")), event);
    }

    // Get the Current Admin of the Factory Contract
    pub fn get_c_admin(e: Env) -> Address {
        e.storage().instance().get::<DataKeyFactory, Address>(&DataKeyFactory::Admin).unwrap_optimized()
    }

    // Returns true if the passed Address is a valid Pool
    pub fn is_c_pool(e: Env, addr: Address) -> bool {
        let key = DataKeyFactory::IsCpool(addr);
        if let Some(is_cpool) = e.storage().persistent().get::<DataKeyFactory, bool>(&key) {
            e.storage().persistent().bump(&key, LARGE_BUMP_AMOUNT);
            is_cpool
        } else {
            false
        }
    }

    pub fn collect(e: Env, caller: Address, addr: Address) {
        assert_with_error!(
            &e,
            caller == e.storage()
                .instance()
                .get::<DataKeyFactory, Address>(&DataKeyFactory::Admin)
                .unwrap_optimized(),
            Error::ErrNotController
        );
        assert_with_error!(
            &e,
            Self::is_c_pool(e.clone(), addr.clone()),
            Error::ErrNotCPool
        );
        caller.require_auth();
        e.storage().instance().bump(SHARED_BUMP_AMOUNT);

        let curr =  &e.current_contract_address().clone();
        let init_args: Vec<Val> = (
            curr.clone(),
        ).into_val(&e);
        
        let val = e.invoke_contract::<i128>(&addr, &symbol_short!("balance"), init_args);
        let init_args: Vec<Val> = (
            curr.clone(),
            caller.clone(),
            val.clone()
        ).into_val(&e);

        e.invoke_contract::<()>(&addr, &symbol_short!("xfer"), init_args)
    }
}

mod test;
