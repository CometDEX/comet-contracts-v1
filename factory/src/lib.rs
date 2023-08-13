#![no_std]
#![allow(unused)]
use soroban_sdk::{contractimpl, contracttype, Address, Bytes, BytesN, Env, Symbol, Vec, contract, symbol_short, vec, IntoVal, Val};

// Importing the Pool Contract WASM
mod contract {
    soroban_sdk::contractimport!(file = "../target/wasm32-unknown-unknown/release/contracts.wasm");
}

// Keys which will give access to the corresponding data
#[derive(Clone)]
#[contracttype]
pub enum DataKeyFactory {
    IsCpool(Address),
    Admin,
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
    pub fn init(e: Env, user: Address) {
        assert!(
            !e.storage().persistent().has(&DataKeyFactory::Admin),
            "admin already initialized"
        );
        user.require_auth();
        let key = DataKeyFactory::Admin;
        e.storage().persistent().set(&key, &user);
    }

    // Create a new Comet Pool
    pub fn new_c_pool(e: Env, salt: BytesN<32>, wasm_hash: BytesN<32>, user: Address) -> Address {
        user.require_auth();
        // let mut salt = Bytes::new(&e);
        // let salt = e.crypto().sha256(&salt);
        // let id = e.deployer().with_current_contract(salt).deploy(wasm_hash);
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
        assert!(
            caller == e.storage().persistent().get::<DataKeyFactory, Address>(&DataKeyFactory::Admin).unwrap(),
            "ERR_NOT_CONTROLLER"
        );
        caller.require_auth();
        e.storage().persistent().set(&DataKeyFactory::Admin, &user);
        let event: SetAdminEvent = SetAdminEvent {
            caller,
            admin: user,
        };
        e.events()
            .publish((symbol_short!("LOG"), symbol_short!("SET_ADMIN")), event);
    }

    // Get the Current Admin of the Factory Contract
    pub fn get_c_admin(e: Env) -> Address {
        e.storage().persistent().get::<DataKeyFactory, Address>(&DataKeyFactory::Admin).unwrap()
    }

    // Returns true if the passed Address is a valid Pool
    pub fn is_c_pool(e: Env, addr: Address) -> bool {
        let key = DataKeyFactory::IsCpool(addr);
        e.storage().persistent().get::<DataKeyFactory, bool>(&key).unwrap_or(false)
    }

    pub fn collect(e: Env, caller: Address, addr: Address) {
        assert!(
            caller == e.storage().persistent().get::<DataKeyFactory, Address>(&DataKeyFactory::Admin).unwrap(),
            "ERR_NOT_ADMIN"
        );
        caller.require_auth();
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
