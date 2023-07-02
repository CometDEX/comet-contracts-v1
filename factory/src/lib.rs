#![no_std]
#![allow(unused)]
use soroban_sdk::{contractimpl, contracttype, Address, Bytes, BytesN, Env, RawVal, Symbol, Vec};

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

pub struct Factory;

#[contractimpl]
impl Factory {
    // Initialize the Admin for the Factory Contract
    pub fn init(e: Env, user: Address) {
        assert!(
            !e.storage().has(&DataKeyFactory::Admin),
            "admin already initialized"
        );
        user.require_auth();
        let key = DataKeyFactory::Admin;
        e.storage().set(&key, &user);
    }

    // Create a new Comet Pool
    pub fn new_c_pool(
        e: Env,
        init_fn: Symbol,
        init_args: Vec<RawVal>,
        wasm_hash: BytesN<32>,
        user: Address,
    ) -> BytesN<32> {
        user.require_auth();
        let mut salt = Bytes::new(&e);
        let salt = e.crypto().sha256(&salt);
        let id = e.deployer().with_current_contract(&salt).deploy(&wasm_hash);

        contract::Client::new(&e, &id)
            .init(&e.current_contract_address(), &e.current_contract_address());
        let key = DataKeyFactory::IsCpool(Address::from_contract_id(&e, &id));
        e.storage().set(&key, &true);
        contract::Client::new(&e, &id).set_controller(&e.current_contract_address(), &user);
        let event: NewPoolEvent = NewPoolEvent {
            caller: user,
            pool: Address::from_contract_id(&e, &id),
        };
        e.events()
            .publish((Symbol::short("LOG"), Symbol::short("NEW_POOL")), event);
        id
    }

    // Set a new admin for the factory contract
    pub fn set_c_admin(e: Env, caller: Address, user: Address) {
        assert!(
            caller == e.storage().get(&DataKeyFactory::Admin).unwrap().unwrap(),
            "ERR_NOT_CONTROLLER"
        );
        caller.require_auth();
        e.storage().set(&DataKeyFactory::Admin, &user);
        let event: SetAdminEvent = SetAdminEvent {
            caller,
            admin: user,
        };
        e.events()
            .publish((Symbol::short("LOG"), Symbol::short("SET_ADMIN")), event);
    }

    // Get the Current Admin of the Factory Contract
    pub fn get_c_admin(e: Env) -> Address {
        e.storage().get(&DataKeyFactory::Admin).unwrap().unwrap()
    }

    // Returns true if the passed Address is a valid Pool
    pub fn is_c_pool(e: Env, addr: Address) -> bool {
        let key = DataKeyFactory::IsCpool(addr);
        e.storage().get(&key).unwrap_or(Ok(false)).unwrap()
    }

    pub fn collect(e: Env, caller: Address, addr: Address) {
        assert!(
            caller == e.storage().get(&DataKeyFactory::Admin).unwrap().unwrap(),
            "ERR_NOT_ADMIN"
        );
        caller.require_auth();
        let val = contract::Client::new(&e, &addr.contract_id().unwrap())
            .balance(&e.current_contract_address());
        contract::Client::new(&e, &addr.contract_id().unwrap()).xfer(
            &e.current_contract_address(),
            &caller,
            &val,
        );
    }
}

mod test;
