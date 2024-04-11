use soroban_sdk::{
    assert_with_error, symbol_short, unwrap::UnwrapOptimized, Address, Bytes, BytesN, Env, IntoVal,
    Val, Vec,
};

use crate::{
    error::Error, DataKeyFactory, NewPoolEvent, SetAdminEvent, LARGE_BUMP_AMOUNT,
    LARGE_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD,
};

pub fn execute_init(e: Env, user: Address, pool_wasm_hash: BytesN<32>) {
    e.storage().instance().set(&DataKeyFactory::Admin, &user);
    e.storage()
        .instance()
        .set(&DataKeyFactory::WasmHash, &pool_wasm_hash);
}

pub fn execute_new_c_pool(e: Env, salt: BytesN<32>, user: Address) -> Address {
    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    let wasm_hash = e
        .storage()
        .instance()
        .get::<DataKeyFactory, BytesN<32>>(&DataKeyFactory::WasmHash)
        .unwrap_optimized();

    // build salt dervied from user and provided salt to
    let mut as_u8s: [u8; 56] = [0; 56];
    user.to_string().copy_into_slice(&mut as_u8s);
    let mut salt_as_bytes: Bytes = salt.into_val(&e);
    salt_as_bytes.extend_from_array(&as_u8s);
    let new_salt = e.crypto().keccak256(&salt_as_bytes);

    let id = e
        .deployer()
        .with_current_contract(new_salt)
        .deploy(wasm_hash);

    let val = e.current_contract_address().clone();
    let init_args: Vec<Val> = (val.clone(), user.clone()).into_val(&e);
    e.invoke_contract::<()>(&id, &symbol_short!("init"), init_args);

    let key = DataKeyFactory::IsCpool(id.clone());
    e.storage().persistent().set(&key, &true);
    e.storage()
        .persistent()
        .extend_ttl(&key, LARGE_LIFETIME_THRESHOLD, LARGE_BUMP_AMOUNT);
    let event: NewPoolEvent = NewPoolEvent {
        caller: user,
        pool: id.clone(),
    };
    e.events()
        .publish((symbol_short!("LOG"), symbol_short!("NEW_POOL")), event);
    id
}

pub fn execute_set_c_admin(e: Env, caller: Address, user: Address) {
    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    e.storage().instance().set(&DataKeyFactory::Admin, &user);
    let event: SetAdminEvent = SetAdminEvent {
        caller,
        admin: user,
    };
    e.events()
        .publish((symbol_short!("LOG"), symbol_short!("SET_ADMIN")), event);
}

pub fn execute_collect(e: Env, caller: Address, addr: Address) {
    assert_with_error!(
        &e,
        execute_is_c_pool(e.clone(), addr.clone()),
        Error::ErrNotCPool
    );
    e.storage()
        .instance()
        .extend_ttl(SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);

    let curr = &e.current_contract_address().clone();
    let init_args: Vec<Val> = (curr.clone(),).into_val(&e);

    let val = e.invoke_contract::<i128>(&addr, &symbol_short!("balance"), init_args);
    let init_args: Vec<Val> = (curr.clone(), caller.clone(), val.clone()).into_val(&e);

    e.invoke_contract::<()>(&addr, &symbol_short!("transfer"), init_args)
}

// Returns true if the passed Address is a valid Pool
pub fn execute_is_c_pool(e: Env, addr: Address) -> bool {
    let key = DataKeyFactory::IsCpool(addr);
    if let Some(is_cpool) = e.storage().persistent().get::<DataKeyFactory, bool>(&key) {
        e.storage()
            .persistent()
            .extend_ttl(&key, LARGE_LIFETIME_THRESHOLD, LARGE_BUMP_AMOUNT);
        is_cpool
    } else {
        false
    }
}
