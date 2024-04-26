use soroban_sdk::{
    symbol_short, unwrap::UnwrapOptimized, vec, Address, Bytes, BytesN, Env, IntoVal, Val, Vec,
};

use crate::{DataKeyFactory, NewPoolEvent};

pub(crate) const DAY_IN_LEDGERS: u32 = 17280;

pub(crate) const SHARED_BUMP_AMOUNT: u32 = 31 * DAY_IN_LEDGERS;
pub(crate) const SHARED_LIFETIME_THRESHOLD: u32 = SHARED_BUMP_AMOUNT - DAY_IN_LEDGERS;

pub(crate) const LARGE_BUMP_AMOUNT: u32 = 120 * DAY_IN_LEDGERS;
pub(crate) const LARGE_LIFETIME_THRESHOLD: u32 = LARGE_BUMP_AMOUNT - 20 * DAY_IN_LEDGERS;

pub fn execute_init(e: Env, pool_wasm_hash: BytesN<32>) {
    e.storage()
        .instance()
        .set(&DataKeyFactory::WasmHash, &pool_wasm_hash);
}

pub fn execute_new_c_pool(
    e: Env,
    salt: BytesN<32>,
    controller: Address,
    tokens: Vec<Address>,
    weights: Vec<i128>,
    balances: Vec<i128>,
    swap_fee: i128,
) -> Address {
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
    controller.to_string().copy_into_slice(&mut as_u8s);
    let mut salt_as_bytes: Bytes = salt.into_val(&e);
    salt_as_bytes.extend_from_array(&as_u8s);
    let new_salt = e.crypto().keccak256(&salt_as_bytes);

    let id = e
        .deployer()
        .with_current_contract(new_salt)
        .deploy(wasm_hash);

    let init_args: Vec<Val> = vec![
        &e,
        controller.into_val(&e),
        tokens.into_val(&e),
        weights.into_val(&e),
        balances.into_val(&e),
        swap_fee.into_val(&e),
    ];
    e.invoke_contract::<()>(&id, &symbol_short!("init"), init_args);

    let key = DataKeyFactory::IsCpool(id.clone());
    e.storage().persistent().set(&key, &true);
    e.storage()
        .persistent()
        .extend_ttl(&key, LARGE_LIFETIME_THRESHOLD, LARGE_BUMP_AMOUNT);
    let event: NewPoolEvent = NewPoolEvent {
        caller: controller,
        pool: id.clone(),
    };
    e.events()
        .publish((symbol_short!("LOG"), symbol_short!("NEW_POOL")), event);
    id
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
