//! Definition of the Events used in the contract
use soroban_sdk::{contracttype, Address, Env, Symbol};

// Swap Token Event, emitted when tokens are swapped
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SwapEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_out: Address,
    pub token_amount_in: i128,
    pub token_amount_out: i128,
}

// Join Pool Event, emitted a when a user joins the pool
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_amount_in: i128,
}

// Exit Pool Event, emitted a when a user exits the pool
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExitEvent {
    pub caller: Address,
    pub token_out: Address,
    pub token_amount_out: i128,
}

// Event to be emitted when a user incremenets the allowance for the LP Token for a particular user
pub fn incr_allow_event(e: &Env, from: Address, to: Address, amount: i128) {
    let topics = (Symbol::new(e, "incr_allow"), from, to);
    e.events().publish(topics, amount);
}

// Event to be emitted when a user decrement the allowance for the LP Token for a particular user
pub fn decr_allow_event(e: &Env, from: Address, to: Address, amount: i128) {
    let topics = (Symbol::new(e, "decr_allow"), from, to);
    e.events().publish(topics, amount);
}

// Event to be emitted when transfer of LP Token happens from one address to another
pub fn transfer_event(e: &Env, from: Address, to: Address, amount: i128) {
    let topics = (Symbol::short("transfer"), from, to);
    e.events().publish(topics, amount);
}

// Event to be emitted when new LP Tokens are minted
pub fn mint_event(e: &Env, admin: Address, to: Address, amount: i128) {
    let topics = (Symbol::short("mint"), admin, to);
    e.events().publish(topics, amount);
}

// Event to be emitted when Admin burns LP Tokens from Deauthorized balances
pub fn clawback_event(e: &Env, admin: Address, from: Address, amount: i128) {
    let topics = (Symbol::short("clawback"), admin, from);
    e.events().publish(topics, amount);
}

// Event to be emitted when a user Address is authorized or deauthorized
pub fn set_auth_event(e: &Env, admin: Address, id: Address, authorize: bool) {
    let topics = (Symbol::short("set_auth"), admin, id);
    e.events().publish(topics, authorize);
}

// Event to be emitted when a new Admin is set for the LP Token
pub fn set_admin_event(e: &Env, admin: Address, new_admin: Address) {
    let topics = (Symbol::short("set_admin"), admin);
    e.events().publish(topics, new_admin);
}

// Event to be emitted when LP Tokens are Burned
pub fn burn_event(e: &Env, from: Address, amount: i128) {
    let topics = (Symbol::short("burn"), from);
    e.events().publish(topics, amount);
}
