//! Definition of the Events used in the contract
use soroban_sdk::{contractevent, Address};

// Swap Token Event, emitted when tokens are swapped
#[contractevent]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SwapEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_out: Address,
    pub token_amount_in: i128,
    pub token_amount_out: i128,
}

// Join Pool Event, emitted a when a user joins the pool
#[contractevent]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_amount_in: i128,
}

// Exit Pool Event, emitted a when a user exits the pool
#[contractevent]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExitEvent {
    pub caller: Address,
    pub token_out: Address,
    pub token_amount_out: i128,
}

// Join Pool Event, emitted a when a user joins the pool
#[contractevent]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DepositEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_amount_in: i128,
}

// Exit Pool Event, emitted a when a user exits the pool
#[contractevent]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WithdrawEvent {
    pub caller: Address,
    pub token_out: Address,
    pub token_amount_out: i128,
    pub pool_amount_in: i128,
}
