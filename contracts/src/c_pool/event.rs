//! Definition of the Events used in the contract
use soroban_sdk::{contractevent, contracttype, Address};

// Swap Token Event, emitted when tokens are swapped
#[contractevent(topics = ["POOL", "swap"], data_format = "map")]
pub struct SwapEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_out: Address,
    pub token_amount_in: i128,
    pub token_amount_out: i128,
}

// Join Pool Event, emitted a when a user joins the pool
#[contractevent(topics = ["POOL", "join_pool"], data_format = "map")]
pub struct JoinEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_amount_in: i128,
}

// Exit Pool Event, emitted a when a user exits the pool
#[contractevent(topics = ["POOL", "exit_pool"], data_format = "map")]
pub struct ExitEvent {
    pub caller: Address,
    pub token_out: Address,
    pub token_amount_out: i128,
}

// Join Pool Event, emitted a when a user joins the pool
#[contractevent(topics = ["POOL", "deposit"], data_format = "map")]
pub struct DepositEvent {
    pub caller: Address,
    pub token_in: Address,
    pub token_amount_in: i128,
}

// Exit Pool Event, emitted a when a user exits the pool
#[contractevent(topics = ["POOL", "withdraw"], data_format = "map")]
pub struct WithdrawEvent {
    pub caller: Address,
    pub token_out: Address,
    pub token_amount_out: i128,
    pub pool_amount_in: i128,
}

// Freeze Event, emitted when the controller updates the pool's freeze status
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FreezeEvent {
    pub controller: Address,
    pub frozen: bool,
}

// Gulp Event, emitted when recorded reserves are synchronized with the token balance
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GulpEvent {
    pub token: Address,
    pub previous_balance: i128,
    pub new_balance: i128,
}
