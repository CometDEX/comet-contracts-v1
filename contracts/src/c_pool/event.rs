//! Definition of the Events used in the contract
use soroban_sdk::{contractevent, Address};

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
#[contractevent(topics = ["POOL", "freeze"], data_format = "map")]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FreezeEvent {
    pub controller: Address,
    pub frozen: bool,
}

// Gulp Event, emitted when recorded reserves are synchronized with the token balance
#[contractevent(topics = ["POOL", "gulp"], data_format = "map")]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GulpEvent {
    pub token: Address,
    pub previous_balance: i128,
    pub new_balance: i128,
}

// Controller Proposal Event, emitted when the current controller proposes or cancels a transfer
#[contractevent(topics = ["POOL", "set_ctrl"], data_format = "single-value")]
pub struct SetControllerEvent {
    #[topic]
    pub controller: Address,
    pub manager: Address,
}

// Controller Acceptance Event, emitted when a pending controller accepts the transfer
#[contractevent(topics = ["POOL", "acpt_ctrl"], data_format = "single-value")]
pub struct AcceptControllerEvent {
    #[topic]
    pub previous_controller: Address,
    pub new_controller: Address,
}
