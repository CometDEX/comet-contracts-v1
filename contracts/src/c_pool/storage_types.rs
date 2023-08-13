//! Declaration of the Storage Keys
use soroban_sdk::{contracttype, Address, Map, Vec};
pub(crate) const BALANCE_BUMP_AMOUNT: u32 = 518400; // 30 days
// Token Details Struct
#[contracttype]
#[derive(Clone, Default, Debug, Eq, PartialEq)]
pub struct Record {
    pub bound: bool,
    pub index: u32,
    pub denorm: i128,
    pub balance: i128,
}

// Data Keys for Pool' Storage Data
#[derive(Clone)]
#[contracttype]
pub enum DataKey {
    Factory,       // Address of the Factory Contract
    Controller,    // Address of the Controller Account
    SwapFee,       // i128
    TotalWeight,   // i128
    AllTokenVec,   // Vec<Address>
    AllRecordData, // Map<Address, Record>
    TokenShare,    // Address
    TotalShares,   // i128
    PublicSwap,    // bool
    Finalize,      // bool
    Freeze,        // bool
}

// Data Keys for the LP Token
#[derive(Clone)]
#[contracttype]
pub enum DataKeyToken {
    Allowance(AllowanceDataKey),
    Balance(Address),
    Nonce(Address),
    State(Address),
    Admin,
    Decimals,
    Name,
    Symbol,
}

#[derive(Clone)]
#[contracttype]
pub struct AllowanceDataKey {
    pub from: Address,
    pub spender: Address,
}
