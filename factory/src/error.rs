use soroban_sdk::contracterror;

// Error codes based on the Comet pool contract
#[contracterror]
#[derive(Copy, Clone, Debug)]
#[repr(u32)]
pub enum Error {
    ErrNotController = 5,
    AlreadyInitialized = 7,
}