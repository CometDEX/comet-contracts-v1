#![no_std]

pub use soroban_sdk::token::{StellarAssetClient, TokenClient};

#[cfg(any(test, feature = "testutils"))]
pub mod testutils;
