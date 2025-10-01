//! Comet Pool Constants

use soroban_sdk::{symbol_short, Symbol};

pub const POOL: Symbol = symbol_short!("POOL");

/// c_math 256 bit constants
/// kept as i128 to avoid requiring `env` to define constants
pub const BONE: i128 = 10i128.pow(18);
pub const MIN_CPOW_BASE: i128 = 1;
pub const MAX_CPOW_BASE: i128 = (2 * BONE) - 1;
pub const CPOW_PRECISION: i128 = 10i128.pow(8);

/// constants
pub const STROOP: i128 = 10i128.pow(7);
pub const STROOP_SCALAR: i128 = 10i128.pow(11);
pub const MAX_IN_RATIO: i128 = (STROOP / 3) + 1;
pub const MAX_OUT_RATIO: i128 = (STROOP / 3) + 1;
pub const INIT_POOL_SUPPLY: i128 = STROOP * 100;
pub const MIN_FEE: i128 = 00_00010; // 0.0001%
pub const MAX_FEE: i128 = 99_99990; // 99.9999%
pub const MIN_WEIGHT: i128 = STROOP / 10; // 10%
pub const MAX_WEIGHT: i128 = MIN_WEIGHT * 9; // 90%
pub const MIN_BALANCE: i128 = 100;
pub const MAX_FEE_RECIPIENTS: u32 = 5;

/// Maximum allowed value for low_util_balance and high_util_balance to prevent overflow
/// when multiplied by the maximum scalar (10^18 for 0-decimal tokens).
/// This cap allows up to ~170 billion tokens, which is sufficient for all practical use cases.
/// Calculated as: i128::MAX / 10^18 ≈ 1.7e20
pub const MAX_UTIL_BALANCE: i128 = 170_141_183_460_469_231_731; // i128::MAX / 10^18
