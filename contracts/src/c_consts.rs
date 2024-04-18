//! Comet Pool Constants

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
pub const EXIT_FEE: i128 = 0;
pub const MIN_FEE: i128 = 10;
pub const MAX_FEE: i128 = 10i128.pow(6);
pub const MIN_BOUND_TOKENS: u32 = 2;
pub const MAX_BOUND_TOKENS: u32 = 8;
pub const MAX_TOTAL_WEIGHT: i128 = STROOP * 50;
pub const MIN_WEIGHT: i128 = STROOP;
pub const MAX_WEIGHT: i128 = STROOP * 50;
pub const MIN_BALANCE: i128 = 100;

