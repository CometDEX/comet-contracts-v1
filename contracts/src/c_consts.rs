//! Comet Pool Constants

use fixed_point_math::STROOP;

pub const BONE: i128 = STROOP as i128;
pub const MIN_CPOW_BASE: i128 = 1;
pub const MAX_CPOW_BASE: i128 = (2 * BONE) - 1;
pub const CPOW_PRECISION: i128 = 1_000000_i128;
pub const EXIT_FEE: i128 = 0;
pub const TOTAL_WEIGHT: i128 = BONE * 50;
pub const INIT_POOL_SUPPLY: i128 = BONE * 100;
pub const MIN_FEE: i128 = 10;
pub const MAX_FEE: i128 = 1_000000_i128;
pub const MAX_IN_RATIO: i128 = BONE / 2;
pub const MAX_OUT_RATIO: i128 = (BONE / 3) + 1;
pub const MIN_BOUND_TOKENS: u32 = 2;
pub const MAX_BOUND_TOKENS: u32 = 8;
pub const MIN_WEIGHT: i128 = BONE;
pub const MAX_WEIGHT: i128 = BONE * 50;
pub const MIN_BALANCE: i128 = (1_0000000 / 1_00000) as i128;
