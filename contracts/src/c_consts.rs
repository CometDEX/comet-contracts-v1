//! Comet Pool Constants

/// c_math 256 bit constants
/// kept as i128 to avoid requiring `env` to define constants
pub const BONE: i128 = 10i128.pow(18);
pub const MIN_CPOW_BASE: i128 = 1;
pub const MAX_CPOW_BASE: i128 = (2 * BONE) - 1;
pub const CPOW_PRECISION: i128 = 10i128.pow(8);
pub const MAX_CPOW_ITERS: i128 = 50;

/// constants
pub const STROOP: i128 = 10i128.pow(7);
pub const STROOP_SCALAR: i128 = 10i128.pow(11);
pub const MAX_IN_RATIO: i128 = (STROOP / 3) + 1;
pub const MAX_OUT_RATIO: i128 = (STROOP / 3) + 1;
pub const INIT_POOL_SUPPLY: i128 = STROOP * 100;
pub const MIN_FEE: i128 = 10; // 0.0001%
pub const MAX_FEE: i128 = STROOP / 10; // 10%
pub const MIN_BOUND_TOKENS: u32 = 2;
pub const MAX_BOUND_TOKENS: u32 = 8;
pub const MAX_TOTAL_WEIGHT: i128 = STROOP * 50;
pub const MIN_WEIGHT: i128 = STROOP / 10; // 10%
/// The largest reciprocal exponent reachable from the configured minimum weight.
///
/// This must round up to match the directed reciprocal constructed by `c_math`.
pub const MAX_CPOW_EXP: i128 = (BONE * STROOP + MIN_WEIGHT - 1) / MIN_WEIGHT;
const MAX_FORMALLY_PROVEN_CPOW_EXP: i128 = 10 * BONE;
const _: () = assert!(MAX_CPOW_EXP <= MAX_FORMALLY_PROVEN_CPOW_EXP);
pub const MAX_WEIGHT: i128 = MIN_WEIGHT * 9; // 90%

// Keep every successful pool operation inside the documented c_pow operating
// band [0.5, 1.6]. These guards tie the convergence proof to the pool
// configuration without adding runtime checks.
const _: () = assert!(5 * MAX_IN_RATIO <= 3 * STROOP);
const _: () = assert!(8 * MAX_OUT_RATIO < 3 * STROOP);
const _: () =
    assert!(2 * MAX_OUT_RATIO * STROOP < STROOP * STROOP - (STROOP - MIN_WEIGHT) * MAX_FEE);
const _: () = assert!(MAX_WEIGHT <= STROOP);

pub const MIN_BALANCE: i128 = 100;
