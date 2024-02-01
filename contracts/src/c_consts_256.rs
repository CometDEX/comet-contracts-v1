//! Comet Pool Constants, 256 bit integers
use soroban_sdk::{I256, Env};

//================================================================
// Function to return BONE constant
pub fn get_bone(e: &Env) -> I256 {
    I256::from_i128(e, 1e18)
}


//================================================================
// Function to return MIN_BOUND_TOKENS constant
pub fn get_min_bound_tokens(e: &Env) -> u32 {
    2
}

// Function to return MAX_BOUND_TOKENS constant
pub fn get_max_bound_tokens(e: &Env) -> u32 {
    8
}

//================================================================
// Function to return MIN_FEE constant
pub fn get_min_fee(e: &Env) -> I256 {
    get_bone(e).div(&I256::from_i128(e, 1e6))
}

// Function to return MAX_FEE constant
pub fn get_max_fee(e: &Env) -> i128 {
    get_bone(e).div(&I256::from_i128(e, 10))
}

// Function to return EXIT_FEE constant
pub fn get_exit_fee(e: &Env) -> I256 {
    I256::from_i128(env, 0)
}

//================================================================
// Function to return MIN_WEIGHT constant
pub fn get_min_weight(e: &Env) -> I256 {
    get_bone(e)
}

// Function to return MAX_WEIGHT constant
pub fn get_max_weight(e: &Env) -> I256 {
    get_bone(e) * I256::from_i128(e, 50)
}

// Function to return MAX_TOTAL_WEIGHT constant
pub fn get_max_total_weight(e: &Env) -> I256 {
    get_bone(e) * I256::from_i128(e, 50)
}

// Function to return MIN_BALANCE constant
pub fn get_min_balance(e: &Env) -> i128 {
    get_bone(e).div(&I256::from_i128(e, 1e12))
}

//================================================================
// Function to return INIT_POOL_SUPPLY constant
pub fn get_init_pool_supply(e: &Env) -> I256 {
    get_bone(e) * I256::from_i128(e, 100)
}

//================================================================
// Function to return MIN_CPOW_BASE constant
pub fn get_min_cpow_base(e: &Env) -> I256 {
    I256::from_i128(e, 1)
}

// Function to return MAX_CPOW_BASE constant
pub fn get_max_cpow_base(e: &Env) -> I256 {
    (2 * get_bone(e)) - I256::from_i128(e, 1)
}

// Function to return CPOW_PRECISION constant
pub fn get_cpow_precision(e: &Env) -> I256 {
    get_bone(e).div(&I256::from_i128(e, 1e10))
}

//================================================================
// Function to return MAX_IN_RATIO constant
pub fn get_max_in_ratio(e: &Env) -> I256 {
    get_bone(e).div(&I256::from_i128(e, 2))
}

// Function to return MAX_OUT_RATIO constant
pub fn get_max_out_ratio(e: &Env) -> I256 {
    (get_bone(e).div(&I256::from_i128(e, 3))).add(&I256::from_i128(e, 1))
}





