use soroban_sdk::{assert_with_error, Address, Env};

use crate::{
    c_consts::{MAX_FEE, MIN_FEE},
    c_pool::{
        error::Error,
        metadata::{
            read_finalize, write_controller, write_freeze, write_public_swap, write_swap_fee,
        },
    },
};

// Sets the swap fee, can only be set by the controller (pool admin)
pub fn execute_set_swap_fee(e: Env, fee: i128) {
    assert_with_error!(&e, fee >= 0, Error::ErrNegative);
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);
    assert_with_error!(&e, fee >= MIN_FEE, Error::ErrMinFee);
    assert_with_error!(&e, fee <= MAX_FEE, Error::ErrMaxFee);
    write_swap_fee(&e, fee);
}

// Sets the value of the controller address, only can be set by the current controller
pub fn execute_set_controller(e: Env, manager: Address) {
    write_controller(&e, manager);
}

pub fn execute_set_public_swap(e: Env, val: bool) {
    assert_with_error!(&e, !read_finalize(&e), Error::ErrFinalized);
    write_public_swap(&e, val);
}

pub fn execute_set_freeze_status(e: Env, val: bool) {
    write_freeze(&e, val);
}
