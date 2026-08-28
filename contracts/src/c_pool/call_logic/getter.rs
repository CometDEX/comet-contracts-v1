use soroban_sdk::{panic_with_error, Address, Env, Map};

use crate::{
    c_math::calc_spot_price,
    c_pool::{
        error::Error,
        metadata::{read_record, read_swap_fee},
        storage_types::Record,
    },
};

fn find_record(record: &Map<Address, Record>, token: Address) -> Result<Record, Error> {
    record.get(token).ok_or(Error::ErrNotBound)
}

fn require_record(e: &Env, record: &Map<Address, Record>, token: Address) -> Record {
    find_record(record, token).unwrap_or_else(|error| panic_with_error!(e, error))
}

pub fn execute_get_balance(e: Env, token: Address) -> i128 {
    require_record(&e, &read_record(&e), token).balance
}

pub fn execute_get_normalized_weight(e: Env, token: Address) -> i128 {
    require_record(&e, &read_record(&e), token).weight
}

// Calculate the spot considering the swap fee
pub fn execute_get_spot_price(e: Env, token_in: Address, token_out: Address) -> i128 {
    let record = read_record(&e);
    let in_record = require_record(&e, &record, token_in);
    let out_record = require_record(&e, &record, token_out);
    let swap_fee = read_swap_fee(&e);
    calc_spot_price(&in_record, &out_record, swap_fee)
}

// Get the spot price without considering the swap fee
pub fn execute_get_spot_price_sans_fee(e: Env, token_in: Address, token_out: Address) -> i128 {
    let record = read_record(&e);
    let in_record = require_record(&e, &record, token_in);
    let out_record = require_record(&e, &record, token_out);
    calc_spot_price(&in_record, &out_record, 0)
}

#[cfg(test)]
mod tests {
    use super::find_record;
    use crate::c_pool::{error::Error, storage_types::Record};
    use soroban_sdk::{testutils::Address as _, Address, Env, Map};

    #[test]
    fn test_find_record_reports_not_bound() {
        let e = Env::default();
        let token = Address::generate(&e);
        let missing = Address::generate(&e);
        let expected = Record {
            balance: 100,
            weight: 5_000_000,
            scalar: 1,
            index: 0,
        };
        let mut records = Map::new(&e);
        records.set(token.clone(), expected.clone());

        assert_eq!(find_record(&records, token), Ok(expected));
        assert_eq!(find_record(&records, missing), Err(Error::ErrNotBound));
    }
}
