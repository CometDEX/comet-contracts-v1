#![cfg(test)]
extern crate std;
use soroban_sdk::Env;
use soroban_sdk::I256;

use crate::c_consts::BONE;
use crate::c_num::c_pow;
use crate::tests::generated_c_pow_vectors::C_POW_HIGH_PRECISION_CASES;

#[test]
#[should_panic = "Error(Contract, #34)"]
fn test_c_pow_low() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i32(&env, 0),
        &I256::from_i32(&env, 2),
        false,
    );
}

#[test]
#[should_panic = "Error(Contract, #35)"]
fn test_c_pow_high() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i128(&env, 2 * BONE),
        &I256::from_i32(&env, 2),
        false,
    );
}

#[test]
fn test_c_pow_integer_rounding_direction() {
    let env = Env::default();
    let base = I256::from_i128(&env, BONE + 1);
    let exp = I256::from_i128(&env, 2 * BONE);

    assert_eq!(c_pow(&env, &base, &exp, false).to_i128().unwrap(), BONE + 2);
    assert_eq!(c_pow(&env, &base, &exp, true).to_i128().unwrap(), BONE + 3);
}

#[test]
fn test_c_pow_fractional_rounding_direction() {
    let env = Env::default();
    // Expected bounds were calculated with 100-digit decimal precision.
    let cases = [
        (
            750_000_000_000_000_000,
            1_250_000_000_000_000_000,
            697_953_644_326_574_699,
            697_953_644_326_574_700,
        ),
        (
            1_300_000_000_000_000_000,
            800_000_000_000_000_000,
            1_233_544_104_071_173_995,
            1_233_544_104_071_173_996,
        ),
        (
            999_999_580_000_000_000,
            1_250_000_000_000_000_000,
            999_999_475_000_027_562,
            999_999_475_000_027_563,
        ),
        (
            1_000_000_420_000_000_000,
            1_250_000_000_000_000_000,
            1_000_000_525_000_027_562,
            1_000_000_525_000_027_563,
        ),
    ];

    for (base, exp, expected_floor, expected_ceil) in cases {
        let base_256 = I256::from_i128(&env, base);
        let exp_256 = I256::from_i128(&env, exp);
        let rounded_down = c_pow(&env, &base_256, &exp_256, false).to_i128().unwrap();
        let rounded_up = c_pow(&env, &base_256, &exp_256, true).to_i128().unwrap();

        assert!(
            rounded_down <= expected_floor,
            "round down exceeded base={base} exp={exp}: result={rounded_down} floor={expected_floor}"
        );
        assert!(
            rounded_up >= expected_ceil,
            "round up fell below base={base} exp={exp}: result={rounded_up} ceil={expected_ceil}"
        );
    }
}

#[test]
fn test_c_pow_high_precision_corpus() {
    let env = Env::default();
    env.cost_estimate().budget().reset_unlimited();

    assert!(C_POW_HIGH_PRECISION_CASES.len() >= 1_000);
    for &(base, exponent, expected_floor, expected_ceil) in C_POW_HIGH_PRECISION_CASES {
        let base_256 = I256::from_i128(&env, base);
        let exponent_256 = I256::from_i128(&env, exponent);
        let rounded_down = c_pow(&env, &base_256, &exponent_256, false)
            .to_i128()
            .unwrap();
        let rounded_up = c_pow(&env, &base_256, &exponent_256, true)
            .to_i128()
            .unwrap();

        assert!(
            rounded_down <= expected_floor,
            "round down exceeded base={base} exponent={exponent}: result={rounded_down} floor={expected_floor}"
        );
        assert!(
            rounded_up >= expected_ceil,
            "round up fell below base={base} exponent={exponent}: result={rounded_up} ceil={expected_ceil}"
        );
        assert!(
            rounded_down <= rounded_up,
            "bounds crossed for base={base} exponent={exponent}: down={rounded_down} up={rounded_up}"
        );
    }
}

#[test]
#[should_panic = "Error(Contract, #18)"]
fn test_c_pow_rejects_unconverged_approximation() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i128(&env, BONE / 100),
        &I256::from_i128(&env, BONE / 5),
        false,
    );
}
