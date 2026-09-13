#![cfg(test)]
extern crate std;
use soroban_fixed_point_math::SorobanFixedPoint;
use soroban_sdk::Env;
use soroban_sdk::I256;

use crate::c_consts::{BONE, MAX_CPOW_EXP, MIN_WEIGHT, STROOP_SCALAR};
use crate::c_num::c_pow;

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
#[should_panic = "Error(Contract, #40)"]
fn test_c_pow_negative_exp() {
    let env = Env::default();
    c_pow(
        &env,
        &I256::from_i128(&env, BONE),
        &I256::from_i32(&env, -1),
        false,
    );
}

#[test]
#[should_panic = "Error(Contract, #40)"]
fn test_c_pow_high_exp() {
    let env = Env::default();
    c_pow(
        &env,
        &I256::from_i128(&env, BONE),
        &I256::from_i128(&env, MAX_CPOW_EXP + 1),
        false,
    );
}

#[test]
fn test_c_pow_exp_limit_covers_min_weight_reciprocal() {
    let env = Env::default();
    let bone = I256::from_i128(&env, BONE);
    let normalized_min_weight = I256::from_i128(&env, MIN_WEIGHT * STROOP_SCALAR);
    let reciprocal = bone
        .fixed_div_ceil(&env, &normalized_min_weight, &bone)
        .to_i128()
        .unwrap();

    assert_eq!(MAX_CPOW_EXP, reciprocal);
}

#[test]
fn test_c_pow_fractional_bounds() {
    let env = Env::default();
    // Exact floor and ceil values were calculated with 100-digit precision.
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
            100_000_000_000_000_000,
            500_000_000_000_000_000,
            316_227_766_016_837_933,
            316_227_766_016_837_934,
        ),
        (1, 500_000_000_000_000_000, 1_000_000_000, 1_000_000_000),
        (
            1_999_999_999_999_999_999,
            500_000_000_000_000_000,
            1_414_213_562_373_095_048,
            1_414_213_562_373_095_049,
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
        (BONE, BONE / 4, BONE, BONE),
        (BONE + 1, BONE / 4, BONE, BONE + 1),
        (BONE - 1, BONE / 4, BONE - 1, BONE),
    ];

    for (base, exp, expected_floor, expected_ceil) in cases {
        let base = I256::from_i128(&env, base);
        let exp = I256::from_i128(&env, exp);
        let lower = c_pow(&env, &base, &exp, false).to_i128().unwrap();
        let upper = c_pow(&env, &base, &exp, true).to_i128().unwrap();

        assert!(
            lower <= upper,
            "invalid interval: lower={lower} upper={upper}"
        );
        assert!(
            lower <= expected_floor,
            "lower bound exceeded exact floor: lower={lower} floor={expected_floor}"
        );
        assert!(
            upper >= expected_ceil,
            "upper bound fell below exact ceil: upper={upper} ceil={expected_ceil}"
        );
    }
}

#[test]
fn test_c_pow_pool_operating_band_tracks_signal() {
    let env = Env::default();
    env.cost_estimate().budget().reset_unlimited();

    // Successful pool operations are confined to a narrower band than c_pow's
    // validity domain. Measure uncertainty against the guaranteed movement
    // away from one used by pool formulas, not against the full power value.
    let bases = [
        BONE / 2,
        3 * BONE / 5,
        633 * BONE / 1000,
        3 * BONE / 4,
        BONE - 1,
        BONE,
        BONE + 1,
        4 * BONE / 3,
        3 * BONE / 2,
        8 * BONE / 5,
    ];
    let exponents = [
        BONE / 10,
        BONE / 9,
        BONE / 2,
        9 * BONE / 10,
        BONE,
        BONE + BONE / 9,
        11 * BONE / 2,
        9 * BONE,
        MAX_CPOW_EXP - BONE / 10,
        MAX_CPOW_EXP,
    ];

    for base in bases {
        for exp in exponents {
            let base_i256 = I256::from_i128(&env, base);
            let exp_i256 = I256::from_i128(&env, exp);
            let lower = c_pow(&env, &base_i256, &exp_i256, false).to_i128().unwrap();
            let upper = c_pow(&env, &base_i256, &exp_i256, true).to_i128().unwrap();
            let gap = upper - lower;
            let guaranteed_movement = if base > BONE {
                lower - BONE
            } else if base < BONE {
                BONE - upper
            } else {
                0
            };
            let power_relative_limit = upper / 1_000_000_000 + 1;
            let signal_relative_limit = guaranteed_movement / 100_000_000 + 16;
            let max_gap = core::cmp::min(power_relative_limit, signal_relative_limit);

            assert!(
                gap <= max_gap,
                "loose pool-domain interval: base={base} exp={exp} lower={lower} upper={upper} gap={gap} movement={guaranteed_movement} limit={max_gap}"
            );
        }
    }
}

#[test]
fn test_c_pow_first_term_convergence_rounds_toward_bound() {
    let env = Env::default();
    let quarter = I256::from_i128(&env, BONE / 4);

    // ceiling: series gives exactly BONE (term floors to 0) - one unit too low
    let base = I256::from_i128(&env, BONE + 1);
    assert_eq!(
        c_pow(&env, &base, &quarter, true).to_i128().unwrap(),
        BONE + 1
    );
    assert_eq!(c_pow(&env, &base, &quarter, false).to_i128().unwrap(), BONE);

    // floor: series gives BONE - 1e8 exactly - one unit too high
    let base = I256::from_i128(&env, BONE - 400_000_000);
    // The exact floor is BONE - 100_000_001; the formal term and tail bounds
    // conservatively place the returned lower bound one additional unit below it.
    assert_eq!(
        c_pow(&env, &base, &quarter, false).to_i128().unwrap(),
        BONE - 100_000_002
    );
    // The exact ceiling is BONE - 1e8; the accumulated error budget returns a
    // valid one-unit-loose upper bound.
    assert_eq!(
        c_pow(&env, &base, &quarter, true).to_i128().unwrap(),
        BONE - 100_000_000 + 1
    );

    let base = I256::from_i128(&env, BONE + 2);
    let exp = I256::from_i128(&env, 4 * BONE / 5);
    assert_eq!(c_pow(&env, &base, &exp, false).to_i128().unwrap(), BONE);
}

#[test]
fn test_c_pow_base_one_is_exact() {
    let env = Env::default();
    let base = I256::from_i128(&env, BONE);
    let exp = I256::from_i128(&env, BONE * 5 / 4);

    assert_eq!(c_pow(&env, &base, &exp, true).to_i128().unwrap(), BONE);
    assert_eq!(c_pow(&env, &base, &exp, false).to_i128().unwrap(), BONE);

    // and the neighbouring ratio BONE - 1 must stay at or below BONE when rounding up
    let base = I256::from_i128(&env, BONE - 1);
    assert_eq!(c_pow(&env, &base, &exp, true).to_i128().unwrap(), BONE - 1);
}
