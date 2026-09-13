//! Comet Pool Arithmetic Primitives

use c_consts::BONE;
use soroban_fixed_point_math::SorobanFixedPoint;
use soroban_sdk::{assert_with_error, unwrap::UnwrapOptimized, Env, I256};

use crate::{
    c_consts::{self, CPOW_PRECISION, MAX_CPOW_BASE, MAX_CPOW_EXP, MAX_CPOW_ITERS, MIN_CPOW_BASE},
    c_pool::error::Error,
};

/// Perform a - b, or panic if a < b
pub fn sub_no_negative(e: &Env, a: &I256, b: &I256) -> I256 {
    assert_with_error!(e, a >= b, Error::ErrSubUnderflow);
    a.sub(&b)
}

/// Calculate base^exp where base and exp are fixed point numbers with 18 decimals.
///
/// Approximates the result such that:
/// -> base^(int exp) * approximate of base^(decimal exp)
///
/// Returns an upper bound when `round_up` is true and a lower bound otherwise.
///
/// Aborts with `ErrCPowExpOutOfRange` if the exponent invariant is violated.
/// This is not expected to occur through valid pool operations.
pub fn c_pow(e: &Env, base: &I256, exp: &I256, round_up: bool) -> I256 {
    assert_with_error!(
        e,
        base >= &I256::from_i128(e, MIN_CPOW_BASE),
        Error::ErrCPowBaseTooLow
    );
    assert_with_error!(
        e,
        base <= &I256::from_i128(e, MAX_CPOW_BASE),
        Error::ErrCPowBaseTooHigh
    );

    let bone = I256::from_i128(e, BONE);
    let zero = I256::from_i32(e, 0);
    // Pool initialization constrains token weights so every exponent constructed
    // by c_math is in [0, MAX_CPOW_EXP]. Failure indicates invalid stored state or
    // an internal configuration/math bug.
    assert_with_error!(
        e,
        exp >= &zero && exp <= &I256::from_i128(e, MAX_CPOW_EXP),
        Error::ErrCPowExpOutOfRange
    );
    if base == &bone || exp == &zero {
        return bone;
    }
    let int = exp.div(&bone);
    let remain = exp.sub(&int.mul(&bone));
    let whole_pow = c_powi(
        e,
        &base,
        &(int.to_i128().unwrap_optimized() as u32),
        round_up,
    );
    if remain == I256::from_i128(e, 0) {
        return whole_pow;
    }
    let partial_result = c_pow_approx(
        e,
        &base,
        &remain,
        &I256::from_i128(e, CPOW_PRECISION),
        round_up,
    );
    if round_up {
        whole_pow.fixed_mul_ceil(e, &partial_result, &bone)
    } else {
        whole_pow.fixed_mul_floor(e, &partial_result, &bone)
    }
}

/// Upper bound for the magnitude of the current exact binomial-series term.
fn term_magnitude_bound(e: &Env, term: &I256, term_error: &I256) -> I256 {
    let zero = I256::from_i32(e, 0);
    let abs_term = if term < &zero {
        zero.sub(term)
    } else {
        term.clone()
    };
    abs_term.add(term_error)
}

/// Upper bound for the magnitude of the next exact binomial-series term.
///
/// For fractional `a` and `k >= 1`, the exact magnitude ratio is strictly below
/// `abs(x)`, where all values are scaled by `BONE`.
fn next_term_magnitude_bound(
    e: &Env,
    term: &I256,
    term_error: &I256,
    abs_x: &I256,
    bone: &I256,
) -> I256 {
    term_magnitude_bound(e, term, term_error).fixed_mul_ceil(e, abs_x, bone)
}

// Calculate a^n where n is an integer
fn c_powi(e: &Env, a: &I256, n: &u32, round_up: bool) -> I256 {
    let bone = I256::from_i128(e, BONE);
    let mut z = if n % 2 != 0 { a.clone() } else { bone.clone() };

    let mut a = a.clone();
    let mut n = n / 2;
    while n != 0 {
        a = if round_up {
            a.fixed_mul_ceil(e, &a, &bone)
        } else {
            a.fixed_mul_floor(e, &a, &bone)
        };
        if n % 2 != 0 {
            z = if round_up {
                z.fixed_mul_ceil(e, &a, &bone)
            } else {
                z.fixed_mul_floor(e, &a, &bone)
            };
        }
        n = n / 2
    }
    z
}

/// Bound `(1 + x)^exp` for `-1 < x < 1` and `0 < exp < 1`.
///
/// The expensive recurrence remains single-sided. A small analytic error budget
/// encloses its fixed-point floors, and the omitted series is enclosed using the
/// alternating-series theorem (`x > 0`) or a geometric majorant (`x < 0`). See
/// `CPOW_BOUNDS.md` for the proof.
fn c_pow_approx(e: &Env, base: &I256, exp: &I256, precision: &I256, round_up: bool) -> I256 {
    // term 0
    let bone = I256::from_i128(e, BONE);
    let zero = I256::from_i32(e, 0);
    let n_1 = I256::from_i32(e, -1);
    let x = base.sub(&bone);
    let mut term = bone.clone();
    let mut sum = term.clone();
    let prec = precision.clone();
    // Capped to limit iterations in the event of a poor approximation. The
    // remainder bound below remains valid even when this cap is reached.
    // Max resource impact at 50 iterations:
    //  -> CPU: 5M inst
    //  -> Mem: 150 kB
    let mut iters: i128 = 0;
    for i in 1..=MAX_CPOW_ITERS {
        iters = i;
        let big_k = I256::from_i128(e, i * BONE);
        let c = exp.sub(&big_k.sub(&bone));
        term = term.fixed_mul_floor(e, &c.fixed_mul_floor(e, &x, &bone), &bone);
        term = term.fixed_div_floor(e, &big_k, &bone);
        sum = sum.add(&term);

        let abs_term = if term < zero {
            term.mul(&n_1)
        } else {
            term.clone()
        };
        if abs_term <= prec {
            break;
        }
    }
    // If T_k is the exact scaled term and t_k is the computed term, then
    // |T_1 - t_1| < 1 and |T_k - t_k| < 3k - 2. Summing those per-term bounds
    // gives |S_k - s_k| < (3k^2 - k) / 2. Keep the error as a cheap scalar and
    // construct only the I256 bounds required by the selected return path.
    let sum_error = (3 * iters * iters - iters) / 2;

    if round_up {
        let mut upper = sum.add(&I256::from_i128(e, sum_error));
        if x > zero {
            // For x > 0 the exact terms alternate with decreasing magnitude.
            // The next term is positive exactly when the iteration count is
            // even, and its magnitude is bounded by the current term.
            if iters % 2 == 0 {
                let term_error = I256::from_i128(e, 3 * iters - 2);
                let tail = term_magnitude_bound(e, &term, &term_error);
                upper = upper.add(&tail);
            }
            upper
        } else {
            // For x < 0 every non-constant exact term is negative, so every
            // exact partial sum is an upper bound. A positive exponent also
            // preserves base < 1.
            if upper > bone {
                bone
            } else {
                upper
            }
        }
    } else {
        // For N = 1, t_1 is an exact floor and the computed partial sum is
        // already a lower bound. Later partial sums use the symmetric bound.
        let mut lower = if iters == 1 {
            sum
        } else {
            sum.sub(&I256::from_i128(e, sum_error))
        };

        if x > zero {
            // For x > 0 the exact terms alternate with decreasing magnitude.
            // The next term is negative exactly when the iteration count is
            // odd, so only those paths require a tail object.
            if iters % 2 != 0 {
                let term_error = I256::from_i128(e, 3 * iters - 2);
                let tail = if iters == 1 {
                    next_term_magnitude_bound(e, &term, &term_error, &x, &bone)
                } else {
                    term_magnitude_bound(e, &term, &term_error)
                };
                lower = lower.sub(&tail);
            }
            // A positive exponent preserves base > 1.
            if lower < bone {
                bone
            } else {
                lower
            }
        } else {
            // Successive term magnitudes have ratio < q = |x|. Thus the
            // omitted tail is at most |T_k| q / (1 - q).
            let term_error = I256::from_i128(e, 3 * iters - 2);
            let current_term = term_magnitude_bound(e, &term, &term_error);
            let abs_x = zero.sub(&x);
            let tail = if iters > 1 && abs_x <= I256::from_i128(e, BONE / 2) {
                // q / (1 - q) <= 1, so the current term bounds the tail.
                current_term
            } else {
                let next_term = current_term.fixed_mul_ceil(e, &abs_x, &bone);
                let one_minus_q = bone.sub(&abs_x);
                next_term.fixed_div_ceil(e, &one_minus_q, &bone)
            };
            lower = lower.sub(&tail);
            if lower < zero {
                zero
            } else {
                lower
            }
        }
    }
}
