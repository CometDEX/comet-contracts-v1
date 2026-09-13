# Machine-checked c_pow lemmas

This Lean project machine-checks the `c_pow` recurrence-error budget, geometric-tail simplification, operating-band convergence, composition, configured limits, and application-specific signed-`I256` magnitude and denominator bounds used by `contracts/CPOW_BOUNDS.md`.

The checked-in Lean constants are generated from the production Rust constants,
so the proof cannot silently keep using old pool ratios, fees, weights,
precision, exponent, or iteration limits. From the repository root, check that
the generated module is current with:

```sh
rustc --edition=2021 verification/generate_constants.rs -o /tmp/generate-cpow-constants
/tmp/generate-cpow-constants --check verification/CometCPow/GeneratedConstants.lean
```

To regenerate it after changing a source constant, replace the `--check` line
with:

```sh
/tmp/generate-cpow-constants > verification/CometCPow/GeneratedConstants.lean
```

Then run the proofs with:

```sh
cd verification
lake update
lake build
```

The project pins Lean and mathlib to version 4.19.0. The
`c_pow formal verification` workflow first rejects a stale generated constants
module, then runs the build for every relevant pull-request change and rejects
proof sources containing `sorry`, `admit`, or custom `axiom` declarations. It
also audits the compiled `CometCPow` namespace transitively, allowing only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

The verification project is development-only. It is not a dependency of any
Rust crate and does not alter the contract's instructions, memory use, or WASM
size.

## Checked claims

| Proof obligation | Lean theorem |
| --- | --- |
| Mathematical floor/ceiling errors are below one raw unit | `floor_isFloor`, `ceil_isCeil`, `IsFloor.abs_error_lt_one`, `IsCeil.abs_error_lt_one` |
| One recurrence step adds less than three raw units | `recurrence_increment_lt_three` |
| The raw recurrence inequality implies the `3k - 2` term budget through iteration 50 | `recurrence_error_budget` |
| The summed scalar budgets equal `(3N² - N) / 2` | `sum_error_budget` |
| `q / (1 - q) <= 1` when `q <= 1/2` | `geometric_tail_le_current` |
| The fractional binomial recurrence implies the exact-term bound `abs(Tₙ) <= S qⁿ` | `fractional_binomial_factor_le_one`, `fractional_binomial_step_contracts`, `fractional_binomial_terms_geometric_bound` |
| Production input/output ratios, fees, and weights retain the `[0.5, 1.6]` operating envelope | Generated `MAX_IN_RATIO`, `MAX_OUT_RATIO`, `MAX_FEE`, and `MAX_WEIGHT`; the `configured_*_margin` and `configured_*_base_*` lemmas in `PoolConfig.lean` |
| Every base in `[0.5, 1.6]` satisfies `abs(x) <= 3/5` | `operating_base_implies_abs_x_le_three_fifths` |
| The computed term reaches production precision by iteration 46 throughout `[0.5, 1.6]`, before the configured cap | `pool_operating_band_numeric_margin`, `pool_operating_band_iteration_within_cap`, `pool_operating_band_converges_by_iteration_46`, `pool_operating_base_converges_by_iteration_46` |
| Non-negative directed bounds compose under multiplication | `mul_lower_bound`, `mul_upper_bound` |
| The production Rust precision, exponent, scale, pool-configuration, and iteration constants discharge the proof premises | Generated constants in `GeneratedConstants.lean`; `configured_exponent_limit`, `term_error_at_iteration_cap`, `real_scale_exceeds_term_error_cap`, `sum_error_at_iteration_cap` |
| The final conservative raw product and every recurrence denominator fit signed 256-bit arithmetic | `final_raw_product_fits_i256`, `cpow_raw_magnitude_bound_fits_i256`, `cpow_denominator_bound_fits_i256`, `cpow_denominator_fits_i256` |

## Fixed-point implementation refinement

The reusable checked-`I256` model and proofs that the positive-denominator `I256` algorithms refine mathematical floor and ceiling are maintained alongside `src/i256.rs` on the companion `proof/formalize-i256-fixed-point` branch of `soroban-fixed-point-math`, pinned here to proof commit [`649f02a`](https://github.com/blnt-protocol/soroban-fixed-point-math/commit/649f02aab503e0502f495b64de5575da2c28434b). That proof commit is based on `script3` upstream commit `c85960e`; its source is byte-for-byte identical to the implementation shipped by the exact `soroban-fixed-point-math` 1.5.0 dependency pinned here. This project retains only the `c_pow`-specific magnitude and denominator bounds.

All production fixed-point denominators in `c_pow` are positive. Negative-denominator behavior is therefore outside the proof composition required by this contract.

## Assurance boundary

This project checks supporting mathematical and bounded-integer lemmas, but it does not yet establish the complete `c_pow` postcondition. The remaining work is to formalize the generalized binomial series and its equality to real exponentiation, instantiate the recurrence lemmas for every branch of an executable `c_pow` model, mechanically compose this project's operating bounds with the upstream fixed-point refinement theorems, and connect that model to the Rust control flow. The upstream Rust-to-Lean source correspondence is reviewed rather than produced by verified Rust extraction, and primitive Soroban host operations are trusted to satisfy their protocol-specified checked-integer semantics. Until those links are completed, `contracts/CPOW_BOUNDS.md` remains a human-reviewed proof argument rather than a fully machine-checked proof of the deployed contract.
