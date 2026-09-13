# Comet Pool Public Entrypoint Proof Coverage

This document summarizes what the Lean project proves at the public-entrypoint boundary and why those results matter for pool arithmetic. “Covered” means Lean proves the stated property from a successful executable, source-shaped model of the relevant arithmetic or configuration path. The models are handwritten rather than extracted from Rust. See the [verification README](README.md) for the complete theorem graph and implementation-level proof obligations.

## At a glance

| Scope | Coverage | Principal result |
| --- | ---: | --- |
| `c_pow` asset-moving operations | 6 of 6 | The minimum configured fee dominates the complete certified pool-adverse arithmetic-error budget, making every computed amount strictly pool-favoring relative to the continuous fee-free ideal |
| Proportional liquidity operations | 2 of 2 | Directional rounding cannot undercharge a join or overpay an exit |
| Initialization | 1 of 1 | Successful modeled initialization establishes the checked configuration and record invariants |
| Spot-price getters | 2 of 2 | Successful active-pool calculations satisfy explicit error, fee, and post-swap monotonicity properties |
| Remaining pool-specific entrypoints | 0 of 8 | Administrative transitions and simple storage getters are not modeled |
| SEP-41 token methods | 0 of 10 | Intentionally out of scope |

Overall, 11 of the 19 pool-specific public entrypoints have source-shaped configuration or arithmetic proofs. These results concern successful computed amounts and configuration values; authorization, storage effects, external calls, transfers, LP-token minting and burning, TTL behavior, and events remain outside the machine-checked boundary unless stated otherwise.

## Results by asset-moving operation

For operations using `c_pow`, the percentages are strict bounds relative to the stated minimum-fee comparison value, not percentages of the operation amount, actual fee collected, or Soroban transaction fee. Separate fee-dominance theorems prove that the exact configured fee advantage covers each complete adverse-error budget. Proportional joins and exits do not use `c_pow`; their directional rounding gives zero pool-adverse arithmetic error.

| Public operation | Proven pool-adverse error bound | Net arithmetic result versus the continuous fee-free ideal |
| --- | ---: | --- |
| `swap_exact_amount_in` | `< 2.125%` of the minimum fee's spot-normalized output value | Computed output is strictly lower |
| `swap_exact_amount_out` | `< 4.501%` of the adjusted minimum fee's spot-normalized input value | Computed input is strictly higher |
| `dep_tokn_amt_in_get_lp_tokns_out` | `< 1.223%` of the weighted minimum-fee value | Computed LP output is strictly lower |
| `dep_lp_tokn_amt_out_get_tokn_in` | `< 1.107%` of the adjusted weighted minimum-fee value | Computed token input is strictly higher |
| `wdr_tokn_amt_in_get_lp_tokns_out` | `< 3.001%` of the weighted minimum-fee value | Computed token output is strictly lower |
| `wdr_tokn_amt_out_get_lp_tokns_in` | `< 4.751%` of the adjusted weighted minimum-fee value | Computed LP input is strictly higher |
| `join_pool` | `0%` adverse rounding | Every token input is at least its ideal proportional amount |
| `exit_pool` | `0%` adverse rounding | Every token output is at most its ideal proportional amount |

These results rule out the analyzed numerical failure mode on successful modeled paths: fixed-point rounding and finite-series approximation cannot consume the minimum configured fee advantage and give a caller a result better than the corresponding fee-free ideal.

## Additional verified properties

| Public entrypoint | Established machine-checked outcome |
| --- | --- |
| `init` | Enforces the modeled initialization guards; preserves token, weight, balance, queried-decimal, and index alignment; derives valid positive scalars; establishes the exact total weight and a positive configured initial LP mint amount |
| `get_spot_price` | Establishes checked representability and a two-sided error envelope; proves the fee-adjusted result is not below the zero-fee result, is monotone in the fee, and cannot decrease after the modeled swap balance update |
| `get_spot_price_sans_fee` | Inherits the checked representability and error envelope and proves that the zero-fee final division is an identity |

The initialization model does not cover the resulting persistent LP supply. The spot-price models require positive divisors for active token records and do not model record lookup.

## Security interpretation

For the six modeled `c_pow` operations, the machine-checked results rule out the analyzed numerical exploit class on every successful source-shaped path satisfying the stated configuration and domain assumptions: fixed-point rounding and finite-series approximation cannot consume the minimum configured fee advantage and give the caller a result better than the corresponding continuous fee-free ideal. The proportional join and exit results separately prove that their rounding cannot undercharge or overpay the caller, respectively. These conclusions provide strong assurance about the pool's arithmetic core, but they are not a proof that the deployed contract as a whole is secure or solvent.

The verification does not establish cross-call balance conservation, persistent-state invariant preservation, or whole-pool solvency because actual token transfers, LP-token minting and burning, and storage transitions are not modeled end to end. It also does not cover controller or freeze authorization, reentrancy or callback behavior, hostile external-token behavior, all failure and panic paths, resource-exhaustion or execution-cost bounds, compiler or Soroban runtime correctness, or broader economic attacks. The handwritten correspondence between the Rust implementation and Lean models remains a reviewed trust assumption. Consequently, these proofs complement rather than replace a contract audit, integration testing, and deployment-specific operational review.

The Lean project builds without `sorry`, `admit`, or project-defined axioms. The namespace-wide compiled-declaration audit allows Lean's standard `propext`, `Classical.choice`, and `Quot.sound` foundations plus the unsafe compiler-only `lcProof` placeholder used by generated `_cstage1` implementation declarations. Lean does not permit `lcProof` in kernel-checked theorem definitions, so the theorem trust base remains limited to the standard three foundations.

## Coverage inventory

### Covered pool entrypoints

- Configuration: `init`.
- Asset-moving arithmetic: `join_pool`, `exit_pool`, `swap_exact_amount_in`, `swap_exact_amount_out`, `dep_tokn_amt_in_get_lp_tokns_out`, `dep_lp_tokn_amt_out_get_tokn_in`, `wdr_tokn_amt_in_get_lp_tokns_out`, and `wdr_tokn_amt_out_get_lp_tokns_in`.
- Price arithmetic: `get_spot_price` and `get_spot_price_sans_fee`.

### Pool entrypoints not covered

| Public entrypoint | Missing machine-checked composition |
| --- | --- |
| `set_controller`, `set_freeze_status` | Authorization and persistent controller or freeze-state transitions |
| `get_total_supply` | Correspondence between persistent `TotalShares` and the returned value; initialization proves only that the configured mint amount is positive |
| `get_controller`, `get_tokens`, `get_balance` | Correspondence between stored values or records and public return values |
| `get_normalized_weight` | Stored-record lookup and public return correspondence; initialization separately proves modeled initial weight bounds |
| `get_swap_fee` | Stored-value lookup and public return correspondence; initialization separately proves the modeled initial fee bounds |

### SEP-41 methods intentionally out of scope

`allowance`, `approve`, `balance`, `transfer`, `transfer_from`, `burn`, `burn_from`, `decimals`, `name`, and `symbol` are not modeled. Their allowance and balance storage, authorization, expiry, conservation, total-supply, metadata, and event properties remain outside this project.

<details>
<summary><strong>Principal theorem index</strong></summary>

| Public entrypoint | Principal Lean result |
| --- | --- |
| `init` | `initializationExecution_establishes_invariants` |
| `join_pool` | `joinPoolExecution_every_token_cannot_undercharge` |
| `exit_pool` | `exitPoolExecution_every_token_cannot_overpay` |
| `swap_exact_amount_in` | `calc_token_out_given_token_in_execution_adverse_error_lt_precise_fee_share`; `calc_token_out_given_token_in_execution_is_pool_favoring` |
| `swap_exact_amount_out` | `calc_token_in_given_token_out_execution_adverse_error_lt_precise_fee_share`; `calc_token_in_given_token_out_execution_is_pool_favoring` |
| `dep_tokn_amt_in_get_lp_tokns_out` | `calc_lp_token_amount_given_token_deposits_in_execution_adverse_error_lt_precise_fee_share`; `calc_lp_token_amount_given_token_deposits_in_execution_is_pool_favoring` |
| `dep_lp_tokn_amt_out_get_tokn_in` | `calc_token_deposits_in_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share`; `calc_token_deposits_in_given_lp_token_amount_execution_is_pool_favoring` |
| `wdr_tokn_amt_in_get_lp_tokns_out` | `calc_token_withdrawal_amount_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share`; `calc_token_withdrawal_amount_given_lp_token_amount_execution_is_pool_favoring` |
| `wdr_tokn_amt_out_get_lp_tokns_in` | `calc_lp_token_amount_given_token_withdrawal_amount_execution_adverse_error_lt_precise_fee_share`; `calc_lp_token_amount_given_token_withdrawal_amount_execution_is_pool_favoring` |
| `get_spot_price` | `calc_spot_price_execution_error_bounds`; `successful_get_spot_price_not_below_sans_fee`; `successful_spot_price_is_monotone_in_fee`; `successful_spot_price_does_not_decrease_after_swap_balance_update` |
| `get_spot_price_sans_fee` | `calc_spot_price_execution_error_bounds`; `SuccessfulSpotPriceRun.sans_fee_returns_ratio` |

</details>

## Shared proof foundation

The `c_pow` entrypoint results above share machine-checked generalized-binomial direction proofs, a concrete three-floor recurrence-error budget, upper-rounded exponentiation-by-squaring refinements, configured exponent limits, and convergence within 46 iterations throughout the supported `[0.5, 1.6]` operating band. Entrypoint-specific low-base cases that can fall outside that band are handled separately by pool-favoring theorems or an explicit bounded execution trace.

The checked i128 and signed-I256 refinements are imported from the pinned `soroban-fixed-point-math` verification dependency. The generated Lean constants bind the proofs to the production Rust configuration, including ratios, weights, fees, precision, iteration and exponent limits, minimum balance, and configured initial mint amount.

## Appendix: Terminology

### Error direction

**Ideal value.** The result of the corresponding continuous real-arithmetic formula, before fixed-point truncation, directional rounding, or finite-series approximation. It is the mathematical reference used by the error theorems, not an independently executable contract path.

**Computed value.** The result returned by the successful source-shaped Lean model of the contract arithmetic. A theorem about a computed value assumes that the model returns `some`, so every modeled checked operation and guard succeeded.

**Approximation error.** The difference between the computed and ideal values that can arise from the finite `c_pow` series and its fixed-point recurrence. Entrypoint theorems compare the full source-shaped arithmetic path, so their bounds also account for surrounding floors and ceilings; those operations are separately shown to round in the pool's favor where claimed.

**Pool-adverse approximation error.** The positive part of the computed-versus-ideal gap in the direction that benefits the caller at the pool's expense. For a fixed-input operation, this is excess computed output, `max(computedOutput - idealOutput, 0)`. For a fixed-output operation, this is deficient computed input, `max(idealInput - computedInput, 0)`. Thus a join is adverse if it requires too little token input, while an exit is adverse if it returns too much token output. A zero adverse error means the approximation is exact or pool-favoring; it does not mean the absolute approximation error is zero.

**Pool-favoring error.** Error in the opposite direction: the caller receives no more than the ideal output or supplies no less than the ideal input. Pool-favoring error may still be nonzero as an absolute numerical error.

**Absolute error.** The unsigned magnitude `|computed - ideal|`, irrespective of who benefits. The percentage bounds in this verification concern only pool-adverse error unless a theorem explicitly says otherwise.

### Fee comparison scale

**Minimum fee rate.** The contract configuration floor `MIN_FEE / STROOP = 1 / 1,000,000`, or `10^-6` of the relevant nominal amount. This is the pool's minimum swap-fee rate, not the Soroban transaction fee paid for ledger execution.

**Nominal ratio.** The operation's unadjusted amount divided by its relevant reserve balance or LP-token supply. It is the dimensionless first-order movement used when expressing the fee and approximation error on a common scale.

**Spot-normalized.** Converted into the same output, input, or LP-token unit as the error using the invariant's local first-order slope at the pre-operation state. This is a mathematical normalization; it does not use an oracle price.

**Minimum fee's spot-normalized value.** A conservative comparison scale obtained by applying the minimum fee rate to the nominal operation size and converting that amount into the theorem's error unit at the invariant's local spot slope. For example, the exact-input swap scale in output-token units is `MIN_FEE_RATE * outputBalance * (inputWeight / outputWeight) * (inputAmount / inputBalance)`. It is not the Soroban transaction fee and is not necessarily the exact fee amount collected by a particular execution; configured swap fees can be higher and integer fee rounding is modeled separately where relevant.

**Adjusted minimum-fee value.** The corresponding minimum-fee comparison scale after including a path-specific source adjustment. In exact-output paths, for example, the contract grosses up the input by dividing through `1 - feeRate`, so the comparison scale includes the same denominator while retaining `MIN_FEE_RATE` as its fee-rate numerator.

**Weighted minimum-fee value.** A minimum-fee comparison scale multiplied by the normalized weight or exponent factors required to express the fee's local effect in the same unit as the entrypoint's adverse error. The exact factor is stated by each theorem rather than assumed to be identical across operations.

**“Less than _p_% of the minimum fee.”** Shorthand for a proved inequality of the form `poolAdverseError < (p / 100) * minimumFeeComparisonValue` on the theorem's stated positive domain. It compares an error with a conservative value derived from the minimum fee; it does not assert that the approximation error is _p_% of the actual fee charged in every execution.

**Fee-free ideal.** The operation's continuous real-valued invariant formula evaluated with fee rate zero, while keeping the same balances, weights, supply, and nominal input or output ratio. It is a mathematical reference value rather than an alternate executable contract path.

**Exact fee advantage.** The directional difference between the fee-adjusted continuous ideal and its fee-free counterpart: reduced ideal output for a fixed-input operation or increased ideal input for a fixed-output operation.

**Fee dominance.** A proved inequality showing that the exact fee advantage is at least the operation's complete certified pool-adverse arithmetic-error budget. Combined with the strict adverse-error bound, it proves that a successful computed fixed-input output is strictly below its fee-free ideal, or that a successful computed fixed-output input is strictly above its fee-free ideal. This comparison is about arithmetic amounts and does not extend the model to transfers, minting, burning, storage, or authorization.

### Arithmetic and proof scope

**`BONE` and one raw unit.** `c_pow` uses `BONE = 10^18` as its fixed-point representation of one. One raw unit therefore represents `10^-18` in the dimensionless `c_pow` value before any entrypoint-specific token scaling.

**Supported operating band.** The proved `c_pow` base interval `[0.5, 1.6]`, within which the baseline series reaches its stopping threshold in at most 46 iterations. Entrypoint-specific low-base cases outside that interval are covered only where the table identifies a separate pool-favoring theorem or bounded execution trace.

**Source-shaped model.** A handwritten Lean function that mirrors the production Rust operation order, checked-arithmetic failures, and branch structure closely enough to compose the arithmetic lemmas at the public-entrypoint boundary. It is not automatically extracted from Rust, so the correspondence assumptions listed in this document remain part of the trusted boundary.

**Machine-checked.** Accepted by the pinned Lean toolchain and declared dependencies without `sorry`, `admit`, or project-defined axioms. The CI namespace audit permits the compiler-only `lcProof` placeholder in generated executable declarations, but Lean excludes that unsafe constant from kernel-checked theorem definitions. This establishes the stated theorem about the Lean model; it does not by itself establish authorization, storage, token-transfer, event, TTL, compiler, runtime, or Rust-to-Lean translation correctness.
