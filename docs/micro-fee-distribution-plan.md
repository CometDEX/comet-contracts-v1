# Swap Fee Recipient Distribution

## Context
- `contracts/src/c_pool/call_logic/pool.rs` remains the central entry point for swap flows (`execute_swap_exact_amount_in` / `..._out`).
- Dynamic swap fees (`read_swap_fee`, `SwapFeeConfig`) still govern the AMM fee curves and must execute before any recipient distribution.
- Helper utilities (`pull_underlying`, `push_underlying`) and record bookkeeping (`DataKey::AllRecordData`) continue to encapsulate token movement and accounting.
- Events (`SwapEvent`, `DepositEvent`, `WithdrawEvent`) remain unchanged; downstream will infer fee distribution from existing token transfer events.

## Goal
Add a fee-recipient mechanism that carves out the pool's `min_fee` share of swap volume after the AMM fee is applied and routes it first to pool-configured recipients and then to optional trade-scoped recipients supplied with each swap call. The mechanism must run whenever the configured fee asset participates in the swap (either coming from or going to the trader) and otherwise leave the swap untouched.

## Scope
- Swaps only. Deposits, withdrawals, and other flows stay unchanged.
- Fees are always taken on both swap legs (exact-in and exact-out); there is no configuration to disable either direction.
- Each pool can define at most one `FeeRule`. The fee asset must be one of the pool's bound tokens.
- If a swap does not involve the fee asset, the rule is skipped entirely for that trade.
- Precision for all percentage math matches the existing STROOP-based scaling used for AMM fees (where `STROOP = 10_000000` represents 100%).

## Requirements & Constraints
- Fee distributions draw exclusively from the pool's configured `min_fee` portion; dynamic fees above `min_fee` remain in the pool.
- Limit checks (`max_amount_in`, `min_amount_out`, price bounds) remain unchanged; micro-fee distributions must not alter trader-facing amounts.
- Input and output AMM math must complete first; the recipient fee is calculated on the post-AMM amounts that would otherwise move between the trader and the pool.
- Pool-level recipient percentages represent desired slices of the min-fee share and must cumulatively stay at or below 100%.
- The recipient list is capped at 5 entries (`MAX_FEE_RECIPIENTS = 5`). Initialization fails if the list exceeds the cap.
- Rounding must never overdraw the pool or trader balances. Any residual dust from flooring operations should remain in the pool.
- Swap entry points accept an optional list of per-trade recipients (max 5) that are applied after pool-level recipients.

## Data Model Additions
```
#[contracttype]
pub struct FeeRecipient {
    pub recipient: Address,
    pub percent: i128, // STROOP precision; 10_000000 == 100%
}

#[contracttype]
pub struct FeeRule {
    pub fee_asset: Address,          // must be bound in the pool
    pub recipients: Vec<FeeRecipient>,
}
```
- Store the optional rule under `DataKey::FeeRule`, keyed globally per pool.
- The contract address remains the custodian of collected amounts until distribution transfers execute.
- Only one fee rule may exist per pool; setting a new rule replaces the prior definition.
- Introduce system constants: `MAX_FEE_RECIPIENTS` (applies to both pool-level and trade-level recipient vectors).
- Percent values represent desired shares of the `min_fee` captured in order and may sum to less than (but not more than) 100%.

## Configuration Interface
- `__constructor(initial_rule: Option<FeeRule>)`
  - Applies the same validation used for rule replacement when `Some(rule)` is supplied.
  - Stores the validated rule immediately so pools can launch with recipients preconfigured.
- Controller-only entry points:
  - `replace_fee_rule(rule: FeeRule)`
  - `clear_fee_rule()`
- Public getter:
  - `get_fee_rule() -> Option<FeeRule>`
- Validation during `__constructor` (when `initial_rule.is_some()`) and `replace_fee_rule`:
  - `rule.fee_asset` must be present in `read_tokens`.
  - `recipients` length `> 0` and `<= MAX_FEE_RECIPIENTS`.
  - Each `recipient.percent` is `> 0`.
  - Sum of `recipient.percent` across the pool rule must be `> 0` and `<= STROOP`.
  - Rejected if any duplicate `recipient` addresses exist.
  - Rejected if any `recipient` is the self address of the contract
- `clear_fee_rule` deletes the entire rule. Partial updates are modelled as `replace_fee_rule` with a freshly prepared vector; callers should construct the complete list on every change to guarantee the sum check.

## Swap Interface Updates
- `swap_exact_amount_in` and `swap_exact_amount_out` accept an optional `Vec<FeeRecipient>` describing trade-scoped recipients (max 5).
- Trade recipients follow the same percent semantics as pool recipients and are applied only to whatever min-fee balance remains after the pool rule executes.
- Input validation enforces the same bounds as the pool rule (percent > 0, cumulative percent across the provided vector `<= STROOP`, no duplicates).

## Execution Flow Updates
1. **Determine rule applicability.**
   - When a swap starts, load the pool-level `FeeRule` (if any).
   - Identify whether the fee asset matches the token the trader sends or receives. If neither leg matches, skip the fee logic and continue the swap unchanged.
2. **Run existing AMM logic.**
   - Execute current fee calculations (`min_fee`, `max_fee` interpolation) and inventory checks to obtain `gross_amount_in` / `gross_amount_out` as today.
3. **Compute fee recipient slice.**
   - Let `leg_amount` be the amount of the fee asset moving between the trader and the pool (post-AMM fee).
   - Read `min_fee_percent` from the stored `SwapFeeConfig` and compute `fee_total = fixed_mul_floor(leg_amount, min_fee_percent, STROOP)`.
   - Compute the pool leg first to preserve existing AMM precision, then treat `fee_total` as the portion available for distribution.
   - Build a priority list by concatenating pool-level recipients (in stored order) with any trade-level recipients supplied in the call.
   - Walk the list in order, granting each recipient up to its requested percentage of the original `fee_total` while capping the payout by whatever balance remains; stop when no fee remains.
4. **Update bookkeeping.**
   - Limit and price checks remain unchanged because trader-facing amounts do not change.
   - Track the portion actually transferred (excluding pool-retained or failed payouts) and reduce the in-memory pool record for the fee asset before persisting balances; any leftover stays in the pool balance.
5. **Distribute fees.**
   - Attempt token transfers for each granted payout from the contract address to the recipient (`fee_asset`), skipping any failures and leaving any untransferred remainder in the pool.
   - Swap events remain unchanged; analytics rely on emitted token transfer logs.

## Helper Utilities
- `fn compute_fee_distribution(rule_recipients: &[FeeRecipient], trade_recipients: Option<&[FeeRecipient]>, min_fee_percent: i128, leg_amount: i128) -> Vec<(Address, i128)>` iterates recipients in priority order, applies cap-by-remaining logic, and returns the concrete payouts while leaving dust in the pool.
- `fn apply_fee_on_leg(e: &Env, rule: &Option<FeeRule>, trade_recipients: Option<&Vec<FeeRecipient>>, leg: SwapLeg, leg_amount: i128) -> Vec<(Address, i128)>` gathers the correct leg amount, calls `compute_fee_distribution`, and accounts for the fee asset balance deltas.
- `fn distribute_fee(e: &Env, fee_asset: &Address, payouts: &[(Address, i128)])` attempts fallible transfers for each payout and leaves any failed amounts in the pool.

## Testing Strategy
- Unit tests:
  - `compute_fee_distribution` rounding behaviour when funded by `min_fee`, dust retention, and partial fulfilment when cumulative percentages exceed the remaining balance.
  - Validation failures: over-cap recipients, percent sum mismatch, zero percent, duplicate addresses, percent exceeding `STROOP`.
- Swap flow tests:
  - No rule configured (regression).
  - Pool-only recipients consuming partial min-fee, leaving remainder with the pool.
  - Trade-supplied recipients sharing the residual min-fee and gracefully handling requests larger than the remaining balance.
  - Swap between tokens that do not include the fee asset: confirm fee logic is bypassed.
  - Exact-out route ensuring overall swap invariants hold while distributions pull from the min-fee portion.
- Stress tests for configuration updates to ensure re-validation runs after every change.

## Deployment & Migration
- The storage key is lazy-initialized on first `set_fee_rule`. No migration is necessary for existing pools.
- Operational rollout mirrors current patterns: deploy updated contract, run smoke swaps without rules, then stage fee rule activation per pool.
- Automation scripts should be updated to include rule management and to verify 100% recipient totals before pushing configs on-chain.

## Risks & Mitigations
- **Configuration mistakes:** Hard validation for percent caps, cumulative totals, and duplicate addresses prevents over-allocation across both pool and trade recipients; provide an off-chain helper to preview allocations.
- **Integrator clarity:** Document that micro-fee distributions draw from pool revenue only, leaving trader-facing limits intact; SDKs should highlight that transfers to recipients come from the contract address.
- **Rounding dust & transfer failures:** Fee splits use floor rounding and leave any dust or failed-transfer amounts in the pool, preventing overdraws while keeping math deterministic.
- **Unexpected asset routes:** Skipping the fee whenever the fee asset is absent avoids draining unrelated pool balances or locking trades.

## Decisions
- Cap both pool-configured and trade-supplied recipient lists at 5 entries each (`MAX_FEE_RECIPIENTS = 5`).
- Distribute only the pool's `min_fee` portion by applying pool recipients first and trade recipients second; any excess stays with the pool.
- Leave `SwapEvent` unchanged and rely on existing `token.transfer` events for analytics instrumentation.
- Build a dedicated test suite exercising min-fee-funded priority splits and per-recipient outcomes for the micro-fee feature.
- Leave rounding dust in the pool; no carry-forward tracking required.

## Next Steps
1. Implement data model definitions in `storage_types.rs` with the new constants.
2. Wire the constructor and controller entry points with the validation logic summarised above.
3. Update swap execution (and swap method signatures) to accept trade recipients and carve out the min-fee-funded distribution after the AMM fee is applied.
