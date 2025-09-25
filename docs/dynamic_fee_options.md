# Dynamic Fee Options

## Background
- Pools historically persisted a single static `swap_fee` via `DataKey::SwapFee`. That value was written during initialization and reused across all swap/join/exit flows.
- The latest revision replaces that scalar with a `SwapFeeConfig` instance stored under `DataKey::SwapFeeConfig`, enabling min/max fee bounds, tracked token selection, and balance thresholds.
- Runtime math in `contracts/src/c_math.rs` still consumes a single fee per call, but call logic now derives that fee dynamically via `metadata::read_swap_fee` before invoking the math helpers.

## Implemented Approach (Option 1)
- `SwapFeeConfig { min_fee, max_fee, tracked_token, low_util_balance, high_util_balance }` is written at init time and can be fetched via `get_swap_fee_config`.
- `metadata::read_swap_fee(&Env)` computes the current fee by:
  - Pulling the tracked token record, scaling its balance to 18 decimals with the stored `scalar`.
  - Clamping the balance between the configured thresholds and deriving a utilization ratio in STROOP precision.
  - Linearly interpolating between `max_fee` and `min_fee` based on that ratio (ratio = 0 → `max_fee`, ratio = STROOP → `min_fee`).
- All swap/join/exit pathways (`contracts/src/c_pool/call_logic/pool.rs`) continue to read a single fee value, but it now reflects live utilization.
- Default helpers (e.g., `tests::utils::create_comet_pool`) set `min_fee == max_fee` to mimic the old constant-fee behaviour when bespoke dynamics are unnecessary.

## Requirements Recap
- Target pool example: 80/20 weights with ~1,000,000,000 units on the 80% side and 100 units on the 20% side.
- Each unit on the 20% side is worth ~0.0004 USD; objective is for the fee to decay from `max_fee` down to `min_fee` once an additional USD 100 of value has entered that side (and corresponding withdrawals occur from the heavy side).
- Fee should reflect a utilization ratio, so operators can configure: starting/max fee, terminal/min fee, and the balance thresholds that map to those endpoints.

## Option 1: Single-Token Linear Interpolation (implemented)
Use one tracked asset (the 20% side) and scale the fee linearly as its on-chain balance moves between two configured thresholds.

**Storage Changes**
- Replace `DataKey::SwapFee` with a `SwapFeeConfig` struct:
  - `min_fee`, `max_fee` (i128, still denominated in `STROOP`).
  - `tracked_token` (Address) to inspect the utilization balance.
  - `low_util_balance`, `high_util_balance` (i128) expressed in raw token units, representing the balances at which the fee should equal `max_fee` and `min_fee` respectively.
  - Optional: `decay_curve` enum reserved for future expansion (e.g., exponential), defaulting to linear.

**Runtime Logic**
1. Add helpers in `contracts/src/c_pool/metadata.rs` to read/write the config and a `current_swap_fee(&Env) -> i128` function that:
   - Loads the tracked token record via `read_record`.
   - Converts its balance to 18-decimal precision with the existing `scalar`.
   - Clips the balance between `low_util_balance` and `high_util_balance` and computes `util = (balance - low) / (high - low)` using `FixedPoint` math.
   - Returns `max_fee - util * (max_fee - min_fee)`.
2. Replace every `read_swap_fee` usage with `current_swap_fee` (no changes needed inside `c_math` since it still receives an i128 fee each call).
3. Guard against division by zero when `low == high` by defaulting to constant `max_fee`.

**Initialization**
- Extend factory/new pool init to accept the new parameters and to set `high_util_balance = initial_balance + deposit_target`, `low_util_balance = initial_balance` for your example.
- Validate `max_fee >= min_fee`, `low_util_balance < high_util_balance`, token exists, etc.

**Pros / Cons**
- ✅ Small storage footprint and minimal performance overhead.
- ✅ Directly matches the described business rule.
- ⚠️ Only one dimension of utilization; unsuitable if multiple tokens should influence fees.

## Option 2: Multi-Asset Utilization Aggregation
Support dynamic fees driven by multiple pool tokens, combining their utilizations before mapping to the fee range.

**Storage Changes**
- Extend `SwapFeeConfig` with:
  - `tracked_tokens: Vec<Address>` and matching `low_balances`, `high_balances` vectors.
  - `aggregation: AggregationMode` (e.g., `Min`, `Max`, `Average`, `WeightedAverage`).

**Runtime Logic**
1. Fetch each tracked record and compute individual utilization ratios as in Option 1.
2. Aggregate according to the configured mode (e.g., `util = min(ratios)` to take the bottleneck asset).
3. Derive `current_fee = max_fee - util * (max_fee - min_fee)`.

**Initialization**
- Factory must accept vector parameters; enforce `tracked_tokens` subset of bound tokens, equal vector lengths, and per-token validation.

**Pros / Cons**
- ✅ Works for general-balanced pools or scenarios where both sides must be considered.
- ⚠️ More storage and math per call; increases complexity of client configuration.
- ⚠️ Additional validation required to keep vectors aligned and bounded.

## Shared Implementation Considerations
- Update `DataKey` enum and all serialization to cover the new struct (mind bumping existing deployments or add migration handling if backward compatibility is required).
- Expose getter endpoints for both `current_swap_fee` and the underlying config so off-chain services can model the curve.
- Update unit/integration tests: new config validation cases, ensure interpolated fees hit endpoints, and adjust snapshots expecting a static fee.
- Decide how to handle controller updates post-init (e.g., add a `set_swap_fee_config` entry point guarded by controller auth).
- Document rounding behavior: stick with the existing 7-decimal STROOP scale and reuse `soroban_fixed_point_math` to avoid precision drift.

## Recommended Next Steps
1. Confirm whether a single tracked token captures the business need; if yes, proceed with Option 1 to reduce scope.
2. Define exact threshold values for the 20% token (raw units vs. value in USD) and how to translate new deposits into balance targets.
3. Once parameters are locked, implement the struct, helper, and factory/init changes, then methodically update all call sites and tests.
