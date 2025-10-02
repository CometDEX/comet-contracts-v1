# Comet Pool Soroban Contract – Security Review Addendum

**Date:** 2025-XX-XX  
**Reviewer:** Codex (GPT-5)  
**Scope:** `contracts/src/c_pool` and supporting modules (`c_math`, `c_num`, `c_consts`, etc.)  
**Notes:** Analysis performed on the Soroban/Stellar build at commit currently checked out locally. Findings focus on storage key behaviour, simulation/submission drift, and general security hardening. Issues are ranked using High/Medium/Low severity.

---

## High Severity

### 1. Self-Swap DoS Via Shared Record Key
- **Location:** `contracts/src/c_pool/call_logic/pool.rs`
- **Summary:** `swap_exact_amount_in` and `swap_exact_amount_out` do not prevent `token_in == token_out`. When this happens the same storage key in `record_map` is updated twice in the same call: the first update (credit) is overwritten by the second (debit) because both calls use `record_map.set(token_in.clone(), …)`. The on-ledger balance ends up reduced while the contract still holds the transferred tokens, letting an attacker loop self-swaps to drain the recorded balance toward zero.
- **Impact:** Future swaps/withdrawals observe the depleted record and revert with `ErrInsufficientBalance`, effectively locking user funds until an administrator calls `gulp` to resync balances. Attacker cost is just swap fees, so this is a practical denial-of-service vector.
- **Recommendation:** Reject requests where the assets are identical (`assert!(token_in != token_out)`); alternatively, deduplicate the writeback logic so `token_in == token_out` updates a single record by combining the add/sub arithmetic. Add regression tests covering the scenario.

---

## Medium Severity

### 2. Dynamic Fee Overflow When Balances Grow
- **Location:** `contracts/src/c_pool/metadata.rs::read_swap_fee`
- **Summary:** The dynamic fee calculation multiplies the tracked token balance by its scalar (`balance * scalar`). Although initialization caps `low/high_util_balance`, there is no ongoing limit on `Record.balance`. Large deposits can push `balance` above `i128::MAX / scalar`, causing the `checked_mul` to fail and the function to panic with `Error::ErrMathApprox`.
- **Impact:** Any swap, join, or deposit that invokes `read_swap_fee` will revert once the tracked balance crosses the overflow threshold. The contract remains bricked until the balance is reduced manually.
- **Recommendation:** Enforce a cap before `checked_mul` (reject growth once `balance` is near the maximum safe value, or clamp the scalar application). Consider enforcing the same bound in deposit/join flows so the condition can never be reached.

---

## Low Severity

### 3. Vector Length Assumptions During Join/Exit
- **Location:** `contracts/src/c_pool/call_logic/pool.rs::execute_join_pool`, `execute_exit_pool`
- **Summary:** The loops access `max_amounts_in` and `min_amounts_out` with `get_unchecked`. If a caller supplies vectors that are too short, the host traps instead of returning a contract error. The end-user gets a generic failure rather than an actionable error code.
- **Impact:** No direct fund risk, but it undermines UX/debuggability and can complicate integration testing.
- **Recommendation:** Assert the auxiliary vectors have the same length as the token list before entering the loop and surface `Error::ErrInvalidVectorLen` on mismatch.

---

## Storage-Key & Simulation Observations
- Instance keys (`Controller`, `SwapFeeConfig`, `FeeRule`, `PublicSwap`, `Finalize`, `Freeze`) are fixed after initialization and refreshed via `extend_ttl`. Persistent collections (`AllTokenVec`, `AllRecordData`) maintain constant cardinality; no new keys are created during normal operation.
- Dynamic keys are limited to LP balances (`DataKeyToken::Balance(addr)`) and temporary allowances (`DataKeyToken::Allowance(from, spender)`). Keys are unique per address tuple, so collisions between simultaneous transactions are practically impossible.
- Because storage writes touch only existing keys after initialization, preflight simulations should align with submission results aside from the usual rent-cost variability. Ensure callers choose allowance expirations strictly in the future to avoid `ErrInvalidExpirationLedger` between simulation and submission when ledger sequence advances.

---

## Suggested Next Steps
1. Patch and test the self-swap condition to prevent balance desync DoS.
2. Introduce an upper-bound guard around the tracked-token balance multiplications and enforce it in deposit/join flows.
3. Add length checks for the join/exit helper vectors and update tests to cover malformed inputs.


## Additional Review (Deep Dive #2)

### Medium Severity

#### 4. Unchecked Supply Update in `burn` / `burn_from` *(Addressed)*
- **Location:** `contracts/src/c_pool/comet.rs:396-423`
- **Summary:** Both token burn entry points fetch `total = get_total_shares(&e)` and then write `put_total_shares(&e, total - amount)`. Unlike the rest of the codebase, this subtraction is unchecked, so if `amount > total` the operation will wrap on WASM targets and produce a very large positive supply instead of failing.
- **Impact:** Under nominal conditions `total >= amount`, but any latent accounting bug or future refactor that violates this invariant turns a single burn into a permanent supply corruption (effectively minting `2^127` shares). Bringing the supply back in sync would require privileged intervention.
- **Recommendation:** Replace with `total.checked_sub(amount).unwrap_or_else(|| panic_with_error!(...))` to match the arithmetic pattern elsewhere and add a regression test that attempts to burn more shares than exist.
- **Status:** Fixed in code (`contracts/src/c_pool/comet.rs`), now using `checked_sub` with `ErrMathApprox` fallback. Full test suite passes post-change.

### Low Severity

#### 5. Balance TTL Requires Periodic Touches
- **Location:** `contracts/src/c_pool/balance.rs` (`BALANCE_BUMP_AMOUNT`, `BALANCE_LIFETIME_THRESHOLD`)
- **Summary:** LP balances live in persistent storage with a 120-day bump window. If an address never calls `balance`, transfers, or participates in any pool action for ~4 months, its balance entry will age out and be deleted by the network.
- **Impact:** Long-term liquidity providers that “set and forget” could lose their recorded LP shares, forcing manual recovery via contract upgrade or replay. This is a broader Soroban rent consideration, but worth communicating before launch.
- **Recommendation:** Document the requirement prominently (docs/UI) and consider lengthening the bump window or introducing a heartbeat mechanism (e.g., controller cron or periodic `balance` calls) to refresh dormant accounts.

#### 6. Muxed Address Metadata Dropped in Events
- **Location:** `contracts/src/c_pool/comet.rs:359-373`
- **Summary:** `TokenInterface::transfer` maps `MuxedAddress` recipients to their underlying `Address` and publishes events with `to_muxed_id: None`, discarding the muxed ID.
- **Impact:** Ledger state is still credited to the underlying account, but downstream indexers lose muxed ID observability, which breaks parity with the reference token contract.
- **Recommendation:** Populate `to_muxed_id` by calling `to.to_muxed_id()` so event consumers retain the full destination metadata.

### Informational

- **Simulation Drift:** All storage keys touched during swaps/joins already exist after initialization, so the main source of simulation/submission divergence remains moving market data (balances, swap fee). Heavy traffic may change fees between simulate and submit; integrators should set conservative `max_price`/`min_amount` slippage bounds.
- **Fee Recipient Ordering:** When trade-specific fee recipients are provided, they are appended after the pool-level list. Percentages are applied independently, so overlapping recipients may be partially refunded to the pool because of rounding. Not a security issue, but worth documenting for integrators expecting additive behaviour.

---

## Updated Next Steps
1. Implement and test the self-swap guard (Finding 1) and the checked supply subtraction (Finding 4).
2. Add safeguards around the dynamic fee overflow edge case (Finding 2).
3. Harden vector-length validation and muxed-address metadata handling (Findings 3 & 6).
4. Decide on an operational plan for balance TTL maintenance (Finding 5).

## Additional Review (Deep Dive #3)

### Medium Severity

#### 7. Total Share Supply TTL Can Expire After ~31 Days
- **Location:** `contracts/src/c_pool/metadata.rs:160-180`
- **Summary:** `DataKey::TotalShares` is persisted with the shared TTL constants (`SHARED_LIFETIME_THRESHOLD`/`SHARED_BUMP_AMOUNT` ≈ 31 days). If the pool is idle longer than that window, the total-supply entry expires. Subsequent joins treat the supply as zero (minting 0 LP shares while still pulling deposits), and withdrawals immediately revert via `sub_no_negative` because the cached supply is 0. Balances themselves live for 120 days, so the state becomes inconsistent until a privileged fix restores the supply.
- **Impact:** A multi-week pause in activity bricks withdrawals and lets the first post-expiry depositor donate funds, introducing both availability and fairness risks.
- **Recommendation:** Align `TotalShares` with the 120-day bump window used for balances (or longer), and add monitoring to refresh the key before expiry. Consider a guard that aborts operations if `get_total_shares` unexpectedly returns 0 after initialization.

### Low Severity

#### 8. Same-Ledger Allowances Immediately Expire
- **Location:** `contracts/src/c_pool/allowance.rs:42-61`
- **Summary:** `write_allowance` allows `expiration_ledger == ledger.sequence()`, but the derived TTL passed to `temporary().extend_ttl` becomes zero. On Soroban a zero bump means the entry expires right away, so the approval vanishes at the end of the same ledger.
- **Impact:** Users setting "this-ledger" expirations via frontends receive a successful simulation but lose the allowance before submission completes under heavy load.
- **Recommendation:** Require `expiration_ledger > ledger.sequence()` for any non-zero approval and surface `Error::ErrInvalidExpirationLedger` on equality; alternatively bump by at least one ledger.

#### 9. Negative-Amount Guard Uses Bare `panic!` *(Addressed)*
- **Location:** `contracts/src/c_pool/token_utility.rs:66-68`
- **Summary:** `check_nonnegative_amount` calls `panic!` with a string message instead of `panic_with_error!`. The resulting host error lacks a stable code, making the failure opaque to integrators and harder to map in tests.
- **Impact:** Low; purely an observability concern, but inconsistent with the rest of the contract’s error handling.
- **Recommendation:** Replace with `panic_with_error!(e, Error::ErrNegative)` (or similar) so clients receive the documented code path.
- **Status:** Resolved by passing `&Env` into `check_nonnegative_amount` and using `panic_with_error!(…, Error::ErrNegative)` (`contracts/src/c_pool/token_utility.rs`, `contracts/src/c_pool/comet.rs`).

---

## Next Steps (Expanded)
1. Implement fixes for Findings 1, 2, 4, and 7 before launch; regression-test swaps, deposits, and burns afterward.
2. Harden the UX cases in Findings 3, 5, 6, 8, and 9, and document allowance/balance TTL expectations for integrators.
3. Add monitoring or automated heartbeats to keep all persistent keys above their TTL thresholds.

## Additional Review (Deep Dive #4)

### Medium Severity

#### 10. Core Pool State Maps Expire After ~31 Days Idle
- **Location:** `contracts/src/c_pool/metadata.rs:12-52`
- **Summary:** `AllTokenVec` (token list) and `AllRecordData` (token→Record map) share the 31-day TTL window. If the contract sees no traffic for that period, both entries expire. The next call to `read_tokens`/`read_record` unwraps `None` and hard-panics, permanently bricking the pool until a privileged migration repopulates state.
- **Impact:** Any month-long outage or lull (e.g., low-volume seasonal pool) renders swaps, joins, and exits unusable, risking total fund lock.
- **Recommendation:** Increase these keys to the 120-day window (or longer) and establish a monitoring/maintenance process that calls a lightweight endpoint (e.g., `get_tokens`) well before expiry. Consider defensive checks that emit graceful errors if the map/vector is missing.

### Informational

- `DataKeyToken::Allowance` entries rely on clients setting expirations sufficiently in the future. Document recommended minimums (e.g., +10 ledgers) for integrator SDKs.

## Next Steps (Final)
1. Prioritize fixes for Findings 1, 2, 4, 7, and 10 before mainnet launch; rerun the full test suite afterward.
2. Address UX/operational gaps in Findings 3, 5, 6, 8, and 9, and update product docs with TTL expectations.
3. Schedule automated keep-alive transactions (or monitoring alerts) to refresh persistent keys under both the 31-day and 120-day windows.
