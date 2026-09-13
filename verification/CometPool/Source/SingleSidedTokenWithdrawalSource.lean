import CometPool.Source.SingleSidedTokenDepositSource
import CometPool.Operations.SingleSidedTokenWithdrawal

set_option maxRecDepth 65536

namespace CometPool

/-!
Executable, source-shaped models for the positive-output arithmetic used by
`wdr_tokn_amt_out_get_lp_tokns_in`. The common checked recurrence is reused
from `ExactInputSwapSource`; this file models the below-one, lower-directed
`c_pow` corrections and the complete caller arithmetic.
-/

/-- Result of the below-one, lower-directed approximation path. -/
structure LowerBelowApproxExecutionResult where
  iterations : ℕ
  xRaw : ℤ
  unadjustedSumRaw : ℤ
  finalTermRaw : ℤ
  partialRaw : ℤ
deriving DecidableEq

/-- Source execution of `c_pow_approx(..., round_up = false)` below one. -/
def lowerBelowApproxExecution
    (baseRaw remainRaw : ℤ) : Option LowerBelowApproxExecutionResult := do
  let xRaw ← SorobanFixedPointMath.I256.sub baseRaw BONE
  let stopped ← exactInputApproxFindStop xRaw remainRaw MAX_CPOW_ITERS 0
  let partialRaw ←
    if stopped.iterations = 1 ∧ xRaw ≠ 0 ∧ stopped.state.term ≠ 0 then
      SorobanFixedPointMath.I256.sub stopped.state.sum 1
    else if stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0 then
      SorobanFixedPointMath.I256.sub stopped.state.sum stopped.state.term
    else if stopped.iterations ≠ 1 ∧ xRaw ≤ 0 then
      SorobanFixedPointMath.I256.add stopped.state.sum stopped.state.term
    else
      some stopped.state.sum
  some {
    iterations := stopped.iterations
    xRaw
    unadjustedSumRaw := stopped.state.sum
    finalTermRaw := stopped.state.term
    partialRaw
  }

private theorem withdrawal_i256_sub_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x - y) = some result from hexec)
  exact h.2.symm

private theorem withdrawal_i256_add_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x + y) = some result from hexec)
  exact h.2.symm

/-- Successful execution exposes exactly the prefixes reached by the source loop. -/
theorem lowerBelowApproxExecution_success
    {baseRaw remainRaw : ℤ} {result : LowerBelowApproxExecutionResult}
    (hexec : lowerBelowApproxExecution baseRaw remainRaw = some result) :
    ∃ state : ExactInputApproxState,
      result.xRaw = baseRaw - BONE ∧
        exactInputApproxSteps result.xRaw remainRaw result.iterations = some state ∧
        result.unadjustedSumRaw = state.sum ∧
        result.finalTermRaw = state.term ∧
        1 ≤ result.iterations ∧ result.iterations ≤ 50 ∧
        (∀ k, 1 ≤ k → k < result.iterations →
          CPOW_PRECISION <
            |(exactInputApproxStateAt result.xRaw remainRaw k).term|) ∧
        (result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
            result.finalTermRaw ≠ 0 →
          result.partialRaw = result.unadjustedSumRaw - 1) ∧
        (result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
            result.finalTermRaw > 0 →
          result.partialRaw = result.unadjustedSumRaw - result.finalTermRaw) ∧
        (result.iterations ≠ 1 ∧ result.xRaw ≤ 0 →
          result.partialRaw = result.unadjustedSumRaw + result.finalTermRaw) ∧
        (¬(result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
              result.finalTermRaw ≠ 0) ∧
            ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
              result.finalTermRaw > 0) ∧
            ¬(result.iterations ≠ 1 ∧ result.xRaw ≤ 0) →
          result.partialRaw = result.unadjustedSumRaw) := by
  rw [lowerBelowApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := withdrawal_i256_sub_success_eq hxRaw
  have hfind := exactInputApproxFindStop_success hstopped
  have hn1 : 1 ≤ stopped.iterations := by
    rcases hfind.2.1 with hzero | hpositive
    · norm_num [MAX_CPOW_ITERS] at hzero
    · omega
  have hn50 : stopped.iterations ≤ 50 := by
    simpa [MAX_CPOW_ITERS] using hfind.2.2.1
  by_cases hfirst :
      stopped.iterations = 1 ∧ xRaw ≠ 0 ∧ stopped.state.term ≠ 0
  · rw [if_pos hfirst] at hafterStop
    rcases Option.bind_eq_some.mp hafterStop with
      ⟨partialRaw, hpartialRaw, hresult⟩
    have hresultEq := Option.some.inj hresult
    subst result
    refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hxEq] using hfind.2.2.2.1
    · intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
    · intro _
      exact withdrawal_i256_sub_success_eq hpartialRaw
    · intro hnot
      exact False.elim (hnot.1 hfirst.1)
    · intro hnot
      exact False.elim (hnot.1 hfirst.1)
    · intro hnot
      exact False.elim (hnot.1 hfirst)
  · rw [if_neg hfirst] at hafterStop
    by_cases habove :
        stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0
    · rw [if_pos habove] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hxEq] using hfind.2.2.2.1
      · intro k hk1 hkn
        simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
      · intro hyes
        exact False.elim (hfirst hyes)
      · intro _
        exact withdrawal_i256_sub_success_eq hpartialRaw
      · intro hnot
        exact False.elim ((not_le.mpr habove.2.1) hnot.2)
      · intro hnot
        exact False.elim (hnot.2.1 habove)
    · rw [if_neg habove] at hafterStop
      by_cases hbelow : stopped.iterations ≠ 1 ∧ xRaw ≤ 0
      · rw [if_pos hbelow] at hafterStop
        rcases Option.bind_eq_some.mp hafterStop with
          ⟨partialRaw, hpartialRaw, hresult⟩
        have hresultEq := Option.some.inj hresult
        subst result
        refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hxEq] using hfind.2.2.2.1
        · intro k hk1 hkn
          simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
        · intro hyes
          exact False.elim (hfirst hyes)
        · intro hyes
          exact False.elim (habove hyes)
        · intro _
          exact withdrawal_i256_add_success_eq hpartialRaw
        · intro hnot
          exact False.elim (hnot.2.2 hbelow)
      · rw [if_neg hbelow] at hafterStop
        rcases Option.bind_eq_some.mp hafterStop with
          ⟨partialRaw, hpartialRaw, hresult⟩
        have hresultEq := Option.some.inj hresult
        subst result
        refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hxEq] using hfind.2.2.2.1
        · intro k hk1 hkn
          simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
        · intro hyes
          exact False.elim (hfirst hyes)
        · intro hyes
          exact False.elim (habove hyes)
        · intro hyes
          exact False.elim (hbelow hyes)
        · intro _
          exact Option.some.inj hpartialRaw.symm

/-- A successful deterministic recurrence exposes every preceding prefix. -/
private theorem exactInputApproxSteps_prefix_of_success
    {xRaw remainRaw : ℤ} {iterations k : ℕ} {state : ExactInputApproxState}
    (hk : k ≤ iterations)
    (hexec : exactInputApproxSteps xRaw remainRaw iterations = some state) :
    ∃ prefixState, exactInputApproxSteps xRaw remainRaw k = some prefixState := by
  induction iterations generalizing state with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      exact ⟨state, hexec⟩
  | succ iterations ih =>
      by_cases hlast : k = iterations + 1
      · subst k
        exact ⟨state, hexec⟩
      · rw [exactInputApproxSteps] at hexec
        rcases Option.bind_eq_some.mp hexec with ⟨previous, hprevious, hstep⟩
        exact ih (by omega) hprevious

/-- Successful lower-directed approximation exposes every executed prefix. -/
theorem lowerBelowApproxExecution_prefix
    {baseRaw remainRaw : ℤ} {result : LowerBelowApproxExecutionResult}
    (hexec : lowerBelowApproxExecution baseRaw remainRaw = some result) :
    ∀ k, 1 ≤ k → k ≤ result.iterations →
      ∃ state, exactInputApproxSteps result.xRaw remainRaw k = some state := by
  obtain ⟨state, hx, hsteps, hsum, hterm, hn1, hn50, hcontinued,
    hfirst, habove, hbelow, hplain⟩ := lowerBelowApproxExecution_success hexec
  intro k hk1 hkn
  exact exactInputApproxSteps_prefix_of_success hkn hsteps

/-- A result strictly before iteration 50 stopped by the precision test. -/
theorem lowerBelowApproxExecution_final_le_of_lt_fifty
    {baseRaw remainRaw : ℤ} {result : LowerBelowApproxExecutionResult}
    (hexec : lowerBelowApproxExecution baseRaw remainRaw = some result)
    (hlt : result.iterations < 50) :
    |(exactInputApproxStateAt result.xRaw remainRaw result.iterations).term| ≤
      CPOW_PRECISION := by
  have hexecOriginal := hexec
  rw [lowerBelowApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := withdrawal_i256_sub_success_eq hxRaw
  have finish : stopped.iterations = result.iterations := by
    by_cases hfirst :
        stopped.iterations = 1 ∧ xRaw ≠ 0 ∧ stopped.state.term ≠ 0
    · rw [if_pos hfirst] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with ⟨partialRaw, hp, hr⟩
      exact congrArg LowerBelowApproxExecutionResult.iterations (Option.some.inj hr)
    · rw [if_neg hfirst] at hafterStop
      by_cases habove :
          stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0
      · rw [if_pos habove] at hafterStop
        rcases Option.bind_eq_some.mp hafterStop with ⟨partialRaw, hp, hr⟩
        exact congrArg LowerBelowApproxExecutionResult.iterations (Option.some.inj hr)
      · rw [if_neg habove] at hafterStop
        by_cases hbelow : stopped.iterations ≠ 1 ∧ xRaw ≤ 0
        · rw [if_pos hbelow] at hafterStop
          rcases Option.bind_eq_some.mp hafterStop with ⟨partialRaw, hp, hr⟩
          exact congrArg LowerBelowApproxExecutionResult.iterations (Option.some.inj hr)
        · rw [if_neg hbelow] at hafterStop
          exact congrArg LowerBelowApproxExecutionResult.iterations
            (Option.some.inj hafterStop)
  have hcap : stopped.iterations < 0 + MAX_CPOW_ITERS := by
    have hstoppedLt : stopped.iterations < 50 := by
      rw [finish]
      exact hlt
    simpa [MAX_CPOW_ITERS] using hstoppedLt
  have hxSuccess := (lowerBelowApproxExecution_success hexecOriginal).choose_spec.1
  have hresultX : result.xRaw = xRaw := hxSuccess.trans hxEq.symm
  simpa [finish, hresultX] using
    exactInputApproxFindStop_final_le_of_lt_cap hstopped hcap

/-- The first below-one lower-directed recurrence term has its production floor. -/
theorem lowerBelowApproxExecution_first_term_refines
    {baseRaw remainRaw : ℤ} {result : LowerBelowApproxExecutionResult}
    (hexec : lowerBelowApproxExecution baseRaw remainRaw = some result) :
    IsFloor
      (exactInputApproxStateAt result.xRaw remainRaw 1).term
      (((remainRaw : ℝ) * (result.xRaw : ℝ)) / BONE) := by
  obtain ⟨state, hstate⟩ := lowerBelowApproxExecution_prefix hexec 1
    (by omega) (lowerBelowApproxExecution_success hexec).choose_spec.2.2.2.2.1
  have href := exactInputApproxSteps_refinements
    (iteration := 1) (by omega) (by omega) hstate
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw 1 = state := by
    simp [exactInputApproxStateAt, hstate]
  have hinitialTerm :
      (exactInputApproxStateAt result.xRaw remainRaw 0).term = BONE := by rfl
  have hmultiplied : state.multiplied = state.coefficientProduct := by
    have hfloor := href.2.1
    rw [hinitialTerm] at hfloor
    have hlower : (state.coefficientProduct : ℝ) < state.multiplied + 1 := by
      simpa [BONE] using hfloor.lt_add_one
    have hupper : state.multiplied ≤ state.coefficientProduct := by
      exact_mod_cast (by simpa [BONE] using hfloor.le)
    have hlowerInt : state.coefficientProduct < state.multiplied + 1 := by
      exact_mod_cast hlower
    omega
  have hterm : state.term = state.multiplied := by
    have hfloor := href.2.2.1
    have hlower : (state.multiplied : ℝ) < state.term + 1 := by
      simpa [hmultiplied] using hfloor.lt_add_one
    have hupper : state.term ≤ state.multiplied := by
      exact_mod_cast (by simpa [hmultiplied] using hfloor.le)
    have hlowerInt : state.multiplied < state.term + 1 := by exact_mod_cast hlower
    omega
  rw [hstateAt, hterm, hmultiplied]
  simpa using href.1

/-- A strict below-one first stop applies the source's one-unit correction. -/
theorem lowerBelowApproxExecution_first_sum
    {baseRaw remainRaw : ℤ} {result : LowerBelowApproxExecutionResult}
    (hbaseStrict : baseRaw < BONE)
    (hremain0 : 0 < remainRaw)
    (hexec : lowerBelowApproxExecution baseRaw remainRaw = some result)
    (hn : result.iterations = 1) :
    let firstTerm := (exactInputApproxStateAt result.xRaw remainRaw 1).term
    firstTerm < 0 ∧ result.partialRaw = BONE + firstTerm - 1 := by
  obtain ⟨state, hx, hsteps, hsum, hterm, hn1, hn50, hcontinued,
    hfirst, habove, hbelow, hplain⟩ := lowerBelowApproxExecution_success hexec
  have hxNegative : result.xRaw < 0 := by rw [hx]; omega
  have hfirstFloor := lowerBelowApproxExecution_first_term_refines hexec
  have hfirstNegative :
      (exactInputApproxStateAt result.xRaw remainRaw 1).term < 0 := by
    have hexactNegative :
        ((remainRaw : ℝ) * (result.xRaw : ℝ)) / BONE < 0 := by
      have hr : (0 : ℝ) < remainRaw := by exact_mod_cast hremain0
      have hxReal : (result.xRaw : ℝ) < 0 := by exact_mod_cast hxNegative
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr hxReal)
        (by norm_num [BONE])
    have hraw :
        ((exactInputApproxStateAt result.xRaw remainRaw 1).term : ℝ) < 0 :=
      lt_of_le_of_lt hfirstFloor.le hexactNegative
    by_contra hnot
    have hnonnegative :
        (0 : ℝ) ≤ (exactInputApproxStateAt result.xRaw remainRaw 1).term := by
      exact_mod_cast (le_of_not_gt hnot)
    linarith
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw 1 = state := by
    have hstepsOne : exactInputApproxSteps result.xRaw remainRaw 1 = some state := by
      simpa [hn] using hsteps
    simp [exactInputApproxStateAt, hstepsOne]
  have hfinal : result.finalTermRaw =
      (exactInputApproxStateAt result.xRaw remainRaw 1).term := by
    rw [hterm, hstateAt]
  have hpartial := hfirst ⟨hn, ne_of_lt hxNegative, by rw [hfinal]; omega⟩
  dsimp
  refine ⟨hfirstNegative, ?_⟩
  rw [hpartial, hsum, hsumPrefix, hn]
  simp [hfinal]

/-- A later strict below-one stop duplicates its final negative term. -/
theorem lowerBelowApproxExecution_later_sum
    {baseRaw remainRaw : ℤ} {result : LowerBelowApproxExecutionResult}
    (hbaseStrict : baseRaw < BONE)
    (hexec : lowerBelowApproxExecution baseRaw remainRaw = some result)
    (hn2 : 2 ≤ result.iterations) :
    result.partialRaw = BONE +
      ∑ k ∈ Finset.range result.iterations,
        (exactInputApproxStateAt result.xRaw remainRaw (k + 1)).term +
      (exactInputApproxStateAt result.xRaw remainRaw result.iterations).term := by
  obtain ⟨state, hx, hsteps, hsum, hterm, hn1, hn50, hcontinued,
    hfirst, habove, hbelow, hplain⟩ := lowerBelowApproxExecution_success hexec
  have hxNegative : result.xRaw < 0 := by rw [hx]; omega
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw result.iterations = state := by
    simp [exactInputApproxStateAt, hsteps]
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  have hpartial := hbelow ⟨by omega, hxNegative.le⟩
  rw [hpartial, hsum, hterm, hsumPrefix, ← hstateAt]

/-- Source control-flow result of below-one, lower-directed `c_pow`. -/
inductive LowerBelowCPowExecutionResult where
  | integer (integerPart : ℕ) (wholeRaw : ℤ)
  | fractional
      (integerPart remainderStroop : ℕ)
      (wholeRaw : ℤ) (approx : LowerBelowApproxExecutionResult)
      (powerRaw : ℤ)
deriving DecidableEq

def LowerBelowCPowExecutionResult.powerRaw : LowerBelowCPowExecutionResult → ℤ
  | .integer _ wholeRaw => wholeRaw
  | .fractional _ _ _ _ powerRaw => powerRaw

/-- Source-shaped `c_pow(..., round_up = false)` for a direct weight below one. -/
def lowerBelowCPowExecution
    (baseRaw exponentBone : ℤ) (exponentStroop : ℕ) :
    Option LowerBelowCPowExecutionResult := do
  if baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw then none
  else if exponentBone ≠
      (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP) then none
  else
    let integerPart := rustU32Cast (exponentBone / BONE).toNat
    let remainderStroop := exponentStroop % STROOP
    let remainRaw := exponentBone - (exponentBone / BONE) * BONE
    let wholeRaw ← lowerPowiExecution baseRaw integerPart
    if remainRaw = 0 then
      some (.integer integerPart wholeRaw)
    else
      let approx ← lowerBelowApproxExecution baseRaw remainRaw
      let powerRaw ←
        SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
          wholeRaw approx.partialRaw BONE
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)

/-- A configured direct weight forces the fractional, zero-integer branch. -/
theorem lowerBelowCPowExecution_configured_components
    {baseRaw exponentBone : ℤ} {exponentStroop : ℕ}
    {integerPart remainderStroop : ℕ} {wholeRaw powerRaw : ℤ}
    {approx : LowerBelowApproxExecutionResult}
    (hexponent0 : 0 < exponentStroop) (hexponentUpper : exponentStroop < STROOP)
    (hexec : lowerBelowCPowExecution baseRaw exponentBone exponentStroop =
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)) :
    integerPart = 0 ∧ remainderStroop = exponentStroop ∧ wholeRaw = BONE ∧
      lowerBelowApproxExecution baseRaw
        (exponentStroop * (BONE / STROOP)) = some approx ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        wholeRaw approx.partialRaw BONE = some powerRaw := by
  rw [lowerBelowCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · rw [if_neg hguard] at hexec
    by_cases hscaled : exponentBone ≠
        (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP)
    · simp [hscaled] at hexec
    · rw [if_neg hscaled] at hexec
      have hscale := not_ne_iff.mp hscaled
      have hsource := scaledExponentSourceSplit exponentStroop
      have hintegerSource : (exponentBone / BONE).toNat = 0 := by
        rw [hscale, hsource.1]
        simp [Nat.div_eq_of_lt hexponentUpper]
      have hremainder : exponentStroop % STROOP = exponentStroop :=
        Nat.mod_eq_of_lt hexponentUpper
      have hremainSource :
          exponentBone - (exponentBone / BONE) * BONE =
            ((exponentStroop * (BONE / STROOP) : ℕ) : ℤ) := by
        rw [hscale, hsource.2, hremainder]
      rw [hintegerSource, rustU32Cast, Nat.zero_mod, hremainder,
        hremainSource] at hexec
      have hremainNonzero :
          (((exponentStroop * (BONE / STROOP) : ℕ) : ℤ)) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hexponent0)
          (by norm_num [BONE, STROOP])
      simp only at hexec
      simp [lowerPowiExecution, lowerPowiLoopExecution, hremainNonzero] at hexec
      have hremainFactors :
          ¬(exponentStroop = 0 ∨ (BONE : ℤ) / STROOP = 0) := by
        norm_num [BONE, STROOP]
        exact Nat.ne_of_gt hexponent0
      rw [if_neg hremainFactors] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨approxResult, happ, hafterApprox⟩
      rcases Option.bind_eq_some.mp hafterApprox with ⟨power, hpower, hresult⟩
      have hfields := Option.some.inj hresult
      cases hfields
      exact ⟨rfl, rfl, rfl, happ, hpower⟩

/-- A configured direct weight cannot take `c_pow`'s integer-only branch. -/
theorem lowerBelowCPowExecution_configured_not_integer
    {baseRaw exponentBone : ℤ} {exponentStroop integerPart : ℕ}
    {wholeRaw : ℤ}
    (hexponent0 : 0 < exponentStroop) (hexponentUpper : exponentStroop < STROOP)
    (hexec : lowerBelowCPowExecution baseRaw exponentBone exponentStroop =
      some (.integer integerPart wholeRaw)) : False := by
  rw [lowerBelowCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · rw [if_neg hguard] at hexec
    by_cases hscaled : exponentBone ≠
        (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP)
    · simp [hscaled] at hexec
    · rw [if_neg hscaled] at hexec
      have hscale := not_ne_iff.mp hscaled
      have hsource := scaledExponentSourceSplit exponentStroop
      have hintegerSource : (exponentBone / BONE).toNat = 0 := by
        rw [hscale, hsource.1]
        simp [Nat.div_eq_of_lt hexponentUpper]
      have hremainder : exponentStroop % STROOP = exponentStroop :=
        Nat.mod_eq_of_lt hexponentUpper
      have hremainSource :
          exponentBone - (exponentBone / BONE) * BONE =
            ((exponentStroop * (BONE / STROOP) : ℕ) : ℤ) := by
        rw [hscale, hsource.2, hremainder]
      rw [hintegerSource, rustU32Cast, Nat.zero_mod, hremainder,
        hremainSource] at hexec
      have hremainNonzero :
          (((exponentStroop * (BONE / STROOP) : ℕ) : ℤ)) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hexponent0)
          (by norm_num [BONE, STROOP])
      simp only at hexec
      simp [lowerPowiExecution, lowerPowiLoopExecution, hremainNonzero] at hexec
      have hremainFactors :
          ¬(exponentStroop = 0 ∨ (BONE : ℤ) / STROOP = 0) := by
        norm_num [BONE, STROOP]
        exact Nat.ne_of_gt hexponent0
      rw [if_neg hremainFactors] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨approx, happ, hafterApprox⟩
      rcases Option.bind_eq_some.mp hafterApprox with ⟨power, hpower, hresult⟩
      cases Option.some.inj hresult

/-- Every successful modeled `c_pow` call satisfies the production base guard. -/
theorem lowerBelowCPowExecution_base_bounds
    {baseRaw exponentBone : ℤ} {exponentStroop : ℕ}
    {result : LowerBelowCPowExecutionResult}
    (hexec : lowerBelowCPowExecution baseRaw exponentBone exponentStroop =
      some result) :
    1 ≤ baseRaw ∧ baseRaw ≤ 2 * BONE - 1 := by
  rw [lowerBelowCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · exact ⟨by omega, by omega⟩

private theorem withdrawal_i128_mul_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem withdrawal_isFloor_integer_eq
    {rounded exact : ℤ} (hfloor : IsFloor rounded (exact : ℝ)) :
    rounded = exact := by
  have hlower : rounded ≤ exact := by exact_mod_cast hfloor.le
  have hupperReal : (exact : ℝ) < rounded + 1 := hfloor.lt_add_one
  have hupper : exact < rounded + 1 := by exact_mod_cast hupperReal
  omega

/-- Checked source intermediates before the withdrawal's `c_pow` call. -/
structure SingleSidedTokenWithdrawalPrefix where
  tokenBalanceRaw : ℤ
  tokenAmountRaw : ℤ
  poolSupplyRaw : ℤ
  feeRaw : ℤ
  weightRaw : ℤ
  weightComplementRaw : ℤ
  weightedFeeRaw : ℤ
  feeMultiplierRaw : ℤ
  beforeFeeRaw : ℤ
  newTokenBalanceRaw : ℤ
  baseRaw : ℤ

/-- Complete successful arithmetic result after the withdrawal's `c_pow` call. -/
structure SingleSidedTokenWithdrawalExecutionResult where
  pre : SingleSidedTokenWithdrawalPrefix
  cpow : LowerBelowCPowExecutionResult
  newPoolSupplyRaw : ℤ
  poolAmountRaw : ℤ
  downscaledRaw : ℤ
  output : ℤ

/-- Source arithmetic through the below-one balance ratio. -/
def singleSidedTokenWithdrawalPrefixExecution
    (inputBalance inputScalar inputAmount poolSupply
      inputWeight fee : ℕ) : Option SingleSidedTokenWithdrawalPrefix := do
  let tokenBalanceRaw ← SorobanFixedPointMath.I128.mul inputBalance inputScalar
  let tokenAmountRaw ← SorobanFixedPointMath.I128.mul inputAmount inputScalar
  let poolSupplyRaw ←
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP)
  let feeRaw ← SorobanFixedPointMath.I128.mul fee (BONE / STROOP)
  let weightRaw ←
    SorobanFixedPointMath.I128.mul inputWeight (BONE / STROOP)
  let weightComplementRaw ← SorobanFixedPointMath.I256.sub BONE weightRaw
  let weightedFeeRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      weightComplementRaw feeRaw BONE
  let feeMultiplierRaw ← SorobanFixedPointMath.I256.sub BONE weightedFeeRaw
  let beforeFeeRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenAmountRaw feeMultiplierRaw.toNat BONE
  let newTokenBalanceRaw ←
    SorobanFixedPointMath.I256.sub tokenBalanceRaw beforeFeeRaw
  let baseRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      newTokenBalanceRaw tokenBalanceRaw.toNat BONE
  some {
    tokenBalanceRaw
    tokenAmountRaw
    poolSupplyRaw
    feeRaw
    weightRaw
    weightComplementRaw
    weightedFeeRaw
    feeMultiplierRaw
    beforeFeeRaw
    newTokenBalanceRaw
    baseRaw
  }

/-- Source arithmetic from `c_pow` through the LP-token ceiling. -/
def singleSidedTokenWithdrawalFinishExecution
    (inputWeight : ℕ) (pre : SingleSidedTokenWithdrawalPrefix) :
    Option SingleSidedTokenWithdrawalExecutionResult := do
  let cpow ← lowerBelowCPowExecution pre.baseRaw pre.weightRaw inputWeight
  let newPoolSupplyRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      cpow.powerRaw pre.poolSupplyRaw BONE
  let poolAmountRaw ←
    SorobanFixedPointMath.I256.sub pre.poolSupplyRaw newPoolSupplyRaw
  let downscaledRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      poolAmountRaw (BONE / STROOP) 1
  let output ← SorobanFixedPointMath.I128.checked downscaledRaw
  some {
    pre
    cpow
    newPoolSupplyRaw
    poolAmountRaw
    downscaledRaw
    output
  }

/-- Executable model of `calc_lp_token_amount_given_token_withdrawal_amount`. -/
def calcLpTokenAmountGivenTokenWithdrawalAmountExecution
    (inputBalance inputScalar inputAmount poolSupply
      inputWeight fee : ℕ) : Option SingleSidedTokenWithdrawalExecutionResult := do
  let pre ← singleSidedTokenWithdrawalPrefixExecution inputBalance inputScalar
    inputAmount poolSupply inputWeight fee
  singleSidedTokenWithdrawalFinishExecution inputWeight pre

/-- Successful prefix execution exposes every checked source operation. -/
theorem singleSidedTokenWithdrawalPrefixExecution_success
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenWithdrawalPrefix}
    (hexec : singleSidedTokenWithdrawalPrefixExecution inputBalance inputScalar
      inputAmount poolSupply inputWeight fee = some result) :
    SorobanFixedPointMath.I128.mul inputBalance inputScalar =
        some result.tokenBalanceRaw ∧
      SorobanFixedPointMath.I128.mul inputAmount inputScalar =
        some result.tokenAmountRaw ∧
      SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP) =
        some result.poolSupplyRaw ∧
      SorobanFixedPointMath.I128.mul fee (BONE / STROOP) =
        some result.feeRaw ∧
      SorobanFixedPointMath.I128.mul inputWeight (BONE / STROOP) =
        some result.weightRaw ∧
      SorobanFixedPointMath.I256.sub BONE result.weightRaw =
        some result.weightComplementRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.weightComplementRaw result.feeRaw BONE =
          some result.weightedFeeRaw ∧
      SorobanFixedPointMath.I256.sub BONE result.weightedFeeRaw =
        some result.feeMultiplierRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.tokenAmountRaw result.feeMultiplierRaw.toNat BONE =
          some result.beforeFeeRaw ∧
      SorobanFixedPointMath.I256.sub result.tokenBalanceRaw
        result.beforeFeeRaw = some result.newTokenBalanceRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        result.newTokenBalanceRaw result.tokenBalanceRaw.toNat BONE =
          some result.baseRaw := by
  rw [singleSidedTokenWithdrawalPrefixExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨tokenBalanceRaw, htokenBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨tokenAmountRaw, htokenAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨poolSupplyRaw, hsupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨feeRaw, hfee, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨weightRaw, hweight, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨weightComplementRaw, hweightComplement, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨weightedFeeRaw, hweightedFee, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨feeMultiplierRaw, hfeeMultiplier, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨beforeFeeRaw, hbeforeFee, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨newTokenBalanceRaw, hnewBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨baseRaw, hbase, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨htokenBalance, htokenAmount, hsupply, hfee, hweight,
    hweightComplement, hweightedFee, hfeeMultiplier, hbeforeFee, hnewBalance,
    hbase⟩

/-- Successful finish execution exposes the remaining checked operations. -/
theorem singleSidedTokenWithdrawalFinishExecution_success
    {inputWeight : ℕ} {pre : SingleSidedTokenWithdrawalPrefix}
    {result : SingleSidedTokenWithdrawalExecutionResult}
    (hexec : singleSidedTokenWithdrawalFinishExecution inputWeight pre =
      some result) :
    result.pre = pre ∧
      lowerBelowCPowExecution pre.baseRaw pre.weightRaw inputWeight =
        some result.cpow ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.cpow.powerRaw pre.poolSupplyRaw BONE =
          some result.newPoolSupplyRaw ∧
      SorobanFixedPointMath.I256.sub pre.poolSupplyRaw
        result.newPoolSupplyRaw = some result.poolAmountRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil result.poolAmountRaw
        (BONE / STROOP) 1 = some result.downscaledRaw ∧
      SorobanFixedPointMath.I128.checked result.downscaledRaw =
        some result.output := by
  rw [singleSidedTokenWithdrawalFinishExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨cpow, hcpow, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨newSupply, hnewSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨poolAmount, hpoolAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨downscaled, hdownscale, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨output, houtput, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨rfl, hcpow, hnewSupply, hpoolAmount, hdownscale, houtput⟩

/-- A complete successful result supplies both source execution phases. -/
theorem calcLpTokenAmountGivenTokenWithdrawalAmountExecution_success
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenWithdrawalExecutionResult}
    (hexec : calcLpTokenAmountGivenTokenWithdrawalAmountExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    ∃ pre,
      singleSidedTokenWithdrawalPrefixExecution inputBalance inputScalar
          inputAmount poolSupply inputWeight fee = some pre ∧
        singleSidedTokenWithdrawalFinishExecution inputWeight pre =
          some result := by
  rw [calcLpTokenAmountGivenTokenWithdrawalAmountExecution] at hexec
  exact Option.bind_eq_some.mp hexec

/-- Fixed-point facts recovered from one successful source-shaped withdrawal. -/
structure SingleSidedTokenWithdrawalRunRefinements
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    (result : SingleSidedTokenWithdrawalExecutionResult) : Prop where
  tokenBalanceEq :
    result.pre.tokenBalanceRaw = (inputBalance : ℤ) * inputScalar
  tokenAmountEq :
    result.pre.tokenAmountRaw = (inputAmount : ℤ) * inputScalar
  poolSupplyEq :
    result.pre.poolSupplyRaw = (poolSupply : ℤ) * (BONE / STROOP)
  tokenBalancePositive : 0 < result.pre.tokenBalanceRaw
  tokenAmountPositive : 0 < result.pre.tokenAmountRaw
  poolSupplyPositive : 0 < result.pre.poolSupplyRaw
  weightRawEq :
    result.pre.weightRaw = (inputWeight : ℤ) * (BONE / STROOP)
  feeMultiplierPositive : 0 < result.pre.feeMultiplierRaw
  feeMultiplierEq :
    (result.pre.feeMultiplierRaw : ℝ) / BONE =
      1 - singleSidedWithdrawalFeeRate
        ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
  beforeFeePositive : 0 < result.pre.beforeFeeRaw
  beforeFeeCeil :
    IsCeil result.pre.beforeFeeRaw
      ((result.pre.tokenAmountRaw : ℝ) /
        ((result.pre.feeMultiplierRaw : ℝ) / BONE))
  baseFloor :
    IsFloor result.pre.baseRaw
      ((BONE : ℝ) *
        (1 - (result.pre.beforeFeeRaw : ℝ) /
          result.pre.tokenBalanceRaw))
  cpowExec :
    lowerBelowCPowExecution result.pre.baseRaw result.pre.weightRaw inputWeight =
      some result.cpow
  newPoolSupplyFloor :
    IsFloor result.newPoolSupplyRaw
      ((result.cpow.powerRaw : ℝ) * result.pre.poolSupplyRaw / BONE)
  poolAmountEq :
    result.poolAmountRaw = result.pre.poolSupplyRaw - result.newPoolSupplyRaw
  outputCeil :
    IsCeil result.output
      ((result.poolAmountRaw : ℝ) / (BONE / STROOP : ℕ))

/-- A successful checked execution supplies every operation-level refinement. -/
theorem calcLpTokenAmountGivenTokenWithdrawalAmountExecution_refines
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenWithdrawalExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hinputAmount : 0 < inputAmount) (hpoolSupply : 0 < poolSupply)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcLpTokenAmountGivenTokenWithdrawalAmountExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    SingleSidedTokenWithdrawalRunRefinements
      (inputBalance := inputBalance) (inputScalar := inputScalar)
      (inputAmount := inputAmount) (poolSupply := poolSupply)
      (inputWeight := inputWeight) (fee := fee) result := by
  obtain ⟨pre, hpreExec, hfinishExec⟩ :=
    calcLpTokenAmountGivenTokenWithdrawalAmountExecution_success hexec
  rcases singleSidedTokenWithdrawalFinishExecution_success hfinishExec with
    ⟨hpre, hcpow, hnewSupply, hpoolAmount, hdownscale, houtput⟩
  subst pre
  rcases singleSidedTokenWithdrawalPrefixExecution_success hpreExec with
    ⟨htokenBalance, htokenAmount, hsupply, hfee, hweight,
      hweightComplement, hweightedFee, hfeeMultiplier, hbeforeFee,
      hnewBalance, hbase⟩
  have htokenBalanceEq := withdrawal_i128_mul_success_eq htokenBalance
  have htokenAmountEq := withdrawal_i128_mul_success_eq htokenAmount
  have hsupplyEq := withdrawal_i128_mul_success_eq hsupply
  have hfeeEq := withdrawal_i128_mul_success_eq hfee
  have hweightEq := withdrawal_i128_mul_success_eq hweight
  have htokenBalance0 : 0 < result.pre.tokenBalanceRaw := by
    rw [htokenBalanceEq]
    positivity
  have htokenAmount0 : 0 < result.pre.tokenAmountRaw := by
    rw [htokenAmountEq]
    positivity
  have hsupply0 : 0 < result.pre.poolSupplyRaw := by
    rw [hsupplyEq]
    exact_mod_cast Nat.mul_pos hpoolSupply (by norm_num [BONE, STROOP])
  have hweightLt : inputWeight < STROOP :=
    lt_of_le_of_lt hweightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have hfeeLt : fee < STROOP :=
    lt_of_le_of_lt hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hweightComplementEq := withdrawal_i256_sub_success_eq hweightComplement
  let weightedFeeExpected : ℤ :=
    (STROOP - inputWeight) * fee * (BONE / (STROOP * STROOP) : ℕ)
  have hweightedFloor := (i256_fixed_mul_floor_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hweightedFee).1
  have hweightedExact :
      ((((result.pre.weightComplementRaw * result.pre.feeRaw : ℤ) : ℝ) /
          BONE)) = (weightedFeeExpected : ℝ) := by
    rw [hweightComplementEq, hweightEq, hfeeEq]
    dsimp [weightedFeeExpected]
    push_cast
    norm_num [BONE, STROOP]
    ring
  have hweightedFeeEq : result.pre.weightedFeeRaw = weightedFeeExpected := by
    apply withdrawal_isFloor_integer_eq
    rw [← hweightedExact]
    exact hweightedFloor
  have hfeeMultiplierRawEq := withdrawal_i256_sub_success_eq hfeeMultiplier
  have hfeeMultiplierEq :
      (result.pre.feeMultiplierRaw : ℝ) / BONE =
        1 - singleSidedWithdrawalFeeRate
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP) := by
    rw [hfeeMultiplierRawEq, hweightedFeeEq,
      singleSidedWithdrawalFeeRate]
    dsimp [weightedFeeExpected]
    push_cast
    norm_num [BONE, STROOP]
    ring
  have hweight0 : 0 ≤ (inputWeight : ℝ) / STROOP := by positivity
  have hweight1 : (inputWeight : ℝ) / STROOP ≤ 1 := by
    apply (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
    exact_mod_cast (le_trans hweightUpper (by norm_num [MAX_WEIGHT, STROOP]))
  have hfee0 : 0 ≤ (fee : ℝ) / STROOP := by positivity
  have hfee1 : (fee : ℝ) / STROOP ≤ 1 := by
    apply (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
    exact_mod_cast hfeeLt.le
  have hfeeMultiplierBounds := single_sided_withdrawal_fee_multiplier_bounds
    hweight0 hweight1 hfee0 hfee1
  have hfeeMultiplier0 : 0 < result.pre.feeMultiplierRaw := by
    have hreal : (0 : ℝ) < result.pre.feeMultiplierRaw / BONE := by
      rw [hfeeMultiplierEq]
      rw [singleSidedWithdrawalFeeRate]
      have hfeeStrict : (fee : ℝ) / STROOP < 1 := by
        apply (div_lt_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
        exact_mod_cast hfeeLt
      have hweightedLeFee :
          (1 - (inputWeight : ℝ) / STROOP) * ((fee : ℝ) / STROOP) ≤
            (fee : ℝ) / STROOP := by
        simpa using mul_le_mul_of_nonneg_right (by linarith :
          1 - (inputWeight : ℝ) / STROOP ≤ 1) hfee0
      linarith
    have hrawReal : (0 : ℝ) < result.pre.feeMultiplierRaw := by
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      rcases div_pos_iff.mp hreal with hpos | hneg
      · exact hpos.1
      · linarith [hneg.2]
    exact_mod_cast hrawReal
  have hfeeMultiplierRange := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked
      (BONE - result.pre.weightedFeeRaw) = some result.pre.feeMultiplierRaw
      from hfeeMultiplier)
  have hfeeMultiplierNatMax :
      (result.pre.feeMultiplierRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hfeeMultiplier0.le]
    rw [← hfeeMultiplierRange.2]
    exact hfeeMultiplierRange.1.2
  have hbeforeFeeCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hfeeMultiplier0) hfeeMultiplierNatMax
      hbeforeFee).1
  have hfeeMultiplierCast :
      (result.pre.feeMultiplierRaw.toNat : ℝ) =
        result.pre.feeMultiplierRaw := by
    exact_mod_cast Int.toNat_of_nonneg hfeeMultiplier0.le
  have hbeforeFeeCeil :
      IsCeil result.pre.beforeFeeRaw
        ((result.pre.tokenAmountRaw : ℝ) /
          ((result.pre.feeMultiplierRaw : ℝ) / BONE)) := by
    rw [hfeeMultiplierCast] at hbeforeFeeCeilRaw
    convert hbeforeFeeCeilRaw using 1
    push_cast
    field_simp [show (result.pre.feeMultiplierRaw : ℝ) ≠ 0 by
      exact_mod_cast ne_of_gt hfeeMultiplier0]
  have hbeforeFee0 : 0 < result.pre.beforeFeeRaw := by
    have hexact :
        0 < (result.pre.tokenAmountRaw : ℝ) /
          ((result.pre.feeMultiplierRaw : ℝ) / BONE) := by
      exact div_pos (by exact_mod_cast htokenAmount0)
        (div_pos (by exact_mod_cast hfeeMultiplier0) (by norm_num [BONE]))
    have hraw : (0 : ℝ) < result.pre.beforeFeeRaw :=
      lt_of_lt_of_le hexact hbeforeFeeCeil.le
    exact_mod_cast hraw
  have hnewBalanceEq := withdrawal_i256_sub_success_eq hnewBalance
  have htokenBalanceRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      ((inputBalance : ℤ) * inputScalar) = some result.pre.tokenBalanceRaw
      from htokenBalance)
  have htokenBalanceNatMax :
      (result.pre.tokenBalanceRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg htokenBalance0.le]
    calc
      result.pre.tokenBalanceRaw ≤ SorobanFixedPointMath.I128.maxValue := by
        rw [← htokenBalanceRange.2]
        exact htokenBalanceRange.1.2
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hbaseFloorRaw := (i256_fixed_div_floor_success_refines
    (Int.pos_iff_toNat_pos.mp htokenBalance0) htokenBalanceNatMax hbase).1
  have htokenBalanceCast :
      (result.pre.tokenBalanceRaw.toNat : ℝ) =
        result.pre.tokenBalanceRaw := by
    exact_mod_cast Int.toNat_of_nonneg htokenBalance0.le
  have hbaseFloor :
      IsFloor result.pre.baseRaw
        ((BONE : ℝ) *
          (1 - (result.pre.beforeFeeRaw : ℝ) /
            result.pre.tokenBalanceRaw)) := by
    rw [htokenBalanceCast, hnewBalanceEq] at hbaseFloorRaw
    convert hbaseFloorRaw using 1
    push_cast
    field_simp [show (result.pre.tokenBalanceRaw : ℝ) ≠ 0 by
      exact_mod_cast ne_of_gt htokenBalance0]
    ring
  have hnewSupplyFloor := (i256_fixed_mul_floor_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hnewSupply).1
  have hpoolAmountEq := withdrawal_i256_sub_success_eq hpoolAmount
  have hdownscaleCeil := (i256_fixed_div_ceil_success_refines
    (by norm_num [BONE, STROOP]) (by
      norm_num [BONE, STROOP, SorobanFixedPointMath.I256.maxValue])
      hdownscale).1
  have houtputEq : result.output = result.downscaledRaw := by
    exact (SorobanFixedPointMath.I128.checked_eq_some_iff.mp houtput).2.symm
  have houtputCeil :
      IsCeil result.output
        ((result.poolAmountRaw : ℝ) / (BONE / STROOP : ℕ)) := by
    rw [houtputEq]
    convert hdownscaleCeil using 1
    push_cast
    ring
  exact {
    tokenBalanceEq := htokenBalanceEq
    tokenAmountEq := htokenAmountEq
    poolSupplyEq := hsupplyEq
    tokenBalancePositive := htokenBalance0
    tokenAmountPositive := htokenAmount0
    poolSupplyPositive := hsupply0
    weightRawEq := hweightEq
    feeMultiplierPositive := hfeeMultiplier0
    feeMultiplierEq := hfeeMultiplierEq
    beforeFeePositive := hbeforeFee0
    beforeFeeCeil := hbeforeFeeCeil
    baseFloor := hbaseFloor
    cpowExec := hcpow
    newPoolSupplyFloor := by
      simpa only [Int.cast_mul] using hnewSupplyFloor
    poolAmountEq := hpoolAmountEq
    outputCeil := houtputCeil
  }

/-
Every successful source-shaped exact-token-output withdrawal has pool-adverse
error strictly below `4751 / 100000 = 4.751%` of the adjusted weighted
minimum-fee value.
-/
theorem calc_lp_token_amount_given_token_withdrawal_amount_execution_adverse_error_lt_precise_fee_share
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenWithdrawalExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hinputAmount : 0 < inputAmount) (hpoolSupply : 0 < poolSupply)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hinputRatio : inputAmount * STROOP ≤ inputBalance * MAX_OUT_RATIO)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcLpTokenAmountGivenTokenWithdrawalAmountExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    singleSidedTokenWithdrawalIdealInput (poolSupply : ℝ)
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
          ((inputAmount : ℝ) / inputBalance) - (result.output : ℝ) <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue (poolSupply : ℝ)
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
          ((inputAmount : ℝ) / inputBalance) := by
  have href := calcLpTokenAmountGivenTokenWithdrawalAmountExecution_refines
    hinputBalance hinputScalar hinputAmount hpoolSupply hweightUpper hfeeUpper
      hexec
  let inputBalanceRaw : ℝ := result.pre.tokenBalanceRaw
  let inputAmountRaw : ℝ := result.pre.tokenAmountRaw
  let poolSupplyRaw : ℝ := result.pre.poolSupplyRaw
  let scale : ℝ := BONE / STROOP
  let weight : ℝ := (inputWeight : ℝ) / STROOP
  let feeRate : ℝ := (fee : ℝ) / STROOP
  let nominalRatio : ℝ := inputAmountRaw / inputBalanceRaw
  let feeMultiplier : ℝ := (result.pre.feeMultiplierRaw : ℝ) / BONE
  let beforeFeeRatio : ℝ :=
    (result.pre.beforeFeeRaw : ℝ) / inputBalanceRaw
  let computedBase : ℝ := (result.pre.baseRaw : ℝ) / BONE
  let computedPower : ℝ := result.cpow.powerRaw
  have hinputBalanceRaw : 0 < inputBalanceRaw := by
    dsimp [inputBalanceRaw]
    exact_mod_cast href.tokenBalancePositive
  have hinputAmountRaw : 0 < inputAmountRaw := by
    dsimp [inputAmountRaw]
    exact_mod_cast href.tokenAmountPositive
  have hpoolSupplyRaw : 0 < poolSupplyRaw := by
    dsimp [poolSupplyRaw]
    exact_mod_cast href.poolSupplyPositive
  have hscale : 0 < scale := by norm_num [scale, BONE, STROOP]
  have hnominal : nominalRatio = inputAmountRaw / inputBalanceRaw := rfl
  have hnominalOriginal :
      nominalRatio = (inputAmount : ℝ) / inputBalance := by
    dsimp [nominalRatio, inputAmountRaw, inputBalanceRaw]
    rw [href.tokenAmountEq, href.tokenBalanceEq]
    push_cast
    have hscalar : (inputScalar : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hnominalUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP := by
    rw [hnominalOriginal]
    have hratioReal :
        (inputAmount : ℝ) * STROOP ≤
          (inputBalance : ℝ) * MAX_OUT_RATIO := by
      exact_mod_cast hinputRatio
    exact (div_le_div_iff₀ (by exact_mod_cast hinputBalance)
      (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2 (by
        simpa [mul_comm] using hratioReal)
  have hweightLowerReal : (MIN_WEIGHT : ℝ) / STROOP ≤ weight := by
    dsimp [weight]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hweightLower)
      (by norm_num [STROOP])
  have hweightUpperReal : weight ≤ (MAX_WEIGHT : ℝ) / STROOP := by
    dsimp [weight]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hweightUpper)
      (by norm_num [STROOP])
  have hweightBounds := single_sided_token_deposit_configured_weight_bounds
    hweightLowerReal hweightUpperReal
  have hfee0 : 0 ≤ feeRate := by positivity
  have hfeeUpperReal : feeRate ≤ (MAX_FEE : ℝ) / STROOP := by
    dsimp [feeRate]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfeeUpper)
      (by norm_num [STROOP])
  have hfee1 : feeRate ≤ 1 :=
    le_trans hfeeUpperReal (by norm_num [MAX_FEE, STROOP])
  have hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate := by
    exact href.feeMultiplierEq
  have hbeforeFeeRatio :
      beforeFeeRatio = (result.pre.beforeFeeRaw : ℝ) / inputBalanceRaw := rfl
  have hbeforeFeeCeil :
      IsCeil result.pre.beforeFeeRaw (inputAmountRaw / feeMultiplier) := by
    simpa [inputAmountRaw, feeMultiplier] using href.beforeFeeCeil
  have hcomputedBase :
      computedBase = (result.pre.baseRaw : ℝ) / BONE := rfl
  have hbaseFloor :
      IsFloor result.pre.baseRaw
        ((BONE : ℝ) * (1 - beforeFeeRatio)) := by
    simpa [beforeFeeRatio, inputBalanceRaw] using href.baseFloor
  have hcaller := single_sided_token_withdrawal_configured_caller_bounds
    hinputBalanceRaw hinputAmountRaw hnominal hweightLowerReal
      hweightUpperReal hfee1 hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil
      hcomputedBase hbaseFloor
  have hbaseGuard := lowerBelowCPowExecution_base_bounds href.cpowExec
  have hbasePositive : 0 < computedBase := by
    dsimp [computedBase]
    have hraw : (0 : ℤ) < result.pre.baseRaw :=
      lt_of_lt_of_le (by omega) hbaseGuard.1
    exact div_pos (by exact_mod_cast hraw) (by norm_num [BONE])
  have hbaseStrict : computedBase < 1 := hcaller.2.2.2.2
  have hbaseRawStrict : result.pre.baseRaw < BONE := by
    have hreal : (result.pre.baseRaw : ℝ) < BONE := by
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      have := (div_lt_one hB).mp (by simpa [computedBase] using hbaseStrict)
      simpa using this
    exact_mod_cast hreal
  have hweightNat0 : 0 < inputWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hweightLower
  have hweightNatUpper : inputWeight < STROOP :=
    lt_of_le_of_lt hweightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have hnewSupplyFloor :
      IsFloor result.newPoolSupplyRaw
        (poolSupplyRaw * (computedPower / (BONE : ℝ))) := by
    convert href.newPoolSupplyFloor using 1
    dsimp [poolSupplyRaw, computedPower]
    ring
  have hpoolAmount :
      (result.poolAmountRaw : ℝ) =
        poolSupplyRaw - result.newPoolSupplyRaw := by
    rw [href.poolAmountEq]
    simp [poolSupplyRaw]
  have houtputCeil :
      IsCeil result.output ((result.poolAmountRaw : ℝ) / scale) := by
    convert href.outputCeil using 1
    norm_num [scale, BONE, STROOP]
  have hrawResult :
      singleSidedTokenWithdrawalIdealInput (poolSupplyRaw / scale)
            weight feeRate nominalRatio - (result.output : ℝ) <
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
            (poolSupplyRaw / scale) weight feeRate nominalRatio := by
    cases hcpowCase : result.cpow with
    | integer integerPart wholeRaw =>
        have hcpowExec :
            lowerBelowCPowExecution result.pre.baseRaw result.pre.weightRaw
                inputWeight = some (.integer integerPart wholeRaw) := by
          simpa [hcpowCase] using href.cpowExec
        exact False.elim <| lowerBelowCPowExecution_configured_not_integer
          hweightNat0 hweightNatUpper hcpowExec
    | fractional integerPart remainderStroop wholeRaw approx powerRaw =>
        have hcpowExec :
            lowerBelowCPowExecution result.pre.baseRaw result.pre.weightRaw
                inputWeight =
              some (.fractional integerPart remainderStroop wholeRaw approx
                powerRaw) := by
          simpa [hcpowCase] using href.cpowExec
        rcases lowerBelowCPowExecution_configured_components hweightNat0
          hweightNatUpper hcpowExec with
            ⟨hinteger, hremainder, hwhole, happ, hpower⟩
        let remainRaw : ℤ := inputWeight * (BONE / STROOP)
        have happExec :
            lowerBelowApproxExecution result.pre.baseRaw remainRaw =
              some approx := by
          simpa [remainRaw] using happ
        have hcomposedFloorRaw := (i256_fixed_mul_floor_success_refines
          (by norm_num [BONE]) (by
            norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hpower).1
        have hcomposedFloor :
            IsFloor powerRaw (approx.partialRaw : ℝ) := by
          rw [hwhole] at hcomposedFloorRaw
          convert hcomposedFloorRaw using 1
          push_cast
          norm_num [BONE]
        have hcomputedPower : computedPower = (powerRaw : ℝ) := by
          dsimp [computedPower]
          rw [hcpowCase]
          rfl
        have hremain0 : 0 < remainRaw := by
          dsimp [remainRaw]
          exact_mod_cast Nat.mul_pos hweightNat0
            (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
        have hfirstFloorRaw := lowerBelowApproxExecution_first_term_refines
          happExec
        have hfirstFloor :
            IsFloor (exactInputApproxStateAt approx.xRaw remainRaw 1).term
              (exactInputBinomialTerm weight computedBase 1) := by
          rw [(exactInputBinomialTerm_one hweightBounds.1.le
            hbaseStrict.le).1]
          convert hfirstFloorRaw using 1
          have hx := (lowerBelowApproxExecution_success happExec).choose_spec.1
          rw [hx]
          dsimp [remainRaw, weight, computedBase]
          push_cast
          norm_num [BONE, STROOP]
          ring
        obtain ⟨finalState, hxRaw, hsteps, hunadjusted, hfinalTerm,
          hn1, hn50, hcontinued, hfirstCorrection, haboveCorrection,
          hbelowCorrection, hplain⟩ := lowerBelowApproxExecution_success happExec
        by_cases hnOne : approx.iterations = 1
        · have hpartial := lowerBelowApproxExecution_first_sum
            hbaseRawStrict hremain0 happExec hnOne
          have hstopRaw := lowerBelowApproxExecution_final_le_of_lt_fifty
            happExec (by omega)
          have hstop :
              |((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ)| ≤
                CPOW_PRECISION := by
            rw [← hnOne]
            exact_mod_cast hstopRaw
          exact baseline_single_sided_token_withdrawal_first_term_adverse_error_lt_precise_fee_share
            hinputBalanceRaw hinputAmountRaw hnominal hweightLowerReal
              hweightUpperReal hfee1 hfeeMultiplier hbeforeFeeRatio
              hbeforeFeeCeil hcomputedBase hbaseFloor hbasePositive hfirstFloor
              hstop (by exact_mod_cast hpartial.2) hcomputedPower hcomposedFloor
              hpoolSupplyRaw hscale hnewSupplyFloor hpoolAmount houtputCeil
        · have hn2 : 2 ≤ approx.iterations := by omega
          have hpartial := lowerBelowApproxExecution_later_sum
            hbaseRawStrict happExec hn2
          by_cases hnTwo : approx.iterations = 2
          · obtain ⟨stepState, hstep⟩ := lowerBelowApproxExecution_prefix
              happExec 2 (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw 2 = stepState := by
              simp [exactInputApproxStateAt, hstep]
            have hstepFacts := exactInputApproxSteps_refinements
              (iteration := 2) (by omega) (by omega) hstep
            have hcoefficientFloor :
                IsFloor stepState.coefficientProduct
                  ((BONE : ℝ) * (weight - 1) * (computedBase - 1)) := by
              convert hstepFacts.1 using 1
              rw [hxRaw]
              dsimp [remainRaw, weight, computedBase]
              push_cast
              norm_num [BONE, STROOP]
              ring
            have hmultiplyFloor :
                IsFloor stepState.multiplied
                  (((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ) *
                    stepState.coefficientProduct / BONE) := by
              simpa using hstepFacts.2.1
            have hdivideFloor :
                IsFloor stepState.term ((stepState.multiplied : ℝ) / 2) := by
              simpa using hstepFacts.2.2.1
            exact baseline_single_sided_token_withdrawal_second_term_adverse_error_lt_precise_fee_share
              hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
                hweightLowerReal hweightUpperReal hfee0 hfeeUpperReal
                hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase
                hbaseFloor hbasePositive hfirstFloor hcoefficientFloor
                hmultiplyFloor hdivideFloor (by
                  have htermAt :
                      (exactInputApproxStateAt approx.xRaw remainRaw 2).term =
                        stepState.term := congrArg ExactInputApproxState.term hstepAt
                  rw [hnTwo] at hpartial
                  rw [htermAt] at hpartial
                  have hpartialInt :
                      approx.partialRaw = BONE +
                        (exactInputApproxStateAt approx.xRaw remainRaw 1).term +
                        2 * stepState.term := by
                    norm_num [Finset.sum_range_succ] at hpartial ⊢
                    linarith
                  exact_mod_cast hpartialInt)
                hcomputedPower hcomposedFloor hpoolSupplyRaw hscale
                hnewSupplyFloor hpoolAmount houtputCeil
          · have hn3 : 3 ≤ approx.iterations := by omega
            let coefficientProduct : ℕ → ℤ := fun k ↦
              (exactInputApproxStateAt approx.xRaw remainRaw k).coefficientProduct
            let multiplied : ℕ → ℤ := fun k ↦
              (exactInputApproxStateAt approx.xRaw remainRaw k).multiplied
            let computedTerm : ℕ → ℤ := fun k ↦
              (exactInputApproxStateAt approx.xRaw remainRaw k).term
            have hcoefficientFloor : ∀ k, 1 ≤ k → k < approx.iterations →
                IsFloor (coefficientProduct (k + 1))
                  ((BONE : ℝ) * (weight - (k : ℝ)) *
                    (computedBase - 1)) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ := lowerBelowApproxExecution_prefix
                happExec (k + 1) (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [coefficientProduct]
              rw [hstepAt]
              convert hstepFacts.1 using 1
              rw [hxRaw]
              dsimp [remainRaw, weight, computedBase]
              push_cast
              norm_num [BONE, STROOP]
              field_simp
              ring
            have hmultiplyFloor : ∀ k, 1 ≤ k → k < approx.iterations →
                IsFloor (multiplied (k + 1))
                  ((computedTerm k : ℝ) *
                    (coefficientProduct (k + 1) : ℝ) / BONE) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ := lowerBelowApproxExecution_prefix
                happExec (k + 1) (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [multiplied, computedTerm, coefficientProduct]
              rw [hstepAt]
              simpa using hstepFacts.2.1
            have hdivideFloor : ∀ k, 1 ≤ k → k < approx.iterations →
                IsFloor (computedTerm (k + 1))
                  ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ := lowerBelowApproxExecution_prefix
                happExec (k + 1) (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [computedTerm, multiplied]
              rw [hstepAt]
              simpa [Nat.cast_add, Nat.cast_one] using hstepFacts.2.2.1
            exact baseline_single_sided_token_withdrawal_later_adverse_error_lt_precise_fee_share
              coefficientProduct multiplied computedTerm
                hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
                hweightLowerReal hweightUpperReal hfee0 hfeeUpperReal
                hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase
                hbaseFloor hbasePositive hn3 hn50 (by
                  intro k hk hkn
                  exact_mod_cast hcontinued k hk hkn)
                hfirstFloor hcoefficientFloor hmultiplyFloor hdivideFloor
                (by exact_mod_cast hpartial) hcomputedPower hcomposedFloor
                hpoolSupplyRaw hscale hnewSupplyFloor hpoolAmount houtputCeil
  have hpoolSupplyOriginal : poolSupplyRaw / scale = (poolSupply : ℝ) := by
    dsimp [poolSupplyRaw, scale]
    rw [href.poolSupplyEq]
    push_cast
    norm_num [BONE, STROOP]
  rw [hpoolSupplyOriginal, hnominalOriginal] at hrawResult
  simpa [weight, feeRate] using hrawResult

end CometPool
