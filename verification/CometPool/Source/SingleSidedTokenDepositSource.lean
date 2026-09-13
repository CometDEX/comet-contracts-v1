import CometPool.Source.ExactOutputSwapSource
import CometPool.Operations.SingleSidedTokenDeposit

set_option maxRecDepth 65536

namespace CometPool

/-!
Executable, source-shaped models for the positive-input arithmetic used by
`dep_tokn_amt_in_get_lp_tokns_out`. The common checked recurrence is reused
from `ExactInputSwapSource`; this file models the above-one, lower-directed
`c_pow` corrections and the complete caller arithmetic.
-/

/-- Result of the above-one, lower-directed approximation path. -/
structure LowerAboveApproxExecutionResult where
  iterations : ℕ
  xRaw : ℤ
  unadjustedSumRaw : ℤ
  finalTermRaw : ℤ
  partialRaw : ℤ
deriving DecidableEq

/-- Source execution of `c_pow_approx(..., round_up = false)` above one. -/
def lowerAboveApproxExecution
    (baseRaw remainRaw : ℤ) : Option LowerAboveApproxExecutionResult := do
  let xRaw ← SorobanFixedPointMath.I256.sub baseRaw BONE
  let stopped ← exactInputApproxFindStop xRaw remainRaw MAX_CPOW_ITERS 0
  let partialRaw ←
    if stopped.iterations = 1 ∧ xRaw ≠ 0 ∧ stopped.state.term ≠ 0 then
      SorobanFixedPointMath.I256.sub stopped.state.sum 1
    else if stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0 then
      SorobanFixedPointMath.I256.sub stopped.state.sum stopped.state.term
    else
      some stopped.state.sum
  some {
    iterations := stopped.iterations
    xRaw
    unadjustedSumRaw := stopped.state.sum
    finalTermRaw := stopped.state.term
    partialRaw
  }

private theorem deposit_i256_sub_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x - y) = some result from hexec)
  exact h.2.symm

private theorem deposit_i256_add_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x + y) = some result from hexec)
  exact h.2.symm

/-- Successful execution exposes exactly the prefixes reached by the source loop. -/
theorem lowerAboveApproxExecution_success
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result) :
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
        (¬(result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
              result.finalTermRaw ≠ 0) ∧
            ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
              result.finalTermRaw > 0) →
          result.partialRaw = result.unadjustedSumRaw) := by
  rw [lowerAboveApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := deposit_i256_sub_success_eq hxRaw
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
    refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_⟩
    · simpa [hxEq] using hfind.2.2.2.1
    · intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
    · intro _
      exact deposit_i256_sub_success_eq hpartialRaw
    · intro hnot
      exact False.elim (hnot.1 hfirst.1)
    · intro hnot
      exact False.elim (hnot.1 hfirst)
  · rw [if_neg hfirst] at hafterStop
    by_cases hlater :
        stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0
    · rw [if_pos hlater] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_⟩
      · simpa [hxEq] using hfind.2.2.2.1
      · intro k hk1 hkn
        simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
      · intro hyes
        exact False.elim (hfirst hyes)
      · intro _
        exact deposit_i256_sub_success_eq hpartialRaw
      · intro hnot
        exact False.elim (hnot.2 hlater)
    · rw [if_neg hlater] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      refine ⟨stopped.state, hxEq, ?_, rfl, rfl, hn1, hn50, ?_, ?_, ?_, ?_⟩
      · simpa [hxEq] using hfind.2.2.2.1
      · intro k hk1 hkn
        simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
      · intro hyes
        exact False.elim (hfirst hyes)
      · intro hyes
        exact False.elim (hlater hyes)
      · intro _
        exact Option.some.inj hpartialRaw.symm

/-- Successful lower-directed approximation exposes every executed prefix. -/
theorem lowerAboveApproxExecution_prefix
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result) :
    ∀ k, 1 ≤ k → k ≤ result.iterations →
      ∃ state, exactInputApproxSteps result.xRaw remainRaw k = some state := by
  rw [lowerAboveApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := deposit_i256_sub_success_eq hxRaw
  have hfind := exactInputApproxFindStop_success hstopped
  by_cases hfirst :
      stopped.iterations = 1 ∧ xRaw ≠ 0 ∧ stopped.state.term ≠ 0
  · rw [if_pos hfirst] at hafterStop
    rcases Option.bind_eq_some.mp hafterStop with
      ⟨partialRaw, hpartialRaw, hresult⟩
    have hresultEq := Option.some.inj hresult
    subst result
    intro k hk1 hkn
    simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn
  · rw [if_neg hfirst] at hafterStop
    by_cases hlater :
        stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0
    · rw [if_pos hlater] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn
    · rw [if_neg hlater] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn

/-- A lower-directed approximation that returns before iteration 50 stopped by precision. -/
theorem lowerAboveApproxExecution_final_le_of_lt_fifty
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result)
    (hlt : result.iterations < 50) :
    |(exactInputApproxStateAt result.xRaw remainRaw result.iterations).term| ≤
      CPOW_PRECISION := by
  rw [lowerAboveApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := deposit_i256_sub_success_eq hxRaw
  by_cases hfirst :
      stopped.iterations = 1 ∧ xRaw ≠ 0 ∧ stopped.state.term ≠ 0
  · rw [if_pos hfirst] at hafterStop
    rcases Option.bind_eq_some.mp hafterStop with
      ⟨partialRaw, hpartialRaw, hresult⟩
    have hresultEq := Option.some.inj hresult
    subst result
    change stopped.iterations < 50 at hlt
    have hcap : stopped.iterations < 0 + MAX_CPOW_ITERS := by
      simpa [MAX_CPOW_ITERS] using hlt
    simpa [MAX_CPOW_ITERS, hxEq] using
      exactInputApproxFindStop_final_le_of_lt_cap hstopped hcap
  · rw [if_neg hfirst] at hafterStop
    by_cases hlater :
        stopped.iterations ≠ 1 ∧ xRaw > 0 ∧ stopped.state.term > 0
    · rw [if_pos hlater] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      change stopped.iterations < 50 at hlt
      have hcap : stopped.iterations < 0 + MAX_CPOW_ITERS := by
        simpa [MAX_CPOW_ITERS] using hlt
      simpa [MAX_CPOW_ITERS, hxEq] using
        exactInputApproxFindStop_final_le_of_lt_cap hstopped hcap
    · rw [if_neg hlater] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      change stopped.iterations < 50 at hlt
      have hcap : stopped.iterations < 0 + MAX_CPOW_ITERS := by
        simpa [MAX_CPOW_ITERS] using hlt
      simpa [MAX_CPOW_ITERS, hxEq] using
        exactInputApproxFindStop_final_le_of_lt_cap hstopped hcap

/-- With a unit base, the lower-directed approximation returns exactly BONE. -/
theorem lowerAboveApproxExecution_unit
    {remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hexec : lowerAboveApproxExecution BONE remainRaw = some result) :
    result.partialRaw = BONE := by
  obtain ⟨state, hx, hsteps, hsum, hterm, hn1, hn50, hcontinued,
      hfirst, hlater, hplain⟩ := lowerAboveApproxExecution_success hexec
  have hx0 : result.xRaw = 0 := by simpa using hx
  have hstateSum : state.sum = BONE := by
    rw [hx0] at hsteps
    exact exactInputApproxSteps_unit_sum hn50 hsteps
  have hnotFirst :
      ¬(result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
        result.finalTermRaw ≠ 0) := by simp [hx0]
  have hnotLater :
      ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
        result.finalTermRaw > 0) := by simp [hx0]
  rw [hplain ⟨hnotFirst, hnotLater⟩, hsum, hstateSum]

/-- The first lower-directed recurrence term has its production floor semantics. -/
theorem lowerAboveApproxExecution_first_term_refines
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result) :
    IsFloor
      (exactInputApproxStateAt result.xRaw remainRaw 1).term
      (((remainRaw : ℝ) * (result.xRaw : ℝ)) / BONE) := by
  obtain ⟨state, hstate⟩ := lowerAboveApproxExecution_prefix hexec 1
    (by omega) (lowerAboveApproxExecution_success hexec).choose_spec.2.2.2.2.1
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

/-- Every executed above-one lower-directed term has binomial parity sign. -/
theorem lowerAboveApproxExecution_term_sign
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hremainUpper : remainRaw < BONE)
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result) :
    ∀ k, 1 ≤ k → k ≤ result.iterations →
      (k % 2 = 1 →
          0 ≤ (exactInputApproxStateAt result.xRaw remainRaw k).term) ∧
        (k % 2 = 0 →
          (exactInputApproxStateAt result.xRaw remainRaw k).term < 0) := by
  have hsuccess := lowerAboveApproxExecution_success hexec
  have hx : 0 < result.xRaw := by rw [hsuccess.choose_spec.1]; omega
  have hn50 := hsuccess.choose_spec.2.2.2.2.2.1
  have hcontinued := hsuccess.choose_spec.2.2.2.2.2.2.1
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk1 hkn
      by_cases hkOne : k = 1
      · subst k
        constructor
        · intro _
          have hfirst := lowerAboveApproxExecution_first_term_refines hexec
          apply hfirst.nonnegative_of_nonnegative_exact
          have hxReal : (0 : ℝ) < result.xRaw := by exact_mod_cast hx
          have hremainReal : (0 : ℝ) < remainRaw := by exact_mod_cast hremain0
          positivity
        · norm_num
      · have hk2 : 2 ≤ k := by omega
        obtain ⟨state, hstate⟩ := lowerAboveApproxExecution_prefix hexec k hk1 hkn
        have hstateAt :
            exactInputApproxStateAt result.xRaw remainRaw k = state := by
          simp [exactInputApproxStateAt, hstate]
        have hstep := exactOutputApproxStep_sign hx hremainUpper hk2
          (le_trans hkn hn50) hstate
        have hprev1 : 1 ≤ k - 1 := by omega
        have hprevLe : k - 1 ≤ result.iterations := by omega
        have hprev := ih (k - 1) (by omega) hprev1 hprevLe
        constructor
        · intro hkOdd
          have hprevEven : (k - 1) % 2 = 0 := by omega
          rw [hstateAt]
          exact hstep.2 (hprev.2 hprevEven)
        · intro hkEven
          have hprevOdd : (k - 1) % 2 = 1 := by omega
          have hprevNonnegative := hprev.1 hprevOdd
          have hprevLarge := hcontinued (k - 1) hprev1 (by omega)
          have hprevPositive :
              0 < (exactInputApproxStateAt result.xRaw remainRaw (k - 1)).term := by
            rw [abs_of_nonneg hprevNonnegative] at hprevLarge
            omega
          rw [hstateAt]
          exact hstep.1 hprevPositive

/-- A first stop either returns BONE or applies the one-unit lower correction. -/
theorem lowerAboveApproxExecution_first_sum
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result)
    (hn : result.iterations = 1) :
    let firstTerm := (exactInputApproxStateAt result.xRaw remainRaw 1).term
    (firstTerm = 0 ∧ result.partialRaw = BONE) ∨
      (0 < firstTerm ∧ result.partialRaw = BONE + firstTerm - 1) := by
  obtain ⟨state, hx, hsteps, hsum, hterm, _, hn50, _, hfirst, _, hplain⟩ :=
    lowerAboveApproxExecution_success hexec
  have hxPositive : 0 < result.xRaw := by rw [hx]; omega
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw 1 = state := by
    have hstepsOne : exactInputApproxSteps result.xRaw remainRaw 1 = some state := by
      simpa [hn] using hsteps
    simp [exactInputApproxStateAt, hstepsOne]
  have htermAt : result.finalTermRaw =
      (exactInputApproxStateAt result.xRaw remainRaw 1).term := by
    rw [hterm, hstateAt]
  have hfirstNonnegative :
      0 ≤ (exactInputApproxStateAt result.xRaw remainRaw 1).term := by
    have hfloor := lowerAboveApproxExecution_first_term_refines hexec
    apply hfloor.nonnegative_of_nonnegative_exact
    have hxReal : (0 : ℝ) < result.xRaw := by exact_mod_cast hxPositive
    positivity
  by_cases hzero :
      (exactInputApproxStateAt result.xRaw remainRaw 1).term = 0
  · left
    refine ⟨hzero, ?_⟩
    have hnotFirst :
        ¬(result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
          result.finalTermRaw ≠ 0) := by
      rw [htermAt, hzero]
      simp
    have hnotLater :
        ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
          result.finalTermRaw > 0) := by simp [hn]
    rw [hplain ⟨hnotFirst, hnotLater⟩, hsum, hsumPrefix, hn]
    simp [hzero]
  · right
    have hpositive :
        0 < (exactInputApproxStateAt result.xRaw remainRaw 1).term := by omega
    refine ⟨hpositive, ?_⟩
    have hadjust := hfirst ⟨hn, ne_of_gt hxPositive, by simpa [htermAt] using hzero⟩
    rw [hadjust, hsum, hsumPrefix, hn]
    simp [htermAt]

/-- At a second stop, the negative term is retained as an even partial. -/
theorem lowerAboveApproxExecution_second_sum
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hremainUpper : remainRaw < BONE)
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result)
    (hn : result.iterations = 2) :
    result.partialRaw = BONE +
      (exactInputApproxStateAt result.xRaw remainRaw 1).term +
      (exactInputApproxStateAt result.xRaw remainRaw 2).term := by
  obtain ⟨state, hx, hsteps, hsum, hterm, _, hn50, _, _, _, hplain⟩ :=
    lowerAboveApproxExecution_success hexec
  have hsign := (lowerAboveApproxExecution_term_sign hbase hremain0
    hremainUpper hexec 2 (by omega) (by omega)).2 (by norm_num)
  have hstateAt : exactInputApproxStateAt result.xRaw remainRaw 2 = state := by
    have hstepsTwo : exactInputApproxSteps result.xRaw remainRaw 2 = some state := by
      simpa [hn] using hsteps
    simp [exactInputApproxStateAt, hstepsTwo]
  have hfinalNegative : result.finalTermRaw < 0 := by
    rw [hterm, ← hstateAt]
    exact hsign
  have hnotFirst :
      ¬(result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
        result.finalTermRaw ≠ 0) := by simp [hn]
  have hnotLater :
      ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
        result.finalTermRaw > 0) := by omega
  have hpartial := hplain ⟨hnotFirst, hnotLater⟩
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  rw [hpartial, hsum, hsumPrefix, hn]
  norm_num [Finset.sum_range_succ]
  ring

/-- Later source correction always selects an even Taylor degree. -/
theorem lowerAboveApproxExecution_later_sum
    {baseRaw remainRaw : ℤ} {result : LowerAboveApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hremainUpper : remainRaw < BONE)
    (hexec : lowerAboveApproxExecution baseRaw remainRaw = some result)
    (hn3 : 3 ≤ result.iterations) :
    ∃ degree evenIndex : ℕ,
      degree = 2 * evenIndex + 2 ∧
        (degree = result.iterations ∨ degree + 1 = result.iterations) ∧
        result.partialRaw = BONE +
          ∑ k ∈ Finset.range degree,
            (exactInputApproxStateAt result.xRaw remainRaw (k + 1)).term := by
  obtain ⟨state, hx, hsteps, hsum, hterm, _, hn50, _, _, hlater, hplain⟩ :=
    lowerAboveApproxExecution_success hexec
  have hxPositive : 0 < result.xRaw := by rw [hx]; omega
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw result.iterations = state := by
    simp [exactInputApproxStateAt, hsteps]
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  have hnotFirst :
      ¬(result.iterations = 1 ∧ result.xRaw ≠ 0 ∧
        result.finalTermRaw ≠ 0) := by omega
  by_cases heven : result.iterations % 2 = 0
  · have hfinalNegative :=
      (lowerAboveApproxExecution_term_sign hbase hremain0 hremainUpper hexec
        result.iterations (by omega) (by omega)).2 heven
    have hfinalRawNegative : result.finalTermRaw < 0 := by
      rw [hterm, ← hstateAt]
      exact hfinalNegative
    have hnotLater :
        ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
          result.finalTermRaw > 0) := by omega
    have hpartial := hplain ⟨hnotFirst, hnotLater⟩
    let degree := result.iterations
    let evenIndex := degree / 2 - 1
    have hdegreeEven : degree = 2 * evenIndex + 2 := by
      dsimp [degree, evenIndex]
      have hdecomp := Nat.mod_add_div result.iterations 2
      omega
    exact ⟨degree, evenIndex, hdegreeEven, Or.inl rfl, by
      rw [hpartial, hsum, hsumPrefix]⟩
  · have hodd : result.iterations % 2 = 1 := by omega
    have hfinalNonnegative :=
      (lowerAboveApproxExecution_term_sign hbase hremain0 hremainUpper hexec
        result.iterations (by omega) (by omega)).1 hodd
    let degree := result.iterations - 1
    let evenIndex := degree / 2 - 1
    have hdegreeEven : degree = 2 * evenIndex + 2 := by
      dsimp [degree, evenIndex]
      have hdecomp := Nat.mod_add_div result.iterations 2
      omega
    by_cases hfinalZero : result.finalTermRaw = 0
    · have hnotLater :
          ¬(result.iterations ≠ 1 ∧ result.xRaw > 0 ∧
            result.finalTermRaw > 0) := by simp [hfinalZero]
      have hpartial := hplain ⟨hnotFirst, hnotLater⟩
      refine ⟨degree, evenIndex, hdegreeEven,
        Or.inr (by dsimp [degree]; omega), ?_⟩
      have htermZero :
          (exactInputApproxStateAt result.xRaw remainRaw result.iterations).term = 0 := by
        rw [hstateAt, ← hterm]
        exact hfinalZero
      rw [hpartial, hsum, hsumPrefix]
      have hnSucc : result.iterations - 1 + 1 = result.iterations := by omega
      rw [← hnSucc, Finset.sum_range_succ]
      dsimp [degree]
      rw [hnSucc, htermZero]
      ring
    · have hfinalPositive : result.finalTermRaw > 0 := by
        have hfinalRawNonnegative : 0 ≤ result.finalTermRaw := by
          rw [hterm, ← hstateAt]
          exact hfinalNonnegative
        omega
      have hpartial := hlater ⟨by omega, hxPositive, hfinalPositive⟩
      refine ⟨degree, evenIndex, hdegreeEven,
        Or.inr (by dsimp [degree]; omega), ?_⟩
      have htermAt : state.term =
          (exactInputApproxStateAt result.xRaw remainRaw result.iterations).term := by
        exact congrArg ExactInputApproxState.term hstateAt.symm
      rw [hpartial, hsum, hterm, hsumPrefix, htermAt]
      have hnSucc : result.iterations - 1 + 1 = result.iterations := by omega
      rw [← hnSucc, Finset.sum_range_succ]
      dsimp [degree]
      ring

/-- Lower-rounded exponentiation-by-squaring loop used by `c_powi`. -/
def lowerPowiLoopExecution : ℕ → ℤ → ℤ → ℕ → Option ℤ
  | 0, zRaw, _, n => if n = 0 then some zRaw else none
  | fuel + 1, zRaw, aRaw, n =>
      if n = 0 then some zRaw else do
        let aNextRaw ←
          SorobanFixedPointMath.FixedPointImpl.fixedMulFloor aRaw aRaw BONE
        let zNextRaw ←
          if n % 2 ≠ 0 then
            SorobanFixedPointMath.FixedPointImpl.fixedMulFloor zRaw aNextRaw BONE
          else some zRaw
        lowerPowiLoopExecution fuel zNextRaw aNextRaw (n / 2)

/-- Source execution of `c_powi(..., round_up = false)`. -/
def lowerPowiExecution (baseRaw : ℤ) (exponent : ℕ) : Option ℤ :=
  let zRaw := if exponent % 2 ≠ 0 then baseRaw else (BONE : ℤ)
  lowerPowiLoopExecution (exponent + 1) zRaw baseRaw (exponent / 2)

/-- Source control-flow result of lower-directed `c_pow`. -/
inductive LowerCPowExecutionResult where
  | integer (integerPart : ℕ) (wholeRaw : ℤ)
  | fractional
      (integerPart remainderStroop : ℕ)
      (wholeRaw : ℤ) (approx : LowerAboveApproxExecutionResult)
      (powerRaw : ℤ)
deriving DecidableEq

def LowerCPowExecutionResult.powerRaw : LowerCPowExecutionResult → ℤ
  | .integer _ wholeRaw => wholeRaw
  | .fractional _ _ _ _ powerRaw => powerRaw

/-- Source-shaped `c_pow(..., round_up = false)` for a scaled direct weight. -/
def lowerCPowExecution
    (baseRaw exponentBone : ℤ) (exponentStroop : ℕ) :
    Option LowerCPowExecutionResult := do
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
      let approx ← lowerAboveApproxExecution baseRaw remainRaw
      let powerRaw ←
        SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
          wholeRaw approx.partialRaw BONE
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)

/-- A configured direct weight forces the fractional, zero-integer branch. -/
theorem lowerCPowExecution_configured_components
    {baseRaw exponentBone : ℤ} {exponentStroop : ℕ}
    {integerPart remainderStroop : ℕ} {wholeRaw powerRaw : ℤ}
    {approx : LowerAboveApproxExecutionResult}
    (hexponent0 : 0 < exponentStroop) (hexponentUpper : exponentStroop < STROOP)
    (hexec : lowerCPowExecution baseRaw exponentBone exponentStroop =
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)) :
    integerPart = 0 ∧ remainderStroop = exponentStroop ∧ wholeRaw = BONE ∧
      lowerAboveApproxExecution baseRaw
        (exponentStroop * (BONE / STROOP)) = some approx ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        wholeRaw approx.partialRaw BONE = some powerRaw := by
  rw [lowerCPowExecution] at hexec
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
theorem lowerCPowExecution_configured_not_integer
    {baseRaw exponentBone : ℤ} {exponentStroop integerPart : ℕ}
    {wholeRaw : ℤ}
    (hexponent0 : 0 < exponentStroop) (hexponentUpper : exponentStroop < STROOP)
    (hexec : lowerCPowExecution baseRaw exponentBone exponentStroop =
      some (.integer integerPart wholeRaw)) : False := by
  rw [lowerCPowExecution] at hexec
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

private theorem deposit_i128_mul_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem deposit_isFloor_integer_eq
    {rounded exact : ℤ} (hfloor : IsFloor rounded (exact : ℝ)) :
    rounded = exact := by
  have hlower : rounded ≤ exact := by exact_mod_cast hfloor.le
  have hupperReal : (exact : ℝ) < rounded + 1 := hfloor.lt_add_one
  have hupper : exact < rounded + 1 := by exact_mod_cast hupperReal
  omega

/-- Checked source intermediates before the `c_pow` call. -/
structure SingleSidedTokenDepositPrefix where
  tokenBalanceRaw : ℤ
  tokenAmountRaw : ℤ
  poolSupplyRaw : ℤ
  feeRaw : ℤ
  weightRaw : ℤ
  weightComplementRaw : ℤ
  weightedFeeRaw : ℤ
  feeMultiplierRaw : ℤ
  adjustedInputRaw : ℤ
  newTokenBalanceRaw : ℤ
  baseRaw : ℤ

/-- Complete successful arithmetic result after the `c_pow` call. -/
structure SingleSidedTokenDepositExecutionResult where
  pre : SingleSidedTokenDepositPrefix
  cpow : LowerCPowExecutionResult
  newPoolSupplyRaw : ℤ
  poolAmountRaw : ℤ
  downscaledRaw : ℤ
  output : ℤ

/-- First half of the source arithmetic, split to keep elaboration incremental. -/
def singleSidedTokenDepositPrefixExecution
    (inputBalance inputScalar inputAmount poolSupply
      inputWeight fee : ℕ) : Option SingleSidedTokenDepositPrefix := do
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
  let adjustedInputRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      tokenAmountRaw feeMultiplierRaw BONE
  let newTokenBalanceRaw ←
    SorobanFixedPointMath.I256.add tokenBalanceRaw adjustedInputRaw
  let baseRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      newTokenBalanceRaw tokenBalanceRaw.toNat BONE
  some {
    tokenBalanceRaw := tokenBalanceRaw
    tokenAmountRaw := tokenAmountRaw
    poolSupplyRaw := poolSupplyRaw
    feeRaw := feeRaw
    weightRaw := weightRaw
    weightComplementRaw := weightComplementRaw
    weightedFeeRaw := weightedFeeRaw
    feeMultiplierRaw := feeMultiplierRaw
    adjustedInputRaw := adjustedInputRaw
    newTokenBalanceRaw := newTokenBalanceRaw
    baseRaw := baseRaw
  }

/-- Second half of the source arithmetic from `c_pow` through downscale. -/
def singleSidedTokenDepositFinishExecution
    (inputWeight : ℕ) (pre : SingleSidedTokenDepositPrefix) :
    Option SingleSidedTokenDepositExecutionResult := do
  let cpow ← lowerCPowExecution pre.baseRaw pre.weightRaw inputWeight
  let newPoolSupplyRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      cpow.powerRaw pre.poolSupplyRaw BONE
  let poolAmountRaw ←
    SorobanFixedPointMath.I256.sub newPoolSupplyRaw pre.poolSupplyRaw
  let downscaledRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      poolAmountRaw (BONE / STROOP) 1
  let output ← SorobanFixedPointMath.I128.checked downscaledRaw
  some {
    pre := pre
    cpow := cpow
    newPoolSupplyRaw := newPoolSupplyRaw
    poolAmountRaw := poolAmountRaw
    downscaledRaw := downscaledRaw
    output := output
  }

/-- Executable model of `calc_lp_token_amount_given_token_deposits_in`. -/
def calcLpTokenAmountGivenTokenDepositsInExecution
    (inputBalance inputScalar inputAmount poolSupply
      inputWeight fee : ℕ) : Option SingleSidedTokenDepositExecutionResult := do
  let pre ← singleSidedTokenDepositPrefixExecution inputBalance inputScalar
    inputAmount poolSupply inputWeight fee
  singleSidedTokenDepositFinishExecution inputWeight pre

/-- Successful prefix execution exposes every checked source operation. -/
theorem singleSidedTokenDepositPrefixExecution_success
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenDepositPrefix}
    (hexec : singleSidedTokenDepositPrefixExecution inputBalance inputScalar
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
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.tokenAmountRaw result.feeMultiplierRaw BONE =
          some result.adjustedInputRaw ∧
      SorobanFixedPointMath.I256.add result.tokenBalanceRaw
        result.adjustedInputRaw = some result.newTokenBalanceRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        result.newTokenBalanceRaw result.tokenBalanceRaw.toNat BONE =
          some result.baseRaw := by
  rw [singleSidedTokenDepositPrefixExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨tokenBalanceRaw, htokenBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨tokenAmountRaw, htokenAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨poolSupplyRaw, hpoolSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨feeRaw, hfee, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨weightRaw, hweight, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨weightComplementRaw, hweightComplement, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨weightedFeeRaw, hweightedFee, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨feeMultiplierRaw, hfeeMultiplier, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨adjustedInputRaw, hadjusted, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨newTokenBalanceRaw, hnewBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨baseRaw, hbase, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨htokenBalance, htokenAmount, hpoolSupply, hfee, hweight,
    hweightComplement, hweightedFee, hfeeMultiplier, hadjusted, hnewBalance, hbase⟩

/-- Successful finish execution exposes the remaining checked operations. -/
theorem singleSidedTokenDepositFinishExecution_success
    {inputWeight : ℕ} {pre : SingleSidedTokenDepositPrefix}
    {result : SingleSidedTokenDepositExecutionResult}
    (hexec : singleSidedTokenDepositFinishExecution inputWeight pre = some result) :
    result.pre = pre ∧
      lowerCPowExecution pre.baseRaw pre.weightRaw inputWeight =
        some result.cpow ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.cpow.powerRaw pre.poolSupplyRaw BONE =
          some result.newPoolSupplyRaw ∧
      SorobanFixedPointMath.I256.sub result.newPoolSupplyRaw
        pre.poolSupplyRaw = some result.poolAmountRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor result.poolAmountRaw
        (BONE / STROOP) 1 = some result.downscaledRaw ∧
      SorobanFixedPointMath.I128.checked result.downscaledRaw =
        some result.output := by
  rw [singleSidedTokenDepositFinishExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨cpow, hcpow, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨newPoolSupplyRaw, hnewSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨poolAmountRaw, hpoolAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨downscaledRaw, hdownscale, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨output, houtput, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨rfl, hcpow, hnewSupply, hpoolAmount, hdownscale, houtput⟩

/-- A complete successful result supplies both source execution phases. -/
theorem calcLpTokenAmountGivenTokenDepositsInExecution_success
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenDepositExecutionResult}
    (hexec : calcLpTokenAmountGivenTokenDepositsInExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    ∃ pre,
      singleSidedTokenDepositPrefixExecution inputBalance inputScalar inputAmount
          poolSupply inputWeight fee = some pre ∧
        singleSidedTokenDepositFinishExecution inputWeight pre = some result := by
  rw [calcLpTokenAmountGivenTokenDepositsInExecution] at hexec
  exact Option.bind_eq_some.mp hexec

/-- Fixed-point facts recovered from one successful source-shaped deposit. -/
structure SingleSidedTokenDepositRunRefinements
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    (result : SingleSidedTokenDepositExecutionResult) : Prop where
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
  feeMultiplierEq :
    (result.pre.feeMultiplierRaw : ℝ) / BONE =
      1 - singleSidedWithdrawalFeeRate
        ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
  adjustedInputNonnegative : 0 ≤ result.pre.adjustedInputRaw
  adjustedInputFloor :
    IsFloor result.pre.adjustedInputRaw
      ((result.pre.tokenAmountRaw : ℝ) *
        (1 - singleSidedWithdrawalFeeRate
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)))
  baseFloor :
    IsFloor result.pre.baseRaw
      ((BONE : ℝ) *
        (1 + (result.pre.adjustedInputRaw : ℝ) /
          result.pre.tokenBalanceRaw))
  cpowExec :
    lowerCPowExecution result.pre.baseRaw result.pre.weightRaw inputWeight =
      some result.cpow
  newPoolSupplyFloor :
    IsFloor result.newPoolSupplyRaw
      ((result.cpow.powerRaw : ℝ) * result.pre.poolSupplyRaw / BONE)
  poolAmountEq :
    result.poolAmountRaw = result.newPoolSupplyRaw - result.pre.poolSupplyRaw
  outputFloor :
    IsFloor result.output
      ((result.poolAmountRaw : ℝ) / (BONE / STROOP : ℕ))

/-- A successful checked execution supplies every operation-level refinement. -/
theorem calcLpTokenAmountGivenTokenDepositsInExecution_refines
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenDepositExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hinputAmount : 0 < inputAmount) (hpoolSupply : 0 < poolSupply)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcLpTokenAmountGivenTokenDepositsInExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    SingleSidedTokenDepositRunRefinements
      (inputBalance := inputBalance) (inputScalar := inputScalar)
      (inputAmount := inputAmount) (poolSupply := poolSupply)
      (inputWeight := inputWeight) (fee := fee) result := by
  obtain ⟨pre, hpreExec, hfinishExec⟩ :=
    calcLpTokenAmountGivenTokenDepositsInExecution_success hexec
  rcases singleSidedTokenDepositFinishExecution_success hfinishExec with
    ⟨hpre, hcpow, hnewSupply, hpoolAmount, hdownscale, houtput⟩
  subst pre
  rcases singleSidedTokenDepositPrefixExecution_success hpreExec with
    ⟨htokenBalance, htokenAmount, hsupply, hfee, hweight,
      hweightComplement, hweightedFee, hfeeMultiplier, hadjusted,
      hnewBalance, hbase⟩
  have htokenBalanceEq := deposit_i128_mul_success_eq htokenBalance
  have htokenAmountEq := deposit_i128_mul_success_eq htokenAmount
  have hsupplyEq := deposit_i128_mul_success_eq hsupply
  have hfeeEq := deposit_i128_mul_success_eq hfee
  have hweightEq := deposit_i128_mul_success_eq hweight
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
  have hweightComplementEq := deposit_i256_sub_success_eq hweightComplement
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
    apply deposit_isFloor_integer_eq
    rw [← hweightedExact]
    exact hweightedFloor
  have hfeeMultiplierRawEq := deposit_i256_sub_success_eq hfeeMultiplier
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
  have hadjustedFloorRaw := (i256_fixed_mul_floor_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hadjusted).1
  have hadjustedFloor :
      IsFloor result.pre.adjustedInputRaw
        ((result.pre.tokenAmountRaw : ℝ) *
          (1 - singleSidedWithdrawalFeeRate
            ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP))) := by
    rw [← hfeeMultiplierEq]
    convert hadjustedFloorRaw using 1
    push_cast
    ring
  have hadjusted0 : 0 ≤ result.pre.adjustedInputRaw :=
    hadjustedFloor.nonnegative_of_nonnegative_exact
      (mul_nonneg (by exact_mod_cast htokenAmount0.le) hfeeMultiplierBounds.1)
  have hnewBalanceEq := deposit_i256_add_success_eq hnewBalance
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
          (1 + (result.pre.adjustedInputRaw : ℝ) /
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
  have hpoolAmountEq := deposit_i256_sub_success_eq hpoolAmount
  have hdownscaleFloor := (i256_fixed_div_floor_success_refines
    (by norm_num [BONE, STROOP]) (by
      norm_num [BONE, STROOP, SorobanFixedPointMath.I256.maxValue])
      hdownscale).1
  have houtputEq : result.output = result.downscaledRaw := by
    exact (SorobanFixedPointMath.I128.checked_eq_some_iff.mp houtput).2.symm
  have houtputFloor :
      IsFloor result.output
        ((result.poolAmountRaw : ℝ) / (BONE / STROOP : ℕ)) := by
    rw [houtputEq]
    convert hdownscaleFloor using 1
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
    feeMultiplierEq := hfeeMultiplierEq
    adjustedInputNonnegative := hadjusted0
    adjustedInputFloor := hadjustedFloor
    baseFloor := hbaseFloor
    cpowExec := hcpow
    newPoolSupplyFloor := by
      simpa only [Int.cast_mul] using hnewSupplyFloor
    poolAmountEq := hpoolAmountEq
    outputFloor := houtputFloor
  }

/-
Every successful source-shaped exact-token-input deposit has pool-adverse
error strictly below `1.223%` of the weighted minimum-fee spot value.
-/
theorem calc_lp_token_amount_given_token_deposits_in_execution_adverse_error_lt_precise_fee_share
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenDepositExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hinputAmount : 0 < inputAmount) (hpoolSupply : 0 < poolSupply)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hinputRatio : inputAmount * STROOP ≤ inputBalance * MAX_IN_RATIO)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcLpTokenAmountGivenTokenDepositsInExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    (result.output : ℝ) -
      singleSidedTokenDepositIdealOutput (poolSupply : ℝ)
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
          ((inputAmount : ℝ) / inputBalance) <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue (poolSupply : ℝ)
          ((inputWeight : ℝ) / STROOP)
          ((inputAmount : ℝ) / inputBalance) := by
  have href := calcLpTokenAmountGivenTokenDepositsInExecution_refines
    hinputBalance hinputScalar hinputAmount hpoolSupply hweightUpper hfeeUpper hexec
  let inputBalanceRaw : ℝ := result.pre.tokenBalanceRaw
  let inputAmountRaw : ℝ := result.pre.tokenAmountRaw
  let poolSupplyRaw : ℝ := result.pre.poolSupplyRaw
  let scale : ℝ := BONE / STROOP
  let weight : ℝ := (inputWeight : ℝ) / STROOP
  let feeRate : ℝ := (fee : ℝ) / STROOP
  let nominalRatio : ℝ := inputAmountRaw / inputBalanceRaw
  let adjustedRatio : ℝ :=
    (result.pre.adjustedInputRaw : ℝ) / inputBalanceRaw
  let feeMultiplier : ℝ := (result.pre.feeMultiplierRaw : ℝ) / BONE
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
  have hweightBounds : 0 < weight ∧ weight < 1 := by
    apply single_sided_token_deposit_configured_weight_bounds
    · dsimp [weight]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hweightLower)
        (by norm_num [STROOP])
    · dsimp [weight]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hweightUpper)
        (by norm_num [STROOP])
  have hfee0 : 0 ≤ feeRate := by positivity
  have hfee1 : feeRate ≤ 1 := by
    dsimp [feeRate]
    apply (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
    exact_mod_cast le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hnominal : nominalRatio = inputAmountRaw / inputBalanceRaw := rfl
  have hnominalOriginal :
      nominalRatio = (inputAmount : ℝ) / inputBalance := by
    dsimp [nominalRatio, inputAmountRaw, inputBalanceRaw]
    rw [href.tokenAmountEq, href.tokenBalanceEq]
    push_cast
    have hscalar : (inputScalar : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP := by
    rw [hnominalOriginal]
    have hratioReal :
        (inputAmount : ℝ) * STROOP ≤
          (inputBalance : ℝ) * MAX_IN_RATIO := by
      exact_mod_cast hinputRatio
    exact (div_le_div_iff₀ (by exact_mod_cast hinputBalance)
      (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2 (by
        simpa [mul_comm] using hratioReal)
  have hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate := by
    exact href.feeMultiplierEq
  have hadjustedRatio :
      adjustedRatio =
        (result.pre.adjustedInputRaw : ℝ) / inputBalanceRaw := rfl
  have hadjustedFloor :
      IsFloor result.pre.adjustedInputRaw (inputAmountRaw * feeMultiplier) := by
    rw [hfeeMultiplier]
    simpa [inputAmountRaw, weight, feeRate] using href.adjustedInputFloor
  have hcomputedBase :
      computedBase = (result.pre.baseRaw : ℝ) / BONE := rfl
  have hbaseFloor :
      IsFloor result.pre.baseRaw
        ((BONE : ℝ) * (1 + adjustedRatio)) := by
    simpa [adjustedRatio, inputBalanceRaw] using href.baseFloor
  have hweightLowerReal : (MIN_WEIGHT : ℝ) / STROOP ≤ weight := by
    dsimp [weight]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hweightLower)
      (by norm_num [STROOP])
  have hweightUpperReal : weight ≤ (MAX_WEIGHT : ℝ) / STROOP := by
    dsimp [weight]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hweightUpper)
      (by norm_num [STROOP])
  have hcaller := single_sided_token_deposit_configured_caller_bounds
    hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
      hweightLowerReal hweightUpperReal
      hfee0 hfee1 hfeeMultiplier href.adjustedInputNonnegative
      hadjustedRatio hadjustedFloor hcomputedBase hbaseFloor
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
        (result.newPoolSupplyRaw : ℝ) - poolSupplyRaw := by
    rw [href.poolAmountEq]
    simp [poolSupplyRaw]
  have houtputFloor :
      IsFloor result.output ((result.poolAmountRaw : ℝ) / scale) := by
    convert href.outputFloor using 1
    norm_num [scale, BONE, STROOP]
  have hpoolSupplyOriginal : poolSupplyRaw / scale = (poolSupply : ℝ) := by
    dsimp [poolSupplyRaw, scale]
    rw [href.poolSupplyEq]
    push_cast
    norm_num [BONE, STROOP]
  have hresult :
      (result.output : ℝ) -
        singleSidedTokenDepositIdealOutput
          (poolSupplyRaw / scale) weight feeRate nominalRatio <
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeeOutputValue
            (poolSupplyRaw / scale) weight nominalRatio := by
    cases hcpowCase : result.cpow with
    | integer integerPart wholeRaw =>
        have hcpowExec :
            lowerCPowExecution result.pre.baseRaw result.pre.weightRaw inputWeight =
              some (.integer integerPart wholeRaw) := by
          simpa [hcpowCase] using href.cpowExec
        exact False.elim <| lowerCPowExecution_configured_not_integer
          hweightNat0 hweightNatUpper hcpowExec
    | fractional integerPart remainderStroop wholeRaw approx powerRaw =>
        have hcpowExec :
            lowerCPowExecution result.pre.baseRaw result.pre.weightRaw inputWeight =
              some (.fractional integerPart remainderStroop wholeRaw approx powerRaw) := by
          simpa [hcpowCase] using href.cpowExec
        rcases lowerCPowExecution_configured_components hweightNat0
          hweightNatUpper hcpowExec with ⟨hinteger, hremainder, hwhole, happ, hpower⟩
        let remainRaw : ℤ := inputWeight * (BONE / STROOP)
        have happExec :
            lowerAboveApproxExecution result.pre.baseRaw remainRaw = some approx := by
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
        have hbaseRawLower : BONE ≤ result.pre.baseRaw := by
          have hreal : (BONE : ℝ) ≤ result.pre.baseRaw := by
            have hB : (0 : ℝ) < BONE := by norm_num [BONE]
            have hbound :=
              (le_div_iff₀ hB).mp (by simpa [computedBase] using hcaller.2.2.2.1)
            norm_num at hbound ⊢
            exact hbound
          exact_mod_cast hreal
        by_cases hunit : result.pre.baseRaw = BONE
        · have hpartialUnit := lowerAboveApproxExecution_unit (by simpa [hunit] using happExec)
          have hpowerUnit : powerRaw = BONE := by
            apply deposit_isFloor_integer_eq
            simpa [hpartialUnit] using hcomposedFloor
          exact baseline_single_sided_token_deposit_unit_base_adverse_error_lt_precise_fee_share
            hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
            hweightLowerReal hweightUpperReal hfee0 hfee1 hfeeMultiplier
            href.adjustedInputNonnegative hadjustedRatio hadjustedFloor
            hcomputedBase hbaseFloor (by simp [computedBase, hunit, BONE])
            (by simp [hcomputedPower, hpowerUnit]) hpoolSupplyRaw hscale
            hnewSupplyFloor hpoolAmount houtputFloor
        · have hbaseRawStrict : BONE < result.pre.baseRaw := by omega
          have hbaseStrict : 1 < computedBase := by
            dsimp [computedBase]
            exact (one_lt_div (by norm_num [BONE] : (0 : ℝ) < BONE)).2
              (by exact_mod_cast hbaseRawStrict)
          have hremain0 : 0 < remainRaw := by
            dsimp [remainRaw]
            exact_mod_cast Nat.mul_pos hweightNat0
              (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
          have hremainUpper : remainRaw < BONE := by
            dsimp [remainRaw]
            have hfactor : 0 < BONE / STROOP := by norm_num [BONE, STROOP]
            have hscaled := (Nat.mul_lt_mul_right hfactor).2 hweightNatUpper
            norm_num [BONE, STROOP] at hscaled ⊢
            exact_mod_cast hscaled
          have hfirstFloorRaw := lowerAboveApproxExecution_first_term_refines happExec
          have hfirstFloor :
              IsFloor (exactInputApproxStateAt approx.xRaw remainRaw 1).term
                (exactOutputBinomialTerm weight computedBase 1) := by
            rw [exactOutputBinomialTerm_one]
            convert hfirstFloorRaw using 1
            have hx := (lowerAboveApproxExecution_success happExec).choose_spec.1
            rw [hx]
            dsimp [remainRaw, weight, computedBase]
            push_cast
            norm_num [BONE, STROOP]
            ring
          have happFacts := lowerAboveApproxExecution_success happExec
          obtain ⟨finalState, hxRaw, hsteps, hunadjusted, hfinalTerm,
            hn1, hn50, hcontinued, hfirstCorrection, hlaterCorrection, hplain⟩ :=
              happFacts
          by_cases hnOne : approx.iterations = 1
          · rcases lowerAboveApproxExecution_first_sum hbaseRawStrict hremain0
              happExec hnOne with hzero | hpositive
            · exact baseline_single_sided_token_deposit_zero_first_term_adverse_error_lt_precise_fee_share
                hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
                hweightLowerReal hweightUpperReal hfee0 hfee1 hfeeMultiplier
                href.adjustedInputNonnegative hadjustedRatio hadjustedFloor
                hcomputedBase hbaseFloor hzero.1
                (by rw [hzero.2, hzero.1]; norm_num [BONE])
                hcomputedPower hcomposedFloor hpoolSupplyRaw hscale
                hnewSupplyFloor hpoolAmount houtputFloor
            · have hstopRaw := lowerAboveApproxExecution_final_le_of_lt_fifty
                happExec (by omega)
              have hstop :
                  |((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ)| ≤
                    CPOW_PRECISION := by
                rw [← hnOne]
                exact_mod_cast hstopRaw
              exact baseline_single_sided_token_deposit_first_term_adverse_error_lt_precise_fee_share
                (firstRounded :=
                  (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
                (computedPowerRaw := powerRaw) hinputBalanceRaw hinputAmountRaw
                hnominal hnominalUpper hweightLowerReal hweightUpperReal hfee0
                hfee1 hfeeMultiplier href.adjustedInputNonnegative
                hadjustedRatio hadjustedFloor hcomputedBase hbaseFloor
                hpositive.1 hfirstFloor hstop (by exact_mod_cast hpositive.2)
                hcomputedPower hcomposedFloor hpoolSupplyRaw hscale
                hnewSupplyFloor hpoolAmount houtputFloor
          · have hnTwo : 2 ≤ approx.iterations := by omega
            by_cases hsecond : approx.iterations = 2
            · have hpartial := lowerAboveApproxExecution_second_sum
                hbaseRawStrict hremain0 hremainUpper happExec hsecond
              obtain ⟨stepState, hstep⟩ :=
                lowerAboveApproxExecution_prefix happExec 2 (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw 2 = stepState := by
                simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := 2) (by omega) (by omega) hstep
              have hfirstNonnegative :=
                (lowerAboveApproxExecution_term_sign hbaseRawStrict hremain0
                  hremainUpper happExec 1 (by omega) (by omega)).1 (by norm_num)
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
              exact baseline_single_sided_token_deposit_second_term_adverse_error_lt_precise_fee_share
                (firstRounded :=
                  (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
                (coefficientProduct := stepState.coefficientProduct)
                (multiplied := stepState.multiplied)
                (secondRounded := stepState.term)
                (computedPowerRaw := powerRaw)
                hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
                hweightLowerReal hweightUpperReal hfee0 hfee1 hfeeMultiplier
                href.adjustedInputNonnegative hadjustedRatio hadjustedFloor
                hcomputedBase hbaseFloor hbaseStrict hfirstNonnegative
                hfirstFloor hcoefficientFloor hmultiplyFloor hdivideFloor
                (by rw [hstepAt] at hpartial; exact_mod_cast hpartial)
                hcomputedPower hcomposedFloor hpoolSupplyRaw hscale
                hnewSupplyFloor hpoolAmount houtputFloor
            · have hn3 : 3 ≤ approx.iterations := by omega
              obtain ⟨degree, evenIndex, hdegreeEven, hdegreeStop, hpartial⟩ :=
                lowerAboveApproxExecution_later_sum hbaseRawStrict hremain0
                  hremainUpper happExec hn3
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
                obtain ⟨stepState, hstep⟩ := lowerAboveApproxExecution_prefix
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
                obtain ⟨stepState, hstep⟩ := lowerAboveApproxExecution_prefix
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
                obtain ⟨stepState, hstep⟩ := lowerAboveApproxExecution_prefix
                  happExec (k + 1) (by omega) (by omega)
                have hstepAt :
                    exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                      stepState := by simp [exactInputApproxStateAt, hstep]
                have hstepFacts := exactInputApproxSteps_refinements
                  (iteration := k + 1) (by omega) (by omega) hstep
                dsimp [computedTerm, multiplied]
                rw [hstepAt]
                simpa [Nat.cast_add, Nat.cast_one] using hstepFacts.2.2.1
              exact baseline_single_sided_token_deposit_later_adverse_error_lt_precise_fee_share
                coefficientProduct multiplied computedTerm
                (n := approx.iterations) (degree := degree) (evenIndex := evenIndex)
                (computedPowerRaw := powerRaw)
                hinputBalanceRaw hinputAmountRaw hnominal hnominalUpper
                hweightLowerReal hweightUpperReal hfee0 hfee1 hfeeMultiplier
                href.adjustedInputNonnegative hadjustedRatio hadjustedFloor
                hcomputedBase hbaseFloor hn3 hn50 hdegreeEven hdegreeStop
                (by
                  intro k hk hkn
                  exact_mod_cast hcontinued k hk hkn)
                hfirstFloor hcoefficientFloor hmultiplyFloor hdivideFloor
                (by exact_mod_cast hpartial) hcomputedPower hcomposedFloor
                hpoolSupplyRaw hscale hnewSupplyFloor hpoolAmount houtputFloor
  rw [hpoolSupplyOriginal, hnominalOriginal] at hresult
  simpa [weight, feeRate] using hresult

end CometPool
