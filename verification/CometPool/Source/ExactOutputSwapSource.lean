import CometPool.Source.ExactInputSwapSource
import CometPool.Operations.ExactOutputSwap

set_option maxRecDepth 65536

namespace CometPool

/-!
Executable, source-shaped models for the positive-output arithmetic used by
`swap_exact_amount_out`. The common checked recurrence and upper-rounded
`c_powi` execution are reused from `ExactInputSwapSource`.
-/

/-- Result of the above-one, upper-directed approximation path. -/
structure ExactOutputApproxExecutionResult where
  iterations : ℕ
  xRaw : ℤ
  unadjustedSumRaw : ℤ
  finalTermRaw : ℤ
  partialRaw : ℤ
deriving DecidableEq

/-- Source execution of `c_pow_approx(..., round_up = true)` for exact output. -/
def exactOutputApproxExecution
    (baseRaw remainRaw : ℤ) : Option ExactOutputApproxExecutionResult := do
  let xRaw ← SorobanFixedPointMath.I256.sub baseRaw BONE
  let stopped ← exactInputApproxFindStop xRaw remainRaw MAX_CPOW_ITERS 0
  let partialRaw ←
    if stopped.iterations = 1 ∧ xRaw ≠ 0 then
      SorobanFixedPointMath.I256.add stopped.state.sum 1
    else if xRaw > 0 ∧ stopped.state.term < 0 then
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

private theorem i256_sub_success_eq_out
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x - y) = some result from hexec)
  exact h.2.symm

private theorem i256_add_success_eq_out
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x + y) = some result from hexec)
  exact h.2.symm

/-- Successful execution exposes exactly the prefixes reached by the source loop. -/
theorem exactOutputApproxExecution_success
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result) :
    ∃ state : ExactInputApproxState,
      result.xRaw = baseRaw - BONE ∧
        exactInputApproxSteps result.xRaw remainRaw result.iterations = some state ∧
        result.unadjustedSumRaw = state.sum ∧
        result.finalTermRaw = state.term ∧
        1 ≤ result.iterations ∧ result.iterations ≤ 50 ∧
        (∀ k, 1 ≤ k → k < result.iterations →
          CPOW_PRECISION <
            |(exactInputApproxStateAt result.xRaw remainRaw k).term|) ∧
        (result.iterations = 1 ∧ result.xRaw ≠ 0 →
          result.partialRaw = result.unadjustedSumRaw + 1) ∧
        (¬(result.iterations = 1 ∧ result.xRaw ≠ 0) ∧
            result.xRaw > 0 ∧ result.finalTermRaw < 0 →
          result.partialRaw =
            result.unadjustedSumRaw - result.finalTermRaw) ∧
        (¬(result.iterations = 1 ∧ result.xRaw ≠ 0) ∧
            ¬(result.xRaw > 0 ∧ result.finalTermRaw < 0) →
          result.partialRaw = result.unadjustedSumRaw) := by
  rw [exactOutputApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := i256_sub_success_eq_out hxRaw
  have hfind := exactInputApproxFindStop_success hstopped
  have hn1 : 1 ≤ stopped.iterations := by
    rcases hfind.2.1 with hzero | hpositive
    · norm_num [MAX_CPOW_ITERS] at hzero
    · omega
  have hn50 : stopped.iterations ≤ 50 := by
    simpa [MAX_CPOW_ITERS] using hfind.2.2.1
  by_cases hfirst : stopped.iterations = 1 ∧ xRaw ≠ 0
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
      exact i256_add_success_eq_out hpartialRaw
    · intro hnot
      exact False.elim (hnot.1 hfirst)
    · intro hnot
      exact False.elim (hnot.1 hfirst)
  · rw [if_neg hfirst] at hafterStop
    by_cases hadjust : xRaw > 0 ∧ stopped.state.term < 0
    · rw [if_pos hadjust] at hafterStop
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
        exact i256_sub_success_eq_out hpartialRaw
      · intro hnot
        exact False.elim (hnot.2 hadjust)
    · rw [if_neg hadjust] at hafterStop
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
        exact False.elim (hadjust hyes.2)
      · intro _
        exact Option.some.inj hpartialRaw.symm

/-- Successful exact-output approximation exposes every executed prefix. -/
theorem exactOutputApproxExecution_prefix
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result) :
    ∀ k, 1 ≤ k → k ≤ result.iterations →
      ∃ state, exactInputApproxSteps result.xRaw remainRaw k = some state := by
  rw [exactOutputApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with
    ⟨stopped, hstopped, hafterStop⟩
  have hxEq := i256_sub_success_eq_out hxRaw
  have hfind := exactInputApproxFindStop_success hstopped
  by_cases hfirst : stopped.iterations = 1 ∧ xRaw ≠ 0
  · rw [if_pos hfirst] at hafterStop
    rcases Option.bind_eq_some.mp hafterStop with
      ⟨partialRaw, hpartialRaw, hresult⟩
    have hresultEq := Option.some.inj hresult
    subst result
    intro k hk1 hkn
    simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn
  · rw [if_neg hfirst] at hafterStop
    by_cases hadjust : xRaw > 0 ∧ stopped.state.term < 0
    · rw [if_pos hadjust] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn
    · rw [if_neg hadjust] at hafterStop
      rcases Option.bind_eq_some.mp hafterStop with
        ⟨partialRaw, hpartialRaw, hresult⟩
      have hresultEq := Option.some.inj hresult
      subst result
      intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn

/-- The first exact-output recurrence term has its production floor semantics. -/
theorem exactOutputApproxExecution_first_term_refines
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result) :
    IsFloor
      (exactInputApproxStateAt result.xRaw remainRaw 1).term
      (((remainRaw : ℝ) * (result.xRaw : ℝ)) / BONE) := by
  obtain ⟨state, hstate⟩ := exactOutputApproxExecution_prefix hexec 1
    (by omega) (exactOutputApproxExecution_success hexec).choose_spec.2.2.2.2.1
  have hrefinements := exactInputApproxSteps_refinements
    (iteration := 1) (by omega) (by omega) hstate
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw 1 = state := by
    simp [exactInputApproxStateAt, hstate]
  have hinitialTerm :
      (exactInputApproxStateAt result.xRaw remainRaw 0).term = BONE := by rfl
  have hmultiplied : state.multiplied = state.coefficientProduct := by
    have hfloor := hrefinements.2.1
    rw [hinitialTerm] at hfloor
    have hlower : (state.coefficientProduct : ℝ) < state.multiplied + 1 := by
      simpa [BONE] using hfloor.lt_add_one
    have hupper : state.multiplied ≤ state.coefficientProduct := by
      exact_mod_cast (by simpa [BONE] using hfloor.le)
    have hlowerInt : state.coefficientProduct < state.multiplied + 1 := by
      exact_mod_cast hlower
    omega
  have hterm : state.term = state.multiplied := by
    have hfloor := hrefinements.2.2.1
    have hlower : (state.multiplied : ℝ) < state.term + 1 := by
      simpa [hmultiplied] using hfloor.lt_add_one
    have hupper : state.term ≤ state.multiplied := by
      exact_mod_cast (by simpa [hmultiplied] using hfloor.le)
    have hlowerInt : state.multiplied < state.term + 1 := by exact_mod_cast hlower
    omega
  rw [hstateAt, hterm, hmultiplied]
  simpa using hrefinements.1

/-- Above-one recurrence floors preserve the alternating term signs. -/
theorem exactOutputApproxStep_sign
    {xRaw remainRaw : ℤ} {iteration : ℕ} {state : ExactInputApproxState}
    (hx : 0 < xRaw) (hremainUpper : remainRaw < BONE)
    (hiteration2 : 2 ≤ iteration) (hiteration50 : iteration ≤ 50)
    (hexec : exactInputApproxSteps xRaw remainRaw iteration = some state) :
    (0 < (exactInputApproxStateAt xRaw remainRaw (iteration - 1)).term →
        state.term < 0) ∧
      ((exactInputApproxStateAt xRaw remainRaw (iteration - 1)).term < 0 →
        0 ≤ state.term) := by
  have href := exactInputApproxSteps_refinements
    (by omega) hiteration50 hexec
  have hcoefficientExact :
      (((remainRaw : ℝ) - ((iteration : ℝ) - 1) * BONE) *
          (xRaw : ℝ)) / BONE < 0 := by
    have hremainReal : (remainRaw : ℝ) < BONE := by exact_mod_cast hremainUpper
    have hiterationReal : (2 : ℝ) ≤ iteration := by exact_mod_cast hiteration2
    have hcoefficient :
        (remainRaw : ℝ) - ((iteration : ℝ) - 1) * BONE < 0 := by
      have hbone : (0 : ℝ) < BONE := by norm_num [BONE]
      nlinarith
    have hxReal : (0 : ℝ) < xRaw := by exact_mod_cast hx
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcoefficient hxReal)
      (by norm_num [BONE])
  have hcoefficientNegative : state.coefficientProduct < 0 := by
    have hle := href.1.le
    exact_mod_cast lt_of_le_of_lt hle hcoefficientExact
  constructor
  · intro hprevious
    have hmultipliedExact :
        (((exactInputApproxStateAt xRaw remainRaw (iteration - 1)).term : ℝ) *
          (state.coefficientProduct : ℝ)) / BONE < 0 := by
      have hpreviousReal :
          (0 : ℝ) < (exactInputApproxStateAt xRaw remainRaw
            (iteration - 1)).term := by exact_mod_cast hprevious
      have hcoefficientReal : (state.coefficientProduct : ℝ) < 0 := by
        exact_mod_cast hcoefficientNegative
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg hpreviousReal hcoefficientReal)
        (by norm_num [BONE])
    have hmultipliedNegative : state.multiplied < 0 := by
      exact_mod_cast lt_of_le_of_lt href.2.1.le hmultipliedExact
    have htermExact : (state.multiplied : ℝ) / iteration < 0 := by
      exact div_neg_of_neg_of_pos (by exact_mod_cast hmultipliedNegative)
        (by positivity)
    exact_mod_cast lt_of_le_of_lt href.2.2.1.le htermExact
  · intro hprevious
    have hmultipliedExact :
        0 ≤ (((exactInputApproxStateAt xRaw remainRaw (iteration - 1)).term : ℝ) *
          (state.coefficientProduct : ℝ)) / BONE := by
      have hpreviousReal :
          (exactInputApproxStateAt xRaw remainRaw
            (iteration - 1)).term < (0 : ℝ) := by exact_mod_cast hprevious
      have hcoefficientReal : (state.coefficientProduct : ℝ) < 0 := by
        exact_mod_cast hcoefficientNegative
      exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hpreviousReal.le
        hcoefficientReal.le) (by norm_num [BONE])
    have hmultipliedNonnegative : 0 ≤ state.multiplied :=
      href.2.1.nonnegative_of_nonnegative_exact hmultipliedExact
    have htermExact : 0 ≤ (state.multiplied : ℝ) / iteration := by positivity
    exact href.2.2.1.nonnegative_of_nonnegative_exact htermExact

/-- Every executed above-one term has its generalized-binomial parity sign. -/
theorem exactOutputApproxExecution_term_sign
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hremainUpper : remainRaw < BONE)
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result) :
    ∀ k, 1 ≤ k → k ≤ result.iterations →
      (k % 2 = 1 →
          0 ≤ (exactInputApproxStateAt result.xRaw remainRaw k).term) ∧
        (k % 2 = 0 →
          (exactInputApproxStateAt result.xRaw remainRaw k).term < 0) := by
  have hsuccess := exactOutputApproxExecution_success hexec
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
          have hfirst := exactOutputApproxExecution_first_term_refines hexec
          apply hfirst.nonnegative_of_nonnegative_exact
          have hxReal : (0 : ℝ) < result.xRaw := by exact_mod_cast hx
          have hremainReal : (0 : ℝ) < remainRaw := by exact_mod_cast hremain0
          positivity
        · norm_num
      · have hk2 : 2 ≤ k := by omega
        obtain ⟨state, hstate⟩ := exactOutputApproxExecution_prefix hexec k
          hk1 hkn
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

/-- A first-iteration stop applies exactly the source one-unit upper correction. -/
theorem exactOutputApproxExecution_first_sum
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hbase : BONE < baseRaw)
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result)
    (hn : result.iterations = 1) :
    result.partialRaw = BONE +
      (exactInputApproxStateAt result.xRaw remainRaw 1).term + 1 := by
  obtain ⟨state, hx, hsteps, hsum, _, _, hn50, _, hfirst, _, _⟩ :=
    exactOutputApproxExecution_success hexec
  have hxPositive : 0 < result.xRaw := by rw [hx]; omega
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  rw [hfirst ⟨hn, ne_of_gt hxPositive⟩, hsum, hsumPrefix, hn]
  simp

/-- At a second-iteration stop, source correction removes the negative term. -/
theorem exactOutputApproxExecution_second_sum
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hremainUpper : remainRaw < BONE)
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result)
    (hn : result.iterations = 2) :
    result.partialRaw = BONE +
      (exactInputApproxStateAt result.xRaw remainRaw 1).term := by
  obtain ⟨state, hx, hsteps, hsum, hterm, _, hn50, _, _, hadjust, _⟩ :=
    exactOutputApproxExecution_success hexec
  have hxPositive : 0 < result.xRaw := by rw [hx]; omega
  have hsign := (exactOutputApproxExecution_term_sign hbase hremain0
    hremainUpper hexec 2 (by omega) (by omega)).2 (by norm_num)
  have hstateAt : exactInputApproxStateAt result.xRaw remainRaw 2 = state := by
    have hstepsTwo : exactInputApproxSteps result.xRaw remainRaw 2 = some state := by
      simpa [hn] using hsteps
    simp [exactInputApproxStateAt, hstepsTwo]
  have hfinalNegative : result.finalTermRaw < 0 := by rw [hterm, ← hstateAt]; exact hsign
  have hpartial := hadjust ⟨by simp [hn, hxPositive], hxPositive, hfinalNegative⟩
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  have htermAt : state.term =
      (exactInputApproxStateAt result.xRaw remainRaw 2).term := by
    exact congrArg ExactInputApproxState.term hstateAt.symm
  rw [hpartial, hsum, hterm, hsumPrefix, htermAt, hn]
  norm_num [Finset.sum_range_succ]
  ring

/--
After the second iteration, source correction always selects an odd Taylor
degree: it removes a negative even final term and retains a nonnegative odd one.
-/
theorem exactOutputApproxExecution_later_sum
    {baseRaw remainRaw : ℤ} {result : ExactOutputApproxExecutionResult}
    (hbase : BONE < baseRaw) (hremain0 : 0 < remainRaw)
    (hremainUpper : remainRaw < BONE)
    (hexec : exactOutputApproxExecution baseRaw remainRaw = some result)
    (hn3 : 3 ≤ result.iterations) :
    ∃ degree oddIndex : ℕ,
      degree = 2 * oddIndex + 1 ∧
        (degree = result.iterations ∨ degree + 1 = result.iterations) ∧
        result.partialRaw = BONE +
          ∑ k ∈ Finset.range degree,
            (exactInputApproxStateAt result.xRaw remainRaw (k + 1)).term := by
  obtain ⟨state, hx, hsteps, hsum, hterm, _, hn50, _, _, hadjust, hplain⟩ :=
    exactOutputApproxExecution_success hexec
  have hxPositive : 0 < result.xRaw := by rw [hx]; omega
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw result.iterations = state := by
    simp [exactInputApproxStateAt, hsteps]
  have hsumPrefix := exactInputApproxSteps_sum hn50 hsteps
  have hnotFirst : ¬(result.iterations = 1 ∧ result.xRaw ≠ 0) := by omega
  have hdecomp := Nat.mod_add_div result.iterations 2
  by_cases heven : result.iterations % 2 = 0
  · have hfinalNegative :=
      (exactOutputApproxExecution_term_sign hbase hremain0 hremainUpper hexec
        result.iterations (by omega) (by omega)).2 heven
    have hfinalRawNegative : result.finalTermRaw < 0 := by
      rw [hterm, ← hstateAt]
      exact hfinalNegative
    have hpartial := hadjust
      ⟨hnotFirst, hxPositive, hfinalRawNegative⟩
    let degree := result.iterations - 1
    let oddIndex := degree / 2
    have hdegreeOdd : degree = 2 * oddIndex + 1 := by
      dsimp [degree, oddIndex]
      omega
    refine ⟨degree, oddIndex, hdegreeOdd, Or.inr (by dsimp [degree]; omega), ?_⟩
    have htermAt : state.term =
        (exactInputApproxStateAt result.xRaw remainRaw result.iterations).term := by
      exact congrArg ExactInputApproxState.term hstateAt.symm
    rw [hpartial, hsum, hterm, hsumPrefix, htermAt]
    have hnSucc : result.iterations - 1 + 1 = result.iterations := by omega
    rw [← hnSucc, Finset.sum_range_succ]
    dsimp [degree]
    ring
  · have hodd : result.iterations % 2 = 1 := by omega
    have hfinalNonnegative :=
      (exactOutputApproxExecution_term_sign hbase hremain0 hremainUpper hexec
        result.iterations (by omega) (by omega)).1 hodd
    have hfinalRawNonnegative : 0 ≤ result.finalTermRaw := by
      rw [hterm, ← hstateAt]
      exact hfinalNonnegative
    have hnotAdjust : ¬(result.xRaw > 0 ∧ result.finalTermRaw < 0) := by omega
    have hpartial := hplain ⟨hnotFirst, hnotAdjust⟩
    let degree := result.iterations
    let oddIndex := degree / 2
    have hdegreeOdd : degree = 2 * oddIndex + 1 := by
      dsimp [degree, oddIndex]
      omega
    exact ⟨degree, oddIndex, hdegreeOdd, Or.inl rfl, by
      rw [hpartial, hsum, hsumPrefix]⟩

/-- Source control-flow result of exact-output `c_pow`. -/
inductive ExactOutputCPowExecutionResult where
  | integer (integerPart : ℕ) (wholeRaw : ℤ)
  | fractional
      (integerPart remainderStroop : ℕ)
      (wholeRaw : ℤ) (approx : ExactOutputApproxExecutionResult)
      (powerRaw : ℤ)
deriving DecidableEq

def ExactOutputCPowExecutionResult.powerRaw :
    ExactOutputCPowExecutionResult → ℤ
  | .integer _ wholeRaw => wholeRaw
  | .fractional _ _ _ _ powerRaw => powerRaw

/-- Source-shaped exact-output execution of `c_pow(..., round_up = true)`. -/
def exactOutputCPowExecution
    (baseRaw exponentBone : ℤ) (exponentStroop : ℕ) :
    Option ExactOutputCPowExecutionResult := do
  if baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw then
    none
  else if exponentBone ≠
      (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP) then
    none
  else
    let integerPart := rustU32Cast (exponentBone / BONE).toNat
    let remainderStroop := exponentStroop % STROOP
    let remainRaw := exponentBone - (exponentBone / BONE) * BONE
    let wholeRaw ← upperPowiExecution baseRaw integerPart
    if remainRaw = 0 then
      some (.integer integerPart wholeRaw)
    else
      let approx ← exactOutputApproxExecution baseRaw remainRaw
      let powerRaw ←
        SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
          wholeRaw approx.partialRaw BONE
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)

theorem exactOutputCPowExecution_integer_components
    {baseRaw exponentBone : ℤ} {exponentStroop integerPart : ℕ}
    {wholeRaw : ℤ}
    (hintegerPart : exponentStroop / STROOP ≤ 9)
    (hexec : exactOutputCPowExecution baseRaw exponentBone exponentStroop =
      some (.integer integerPart wholeRaw)) :
    integerPart = exponentStroop / STROOP ∧
      exponentStroop % STROOP = 0 ∧
      upperPowiExecution baseRaw integerPart = some wholeRaw := by
  rw [exactOutputCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · rw [if_neg hguard] at hexec
    by_cases hscaled : exponentBone ≠
        (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP)
    · simp [hscaled] at hexec
    · rw [if_neg hscaled] at hexec
      have hscale := not_ne_iff.mp hscaled
      have hsource := scaledExponentSourceSplit exponentStroop
      have hintegerSource :
          (exponentBone / BONE).toNat = exponentStroop / STROOP := by
        rw [hscale, hsource.1]
        rfl
      have hremainSource :
          exponentBone - (exponentBone / BONE) * BONE =
            ((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) := by
        rw [hscale]
        exact hsource.2
      rw [hintegerSource, hremainSource] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨whole, hwhole, hafterWhole⟩
      by_cases hremainder : exponentStroop % STROOP = 0
      · have hremainZero :
            (((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) : ℤ) = 0 := by
          simp [hremainder]
        rw [if_pos hremainZero] at hafterWhole
        have hresult := Option.some.inj hafterWhole
        cases hresult
        exact ⟨rustU32Cast_eq_self_of_le_nine hintegerPart, hremainder, hwhole⟩
      · have hremainNonzero :
            (((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) : ℤ) ≠ 0 := by
          exact_mod_cast Nat.mul_ne_zero hremainder (by norm_num [BONE, STROOP])
        rw [if_neg hremainNonzero] at hafterWhole
        rcases Option.bind_eq_some.mp hafterWhole with
          ⟨approx, happox, hafterApprox⟩
        rcases Option.bind_eq_some.mp hafterApprox with
          ⟨power, hpower, hresult⟩
        cases hresult

theorem exactOutputCPowExecution_fractional_components
    {baseRaw exponentBone : ℤ}
    {exponentStroop integerPart remainderStroop : ℕ}
    {wholeRaw powerRaw : ℤ} {approx : ExactOutputApproxExecutionResult}
    (hintegerPart : exponentStroop / STROOP ≤ 9)
    (hexec : exactOutputCPowExecution baseRaw exponentBone exponentStroop =
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)) :
    integerPart = exponentStroop / STROOP ∧
      remainderStroop = exponentStroop % STROOP ∧
      remainderStroop ≠ 0 ∧
      upperPowiExecution baseRaw integerPart = some wholeRaw ∧
      exactOutputApproxExecution baseRaw
        (remainderStroop * (BONE / STROOP)) = some approx ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        wholeRaw approx.partialRaw BONE = some powerRaw := by
  rw [exactOutputCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · rw [if_neg hguard] at hexec
    by_cases hscaled : exponentBone ≠
        (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP)
    · simp [hscaled] at hexec
    · rw [if_neg hscaled] at hexec
      have hscale := not_ne_iff.mp hscaled
      have hsource := scaledExponentSourceSplit exponentStroop
      have hintegerSource :
          (exponentBone / BONE).toNat = exponentStroop / STROOP := by
        rw [hscale, hsource.1]
        rfl
      have hremainSource :
          exponentBone - (exponentBone / BONE) * BONE =
            ((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) := by
        rw [hscale]
        exact hsource.2
      rw [hintegerSource, hremainSource] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨whole, hwhole, hafterWhole⟩
      by_cases hremainder : exponentStroop % STROOP = 0
      · have hremainZero :
            (((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) : ℤ) = 0 := by
          simp [hremainder]
        rw [if_pos hremainZero] at hafterWhole
        cases Option.some.inj hafterWhole
      · have hremainNonzero :
            (((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) : ℤ) ≠ 0 := by
          exact_mod_cast Nat.mul_ne_zero hremainder (by norm_num [BONE, STROOP])
        rw [if_neg hremainNonzero] at hafterWhole
        rcases Option.bind_eq_some.mp hafterWhole with
          ⟨approxResult, happox, hafterApprox⟩
        rcases Option.bind_eq_some.mp hafterApprox with
          ⟨power, hpower, hresult⟩
        have hfields := Option.some.inj hresult
        cases hfields
        exact ⟨rustU32Cast_eq_self_of_le_nine hintegerPart,
          rfl, hremainder, hwhole, happox, hpower⟩

/-- Successful checked `i128` ceiling division has exact ceiling semantics. -/
theorem i128_fixed_div_ceil_success_refines
    {x denominator result : ℤ} {y : ℕ}
    (hy : 0 < y)
    (hymax : (y : ℤ) ≤ SorobanFixedPointMath.I128.maxValue)
    (hexec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil
        x y denominator = some result) :
    IsCeil result ((((x * denominator : ℤ) : ℝ) / (y : ℝ))) ∧
      SorobanFixedPointMath.I128.InRange result := by
  have hprod : SorobanFixedPointMath.I128.InRange (x * denominator) := by
    by_contra hprod
    have hnone :
        SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil
          x y denominator = none := by
      simpa [SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil] using
        (SorobanFixedPointMath.I128FixedPointImpl.mulDivCeil_eq_none_of_product_out_of_range
          (x := x) (y := denominator) (d := y) hprod)
    rw [hexec] at hnone
    cases hnone
  have hvalueExec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil
          x y denominator =
        some (SorobanFixedPointMath.I128FixedPointImpl.mulDivCeilValue
          x denominator y) := by
    simpa [SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil] using
      (SorobanFixedPointMath.I128FixedPointImpl.mulDivCeil_eq_some
        (x := x) (y := denominator) (d := y) hprod hy hymax)
  have hresult :
      result = SorobanFixedPointMath.I128FixedPointImpl.mulDivCeilValue
        x denominator y :=
    Option.some.inj (hexec.symm.trans hvalueExec)
  rw [hresult]
  exact ⟨
    SorobanFixedPointMath.FixedPointImpl.mulDivCeilValue_isCeil
      x denominator hy,
    SorobanFixedPointMath.I128FixedPointImpl.mulDivCeilValue_inRange
      hprod hy⟩

private theorem i128_mul_success_eq_out
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem i128_sub_success_eq_out
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x - y) = some result from hexec)
  exact h.2.symm

/-- Successful arithmetic trace for `calc_token_in_given_token_out`. -/
structure SuccessfulExactOutputMathRun
    (inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ) where
  tokenBalanceIn : ℤ
  tokenBalanceOut : ℤ
  tokenAmountOut : ℤ
  feeComplement : ℤ
  feeAdjustRatio : ℤ
  weightRatioStroop : ℤ
  weightRatioBone : ℤ
  remainingOut : ℤ
  baseRaw : ℤ
  cpow : ExactOutputCPowExecutionResult
  balanceRatio : ℤ
  tokenAmountIn : ℤ
  adjustedIn : ℤ
  downscaled : ℤ
  output : ℤ
  tokenBalanceInExec :
    SorobanFixedPointMath.I128.mul inBalance inScalar = some tokenBalanceIn
  tokenBalanceOutExec :
    SorobanFixedPointMath.I128.mul outBalance outScalar = some tokenBalanceOut
  tokenAmountOutExec :
    SorobanFixedPointMath.I128.mul amountOut outScalar = some tokenAmountOut
  feeComplementExec :
    SorobanFixedPointMath.I128.sub STROOP fee = some feeComplement
  feeAdjustRatioExec :
    SorobanFixedPointMath.I128.mul feeComplement (BONE / STROOP) =
      some feeAdjustRatio
  weightRatioExec :
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil
      outWeight inWeight STROOP = some weightRatioStroop
  weightRatioBoneExec :
    SorobanFixedPointMath.I128.mul weightRatioStroop (BONE / STROOP) =
      some weightRatioBone
  remainingOutExec :
    SorobanFixedPointMath.I256.sub tokenBalanceOut tokenAmountOut =
      some remainingOut
  baseExec :
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenBalanceOut remainingOut.toNat BONE = some baseRaw
  cpowExec :
    exactOutputCPowExecution baseRaw weightRatioBone weightRatioStroop.toNat =
      some cpow
  balanceRatioExec :
    SorobanFixedPointMath.I256.sub cpow.powerRaw BONE = some balanceRatio
  tokenAmountInExec :
    SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
      tokenBalanceIn balanceRatio BONE = some tokenAmountIn
  adjustedInExec :
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenAmountIn feeAdjustRatio.toNat BONE = some adjustedIn
  downscaleExec :
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      adjustedIn inScalar 1 = some downscaled
  outputExec : SorobanFixedPointMath.I128.checked downscaled = some output

/-- Executable model of `calc_token_in_given_token_out`. -/
def calcTokenInGivenTokenOutExecution
    (inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ) : Option ℤ := do
  let tokenBalanceIn ← SorobanFixedPointMath.I128.mul inBalance inScalar
  let tokenBalanceOut ← SorobanFixedPointMath.I128.mul outBalance outScalar
  let tokenAmountOut ← SorobanFixedPointMath.I128.mul amountOut outScalar
  let feeComplement ← SorobanFixedPointMath.I128.sub STROOP fee
  let feeAdjustRatio ←
    SorobanFixedPointMath.I128.mul feeComplement (BONE / STROOP)
  let weightRatioStroop ←
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivCeil
      outWeight inWeight STROOP
  let weightRatioBone ←
    SorobanFixedPointMath.I128.mul weightRatioStroop (BONE / STROOP)
  let remainingOut ← SorobanFixedPointMath.I256.sub tokenBalanceOut tokenAmountOut
  let baseRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenBalanceOut remainingOut.toNat BONE
  let cpow ←
    exactOutputCPowExecution baseRaw weightRatioBone weightRatioStroop.toNat
  let balanceRatio ← SorobanFixedPointMath.I256.sub cpow.powerRaw BONE
  let tokenAmountIn ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
      tokenBalanceIn balanceRatio BONE
  let adjustedIn ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenAmountIn feeAdjustRatio.toNat BONE
  let downscaled ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil adjustedIn inScalar 1
  SorobanFixedPointMath.I128.checked downscaled

/-- A successful modeled return reconstructs every source arithmetic result. -/
theorem successfulExactOutputMathRun_of_execution
    {inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ} {output : ℤ}
    (hexec : calcTokenInGivenTokenOutExecution inBalance inScalar outBalance
      outScalar amountOut inWeight outWeight fee = some output) :
    ∃ run : SuccessfulExactOutputMathRun inBalance inScalar outBalance
        outScalar amountOut inWeight outWeight fee,
      run.output = output := by
  rw [calcTokenInGivenTokenOutExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceIn, htokenBalanceIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceOut, htokenBalanceOut, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenAmountOut, htokenAmountOut, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨feeComplement, hfeeComplement, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨feeAdjustRatio, hfeeAdjustRatio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨weightRatioStroop, hweightRatio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨weightRatioBone, hweightRatioBone, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨remainingOut, hremainingOut, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨baseRaw, hbase, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨cpow, hcpow, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨balanceRatio, hbalanceRatio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenAmountIn, htokenAmountIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨adjustedIn, hadjustedIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨downscaled, hdownscaled, houtput⟩
  exact ⟨{
    tokenBalanceIn := tokenBalanceIn
    tokenBalanceOut := tokenBalanceOut
    tokenAmountOut := tokenAmountOut
    feeComplement := feeComplement
    feeAdjustRatio := feeAdjustRatio
    weightRatioStroop := weightRatioStroop
    weightRatioBone := weightRatioBone
    remainingOut := remainingOut
    baseRaw := baseRaw
    cpow := cpow
    balanceRatio := balanceRatio
    tokenAmountIn := tokenAmountIn
    adjustedIn := adjustedIn
    downscaled := downscaled
    output := output
    tokenBalanceInExec := htokenBalanceIn
    tokenBalanceOutExec := htokenBalanceOut
    tokenAmountOutExec := htokenAmountOut
    feeComplementExec := hfeeComplement
    feeAdjustRatioExec := hfeeAdjustRatio
    weightRatioExec := hweightRatio
    weightRatioBoneExec := hweightRatioBone
    remainingOutExec := hremainingOut
    baseExec := hbase
    cpowExec := hcpow
    balanceRatioExec := hbalanceRatio
    tokenAmountInExec := htokenAmountIn
    adjustedInExec := hadjustedIn
    downscaleExec := hdownscaled
    outputExec := houtput
  }, rfl⟩

/-- Fixed-point facts recovered from one successful exact-output execution. -/
structure ExactOutputRunRefinements
    {inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ}
    (run : SuccessfulExactOutputMathRun inBalance inScalar outBalance
      outScalar amountOut inWeight outWeight fee) : Prop where
  tokenBalanceInEq : run.tokenBalanceIn = (inBalance : ℤ) * inScalar
  tokenBalanceOutEq : run.tokenBalanceOut = (outBalance : ℤ) * outScalar
  tokenAmountOutEq : run.tokenAmountOut = (amountOut : ℤ) * outScalar
  inputBalancePositive : 0 < run.tokenBalanceIn
  outputBalancePositive : 0 < run.tokenBalanceOut
  outputAmountPositive : 0 < run.tokenAmountOut
  remainingOutPositive : 0 < run.remainingOut
  weightRatioPositive : 0 < run.weightRatioStroop
  baseCeil :
    IsCeil run.baseRaw
      ((BONE : ℝ) *
        (1 / (1 - (run.tokenAmountOut : ℝ) / run.tokenBalanceOut)))
  exponentCeil :
    IsCeil run.weightRatioStroop
      ((STROOP : ℝ) * ((outWeight : ℝ) / inWeight))
  tokenAmountInCeil :
    IsCeil run.tokenAmountIn
      ((run.tokenBalanceIn : ℝ) *
        (run.cpow.powerRaw / (BONE : ℝ) - 1))
  adjustedInCeil :
    IsCeil run.adjustedIn
      ((run.tokenAmountIn : ℝ) / (1 - (fee : ℝ) / STROOP))
  outputCeil : IsCeil run.output ((run.adjustedIn : ℝ) / inScalar)

/-- Successful checked outer arithmetic refines all exact-output operations. -/
theorem successfulExactOutputMathRun_refines
    {inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountOut : 0 < amountOut)
    (hinWeight : 0 < inWeight) (hinWeightMax : inWeight ≤ STROOP)
    (houtWeight : 0 < outWeight)
    (houtputRatio : amountOut * STROOP ≤ outBalance * MAX_OUT_RATIO)
    (hfeeUpper : fee ≤ MAX_FEE)
    (run : SuccessfulExactOutputMathRun inBalance inScalar outBalance
      outScalar amountOut inWeight outWeight fee) :
    ExactOutputRunRefinements run := by
  have htokenBalanceIn := i128_mul_success_eq_out run.tokenBalanceInExec
  have htokenBalanceOut := i128_mul_success_eq_out run.tokenBalanceOutExec
  have htokenAmountOut := i128_mul_success_eq_out run.tokenAmountOutExec
  have hfeeComplement := i128_sub_success_eq_out run.feeComplementExec
  have hfeeAdjustRatio := i128_mul_success_eq_out run.feeAdjustRatioExec
  have htokenBalanceIn0 : 0 < run.tokenBalanceIn := by
    rw [htokenBalanceIn]
    positivity
  have htokenBalanceOut0 : 0 < run.tokenBalanceOut := by
    rw [htokenBalanceOut]
    positivity
  have htokenAmountOut0 : 0 < run.tokenAmountOut := by
    rw [htokenAmountOut]
    positivity
  have hamountLtBalance : amountOut < outBalance := by
    have hmax : MAX_OUT_RATIO < STROOP := by
      norm_num [MAX_OUT_RATIO, STROOP]
    nlinarith
  have hremainingEq := i256_sub_success_eq_out run.remainingOutExec
  have hremaining0 : 0 < run.remainingOut := by
    rw [hremainingEq, htokenBalanceOut, htokenAmountOut]
    have hscalar : (0 : ℤ) < outScalar := by exact_mod_cast houtScalar
    have hamount : (amountOut : ℤ) < outBalance := by exact_mod_cast hamountLtBalance
    nlinarith
  have hremainingRange := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked
      (run.tokenBalanceOut - run.tokenAmountOut) = some run.remainingOut
      from run.remainingOutExec)
  have hremainingNatMax :
      (run.remainingOut.toNat : ℤ) ≤ SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hremaining0.le]
    rw [← hremainingRange.2]
    exact hremainingRange.1.2
  have hbaseCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hremaining0) hremainingNatMax run.baseExec).1
  have hremainingCast : (run.remainingOut.toNat : ℝ) = run.remainingOut := by
    exact_mod_cast Int.toNat_of_nonneg hremaining0.le
  have hbaseCeil :
      IsCeil run.baseRaw
        ((BONE : ℝ) *
          (1 / (1 - (run.tokenAmountOut : ℝ) / run.tokenBalanceOut))) := by
    rw [hremainingCast, hremainingEq] at hbaseCeilRaw
    convert hbaseCeilRaw using 1
    push_cast
    have hbalanceReal : (0 : ℝ) < run.tokenBalanceOut := by
      exact_mod_cast htokenBalanceOut0
    have hamountReal : (run.tokenAmountOut : ℝ) < run.tokenBalanceOut := by
      rw [htokenBalanceOut, htokenAmountOut]
      push_cast
      have hscalar : (0 : ℝ) < outScalar := by exact_mod_cast houtScalar
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hamountLtBalance) hscalar
    field_simp
    ring
  have hinWeightMaxI128 :
      (inWeight : ℤ) ≤ SorobanFixedPointMath.I128.maxValue := by
    calc
      (inWeight : ℤ) ≤ STROOP := by exact_mod_cast hinWeightMax
      _ ≤ SorobanFixedPointMath.I128.maxValue := by
        norm_num [STROOP, SorobanFixedPointMath.I128.maxValue]
  have hexponentCeilRaw := (i128_fixed_div_ceil_success_refines
    hinWeight hinWeightMaxI128 run.weightRatioExec).1
  have hexponentCeil :
      IsCeil run.weightRatioStroop
        ((STROOP : ℝ) * ((outWeight : ℝ) / inWeight)) := by
    convert hexponentCeilRaw using 1
    all_goals push_cast
    ring
  have hweightRatioPositive : 0 < run.weightRatioStroop := by
    have hexact :
        0 < (STROOP : ℝ) * ((outWeight : ℝ) / inWeight) := by
      exact mul_pos (by norm_num [STROOP])
        (div_pos (by exact_mod_cast houtWeight) (by exact_mod_cast hinWeight))
    have hreal : (0 : ℝ) < run.weightRatioStroop :=
      lt_of_lt_of_le hexact hexponentCeil.le
    exact_mod_cast hreal
  have hbalanceRatioEq := i256_sub_success_eq_out run.balanceRatioExec
  have htokenAmountInCeilRaw := (i256_fixed_mul_ceil_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue])
      run.tokenAmountInExec).1
  have htokenAmountInCeil :
      IsCeil run.tokenAmountIn
        ((run.tokenBalanceIn : ℝ) *
          (run.cpow.powerRaw / (BONE : ℝ) - 1)) := by
    rw [hbalanceRatioEq] at htokenAmountInCeilRaw
    convert htokenAmountInCeilRaw using 1
    all_goals push_cast
    field_simp [show (BONE : ℝ) ≠ 0 by norm_num [BONE]]
  have hfeeStroop : fee < STROOP :=
    lt_of_le_of_lt hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hfeeAdjustEq :
      run.feeAdjustRatio =
        (STROOP - fee : ℕ) * (BONE / STROOP) := by
    rw [hfeeAdjustRatio, hfeeComplement]
    norm_num [Nat.cast_sub (Nat.le_of_lt hfeeStroop)]
  have hfeeAdjust0 : 0 < run.feeAdjustRatio := by
    rw [hfeeAdjustEq]
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hfeeStroop)
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hfeeAdjustRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      (run.feeComplement * ((BONE : ℤ) / STROOP)) = some run.feeAdjustRatio
      from run.feeAdjustRatioExec)
  have hfeeAdjustNatMax :
      (run.feeAdjustRatio.toNat : ℤ) ≤ SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hfeeAdjust0.le]
    calc
      run.feeAdjustRatio ≤ SorobanFixedPointMath.I128.maxValue :=
        by rw [← hfeeAdjustRange.2]; exact hfeeAdjustRange.1.2
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hadjustedCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hfeeAdjust0) hfeeAdjustNatMax
      run.adjustedInExec).1
  have hfeeAdjustCast : (run.feeAdjustRatio.toNat : ℝ) = run.feeAdjustRatio := by
    exact_mod_cast Int.toNat_of_nonneg hfeeAdjust0.le
  have hadjustedCeil :
      IsCeil run.adjustedIn
        ((run.tokenAmountIn : ℝ) / (1 - (fee : ℝ) / STROOP)) := by
    rw [hfeeAdjustCast, hfeeAdjustEq] at hadjustedCeilRaw
    convert hadjustedCeilRaw using 1
    push_cast
    rw [Nat.cast_sub (Nat.le_of_lt hfeeStroop)]
    norm_num [BONE, STROOP]
    have hdenom : (10000000 : ℝ) - (fee : ℝ) ≠ 0 := by
      have hfeeReal : (fee : ℝ) < 10000000 := by exact_mod_cast hfeeStroop
      linarith
    field_simp [hdenom]
    ring
  have hinProductRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      ((inBalance : ℤ) * inScalar) = some run.tokenBalanceIn
      from run.tokenBalanceInExec)
  have hinScalarProduct :
      (inScalar : ℤ) ≤ (inBalance : ℤ) * inScalar := by
    have hbalanceOne : (1 : ℤ) ≤ inBalance := by exact_mod_cast hinBalance
    have hscalar0 : (0 : ℤ) ≤ inScalar := by positivity
    simpa using mul_le_mul_of_nonneg_right hbalanceOne hscalar0
  have hinScalarMax :
      (inScalar : ℤ) ≤ SorobanFixedPointMath.I256.maxValue :=
    hinScalarProduct.trans <| hinProductRange.1.2.trans <| by
      norm_num [SorobanFixedPointMath.I128.maxValue,
        SorobanFixedPointMath.I256.maxValue]
  have hdownscaleCeilRaw := (i256_fixed_div_ceil_success_refines
    hinScalar hinScalarMax run.downscaleExec).1
  have houtputEq : run.output = run.downscaled := by
    have hchecked := SorobanFixedPointMath.I128.checked_eq_some_iff.mp run.outputExec
    exact hchecked.2.symm
  have houtputCeil : IsCeil run.output ((run.adjustedIn : ℝ) / inScalar) := by
    rw [houtputEq]
    convert hdownscaleCeilRaw using 1
    all_goals push_cast
    ring
  exact {
    tokenBalanceInEq := htokenBalanceIn
    tokenBalanceOutEq := htokenBalanceOut
    tokenAmountOutEq := htokenAmountOut
    inputBalancePositive := htokenBalanceIn0
    outputBalancePositive := htokenBalanceOut0
    outputAmountPositive := htokenAmountOut0
    remainingOutPositive := hremaining0
    weightRatioPositive := hweightRatioPositive
    baseCeil := hbaseCeil
    exponentCeil := hexponentCeil
    tokenAmountInCeil := htokenAmountInCeil
    adjustedInCeil := hadjustedCeil
    outputCeil := houtputCeil
  }

/-
Every successful source-shaped exact-output math run has pool-adverse error
strictly below `4.501%` of the minimum fee's spot-normalized value.
-/
theorem successfulExactOutputMathRun_adverse_error_lt_precise_fee_share
    {inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountOut : 0 < amountOut)
    (hinWeightLower : MIN_WEIGHT ≤ inWeight)
    (hinWeightUpper : inWeight ≤ MAX_WEIGHT)
    (houtWeightLower : MIN_WEIGHT ≤ outWeight)
    (houtWeightUpper : outWeight ≤ MAX_WEIGHT)
    (houtputRatio : amountOut * STROOP ≤ outBalance * MAX_OUT_RATIO)
    (hfeeUpper : fee ≤ MAX_FEE)
    (run : SuccessfulExactOutputMathRun inBalance inScalar outBalance
      outScalar amountOut inWeight outWeight fee) :
    exactOutputIdealInput
          ((run.tokenBalanceIn : ℝ) / inScalar)
          ((fee : ℝ) / STROOP)
          ((run.tokenAmountOut : ℝ) / run.tokenBalanceOut)
          ((outWeight : ℝ) / inWeight) -
        (run.output : ℝ) <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE * exactOutputAdjustedMinimumFeeInputValue
          ((run.tokenBalanceIn : ℝ) / inScalar)
          ((fee : ℝ) / STROOP)
          ((outWeight : ℝ) / inWeight)
          ((run.tokenAmountOut : ℝ) / run.tokenBalanceOut) := by
  let inputBalance : ℝ := run.tokenBalanceIn
  let outputBalance : ℝ := run.tokenBalanceOut
  let outputAmount : ℝ := run.tokenAmountOut
  let scale : ℝ := inScalar
  let feeRate : ℝ := (fee : ℝ) / STROOP
  let nominalRatio : ℝ := outputAmount / outputBalance
  let computedBase : ℝ := (run.baseRaw : ℝ) / BONE
  let idealExponent : ℝ := (outWeight : ℝ) / inWeight
  let computedExponent : ℝ := (run.weightRatioStroop : ℝ) / STROOP
  change exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio
        idealExponent - (run.output : ℝ) <
    EXACT_OUTPUT_ADVERSE_FEE_SHARE *
      exactOutputAdjustedMinimumFeeInputValue (inputBalance / scale) feeRate
        idealExponent nominalRatio
  have hinWeight : 0 < inWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hinWeightLower
  have houtWeight : 0 < outWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) houtWeightLower
  have hinWeightMax : inWeight ≤ STROOP :=
    le_trans hinWeightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have href := successfulExactOutputMathRun_refines hinBalance hinScalar
    houtBalance houtScalar hamountOut hinWeight hinWeightMax houtWeight
      houtputRatio hfeeUpper run
  have hinputBalance : 0 < inputBalance := by
    dsimp only [inputBalance]
    exact_mod_cast href.inputBalancePositive
  have houtputBalance : 0 < outputBalance := by
    dsimp only [outputBalance]
    exact_mod_cast href.outputBalancePositive
  have houtputAmount : 0 < outputAmount := by
    dsimp only [outputAmount]
    exact_mod_cast href.outputAmountPositive
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact_mod_cast hinScalar
  have hnominalOriginal :
      nominalRatio = (amountOut : ℝ) / outBalance := by
    dsimp [nominalRatio, outputAmount, outputBalance]
    rw [href.tokenAmountOutEq, href.tokenBalanceOutEq]
    push_cast
    have hscalarReal : (outScalar : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP := by
    rw [hnominalOriginal]
    have hratioReal :
        (amountOut : ℝ) * STROOP ≤
          (outBalance : ℝ) * MAX_OUT_RATIO := by
      exact_mod_cast houtputRatio
    have houtBalanceReal : (0 : ℝ) < outBalance := by exact_mod_cast houtBalance
    have hstroopReal : (0 : ℝ) < STROOP := by norm_num [STROOP]
    exact (div_le_div_iff₀ houtBalanceReal hstroopReal).2 (by
      simpa [mul_comm] using hratioReal)
  have hratio0 : 0 ≤ nominalRatio := by positivity
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hfeeUpperReal : feeRate < 1 := by
    have hfeeStroop : fee < STROOP :=
      lt_of_le_of_lt hfeeUpper (by norm_num [MAX_FEE, STROOP])
    dsimp [feeRate]
    exact (div_lt_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
      (by exact_mod_cast hfeeStroop)
  have hidealExponentLower : 1 / 9 ≤ idealExponent := by
    dsimp [idealExponent]
    have houtWeightReal : (MIN_WEIGHT : ℝ) ≤ outWeight := by
      exact_mod_cast houtWeightLower
    have hinWeightReal : (inWeight : ℝ) ≤ MAX_WEIGHT := by
      exact_mod_cast hinWeightUpper
    apply (le_div_iff₀ (by exact_mod_cast hinWeight)).2
    calc
      (1 / 9 : ℝ) * inWeight ≤ (1 / 9 : ℝ) * MAX_WEIGHT :=
        mul_le_mul_of_nonneg_left hinWeightReal (by norm_num)
      _ = MIN_WEIGHT := by norm_num [MAX_WEIGHT, MIN_WEIGHT]
      _ ≤ outWeight := houtWeightReal
  have hidealExponentUpper : idealExponent ≤ 9 := by
    dsimp [idealExponent]
    have houtWeightReal : (outWeight : ℝ) ≤ MAX_WEIGHT := by
      exact_mod_cast houtWeightUpper
    have hinWeightReal : (MIN_WEIGHT : ℝ) ≤ inWeight := by
      exact_mod_cast hinWeightLower
    apply (div_le_iff₀ (by exact_mod_cast hinWeight)).2
    calc
      (outWeight : ℝ) ≤ MAX_WEIGHT := houtWeightReal
      _ = 9 * MIN_WEIGHT := by norm_num [MAX_WEIGHT, MIN_WEIGHT]
      _ ≤ 9 * inWeight :=
        mul_le_mul_of_nonneg_left hinWeightReal (by norm_num)
  have hbaseFacts := exact_output_base_ceil_refines hratio0 hratio1
    (show computedBase = (run.baseRaw : ℝ) / BONE from rfl) href.baseCeil
  have hbaseRawPositive : BONE < run.baseRaw := by
    have hidealBaseStrict : (1 : ℝ) < 1 / (1 - nominalRatio) := by
      have hratioPositive : 0 < nominalRatio := by positivity
      have hdenom : 0 < 1 - nominalRatio := by linarith
      exact (one_lt_div hdenom).2 (by linarith)
    have hcomputedStrict : 1 < computedBase :=
      lt_of_lt_of_le hidealBaseStrict hbaseFacts.1
    dsimp [computedBase] at hcomputedStrict
    have hreal : (BONE : ℝ) < run.baseRaw := by
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      simpa only [one_mul] using (lt_div_iff₀ hB).mp hcomputedStrict
    exact_mod_cast hreal
  have hbaseRaw0 : 0 ≤ run.baseRaw := by omega
  have htoNat :
      ((run.weightRatioStroop.toNat : ℕ) : ℤ) = run.weightRatioStroop :=
    Int.toNat_of_nonneg href.weightRatioPositive.le
  have htoNatReal :
      ((run.weightRatioStroop.toNat : ℕ) : ℝ) =
        (run.weightRatioStroop : ℝ) := by
    exact_mod_cast htoNat
  have hcomputedExponentUpper :
      computedExponent < idealExponent + 1 / (STROOP : ℝ) := by
    exact (exact_output_exponent_ceil_refines
      (show computedExponent = (run.weightRatioStroop : ℝ) / STROOP from rfl)
      href.exponentCeil).2
  have hrawQuotientLeNine : run.weightRatioStroop.toNat / STROOP ≤ 9 := by
    have hrawStrict :
        (run.weightRatioStroop.toNat : ℝ) < 9 * STROOP + 1 := by
      rw [htoNatReal]
      dsimp [computedExponent] at hcomputedExponentUpper
      have hstroop : (0 : ℝ) < STROOP := by norm_num [STROOP]
      have hscaled := (div_lt_iff₀ hstroop).mp hcomputedExponentUpper
      calc
        (run.weightRatioStroop : ℝ) <
            (idealExponent + 1 / (STROOP : ℝ)) * STROOP := hscaled
        _ ≤ (9 + 1 / (STROOP : ℝ)) * STROOP :=
          mul_le_mul_of_nonneg_right
            (add_le_add_right hidealExponentUpper _) hstroop.le
        _ = 9 * STROOP + 1 := by norm_num [STROOP]
    have hrawUpper : run.weightRatioStroop.toNat ≤ 9 * STROOP := by
      have hrawStrictNat :
          run.weightRatioStroop.toNat < 9 * STROOP + 1 := by
        exact_mod_cast hrawStrict
      omega
    exact Nat.div_le_of_le_mul (by simpa [mul_comm] using hrawUpper)
  cases hcpowCase : run.cpow with
  | integer integerPart wholeRaw =>
      have hcpowExec :
          exactOutputCPowExecution run.baseRaw run.weightRatioBone
              run.weightRatioStroop.toNat =
            some (.integer integerPart wholeRaw) := by
        simpa [hcpowCase] using run.cpowExec
      have hcomponents := exactOutputCPowExecution_integer_components
        hrawQuotientLeNine hcpowExec
      have hwholeTrace := upperPowiExecution_refines hbaseRaw0 hcomponents.2.2
      have hdecomp := Nat.mod_add_div run.weightRatioStroop.toNat STROOP
      have hexponentInteger : (integerPart : ℝ) = computedExponent := by
        have hnat :
            run.weightRatioStroop.toNat = STROOP * integerPart := by
          rw [← hcomponents.1, hcomponents.2.1] at hdecomp
          omega
        dsimp [computedExponent]
        rw [← htoNatReal, hnat]
        norm_num [STROOP]
      exact baseline_swap_exact_amount_out_integer_adverse_error_lt_precise_fee_share
        (integerPart := integerPart) (inputBalance := inputBalance)
        (outputBalance := outputBalance) (outputAmount := outputAmount)
        (nominalRatio := nominalRatio) (feeRate := feeRate)
        (computedBase := computedBase) (idealExponent := idealExponent)
        (computedPower := (wholeRaw : ℝ)) (scale := scale)
        (computedBaseRaw := run.baseRaw)
        (computedExponentRaw := run.weightRatioStroop)
        (tokenAmountIn := run.tokenAmountIn) (adjustedInput := run.adjustedIn)
        (output := run.output) hinputBalance houtputBalance houtputAmount
        (by rfl) hratioUpper hfeeUpperReal (by rfl) href.baseCeil
        hidealExponentLower hexponentInteger href.exponentCeil
        (by simpa [computedBase] using hwholeTrace) hscale
        (by simpa [hcpowCase] using href.tokenAmountInCeil)
        href.adjustedInCeil href.outputCeil
  | fractional integerPart remainderStroop wholeRaw approx powerRaw =>
      have hcpowExec :
          exactOutputCPowExecution run.baseRaw run.weightRatioBone
              run.weightRatioStroop.toNat =
            some (.fractional integerPart remainderStroop wholeRaw approx powerRaw) := by
        simpa [hcpowCase] using run.cpowExec
      have hcomponents := exactOutputCPowExecution_fractional_components
        hrawQuotientLeNine hcpowExec
      let remainRaw : ℤ := remainderStroop * (BONE / STROOP)
      let a : ℝ := (remainderStroop : ℝ) / STROOP
      let wholeComputed : ℝ := (wholeRaw : ℝ) / BONE
      let computedPower : ℝ := powerRaw
      have happExec : exactOutputApproxExecution run.baseRaw remainRaw = some approx := by
        simpa [remainRaw] using hcomponents.2.2.2.2.1
      have hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed := by
        simpa [computedBase, wholeComputed] using
          upperPowiExecution_refines hbaseRaw0 hcomponents.2.2.2.1
      have hremainder0 : 0 < remainderStroop :=
        Nat.pos_of_ne_zero hcomponents.2.2.1
      have hremainderLt : remainderStroop < STROOP := by
        rw [hcomponents.2.1]
        exact Nat.mod_lt _ (by norm_num [STROOP])
      have ha0 : 0 ≤ a := by positivity
      have ha1 : a ≤ 1 := by
        dsimp [a]
        exact (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
          (by exact_mod_cast hremainderLt.le)
      have hcomputedExponentSplit :
          computedExponent = (integerPart : ℝ) + a := by
        have hdecomp := Nat.mod_add_div run.weightRatioStroop.toNat STROOP
        have hnat :
            run.weightRatioStroop.toNat =
              remainderStroop + STROOP * integerPart := by
          rw [hcomponents.1, hcomponents.2.1]
          exact hdecomp.symm
        dsimp [computedExponent, a]
        rw [← htoNatReal, hnat]
        push_cast
        norm_num [STROOP]
        ring
      have happFacts := exactOutputApproxExecution_success happExec
      obtain ⟨finalState, hxRaw, hsteps, hunadjusted, hfinalTerm, hn1, hn50,
        hcontinued, hfirstCorrection, hlaterCorrection, hplain⟩ := happFacts
      have hfirstFloorRaw := exactOutputApproxExecution_first_term_refines happExec
      have hfirstFloor :
          IsFloor
            (exactInputApproxStateAt approx.xRaw remainRaw 1).term
            ((BONE : ℝ) * a * (computedBase - 1)) := by
        convert hfirstFloorRaw using 1
        rw [hxRaw]
        dsimp [remainRaw, a, computedBase]
        push_cast
        norm_num [BONE, STROOP]
        ring
      have hcomposedCeilRaw := (i256_fixed_mul_ceil_success_refines
        (by norm_num [BONE]) (by
          norm_num [BONE, SorobanFixedPointMath.I256.maxValue])
        hcomponents.2.2.2.2.2).1
      by_cases hfirst : approx.iterations = 1
      · have hpartial := exactOutputApproxExecution_first_sum
          hbaseRawPositive happExec hfirst
        have hcomposedCeil :
            IsCeil powerRaw
              (wholeComputed *
                ((BONE : ℝ) +
                  ((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ) +
                    1)) := by
          have hpartialReal :
              (approx.partialRaw : ℝ) =
                (BONE : ℝ) +
                  ((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ) + 1 := by
            exact_mod_cast hpartial
          rw [← hpartialReal]
          dsimp [wholeComputed]
          convert hcomposedCeilRaw using 1
          all_goals push_cast
          all_goals ring
        exact baseline_swap_exact_amount_out_first_term_adverse_error_lt_precise_fee_share
          (integerPart := integerPart) (inputBalance := inputBalance)
          (outputBalance := outputBalance) (outputAmount := outputAmount)
          (nominalRatio := nominalRatio) (feeRate := feeRate)
          (computedBase := computedBase) (idealExponent := idealExponent)
          (computedExponent := computedExponent) (a := a)
          (wholeComputed := wholeComputed) (computedPower := computedPower)
          (scale := scale) (computedBaseRaw := run.baseRaw)
          (computedExponentRaw := run.weightRatioStroop)
          (firstRounded :=
            (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
          (computedPowerRaw := powerRaw) (tokenAmountIn := run.tokenAmountIn)
          (adjustedInput := run.adjustedIn) (output := run.output)
          hinputBalance houtputBalance houtputAmount (by rfl) hratioUpper
          hfeeUpperReal (by rfl) href.baseCeil hidealExponentLower (by rfl)
          href.exponentCeil ha0 ha1 hcomputedExponentSplit hfirstFloor
          hwholeTrace (by rfl) hcomposedCeil hscale
          (by simpa [hcpowCase, computedPower] using href.tokenAmountInCeil)
          href.adjustedInCeil href.outputCeil
      · have hn2 : 2 ≤ approx.iterations := by omega
        have hremain0 : 0 < remainRaw := by
          dsimp [remainRaw]
          exact_mod_cast Nat.mul_pos hremainder0
            (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
        have hremainUpper : remainRaw < BONE := by
          dsimp [remainRaw]
          have hfactor : 0 < BONE / STROOP := by norm_num [BONE, STROOP]
          have hscaled := (Nat.mul_lt_mul_right hfactor).2 hremainderLt
          norm_num [BONE, STROOP] at hscaled ⊢
          exact_mod_cast hscaled
        by_cases hsecond : approx.iterations = 2
        · have hpartial := exactOutputApproxExecution_second_sum
            hbaseRawPositive hremain0 hremainUpper happExec hsecond
          have hfirstNonnegative :=
            (exactOutputApproxExecution_term_sign hbaseRawPositive hremain0
              hremainUpper happExec 1 (by omega) (by omega)).1 (by norm_num)
          have hfirstContinued :
              (CPOW_PRECISION : ℝ) <
                (exactInputApproxStateAt approx.xRaw remainRaw 1).term := by
            have hsource := hcontinued 1 (by omega) (by omega)
            rw [abs_of_nonneg hfirstNonnegative] at hsource
            exact_mod_cast hsource
          have hcomposedCeil :
              IsCeil powerRaw
                (wholeComputed *
                  ((BONE : ℝ) +
                    ((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ))) := by
            have hpartialReal :
                (approx.partialRaw : ℝ) =
                  (BONE : ℝ) +
                    ((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ) := by
              exact_mod_cast hpartial
            rw [← hpartialReal]
            dsimp [wholeComputed]
            convert hcomposedCeilRaw using 1
            all_goals push_cast
            all_goals ring
          exact baseline_swap_exact_amount_out_second_term_adverse_error_lt_precise_fee_share
            (integerPart := integerPart) (inputBalance := inputBalance)
            (outputBalance := outputBalance) (outputAmount := outputAmount)
            (nominalRatio := nominalRatio) (feeRate := feeRate)
            (computedBase := computedBase) (idealExponent := idealExponent)
            (computedExponent := computedExponent) (a := a)
            (wholeComputed := wholeComputed) (computedPower := computedPower)
            (scale := scale) (computedBaseRaw := run.baseRaw)
            (computedExponentRaw := run.weightRatioStroop)
            (firstRounded :=
              (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
            (computedPowerRaw := powerRaw) (tokenAmountIn := run.tokenAmountIn)
            (adjustedInput := run.adjustedIn) (output := run.output)
            hinputBalance houtputBalance houtputAmount (by rfl) hratioUpper
            hfeeUpperReal (by rfl) href.baseCeil hidealExponentLower
            hidealExponentUpper (by rfl) href.exponentCeil ha0 ha1
            hcomputedExponentSplit hfirstFloor hfirstContinued hwholeTrace
            (by rfl) hcomposedCeil hscale
            (by simpa [hcpowCase, computedPower] using href.tokenAmountInCeil)
            href.adjustedInCeil href.outputCeil
        · have hn3 : 3 ≤ approx.iterations := by omega
          obtain ⟨degree, oddIndex, hdegreeOdd, hdegreeStop, hpartial⟩ :=
            exactOutputApproxExecution_later_sum hbaseRawPositive hremain0
              hremainUpper happExec hn3
          let coefficientProduct : ℕ → ℤ := fun k ↦
            (exactInputApproxStateAt approx.xRaw remainRaw k).coefficientProduct
          let multiplied : ℕ → ℤ := fun k ↦
            (exactInputApproxStateAt approx.xRaw remainRaw k).multiplied
          let computedTerm : ℕ → ℤ := fun k ↦
            (exactInputApproxStateAt approx.xRaw remainRaw k).term
          have hcoefficientFloor : ∀ k, 1 ≤ k → k < approx.iterations →
              IsFloor (coefficientProduct (k + 1))
                ((BONE : ℝ) * (a - (k : ℝ)) * (computedBase - 1)) := by
            intro k hk hkn
            obtain ⟨stepState, hstep⟩ := exactOutputApproxExecution_prefix happExec
              (k + 1) (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                  stepState := by
              simp [exactInputApproxStateAt, hstep]
            have hstepFacts := exactInputApproxSteps_refinements
              (iteration := k + 1) (by omega) (by omega) hstep
            dsimp [coefficientProduct]
            rw [hstepAt]
            convert hstepFacts.1 using 1
            rw [hxRaw]
            dsimp [remainRaw, a, computedBase]
            push_cast
            norm_num [BONE, STROOP]
            field_simp
            ring
          have hmultiplyFloor : ∀ k, 1 ≤ k → k < approx.iterations →
              IsFloor (multiplied (k + 1))
                ((computedTerm k : ℝ) *
                  (coefficientProduct (k + 1) : ℝ) / BONE) := by
            intro k hk hkn
            obtain ⟨stepState, hstep⟩ := exactOutputApproxExecution_prefix happExec
              (k + 1) (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                  stepState := by
              simp [exactInputApproxStateAt, hstep]
            have hstepFacts := exactInputApproxSteps_refinements
              (iteration := k + 1) (by omega) (by omega) hstep
            dsimp [multiplied, computedTerm, coefficientProduct]
            rw [hstepAt]
            simpa using hstepFacts.2.1
          have hdivideFloor : ∀ k, 1 ≤ k → k < approx.iterations →
              IsFloor (computedTerm (k + 1))
                ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)) := by
            intro k hk hkn
            obtain ⟨stepState, hstep⟩ := exactOutputApproxExecution_prefix happExec
              (k + 1) (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                  stepState := by
              simp [exactInputApproxStateAt, hstep]
            have hstepFacts := exactInputApproxSteps_refinements
              (iteration := k + 1) (by omega) (by omega) hstep
            dsimp [computedTerm, multiplied]
            rw [hstepAt]
            simpa [Nat.cast_add, Nat.cast_one] using hstepFacts.2.2.1
          have hcomputedFractional :
              (approx.partialRaw : ℝ) = (BONE : ℝ) +
                ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ) := by
            exact_mod_cast hpartial
          have hcomposedCeil :
              IsCeil powerRaw (wholeComputed * (approx.partialRaw : ℝ)) := by
            dsimp [wholeComputed]
            convert hcomposedCeilRaw using 1
            all_goals push_cast
            all_goals ring
          exact baseline_swap_exact_amount_out_later_adverse_error_lt_precise_fee_share
            coefficientProduct multiplied computedTerm
            (n := approx.iterations) (degree := degree) (oddIndex := oddIndex)
            (integerPart := integerPart) (inputBalance := inputBalance)
            (outputBalance := outputBalance) (outputAmount := outputAmount)
            (nominalRatio := nominalRatio) (feeRate := feeRate)
            (computedBase := computedBase) (idealExponent := idealExponent)
            (computedExponent := computedExponent) (a := a)
            (computedFractional := (approx.partialRaw : ℝ))
            (wholeComputed := wholeComputed) (computedPower := computedPower)
            (scale := scale) (computedBaseRaw := run.baseRaw)
            (computedExponentRaw := run.weightRatioStroop)
            (computedPowerRaw := powerRaw) (tokenAmountIn := run.tokenAmountIn)
            (adjustedInput := run.adjustedIn) (output := run.output)
            hinputBalance houtputBalance houtputAmount (by rfl) hratioUpper
            hfeeUpperReal (by rfl) href.baseCeil hidealExponentLower
            hidealExponentUpper (by rfl) href.exponentCeil ha0 ha1
            hcomputedExponentSplit hn3 hn50 hdegreeOdd hdegreeStop
            (by
              intro k hk hkn
              exact_mod_cast hcontinued k hk hkn)
            (by
              rw [exactOutputBinomialTerm_one]
              simpa [computedTerm] using hfirstFloor)
            hcoefficientFloor hmultiplyFloor hdivideFloor hcomputedFractional
            hwholeTrace (by rfl) hcomposedCeil hscale
            (by simpa [hcpowCase, computedPower] using href.tokenAmountInCeil)
            href.adjustedInCeil href.outputCeil

/-
Direct theorem for a successful executable `calc_token_in_given_token_out`
model result under the public swap's positive-output, ratio, fee, and weight
configuration invariants.
-/
theorem calc_token_in_given_token_out_execution_adverse_error_lt_precise_fee_share
    {inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ} {output : ℤ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountOut : 0 < amountOut)
    (hinWeightLower : MIN_WEIGHT ≤ inWeight)
    (hinWeightUpper : inWeight ≤ MAX_WEIGHT)
    (houtWeightLower : MIN_WEIGHT ≤ outWeight)
    (houtWeightUpper : outWeight ≤ MAX_WEIGHT)
    (houtputRatio : amountOut * STROOP ≤ outBalance * MAX_OUT_RATIO)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenInGivenTokenOutExecution inBalance inScalar outBalance
      outScalar amountOut inWeight outWeight fee = some output) :
    exactOutputIdealInput (inBalance : ℝ) ((fee : ℝ) / STROOP)
        ((amountOut : ℝ) / outBalance) ((outWeight : ℝ) / inWeight) -
      (output : ℝ) <
    EXACT_OUTPUT_ADVERSE_FEE_SHARE *
      exactOutputAdjustedMinimumFeeInputValue (inBalance : ℝ)
        ((fee : ℝ) / STROOP) ((outWeight : ℝ) / inWeight)
        ((amountOut : ℝ) / outBalance) := by
  obtain ⟨run, houtput⟩ := successfulExactOutputMathRun_of_execution hexec
  have hrun := successfulExactOutputMathRun_adverse_error_lt_precise_fee_share
    hinBalance hinScalar houtBalance houtScalar hamountOut hinWeightLower
      hinWeightUpper houtWeightLower houtWeightUpper houtputRatio hfeeUpper run
  have hinWeight : 0 < inWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hinWeightLower
  have houtWeight : 0 < outWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) houtWeightLower
  have hinWeightMax : inWeight ≤ STROOP :=
    le_trans hinWeightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have href := successfulExactOutputMathRun_refines hinBalance hinScalar
    houtBalance houtScalar hamountOut hinWeight hinWeightMax houtWeight
      houtputRatio hfeeUpper run
  have hinputBalanceEq :
      (run.tokenBalanceIn : ℝ) / inScalar = inBalance := by
    rw [href.tokenBalanceInEq]
    push_cast
    have hscalar : (inScalar : ℝ) ≠ 0 := by positivity
    field_simp
  have hnominalEq :
      (run.tokenAmountOut : ℝ) / run.tokenBalanceOut =
        (amountOut : ℝ) / outBalance := by
    rw [href.tokenAmountOutEq, href.tokenBalanceOutEq]
    push_cast
    have hscalar : (outScalar : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hinputBalanceEq, hnominalEq] at hrun
  have houtputReal : (run.output : ℝ) = output := by exact_mod_cast houtput
  simpa [houtputReal] using hrun

end CometPool
