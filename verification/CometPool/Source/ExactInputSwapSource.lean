import CometPool.Operations.ExactInputSwap
import CometPool.Source.SpotPriceSource
import SorobanFixedPointMath.FixedPointImpl

set_option maxRecDepth 65536

namespace CometPool

/-!
Executable, source-shaped models for the positive-input arithmetic used by
`swap_exact_amount_in`. `none` represents a checked host operation,
`to_i128`, source guard, or `unwrap_optimized` failure.
-/

/-- Successful checked `I256` floor execution has exact floor semantics. -/
theorem i256_fixed_mul_floor_success_refines
    {x y result : ℤ} {denominator : ℕ}
    (hdenominator : 0 < denominator)
    (hdenominatorMax :
      (denominator : ℤ) ≤ SorobanFixedPointMath.I256.maxValue)
    (hexec :
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        x y denominator = some result) :
    IsFloor result ((((x * y : ℤ) : ℝ) / (denominator : ℝ))) ∧
      SorobanFixedPointMath.I256.InRange result := by
  have hprod : SorobanFixedPointMath.I256.InRange (x * y) := by
    by_contra hprod
    have hmul : SorobanFixedPointMath.I256.mul x y = none := by
      simp [SorobanFixedPointMath.I256.mul,
        SorobanFixedPointMath.I256.checked, hprod]
    unfold SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      SorobanFixedPointMath.FixedPointImpl.mulDivFloor at hexec
    rw [hmul] at hexec
    contradiction
  have hvalueExec :=
    SorobanFixedPointMath.FixedPointImpl.mulDivFloor_eq_some
      hprod hdenominator hdenominatorMax
  have hresult :
      result = SorobanFixedPointMath.FixedPointImpl.mulDivFloorValue
        x y denominator :=
    Option.some.inj (hexec.symm.trans hvalueExec)
  rw [hresult]
  exact ⟨
    SorobanFixedPointMath.FixedPointImpl.mulDivFloorValue_isFloor
      x y hdenominator,
    SorobanFixedPointMath.FixedPointImpl.mulDivFloorValue_inRange
      hprod hdenominator⟩

/-- Successful checked `I256` ceiling execution has exact ceiling semantics. -/
theorem i256_fixed_mul_ceil_success_refines
    {x y result : ℤ} {denominator : ℕ}
    (hdenominator : 0 < denominator)
    (hdenominatorMax :
      (denominator : ℤ) ≤ SorobanFixedPointMath.I256.maxValue)
    (hexec :
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        x y denominator = some result) :
    IsCeil result ((((x * y : ℤ) : ℝ) / (denominator : ℝ))) ∧
      SorobanFixedPointMath.I256.InRange result := by
  have hprod : SorobanFixedPointMath.I256.InRange (x * y) := by
    by_contra hprod
    have hmul : SorobanFixedPointMath.I256.mul x y = none := by
      simp [SorobanFixedPointMath.I256.mul,
        SorobanFixedPointMath.I256.checked, hprod]
    unfold SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
      SorobanFixedPointMath.FixedPointImpl.mulDivCeil at hexec
    rw [hmul] at hexec
    contradiction
  have hvalueExec :=
    SorobanFixedPointMath.FixedPointImpl.mulDivCeil_eq_some
      hprod hdenominator hdenominatorMax
  have hresult :
      result = SorobanFixedPointMath.FixedPointImpl.mulDivCeilValue
        x y denominator :=
    Option.some.inj (hexec.symm.trans hvalueExec)
  rw [hresult]
  exact ⟨
    SorobanFixedPointMath.FixedPointImpl.mulDivCeilValue_isCeil
      x y hdenominator,
    SorobanFixedPointMath.FixedPointImpl.mulDivCeilValue_inRange
      hprod hdenominator⟩

theorem i256_fixed_div_floor_success_refines
    {x denominator result : ℤ} {y : ℕ}
    (hy : 0 < y)
    (hymax : (y : ℤ) ≤ SorobanFixedPointMath.I256.maxValue)
    (hexec :
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        x y denominator = some result) :
    IsFloor result ((((x * denominator : ℤ) : ℝ) / (y : ℝ))) ∧
      SorobanFixedPointMath.I256.InRange result := by
  simpa [SorobanFixedPointMath.FixedPointImpl.fixedDivFloor] using
    i256_fixed_mul_floor_success_refines hy hymax hexec

theorem i256_fixed_div_ceil_success_refines
    {x denominator result : ℤ} {y : ℕ}
    (hy : 0 < y)
    (hymax : (y : ℤ) ≤ SorobanFixedPointMath.I256.maxValue)
    (hexec :
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        x y denominator = some result) :
    IsCeil result ((((x * denominator : ℤ) : ℝ) / (y : ℝ))) ∧
      SorobanFixedPointMath.I256.InRange result := by
  simpa [SorobanFixedPointMath.FixedPointImpl.fixedDivCeil] using
    i256_fixed_mul_ceil_success_refines hy hymax hexec

private theorem bone_positive : 0 < BONE := by norm_num [BONE]

private theorem bone_le_i256_max :
    (BONE : ℤ) ≤ SorobanFixedPointMath.I256.maxValue := by
  norm_num [BONE, SorobanFixedPointMath.I256.maxValue]

/-- Raw state after one or more `c_pow_approx` loop iterations. -/
structure ExactInputApproxState where
  coefficientProduct : ℤ
  multiplied : ℤ
  term : ℤ
  sum : ℤ
deriving DecidableEq

private def initialExactInputApproxState : ExactInputApproxState where
  coefficientProduct := 0
  multiplied := 0
  term := BONE
  sum := BONE

/-- One production three-floor recurrence update and its checked sum. -/
def exactInputApproxStep
    (xRaw remainRaw : ℤ) (iteration : ℕ)
    (previous : ExactInputApproxState) : Option ExactInputApproxState := do
  let bigKRaw : ℤ := iteration * BONE
  let kMinusOneRaw ← SorobanFixedPointMath.I256.sub bigKRaw BONE
  let coefficientRaw ←
    SorobanFixedPointMath.I256.sub remainRaw kMinusOneRaw
  let coefficientProduct ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      coefficientRaw xRaw BONE
  let multiplied ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      previous.term coefficientProduct BONE
  let term ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      multiplied bigKRaw.toNat BONE
  let sum ← SorobanFixedPointMath.I256.add previous.sum term
  some { coefficientProduct, multiplied, term, sum }

/-- Checked components recovered from one successful recurrence update. -/
theorem exactInputApproxStep_success_components
    {xRaw remainRaw : ℤ} {iteration : ℕ}
    {previous next : ExactInputApproxState}
    (hexec :
      exactInputApproxStep xRaw remainRaw iteration previous = some next) :
    ∃ kMinusOneRaw coefficientRaw : ℤ,
      SorobanFixedPointMath.I256.sub (iteration * BONE) BONE =
          some kMinusOneRaw ∧
        SorobanFixedPointMath.I256.sub remainRaw kMinusOneRaw =
          some coefficientRaw ∧
        SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
          coefficientRaw xRaw BONE = some next.coefficientProduct ∧
        SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
          previous.term next.coefficientProduct BONE = some next.multiplied ∧
        SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
          next.multiplied (iteration * BONE) BONE = some next.term ∧
        SorobanFixedPointMath.I256.add previous.sum next.term = some next.sum := by
  simp [exactInputApproxStep, Option.bind_eq_some_iff] at hexec
  rcases hexec with
    ⟨kMinusOneRaw, hkMinusOne,
      coefficientRaw, hcoefficient,
      coefficientProduct, hcoefficientProduct,
      multiplied, hmultiplied,
      term, hterm,
      sum, hsum, hnext⟩
  cases hnext
  exact ⟨kMinusOneRaw, coefficientRaw, hkMinusOne, hcoefficient,
    hcoefficientProduct, hmultiplied, hterm, hsum⟩

/-- Deterministic prefix of the recurrence, without applying the stop test. -/
def exactInputApproxSteps (xRaw remainRaw : ℤ) :
    ℕ → Option ExactInputApproxState
  | 0 => some initialExactInputApproxState
  | iteration + 1 => do
      let previous ← exactInputApproxSteps xRaw remainRaw iteration
      exactInputApproxStep xRaw remainRaw (iteration + 1) previous

/-- Total projection used to expose the deterministic executed prefix. -/
def exactInputApproxStateAt
    (xRaw remainRaw : ℤ) (iteration : ℕ) : ExactInputApproxState :=
  (exactInputApproxSteps xRaw remainRaw iteration).getD
    initialExactInputApproxState

private theorem i256_sub_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x - y) = some result from hexec)
  exact h.2.symm

private theorem i256_add_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x + y) = some result from hexec)
  exact h.2.symm

private theorem i128_mul_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem i128_sub_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x - y) = some result from hexec)
  exact h.2.symm

/-- One successful source recurrence step updates the sum by its new term. -/
private theorem exactInputApproxStep_sum_eq
    {xRaw remainRaw : ℤ} {iteration : ℕ}
    {previous next : ExactInputApproxState}
    (hexec :
      exactInputApproxStep xRaw remainRaw iteration previous = some next) :
    next.sum = previous.sum + next.term := by
  obtain ⟨_, _, _, _, _, _, _, hsum⟩ :=
    exactInputApproxStep_success_components hexec
  exact i256_add_success_eq hsum

private theorem iteration_mul_bone_le_i256_max
    {iteration : ℕ} (hiteration : iteration ≤ 50) :
    ((iteration * BONE : ℕ) : ℤ) ≤
      SorobanFixedPointMath.I256.maxValue := by
  calc
    ((iteration * BONE : ℕ) : ℤ) ≤ ((50 * BONE : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right BONE hiteration
    _ ≤ SorobanFixedPointMath.I256.maxValue := by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]

/-- Every successfully evaluated recurrence prefix supplies its three floors. -/
theorem exactInputApproxSteps_refinements
    {xRaw remainRaw : ℤ} {iteration : ℕ}
    (hiteration0 : 1 ≤ iteration) (hiteration50 : iteration ≤ 50)
    {state : ExactInputApproxState}
    (hexec : exactInputApproxSteps xRaw remainRaw iteration = some state) :
    IsFloor state.coefficientProduct
        ((((remainRaw : ℝ) - ((iteration : ℝ) - 1) * BONE) *
          (xRaw : ℝ)) / BONE) ∧
      IsFloor state.multiplied
        ((((exactInputApproxStateAt xRaw remainRaw (iteration - 1)).term : ℝ) *
          (state.coefficientProduct : ℝ)) / BONE) ∧
      IsFloor state.term ((state.multiplied : ℝ) / iteration) ∧
      state.sum =
        (exactInputApproxStateAt xRaw remainRaw (iteration - 1)).sum + state.term := by
  obtain ⟨previousIteration, rfl⟩ : ∃ k, iteration = k + 1 := by
    exact ⟨iteration - 1, by omega⟩
  simp [exactInputApproxSteps, Option.bind_eq_some_iff] at hexec
  rcases hexec with ⟨previous, hprevious, hstep⟩
  obtain ⟨kMinusOneRaw, coefficientRaw, hkMinusOne, hcoefficient,
    hcoefficientProduct, hmultiplied, hterm, hsum⟩ :=
      exactInputApproxStep_success_components hstep
  have hpreviousAt :
      exactInputApproxStateAt xRaw remainRaw previousIteration = previous := by
    simp [exactInputApproxStateAt, hprevious]
  have hkMinusOneEq :
      kMinusOneRaw = ((previousIteration + 1 : ℕ) : ℤ) * BONE - BONE :=
    i256_sub_success_eq hkMinusOne
  have hcoefficientEq : coefficientRaw = remainRaw - kMinusOneRaw :=
    i256_sub_success_eq hcoefficient
  have hcoefficientFloor := (i256_fixed_mul_floor_success_refines
    bone_positive bone_le_i256_max hcoefficientProduct).1
  have hmultipliedFloor := (i256_fixed_mul_floor_success_refines
    bone_positive bone_le_i256_max hmultiplied).1
  have hiterationPositive : 0 < (previousIteration + 1) * BONE := by
    exact Nat.mul_pos (by omega) bone_positive
  have htermFloor := (i256_fixed_div_floor_success_refines
    hiterationPositive
      (iteration_mul_bone_le_i256_max (by omega)) hterm).1
  have hsumEq := i256_add_success_eq hsum
  have hpreviousIndex : previousIteration + 1 - 1 = previousIteration := by omega
  constructor
  · rw [hcoefficientEq, hkMinusOneEq] at hcoefficientFloor
    convert hcoefficientFloor using 1
    all_goals push_cast
    all_goals ring
  constructor
  · rw [hpreviousIndex, hpreviousAt]
    simpa only [Int.cast_mul] using hmultipliedFloor
  constructor
  · convert htermFloor using 1
    push_cast
    have hB : (BONE : ℝ) ≠ 0 := by norm_num [BONE]
    field_simp
    ring
  · rw [hpreviousIndex, hpreviousAt]
    exact hsumEq

/-- Checked absolute value used by the production convergence test. -/
def exactInputAbsExecution (value : ℤ) : Option ℤ :=
  if value < 0 then SorobanFixedPointMath.I256.mul value (-1)
  else some value

/-- A successful checked absolute-value execution returns integer absolute value. -/
theorem exactInputAbsExecution_eq_abs
    {value absValue : ℤ}
    (hexec : exactInputAbsExecution value = some absValue) :
    absValue = |value| := by
  by_cases hvalue : value < 0
  · rw [exactInputAbsExecution, if_pos hvalue] at hexec
    have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
      (show SorobanFixedPointMath.I256.checked (value * (-1)) =
        some absValue from hexec)
    rw [← h.2]
    simp [abs_of_neg hvalue]
  · rw [exactInputAbsExecution, if_neg hvalue] at hexec
    have habs : |value| = value := abs_of_nonneg (le_of_not_gt hvalue)
    exact (Option.some.inj hexec).symm.trans habs.symm

/-- Result selected by the bounded approximation loop. -/
structure ExactInputApproxLoopResult where
  iterations : ℕ
  state : ExactInputApproxState
deriving DecidableEq

/--
Find the first stopping iteration while evaluating only prefixes through that
iteration. At fuel exhaustion, the fiftieth state is returned exactly as in
the Rust `for i in 1..51` loop.
-/
def exactInputApproxFindStop (xRaw remainRaw : ℤ) :
    ℕ → ℕ → Option ExactInputApproxLoopResult
  | 0, completed => do
      let state ← exactInputApproxSteps xRaw remainRaw completed
      some { iterations := completed, state }
  | fuel + 1, completed => do
      let iteration := completed + 1
      let state ← exactInputApproxSteps xRaw remainRaw iteration
      let absTerm ← exactInputAbsExecution state.term
      if absTerm ≤ CPOW_PRECISION then
        some { iterations := iteration, state }
      else
        exactInputApproxFindStop xRaw remainRaw fuel iteration

/--
A successful bounded search exposes only actually executed prefixes, together
with the continuation tests preceding the selected stopping iteration.
-/
theorem exactInputApproxFindStop_success
    {xRaw remainRaw : ℤ} {fuel completed : ℕ}
    {result : ExactInputApproxLoopResult}
    (hexec :
      exactInputApproxFindStop xRaw remainRaw fuel completed = some result) :
    completed ≤ result.iterations ∧
      (fuel = 0 ∨ completed < result.iterations) ∧
      result.iterations ≤ completed + fuel ∧
      exactInputApproxSteps xRaw remainRaw result.iterations =
        some result.state ∧
      (∀ k, completed < k → k ≤ result.iterations →
        ∃ state, exactInputApproxSteps xRaw remainRaw k = some state) ∧
      ∀ k, completed < k → k < result.iterations →
        CPOW_PRECISION <
          |(exactInputApproxStateAt xRaw remainRaw k).term| := by
  induction fuel generalizing completed with
  | zero =>
      simp [exactInputApproxFindStop, Option.bind_eq_some_iff] at hexec
      rcases hexec with ⟨state, hstate, hresult⟩
      subst result
      refine ⟨by simp, Or.inl rfl, by simp, ?_, ?_, ?_⟩
      · simpa using hstate
      · intro k hkCompleted hkResult
        simp at hkResult
        omega
      · intro k hkCompleted hkResult
        simp at hkResult
        omega
  | succ fuel ih =>
      rw [exactInputApproxFindStop] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨state, hstate, hafterState⟩
      rcases Option.bind_eq_some.mp hafterState with
        ⟨absTerm, habsTerm, hafterAbs⟩
      by_cases hstop : absTerm ≤ CPOW_PRECISION
      · rw [if_pos hstop] at hafterAbs
        have hresult := Option.some.inj hafterAbs
        subst result
        refine ⟨by simp, Or.inr (by simp), by simp, ?_, ?_, ?_⟩
        · simpa using hstate
        · intro k hkCompleted hkResult
          change k ≤ completed + 1 at hkResult
          have hk : k = completed + 1 := by omega
          subst k
          exact ⟨state, hstate⟩
        · intro k hkCompleted hkResult
          change k < completed + 1 at hkResult
          omega
      · rw [if_neg hstop] at hafterAbs
        have htail := ih hafterAbs
        refine ⟨by omega, Or.inr (lt_of_lt_of_le (by omega) htail.1),
          by omega, htail.2.2.2.1, ?_, ?_⟩
        · intro k hkCompleted hkResult
          by_cases hk : k = completed + 1
          · subst k
            exact ⟨state, hstate⟩
          · exact htail.2.2.2.2.1 k (by omega) hkResult
        intro k hkCompleted hkResult
        by_cases hk : k = completed + 1
        · subst k
          have hstateAt :
              exactInputApproxStateAt xRaw remainRaw (completed + 1) = state := by
            simp [exactInputApproxStateAt, hstate]
          rw [hstateAt]
          rw [exactInputAbsExecution_eq_abs habsTerm] at hstop
          omega
        · exact htail.2.2.2.2.2 k (by omega) hkResult

/-- A result strictly before fuel exhaustion satisfied the source stop test. -/
theorem exactInputApproxFindStop_final_le_of_lt_cap
    {xRaw remainRaw : ℤ} {fuel completed : ℕ}
    {result : ExactInputApproxLoopResult}
    (hexec :
      exactInputApproxFindStop xRaw remainRaw fuel completed = some result)
    (hcap : result.iterations < completed + fuel) :
    |(exactInputApproxStateAt xRaw remainRaw result.iterations).term| ≤
      CPOW_PRECISION := by
  induction fuel generalizing completed with
  | zero =>
      simp [exactInputApproxFindStop, Option.bind_eq_some_iff] at hexec
      rcases hexec with ⟨state, hstate, hresult⟩
      subst result
      simp at hcap
  | succ fuel ih =>
      rw [exactInputApproxFindStop] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨state, hstate, hafterState⟩
      rcases Option.bind_eq_some.mp hafterState with
        ⟨absTerm, habsTerm, hafterAbs⟩
      by_cases hstop : absTerm ≤ CPOW_PRECISION
      · rw [if_pos hstop] at hafterAbs
        have hresult := Option.some.inj hafterAbs
        subst result
        have hstateAt :
            exactInputApproxStateAt xRaw remainRaw (completed + 1) = state := by
          simp [exactInputApproxStateAt, hstate]
        rw [hstateAt, ← exactInputAbsExecution_eq_abs habsTerm]
        exact hstop
      · rw [if_neg hstop] at hafterAbs
        exact ih hafterAbs (by omega)

/-- The checked sum state is exactly the sum of the executed term prefix. -/
theorem exactInputApproxSteps_sum
    {xRaw remainRaw : ℤ} {iteration : ℕ}
    (hiteration50 : iteration ≤ 50)
    {state : ExactInputApproxState}
    (hexec : exactInputApproxSteps xRaw remainRaw iteration = some state) :
    state.sum = BONE +
      ∑ k ∈ Finset.range iteration,
        (exactInputApproxStateAt xRaw remainRaw (k + 1)).term := by
  induction iteration generalizing state with
  | zero =>
      rw [exactInputApproxSteps] at hexec
      have hstate := Option.some.inj hexec
      subst state
      simp [initialExactInputApproxState]
  | succ iteration ih =>
      have hfull := hexec
      rw [exactInputApproxSteps] at hexec
      rcases Option.bind_eq_some.mp hexec with
        ⟨previous, hprevious, hstep⟩
      have hsum := exactInputApproxStep_sum_eq hstep
      have hcurrentAt :
          exactInputApproxStateAt xRaw remainRaw (iteration + 1) = state := by
        simp [exactInputApproxStateAt, hfull]
      rw [hsum]
      rw [ih (by omega) hprevious]
      rw [Finset.sum_range_succ]
      simp only [Finset.sum_apply, Finset.mem_range, add_assoc]
      rw [hcurrentAt]

/-- Corrected result of the exact-input (`round_up = true`) approximation. -/
structure ExactInputApproxExecutionResult where
  iterations : ℕ
  xRaw : ℤ
  unadjustedSumRaw : ℤ
  partialRaw : ℤ
deriving DecidableEq

/-- Specialized execution of `c_pow_approx(..., round_up = true)`. -/
def exactInputApproxExecution
    (baseRaw remainRaw : ℤ) : Option ExactInputApproxExecutionResult := do
  let xRaw ← SorobanFixedPointMath.I256.sub baseRaw BONE
  let stopped ← exactInputApproxFindStop xRaw remainRaw MAX_CPOW_ITERS 0
  let partialRaw ←
    if stopped.iterations = 1 ∧ xRaw ≠ 0 then
      SorobanFixedPointMath.I256.add stopped.state.sum 1
    else
      some stopped.state.sum
  some {
    iterations := stopped.iterations
    xRaw
    unadjustedSumRaw := stopped.state.sum
    partialRaw
  }

/-- Successful approximation execution exposes the bounded executed prefix. -/
theorem exactInputApproxExecution_success
    {baseRaw remainRaw : ℤ} {result : ExactInputApproxExecutionResult}
    (hexec : exactInputApproxExecution baseRaw remainRaw = some result) :
    ∃ state : ExactInputApproxState,
      result.xRaw = baseRaw - BONE ∧
        exactInputApproxSteps result.xRaw remainRaw result.iterations = some state ∧
        result.unadjustedSumRaw = state.sum ∧
        1 ≤ result.iterations ∧ result.iterations ≤ 50 ∧
        (∀ k, 1 ≤ k → k < result.iterations →
          CPOW_PRECISION <
            |(exactInputApproxStateAt result.xRaw remainRaw k).term|) ∧
        (result.iterations = 1 ∧ result.xRaw ≠ 0 →
          result.partialRaw = result.unadjustedSumRaw + 1) ∧
        (¬(result.iterations = 1 ∧ result.xRaw ≠ 0) →
          result.partialRaw = result.unadjustedSumRaw) := by
  rw [exactInputApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with ⟨stopped, hstopped, hafterStop⟩
  have hxEq := i256_sub_success_eq hxRaw
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
    refine ⟨stopped.state, hxEq, ?_, rfl, hn1, hn50, ?_, ?_, ?_⟩
    · simpa [hxEq] using hfind.2.2.2.1
    · intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
    · intro _
      exact i256_add_success_eq hpartialRaw
    · intro hnot
      exact False.elim (hnot hfirst)
  · rw [if_neg hfirst] at hafterStop
    rcases Option.bind_eq_some.mp hafterStop with
      ⟨partialRaw, hpartialRaw, hresult⟩
    have hresultEq := Option.some.inj hresult
    subst result
    refine ⟨stopped.state, hxEq, ?_, rfl, hn1, hn50, ?_, ?_, ?_⟩
    · simpa [hxEq] using hfind.2.2.2.1
    · intro k hk1 hkn
      simpa [hxEq] using hfind.2.2.2.2.2 k (by omega) hkn
    · intro hyes
      exact False.elim (hfirst hyes)
    · intro _
      exact Option.some.inj hpartialRaw.symm

/-- Successful approximation exposes every prefix that the loop executed. -/
theorem exactInputApproxExecution_prefix
    {baseRaw remainRaw : ℤ} {result : ExactInputApproxExecutionResult}
    (hexec : exactInputApproxExecution baseRaw remainRaw = some result) :
    ∀ k, 1 ≤ k → k ≤ result.iterations →
      ∃ state,
        exactInputApproxSteps result.xRaw remainRaw k = some state := by
  rw [exactInputApproxExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨xRaw, hxRaw, hafterX⟩
  rcases Option.bind_eq_some.mp hafterX with
    ⟨stopped, hstopped, hafterStop⟩
  have hxEq := i256_sub_success_eq hxRaw
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
    rcases Option.bind_eq_some.mp hafterStop with
      ⟨partialRaw, hpartialRaw, hresult⟩
    have hresultEq := Option.some.inj hresult
    subst result
    intro k hk1 hkn
    simpa [hxEq] using hfind.2.2.2.2.1 k (by omega) hkn

private theorem isFloor_zero_eq
    {rounded : ℤ} (hfloor : IsFloor rounded 0) : rounded = 0 := by
  have hlowerReal : (-1 : ℝ) < rounded := by
    linarith [hfloor.lt_add_one]
  have hlower : (-1 : ℤ) < rounded := by
    exact_mod_cast hlowerReal
  have hupper : rounded ≤ 0 := by
    exact_mod_cast hfloor.le
  omega

private theorem isFloor_integer_eq
    {rounded exact : ℤ} (hfloor : IsFloor rounded (exact : ℝ)) :
    rounded = exact := by
  have hlower : rounded ≤ exact := by exact_mod_cast hfloor.le
  have hupperReal : (exact : ℝ) < rounded + 1 := hfloor.lt_add_one
  have hupper : exact < rounded + 1 := by exact_mod_cast hupperReal
  omega

/-- The first successfully executed three-floor recurrence term is one floor. -/
theorem exactInputApproxExecution_first_term_refines
    {baseRaw remainRaw : ℤ} {result : ExactInputApproxExecutionResult}
    (hexec : exactInputApproxExecution baseRaw remainRaw = some result) :
    IsFloor
      (exactInputApproxStateAt result.xRaw remainRaw 1).term
      (((remainRaw : ℝ) * (result.xRaw : ℝ)) / BONE) := by
  obtain ⟨state, hstate⟩ := exactInputApproxExecution_prefix hexec 1
    (by omega) (exactInputApproxExecution_success hexec).choose_spec.2.2.2.1
  have hrefinements := exactInputApproxSteps_refinements
    (iteration := 1) (by omega) (by omega) hstate
  have hstateAt :
      exactInputApproxStateAt result.xRaw remainRaw 1 = state := by
    simp [exactInputApproxStateAt, hstate]
  have hinitialTerm :
      (exactInputApproxStateAt result.xRaw remainRaw 0).term = BONE := by
    rfl
  have hmultiplied : state.multiplied = state.coefficientProduct := by
    apply isFloor_integer_eq
    simpa [hinitialTerm, BONE] using hrefinements.2.1
  have hterm : state.term = state.multiplied := by
    apply isFloor_integer_eq
    simpa [hmultiplied] using hrefinements.2.2.1
  rw [hstateAt, hterm, hmultiplied]
  simpa using hrefinements.1

/-- With zero displacement, every successful recurrence prefix keeps sum `BONE`. -/
theorem exactInputApproxSteps_unit_sum
    {remainRaw : ℤ} {iteration : ℕ}
    (hiteration50 : iteration ≤ 50)
    {state : ExactInputApproxState}
    (hexec : exactInputApproxSteps 0 remainRaw iteration = some state) :
    state.sum = BONE := by
  induction iteration generalizing state with
  | zero =>
      rw [exactInputApproxSteps] at hexec
      have hstate := Option.some.inj hexec
      subst state
      rfl
  | succ iteration ih =>
      rw [exactInputApproxSteps] at hexec
      rcases Option.bind_eq_some.mp hexec with
        ⟨previous, hprevious, hstep⟩
      obtain ⟨_, _, _, _, hcoefficient, hmultiplied, hterm, hsum⟩ :=
        exactInputApproxStep_success_components hstep
      have hcoefficientFloor := (i256_fixed_mul_floor_success_refines
        bone_positive bone_le_i256_max hcoefficient).1
      have hcoefficient0 : state.coefficientProduct = 0 := by
        apply isFloor_zero_eq
        simpa using hcoefficientFloor
      have hmultipliedFloor := (i256_fixed_mul_floor_success_refines
        bone_positive bone_le_i256_max hmultiplied).1
      have hmultiplied0 : state.multiplied = 0 := by
        apply isFloor_zero_eq
        simpa [hcoefficient0] using hmultipliedFloor
      have hiterationPositive : 0 < (iteration + 1) * BONE := by
        exact Nat.mul_pos (by omega) bone_positive
      have htermFloor := (i256_fixed_div_floor_success_refines
        hiterationPositive
          (iteration_mul_bone_le_i256_max (by omega)) hterm).1
      have hterm0 : state.term = 0 := by
        apply isFloor_zero_eq
        simpa [hmultiplied0] using htermFloor
      rw [i256_add_success_eq hsum, hterm0, add_zero]
      exact ih (by omega) hprevious

/-- At a unit base, the checked approximation returns exactly one `BONE`. -/
theorem exactInputApproxExecution_unit
    {remainRaw : ℤ} {result : ExactInputApproxExecutionResult}
    (hexec : exactInputApproxExecution BONE remainRaw = some result) :
    result.partialRaw = BONE := by
  obtain ⟨state, hx, hsteps, hsum, _, hn50, _, _, huncorrected⟩ :=
    exactInputApproxExecution_success hexec
  have hx0 : result.xRaw = 0 := by
    simpa using hx
  have hstateSum : state.sum = BONE := by
    rw [hx0] at hsteps
    exact exactInputApproxSteps_unit_sum hn50 hsteps
  rw [huncorrected (by simp [hx0]), hsum, hstateSum]

/-- Bounded execution of the upper-rounded exponentiation-by-squaring loop. -/
def upperPowiLoopExecution :
    ℕ → ℤ → ℤ → ℕ → Option ℤ
  | 0, zRaw, _, n => if n = 0 then some zRaw else none
  | fuel + 1, zRaw, aRaw, n =>
      if n = 0 then some zRaw else do
        let aNextRaw ←
          SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
            aRaw aRaw BONE
        let zNextRaw ←
          if n % 2 ≠ 0 then
            SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
              zRaw aNextRaw BONE
          else
            some zRaw
        upperPowiLoopExecution fuel zNextRaw aNextRaw (n / 2)

/-- Specialized execution of `c_powi(..., round_up = true)`. -/
def upperPowiExecution (baseRaw : ℤ) (exponent : ℕ) : Option ℤ :=
  let zRaw := if exponent % 2 ≠ 0 then baseRaw else (BONE : ℤ)
  upperPowiLoopExecution (exponent + 1) zRaw baseRaw (exponent / 2)

/-- Successful checked loop execution constructs the abstract `c_powi` trace. -/
theorem upperPowiLoopExecution_refines
    {fuel n : ℕ} {zRaw aRaw resultRaw : ℤ}
    (hz0 : 0 ≤ zRaw) (ha0 : 0 ≤ aRaw)
    (hexec :
      upperPowiLoopExecution fuel zRaw aRaw n = some resultRaw) :
    UpperCPowiLoop
      ((zRaw : ℝ) / BONE) ((aRaw : ℝ) / BONE) n
      ((resultRaw : ℝ) / BONE) := by
  induction fuel generalizing zRaw aRaw n with
  | zero =>
      by_cases hn : n = 0
      · subst n
        simp [upperPowiLoopExecution] at hexec
        subst resultRaw
        exact UpperCPowiLoop.done _ _
      · simp [upperPowiLoopExecution, hn] at hexec
  | succ fuel ih =>
      by_cases hn : n = 0
      · subst n
        simp [upperPowiLoopExecution] at hexec
        subst resultRaw
        exact UpperCPowiLoop.done _ _
      · rw [upperPowiLoopExecution, if_neg hn] at hexec
        rcases Option.bind_eq_some.mp hexec with
          ⟨aNextRaw, haNextExec, hafterSquare⟩
        have haNextRefines := i256_fixed_mul_ceil_success_refines
          bone_positive bone_le_i256_max haNextExec
        have haNext0 : 0 ≤ aNextRaw := by
          have hexact0 :
              (0 : ℝ) ≤ (((aRaw * aRaw : ℤ) : ℝ) / (BONE : ℝ)) := by
            positivity
          have hreal : (0 : ℝ) ≤ (aNextRaw : ℝ) :=
            hexact0.trans haNextRefines.1.le
          exact_mod_cast hreal
        have haNextNorm0 :
            (0 : ℝ) ≤ (aNextRaw : ℝ) / BONE := by positivity
        have hsquare :
            ((aRaw : ℝ) / BONE) * ((aRaw : ℝ) / BONE) ≤
              (aNextRaw : ℝ) / BONE := by
          have hB : (0 : ℝ) < BONE := by norm_num [BONE]
          apply (le_div_iff₀ hB).2
          calc
            ((aRaw : ℝ) / BONE) * ((aRaw : ℝ) / BONE) * BONE =
                (((aRaw * aRaw : ℤ) : ℝ) / BONE) := by
              push_cast
              field_simp
              ring
            _ ≤ (aNextRaw : ℝ) := haNextRefines.1.le
        by_cases hodd : n % 2 ≠ 0
        · rw [if_pos hodd] at hafterSquare
          rcases Option.bind_eq_some.mp hafterSquare with
            ⟨zNextRaw, hzNextExec, htailExec⟩
          have hzNextRefines := i256_fixed_mul_ceil_success_refines
            bone_positive bone_le_i256_max hzNextExec
          have hzNext0 : 0 ≤ zNextRaw := by
            have hexact0 :
                (0 : ℝ) ≤
                  (((zRaw * aNextRaw : ℤ) : ℝ) / (BONE : ℝ)) := by
              positivity
            have hreal : (0 : ℝ) ≤ (zNextRaw : ℝ) :=
              hexact0.trans hzNextRefines.1.le
            exact_mod_cast hreal
          have hzNextNorm0 :
              (0 : ℝ) ≤ (zNextRaw : ℝ) / BONE := by positivity
          have hmultiply :
              ((zRaw : ℝ) / BONE) * ((aNextRaw : ℝ) / BONE) ≤
                (zNextRaw : ℝ) / BONE := by
            have hB : (0 : ℝ) < BONE := by norm_num [BONE]
            apply (le_div_iff₀ hB).2
            calc
              ((zRaw : ℝ) / BONE) * ((aNextRaw : ℝ) / BONE) * BONE =
                  (((zRaw * aNextRaw : ℤ) : ℝ) / BONE) := by
                push_cast
                field_simp
                ring
              _ ≤ (zNextRaw : ℝ) := hzNextRefines.1.le
          have htail := ih hzNext0 haNext0 htailExec
          have hmodlt : n % 2 < 2 := Nat.mod_lt _ (by omega)
          have hmod : n % 2 = 1 := by omega
          have hdecomp := Nat.mod_add_div n 2
          have hnrepr : n = 2 * (n / 2) + 1 := by omega
          rw [hnrepr]
          exact UpperCPowiLoop.odd
            haNextNorm0 hzNextNorm0 hsquare hmultiply htail
        · have hmod : n % 2 = 0 := not_ne_iff.mp hodd
          rw [if_neg hodd] at hafterSquare
          rcases Option.bind_eq_some.mp hafterSquare with
            ⟨zNextRaw, hzNextExec, htailExec⟩
          have hzNext : zNextRaw = zRaw := Option.some.inj hzNextExec.symm
          subst zNextRaw
          have htail := ih hz0 haNext0 htailExec
          have hdecomp := Nat.mod_add_div n 2
          have hnrepr : n = 2 * (n / 2) := by omega
          rw [hnrepr]
          exact UpperCPowiLoop.even haNextNorm0 hsquare htail

/-- Successful checked `c_powi` execution refines the reusable upper trace. -/
theorem upperPowiExecution_refines
    {baseRaw resultRaw : ℤ} {exponent : ℕ}
    (hbase0 : 0 ≤ baseRaw)
    (hexec : upperPowiExecution baseRaw exponent = some resultRaw) :
    UpperCPowiTrace ((baseRaw : ℝ) / BONE) exponent
      ((resultRaw : ℝ) / BONE) := by
  unfold upperPowiExecution at hexec
  by_cases hodd : exponent % 2 ≠ 0
  · simp only [if_pos hodd] at hexec
    have hloop := upperPowiLoopExecution_refines hbase0 hbase0 hexec
    have hmodlt : exponent % 2 < 2 := Nat.mod_lt _ (by omega)
    have hmod : exponent % 2 = 1 := by omega
    have hdecomp := Nat.mod_add_div exponent 2
    have hexponent : exponent = 2 * (exponent / 2) + 1 := by omega
    rw [hexponent]
    exact UpperCPowiTrace.odd hloop
  · have hmod : exponent % 2 = 0 := not_ne_iff.mp hodd
    simp only [if_neg hodd] at hexec
    have hbone0 : (0 : ℤ) ≤ BONE := by positivity
    have hloop := upperPowiLoopExecution_refines hbone0 hbase0 hexec
    have hdecomp := Nat.mod_add_div exponent 2
    have hexponent : exponent = 2 * (exponent / 2) := by omega
    have hboneNorm :
        (((BONE : ℤ) : ℝ) / (BONE : ℝ)) = 1 := by norm_num [BONE]
    rw [hboneNorm] at hloop
    rw [hexponent]
    exact UpperCPowiTrace.even hloop

/-- Source control-flow result of exact-input `c_pow`. -/
inductive ExactInputCPowExecutionResult where
  | integer
      (integerPart : ℕ) (wholeRaw : ℤ)
  | fractional
      (integerPart remainderStroop : ℕ)
      (wholeRaw : ℤ) (approx : ExactInputApproxExecutionResult)
      (powerRaw : ℤ)
deriving DecidableEq

def ExactInputCPowExecutionResult.powerRaw :
    ExactInputCPowExecutionResult → ℤ
  | .integer _ wholeRaw => wholeRaw
  | .fractional _ _ _ _ powerRaw => powerRaw

/-- Rust's nonnegative `i128 as u32` conversion, expressed on naturals. -/
def rustU32Cast (value : ℕ) : ℕ := value % (2 ^ 32)

/-- Scaling a STROOP exponent to BONE preserves its integer/remainder split. -/
theorem scaledExponentSourceSplit (exponentStroop : ℕ) :
    let exponentBone : ℤ :=
      (exponentStroop : ℤ) * ((BONE : ℤ) / STROOP)
    exponentBone / BONE = (exponentStroop / STROOP : ℕ) ∧
      exponentBone - (exponentBone / BONE) * BONE =
        ((exponentStroop % STROOP) * (BONE / STROOP) : ℕ) := by
  dsimp
  have hintegerNat :
      exponentStroop * (BONE / STROOP) / BONE =
        exponentStroop / STROOP := by
    simpa [BONE, STROOP] using
      Nat.mul_div_mul_right (m := BONE / STROOP) exponentStroop STROOP
        (by norm_num [BONE, STROOP])
  have hintegerInt :
      ((exponentStroop : ℤ) * ((BONE : ℤ) / STROOP)) / BONE =
        (exponentStroop / STROOP : ℕ) := by
    norm_num [BONE, STROOP] at hintegerNat ⊢
    exact_mod_cast hintegerNat
  refine ⟨hintegerInt, ?_⟩
  have hremainderNat :
      exponentStroop * (BONE / STROOP) % BONE =
        (exponentStroop % STROOP) * (BONE / STROOP) := by
    simpa [BONE, STROOP] using
      Nat.mul_mod_mul_right (BONE / STROOP) exponentStroop STROOP
  rw [hintegerInt]
  norm_num [BONE, STROOP] at hremainderNat ⊢
  omega

/-- The configured exponent range makes Rust's `u32` conversion lossless. -/
theorem rustU32Cast_eq_self_of_le_nine
    {value : ℕ} (hvalue : value ≤ 9) : rustU32Cast value = value := by
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt hvalue (by norm_num)

/--
Source-shaped execution of `c_pow(..., round_up = true)`. The BONE-scaled
argument is retained and checked against the caller's STROOP-scaled ratio;
`rustU32Cast` models the source `as u32` conversion.
-/
def exactInputCPowExecution
    (baseRaw exponentBone : ℤ) (exponentStroop : ℕ) :
    Option ExactInputCPowExecutionResult := do
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
      let approx ← exactInputApproxExecution baseRaw remainRaw
      let powerRaw ←
        SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
          wholeRaw approx.partialRaw BONE
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)

/-- Successful integer-only `c_pow` exposes its source branch and `c_powi`. -/
theorem exactInputCPowExecution_integer_components
    {baseRaw exponentBone : ℤ} {exponentStroop integerPart : ℕ} {wholeRaw : ℤ}
    (hintegerPart : exponentStroop / STROOP ≤ 9)
    (hexec : exactInputCPowExecution baseRaw exponentBone exponentStroop =
      some (.integer integerPart wholeRaw)) :
    integerPart = exponentStroop / STROOP ∧
      exponentStroop % STROOP = 0 ∧
      upperPowiExecution baseRaw integerPart = some wholeRaw := by
  rw [exactInputCPowExecution] at hexec
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

/-- Successful fractional `c_pow` exposes all checked source components. -/
theorem exactInputCPowExecution_fractional_components
    {baseRaw exponentBone : ℤ}
    {exponentStroop integerPart remainderStroop : ℕ}
    {wholeRaw powerRaw : ℤ} {approx : ExactInputApproxExecutionResult}
    (hintegerPart : exponentStroop / STROOP ≤ 9)
    (hexec : exactInputCPowExecution baseRaw exponentBone exponentStroop =
      some (.fractional integerPart remainderStroop wholeRaw approx powerRaw)) :
    integerPart = exponentStroop / STROOP ∧
      remainderStroop = exponentStroop % STROOP ∧
      remainderStroop ≠ 0 ∧
      upperPowiExecution baseRaw integerPart = some wholeRaw ∧
      exactInputApproxExecution baseRaw
        (remainderStroop * (BONE / STROOP)) = some approx ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        wholeRaw approx.partialRaw BONE = some powerRaw := by
  rw [exactInputCPowExecution] at hexec
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

/-- Successful arithmetic trace for `calc_token_out_given_token_in`. -/
structure SuccessfulExactInputMathRun
    (inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ) where
  tokenBalanceIn : ℤ
  tokenBalanceOut : ℤ
  tokenAmountIn : ℤ
  feeComplement : ℤ
  feeAdjustRatio : ℤ
  weightRatioStroop : ℤ
  weightRatioBone : ℤ
  adjustedIn : ℤ
  totalIn : ℤ
  baseRaw : ℤ
  cpow : ExactInputCPowExecutionResult
  balanceRatio : ℤ
  intermediate : ℤ
  downscaled : ℤ
  output : ℤ
  tokenBalanceInExec :
    SorobanFixedPointMath.I128.mul inBalance inScalar = some tokenBalanceIn
  tokenBalanceOutExec :
    SorobanFixedPointMath.I128.mul outBalance outScalar = some tokenBalanceOut
  tokenAmountInExec :
    SorobanFixedPointMath.I128.mul amountIn inScalar = some tokenAmountIn
  feeComplementExec :
    SorobanFixedPointMath.I128.sub STROOP fee = some feeComplement
  feeAdjustRatioExec :
    SorobanFixedPointMath.I128.mul feeComplement (BONE / STROOP) =
      some feeAdjustRatio
  weightRatioExec :
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      inWeight outWeight STROOP = some weightRatioStroop
  weightRatioBoneExec :
    SorobanFixedPointMath.I128.mul weightRatioStroop (BONE / STROOP) =
      some weightRatioBone
  adjustedInExec :
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      tokenAmountIn feeAdjustRatio BONE = some adjustedIn
  totalInExec :
    SorobanFixedPointMath.I256.add tokenBalanceIn adjustedIn = some totalIn
  baseExec :
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenBalanceIn totalIn.toNat BONE = some baseRaw
  cpowExec :
    exactInputCPowExecution baseRaw weightRatioBone weightRatioStroop.toNat =
      some cpow
  balanceRatioGuard : cpow.powerRaw ≤ BONE
  balanceRatioExec :
    SorobanFixedPointMath.I256.sub BONE cpow.powerRaw = some balanceRatio
  intermediateExec :
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      tokenBalanceOut balanceRatio BONE = some intermediate
  downscaleExec :
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      intermediate outScalar 1 = some downscaled
  outputExec :
    SorobanFixedPointMath.I128.checked downscaled = some output

/-- Executable model of `calc_token_out_given_token_in`. -/
def calcTokenOutGivenTokenInExecution
    (inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ) : Option ℤ := do
  let tokenBalanceIn ←
    SorobanFixedPointMath.I128.mul inBalance inScalar
  let tokenBalanceOut ←
    SorobanFixedPointMath.I128.mul outBalance outScalar
  let tokenAmountIn ←
    SorobanFixedPointMath.I128.mul amountIn inScalar
  let feeComplement ← SorobanFixedPointMath.I128.sub STROOP fee
  let feeAdjustRatio ←
    SorobanFixedPointMath.I128.mul feeComplement (BONE / STROOP)
  let weightRatioStroop ←
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      inWeight outWeight STROOP
  let weightRatioBone ←
    SorobanFixedPointMath.I128.mul weightRatioStroop (BONE / STROOP)
  let adjustedIn ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      tokenAmountIn feeAdjustRatio BONE
  let totalIn ← SorobanFixedPointMath.I256.add tokenBalanceIn adjustedIn
  let baseRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenBalanceIn totalIn.toNat BONE
  let cpow ←
    exactInputCPowExecution baseRaw weightRatioBone weightRatioStroop.toNat
  if cpow.powerRaw ≤ BONE then
    let balanceRatio ←
      SorobanFixedPointMath.I256.sub BONE cpow.powerRaw
    let intermediate ←
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        tokenBalanceOut balanceRatio BONE
    let downscaled ←
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        intermediate outScalar 1
    SorobanFixedPointMath.I128.checked downscaled
  else
    none

/-- A successful modeled return reconstructs every source arithmetic result. -/
theorem successfulExactInputMathRun_of_execution
    {inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ} {output : ℤ}
    (hexec :
      calcTokenOutGivenTokenInExecution inBalance inScalar
        outBalance outScalar amountIn inWeight outWeight fee = some output) :
    ∃ run : SuccessfulExactInputMathRun inBalance inScalar
        outBalance outScalar amountIn inWeight outWeight fee,
      run.output = output := by
  rw [calcTokenOutGivenTokenInExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceIn, htokenBalanceIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceOut, htokenBalanceOut, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenAmountIn, htokenAmountIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨feeComplement, hfeeComplement, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨feeAdjustRatio, hfeeAdjustRatio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨weightRatioStroop, hweightRatio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨weightRatioBone, hweightRatioBone, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨adjustedIn, hadjustedIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨totalIn, htotalIn, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨baseRaw, hbase, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨cpow, hcpow, hexec⟩
  have hpowerGuard : cpow.powerRaw ≤ BONE := by
    by_contra hguard
    rw [if_neg hguard] at hexec
    contradiction
  rw [if_pos hpowerGuard] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨balanceRatio, hbalanceRatio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨intermediate, hintermediate, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨downscaled, hdownscaled, houtput⟩
  exact ⟨{
    tokenBalanceIn := tokenBalanceIn
    tokenBalanceOut := tokenBalanceOut
    tokenAmountIn := tokenAmountIn
    feeComplement := feeComplement
    feeAdjustRatio := feeAdjustRatio
    weightRatioStroop := weightRatioStroop
    weightRatioBone := weightRatioBone
    adjustedIn := adjustedIn
    totalIn := totalIn
    baseRaw := baseRaw
    cpow := cpow
    balanceRatio := balanceRatio
    intermediate := intermediate
    downscaled := downscaled
    output := output
    tokenBalanceInExec := htokenBalanceIn
    tokenBalanceOutExec := htokenBalanceOut
    tokenAmountInExec := htokenAmountIn
    feeComplementExec := hfeeComplement
    feeAdjustRatioExec := hfeeAdjustRatio
    weightRatioExec := hweightRatio
    weightRatioBoneExec := hweightRatioBone
    adjustedInExec := hadjustedIn
    totalInExec := htotalIn
    baseExec := hbase
    cpowExec := hcpow
    balanceRatioGuard := hpowerGuard
    balanceRatioExec := hbalanceRatio
    intermediateExec := hintermediate
    downscaleExec := hdownscaled
    outputExec := houtput
  }, rfl⟩

/--
Floor/ceiling facts recovered from one successful source-shaped exact-input
math run. These are precisely the arithmetic premises used by the operation
theorems in `ExactInputSwap`.
-/
structure ExactInputRunRefinements
    {inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ}
    (run : SuccessfulExactInputMathRun inBalance inScalar
      outBalance outScalar amountIn inWeight outWeight fee) : Prop where
  tokenBalanceInEq :
    run.tokenBalanceIn = (inBalance : ℤ) * inScalar
  tokenBalanceOutEq :
    run.tokenBalanceOut = (outBalance : ℤ) * outScalar
  tokenAmountInEq :
    run.tokenAmountIn = (amountIn : ℤ) * inScalar
  inputBalancePositive : 0 < run.tokenBalanceIn
  inputAmountPositive : 0 < run.tokenAmountIn
  outputBalancePositive : 0 < run.tokenBalanceOut
  adjustedInputNonnegative : 0 ≤ run.adjustedIn
  weightRatioNonnegative : 0 ≤ run.weightRatioStroop
  adjustedFloor :
    IsFloor run.adjustedIn
      ((run.tokenAmountIn : ℝ) * (1 - (fee : ℝ) / STROOP))
  baseCeil :
    IsCeil run.baseRaw
      ((BONE : ℝ) *
        (1 / (1 + (run.adjustedIn : ℝ) / run.tokenBalanceIn)))
  exponentFloor :
    IsFloor run.weightRatioStroop
      ((STROOP : ℝ) * ((inWeight : ℝ) / outWeight))
  intermediateFloor :
    IsFloor run.intermediate
      ((run.tokenBalanceOut : ℝ) *
        (1 - (run.cpow.powerRaw : ℝ) / BONE))
  outputFloor :
    IsFloor run.output ((run.intermediate : ℝ) / outScalar)

/-- Successful checked outer arithmetic refines all real-valued operations. -/
theorem successfulExactInputMathRun_refines
    {inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountIn : 0 < amountIn)
    (houtWeight : 0 < outWeight) (houtWeightMax : outWeight ≤ STROOP)
    (hfeeUpper : fee ≤ MAX_FEE)
    (run : SuccessfulExactInputMathRun inBalance inScalar
      outBalance outScalar amountIn inWeight outWeight fee) :
    ExactInputRunRefinements run := by
  have htokenBalanceIn := i128_mul_success_eq run.tokenBalanceInExec
  have htokenBalanceOut := i128_mul_success_eq run.tokenBalanceOutExec
  have htokenAmountIn := i128_mul_success_eq run.tokenAmountInExec
  have hfeeComplement := i128_sub_success_eq run.feeComplementExec
  have hfeeAdjustRatio := i128_mul_success_eq run.feeAdjustRatioExec
  have hweightRatioBone := i128_mul_success_eq run.weightRatioBoneExec
  have htokenBalanceIn0 : 0 < run.tokenBalanceIn := by
    rw [htokenBalanceIn]
    positivity
  have htokenBalanceOut0 : 0 < run.tokenBalanceOut := by
    rw [htokenBalanceOut]
    positivity
  have htokenAmountIn0 : 0 < run.tokenAmountIn := by
    rw [htokenAmountIn]
    positivity
  have hfeeStroop : fee ≤ STROOP := by
    exact le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hadjustedFloorRaw := (i256_fixed_mul_floor_success_refines
    bone_positive bone_le_i256_max run.adjustedInExec).1
  have hadjustedFloor :
      IsFloor run.adjustedIn
        ((run.tokenAmountIn : ℝ) * (1 - (fee : ℝ) / STROOP)) := by
    rw [hfeeAdjustRatio, hfeeComplement] at hadjustedFloorRaw
    convert hadjustedFloorRaw using 1
    all_goals norm_num [BONE, STROOP]
    all_goals ring
  have hadjustedExact0 :
      0 ≤ (run.tokenAmountIn : ℝ) * (1 - (fee : ℝ) / STROOP) := by
    have hfeeReal : (fee : ℝ) ≤ STROOP := by exact_mod_cast hfeeStroop
    have hstroopReal : (0 : ℝ) < STROOP := by norm_num [STROOP]
    have hfactor : (0 : ℝ) ≤ 1 - (fee : ℝ) / STROOP := by
      apply sub_nonneg.mpr
      exact (div_le_one hstroopReal).2 hfeeReal
    exact mul_nonneg (by exact_mod_cast htokenAmountIn0.le) hfactor
  have hadjusted0 : 0 ≤ run.adjustedIn :=
    hadjustedFloor.nonnegative_of_nonnegative_exact hadjustedExact0
  have htotalEq := i256_add_success_eq run.totalInExec
  have htotal0 : 0 < run.totalIn := by omega
  have htotalRange :=
    SorobanFixedPointMath.I256.checked_eq_some_iff.mp
      (show SorobanFixedPointMath.I256.checked
        (run.tokenBalanceIn + run.adjustedIn) = some run.totalIn
        from run.totalInExec)
  have htotalNatMax :
      ((run.totalIn.toNat : ℕ) : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    have htotalMax :
        run.totalIn ≤ SorobanFixedPointMath.I256.maxValue := by
      rw [← htotalRange.2]
      exact htotalRange.1.2
    simpa [Int.toNat_of_nonneg htotal0.le] using htotalMax
  have hbaseCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp htotal0) htotalNatMax run.baseExec).1
  have htotalCast : ((run.totalIn.toNat : ℕ) : ℝ) = run.totalIn := by
    have htotalCastInt : ((run.totalIn.toNat : ℕ) : ℤ) = run.totalIn :=
      Int.toNat_of_nonneg htotal0.le
    exact_mod_cast htotalCastInt
  have hbaseCeil :
      IsCeil run.baseRaw
        ((BONE : ℝ) *
          (1 / (1 + (run.adjustedIn : ℝ) / run.tokenBalanceIn))) := by
    rw [htotalCast, htotalEq] at hbaseCeilRaw
    convert hbaseCeilRaw using 1
    push_cast
    have hbalanceReal : (0 : ℝ) < run.tokenBalanceIn := by
      exact_mod_cast htokenBalanceIn0
    field_simp
    ring
  have houtWeightMaxI128 :
      (outWeight : ℤ) ≤ SorobanFixedPointMath.I128.maxValue := by
    calc
      (outWeight : ℤ) ≤ STROOP := by exact_mod_cast houtWeightMax
      _ ≤ SorobanFixedPointMath.I128.maxValue := by
        norm_num [STROOP, SorobanFixedPointMath.I128.maxValue]
  have hexponentFloorRaw := (i128_fixed_div_floor_success_refines
    houtWeight houtWeightMaxI128 run.weightRatioExec).1
  have hexponentFloor :
      IsFloor run.weightRatioStroop
        ((STROOP : ℝ) * ((inWeight : ℝ) / outWeight)) := by
    convert hexponentFloorRaw using 1
    all_goals push_cast
    ring
  have hweightRatio0 : 0 ≤ run.weightRatioStroop := by
    apply hexponentFloor.nonnegative_of_nonnegative_exact
    positivity
  have hbalanceRatioEq := i256_sub_success_eq run.balanceRatioExec
  have hintermediateFloorRaw := (i256_fixed_mul_floor_success_refines
    bone_positive bone_le_i256_max run.intermediateExec).1
  have hintermediateFloor :
      IsFloor run.intermediate
        ((run.tokenBalanceOut : ℝ) *
          (1 - (run.cpow.powerRaw : ℝ) / BONE)) := by
    rw [hbalanceRatioEq] at hintermediateFloorRaw
    convert hintermediateFloorRaw using 1
    all_goals push_cast
    have hB : (BONE : ℝ) ≠ 0 := by norm_num [BONE]
    field_simp
  have houtProductRange :=
    SorobanFixedPointMath.I128.checked_eq_some_iff.mp
      (show SorobanFixedPointMath.I128.checked
        ((outBalance : ℤ) * outScalar) = some run.tokenBalanceOut
        from run.tokenBalanceOutExec)
  have houtScalarProduct :
      (outScalar : ℤ) ≤ (outBalance : ℤ) * outScalar := by
    have hbalanceOne : (1 : ℤ) ≤ outBalance := by exact_mod_cast houtBalance
    have hscalar0 : (0 : ℤ) ≤ outScalar := by positivity
    have hnonneg :
        0 ≤ ((outBalance : ℤ) - 1) * (outScalar : ℤ) := by
      exact mul_nonneg (sub_nonneg.mpr hbalanceOne) hscalar0
    nlinarith
  have houtScalarMax :
      (outScalar : ℤ) ≤ SorobanFixedPointMath.I256.maxValue := by
    exact houtScalarProduct.trans <|
      houtProductRange.1.2.trans <| by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hdownscaleFloorRaw := (i256_fixed_div_floor_success_refines
    houtScalar houtScalarMax run.downscaleExec).1
  have houtputEq : run.output = run.downscaled := by
    have hchecked := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
      run.outputExec
    exact hchecked.2.symm
  have houtputFloor :
      IsFloor run.output ((run.intermediate : ℝ) / outScalar) := by
    rw [houtputEq]
    convert hdownscaleFloorRaw using 1
    all_goals push_cast
    ring
  exact {
    tokenBalanceInEq := htokenBalanceIn
    tokenBalanceOutEq := htokenBalanceOut
    tokenAmountInEq := htokenAmountIn
    inputBalancePositive := htokenBalanceIn0
    inputAmountPositive := htokenAmountIn0
    outputBalancePositive := htokenBalanceOut0
    adjustedInputNonnegative := hadjusted0
    weightRatioNonnegative := hweightRatio0
    adjustedFloor := hadjustedFloor
    baseCeil := hbaseCeil
    exponentFloor := hexponentFloor
    intermediateFloor := hintermediateFloor
    outputFloor := houtputFloor
  }

/--
Every successful source-shaped exact-input math run has pool-adverse error
strictly below `17/800` of the minimum fee's spot-normalized value.
-/
theorem successfulExactInputMathRun_adverse_error_lt_precise_fee_share
    {inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountIn : 0 < amountIn)
    (hinWeightLower : MIN_WEIGHT ≤ inWeight)
    (hinWeightUpper : inWeight ≤ MAX_WEIGHT)
    (houtWeightLower : MIN_WEIGHT ≤ outWeight)
    (houtWeightUpper : outWeight ≤ MAX_WEIGHT)
    (hinputRatio : amountIn * STROOP ≤ inBalance * MAX_IN_RATIO)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (run : SuccessfulExactInputMathRun inBalance inScalar
      outBalance outScalar amountIn inWeight outWeight fee) :
    (run.output : ℝ) -
        exactInputIdealOutput
          ((run.tokenBalanceOut : ℝ) / outScalar)
          ((fee : ℝ) / STROOP)
          ((run.tokenAmountIn : ℝ) / run.tokenBalanceIn)
          ((inWeight : ℝ) / outWeight) <
      EXACT_INPUT_ADVERSE_FEE_SHARE * exactInputMinimumFeeOutputValue
          ((run.tokenBalanceOut : ℝ) / outScalar)
          ((inWeight : ℝ) / outWeight)
          ((run.tokenAmountIn : ℝ) / run.tokenBalanceIn) := by
  let inputBalance : ℝ := run.tokenBalanceIn
  let inputAmount : ℝ := run.tokenAmountIn
  let outputBalance : ℝ := run.tokenBalanceOut
  let scale : ℝ := outScalar
  let feeRate : ℝ := (fee : ℝ) / STROOP
  let nominalRatio : ℝ := inputAmount / inputBalance
  let adjustedRatio : ℝ := (run.adjustedIn : ℝ) / inputBalance
  let computedBase : ℝ := (run.baseRaw : ℝ) / BONE
  let idealExponent : ℝ := (inWeight : ℝ) / outWeight
  let computedExponent : ℝ := (run.weightRatioStroop : ℝ) / STROOP
  change (run.output : ℝ) -
      exactInputIdealOutput (outputBalance / scale) feeRate nominalRatio
        idealExponent <
    EXACT_INPUT_ADVERSE_FEE_SHARE *
      exactInputMinimumFeeOutputValue (outputBalance / scale) idealExponent
        nominalRatio
  have hinWeight : 0 < inWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hinWeightLower
  have houtWeight : 0 < outWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) houtWeightLower
  have houtWeightMax : outWeight ≤ STROOP :=
    le_trans houtWeightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have href := successfulExactInputMathRun_refines hinBalance hinScalar
    houtBalance houtScalar hamountIn houtWeight houtWeightMax hfeeUpper run
  have hinputBalance : 0 < inputBalance := by
    dsimp only [inputBalance]
    exact_mod_cast href.inputBalancePositive
  have hinputAmount : 0 < inputAmount := by
    dsimp only [inputAmount]
    exact_mod_cast href.inputAmountPositive
  have houtputBalance : 0 < outputBalance := by
    dsimp only [outputBalance]
    exact_mod_cast href.outputBalancePositive
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact_mod_cast houtScalar
  have hnominalOriginal :
      nominalRatio = (amountIn : ℝ) / inBalance := by
    dsimp [nominalRatio, inputAmount, inputBalance]
    rw [href.tokenAmountInEq, href.tokenBalanceInEq]
    push_cast
    have hscalarReal : (inScalar : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hnominalMax : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP := by
    rw [hnominalOriginal]
    have hratioReal :
        (amountIn : ℝ) * STROOP ≤
          (inBalance : ℝ) * MAX_IN_RATIO := by
      exact_mod_cast hinputRatio
    have hinBalanceReal : (0 : ℝ) < inBalance := by exact_mod_cast hinBalance
    have hstroopReal : (0 : ℝ) < STROOP := by norm_num [STROOP]
    exact (div_le_div_iff₀ hinBalanceReal hstroopReal).2 (by
      simpa [mul_comm] using hratioReal)
  have hfeeLowerReal : MIN_FEE_RATE ≤ feeRate := by
    dsimp [feeRate, MIN_FEE_RATE]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfeeLower)
      (by norm_num [STROOP] : (0 : ℝ) ≤ STROOP)
  have hfee0 : 0 ≤ feeRate := by positivity
  have hfeeUpperReal : feeRate ≤ 1 := by
    have hfeeStroop : fee ≤ STROOP :=
      le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
    dsimp [feeRate]
    exact (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
      (by exact_mod_cast hfeeStroop)
  have hidealExponentPositive : 0 < idealExponent := by
    dsimp [idealExponent]
    positivity
  have hadjustedRatio0 : 0 ≤ adjustedRatio := by
    dsimp only [adjustedRatio]
    exact div_nonneg (by exact_mod_cast href.adjustedInputNonnegative)
      hinputBalance.le
  have hbaseFacts := exact_input_base_ceil_refines
    hadjustedRatio0
    (show computedBase = (run.baseRaw : ℝ) / BONE from rfl)
    href.baseCeil
  have hbaseRaw0 : 0 ≤ run.baseRaw := by
    have hcomputedBase0 : 0 < computedBase :=
      lt_of_lt_of_le
        (one_div_pos.mpr (by linarith [hadjustedRatio0]))
        hbaseFacts.1
    have hreal : (0 : ℝ) < run.baseRaw := by
      dsimp [computedBase] at hcomputedBase0
      rcases (div_pos_iff.mp hcomputedBase0) with hpositive | hnegative
      · exact hpositive.1
      · norm_num [BONE] at hnegative
    exact_mod_cast hreal.le
  have htoNat :
      ((run.weightRatioStroop.toNat : ℕ) : ℤ) =
        run.weightRatioStroop :=
    Int.toNat_of_nonneg href.weightRatioNonnegative
  have htoNatReal :
      ((run.weightRatioStroop.toNat : ℕ) : ℝ) =
        (run.weightRatioStroop : ℝ) := by
    exact_mod_cast htoNat
  have hidealExponentUpper : idealExponent ≤ 9 := by
    dsimp [idealExponent]
    have hinWeightReal : (inWeight : ℝ) ≤ MAX_WEIGHT := by
      exact_mod_cast hinWeightUpper
    have houtWeightReal : (MIN_WEIGHT : ℝ) ≤ outWeight := by
      exact_mod_cast houtWeightLower
    apply (div_le_iff₀ (by exact_mod_cast houtWeight)).2
    calc
      (inWeight : ℝ) ≤ MAX_WEIGHT := hinWeightReal
      _ = 9 * MIN_WEIGHT := by norm_num [MAX_WEIGHT, MIN_WEIGHT]
      _ ≤ 9 * outWeight :=
        mul_le_mul_of_nonneg_left houtWeightReal (by norm_num)
  have hcomputedExponentUpper : computedExponent ≤ idealExponent := by
    exact (exact_input_exponent_floor_refines href.weightRatioNonnegative
      (show computedExponent = (run.weightRatioStroop : ℝ) / STROOP from rfl)
      href.exponentFloor).2
  have hrawQuotientLeNine :
      run.weightRatioStroop.toNat / STROOP ≤ 9 := by
    have hcomputedUpperNine : computedExponent ≤ 9 :=
      le_trans hcomputedExponentUpper hidealExponentUpper
    have hrawUpper : run.weightRatioStroop.toNat ≤ 9 * STROOP := by
      have hreal :
          (run.weightRatioStroop.toNat : ℝ) ≤ 9 * STROOP := by
        rw [htoNatReal]
        dsimp [computedExponent] at hcomputedUpperNine
        exact (div_le_iff₀ (by norm_num [STROOP])).1 hcomputedUpperNine
      exact_mod_cast hreal
    exact Nat.div_le_of_le_mul (by simpa [mul_comm] using hrawUpper)
  cases hcpowCase : run.cpow with
  | integer integerPart wholeRaw =>
      have hcpowExec :
          exactInputCPowExecution run.baseRaw run.weightRatioBone
              run.weightRatioStroop.toNat =
            some (.integer integerPart wholeRaw) := by
        simpa [hcpowCase] using run.cpowExec
      have hcomponents :=
        exactInputCPowExecution_integer_components hrawQuotientLeNine hcpowExec
      have hwholeTrace := upperPowiExecution_refines hbaseRaw0
        hcomponents.2.2
      have hdecomp := Nat.mod_add_div run.weightRatioStroop.toNat STROOP
      have hexponentInteger :
          (integerPart : ℝ) = computedExponent := by
        have hnat :
            run.weightRatioStroop.toNat = STROOP * integerPart := by
          rw [← hcomponents.1, hcomponents.2.1] at hdecomp
          omega
        dsimp [computedExponent]
        rw [← htoNatReal, hnat]
        norm_num [STROOP]
      have hresult :=
        baseline_swap_exact_amount_in_integer_adverse_error_lt_precise_fee_share
          (integerPart := integerPart)
          (inputBalance := inputBalance) (inputAmount := inputAmount)
          (feeRate := feeRate) (nominalRatio := nominalRatio)
          (adjustedRatio := adjustedRatio) (computedBase := computedBase)
          (idealExponent := idealExponent) (computedPower := (wholeRaw : ℝ))
          (outputBalance := outputBalance) (scale := scale)
          (adjustedInput := run.adjustedIn) (computedBaseRaw := run.baseRaw)
          (computedExponentRaw := run.weightRatioStroop)
          (intermediate := run.intermediate) (output := run.output)
          hinputBalance hinputAmount (by rfl) hfeeUpperReal
          href.adjustedInputNonnegative (by rfl) href.adjustedFloor
          (by rfl) href.baseCeil href.weightRatioNonnegative
          hexponentInteger href.exponentFloor hidealExponentPositive
          (by simpa [computedBase] using hwholeTrace)
          houtputBalance hscale
          (by simpa [hcpowCase] using href.intermediateFloor)
          href.outputFloor
      exact hresult
  | fractional integerPart remainderStroop wholeRaw approx powerRaw =>
      have hcpowExec :
          exactInputCPowExecution run.baseRaw run.weightRatioBone
              run.weightRatioStroop.toNat =
            some (.fractional integerPart remainderStroop wholeRaw approx powerRaw) := by
        simpa [hcpowCase] using run.cpowExec
      have hcomponents :=
        exactInputCPowExecution_fractional_components hrawQuotientLeNine hcpowExec
      let remainRaw : ℤ := remainderStroop * (BONE / STROOP)
      let a : ℝ := (remainderStroop : ℝ) / STROOP
      let wholeComputed : ℝ := (wholeRaw : ℝ) / BONE
      let computedPower : ℝ := powerRaw
      have happExec : exactInputApproxExecution run.baseRaw remainRaw = some approx := by
        simpa [remainRaw] using hcomponents.2.2.2.2.1
      have hwholeTrace :
          UpperCPowiTrace computedBase integerPart wholeComputed := by
        simpa [computedBase, wholeComputed] using
          upperPowiExecution_refines hbaseRaw0 hcomponents.2.2.2.1
      have hremainderLt : remainderStroop < STROOP := by
        rw [hcomponents.2.1]
        exact Nat.mod_lt _ (by norm_num [STROOP])
      have ha0 : 0 ≤ a := by positivity
      have ha1 : a ≤ 1 := by
        dsimp [a]
        have hreal : (remainderStroop : ℝ) ≤ STROOP := by
          exact_mod_cast hremainderLt.le
        exact (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2 hreal
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
      have happFacts := exactInputApproxExecution_success happExec
      obtain ⟨finalState, hxRaw, hsteps, hunadjusted, hn1, hn50,
        hcontinued, hcorrected, huncorrected⟩ := happFacts
      have hfirstFloorRaw :=
        exactInputApproxExecution_first_term_refines happExec
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
        bone_positive bone_le_i256_max hcomponents.2.2.2.2.2).1
      by_cases hunit : run.baseRaw = BONE
      · have hunitBase : computedBase = 1 := by
          dsimp [computedBase]
          rw [hunit]
          norm_num [BONE]
        have hpartialUnit : approx.partialRaw = BONE := by
          apply exactInputApproxExecution_unit
          simpa [hunit] using happExec
        have hwholeUpper := hwholeTrace.upper_bound (by positivity : 0 ≤ computedBase)
        have hcomposedUpper :
            wholeComputed * (approx.partialRaw : ℝ) ≤ computedPower := by
          dsimp [computedPower, wholeComputed]
          convert hcomposedCeilRaw.le using 1
          all_goals push_cast
          all_goals ring
        have hpowerUnit : (BONE : ℝ) ≤ computedPower := by
          rw [hpartialUnit] at hcomposedUpper
          rw [hunitBase] at hwholeUpper
          norm_num at hwholeUpper
          calc
            (BONE : ℝ) = 1 * BONE := by ring
            _ ≤ wholeComputed * BONE :=
              mul_le_mul_of_nonneg_right hwholeUpper (by norm_num [BONE])
            _ ≤ computedPower := hcomposedUpper
        have hconservative := baseline_exact_input_cpow_unit_base_has_no_adverse_error
          (computedExponent := computedExponent) hunitBase hpowerUnit
        have hfeePowerPositive := exact_input_minimum_fee_power_value_positive
          hidealExponentPositive (by positivity : 0 < nominalRatio)
        have hcpowBound :
            (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
              EXACT_INPUT_ADVERSE_FEE_SHARE *
                exactInputMinimumFeePowerValue idealExponent nominalRatio := by
          have hshare0 : 0 < EXACT_INPUT_ADVERSE_FEE_SHARE := by
            rw [exact_input_adverse_fee_share_value]
            norm_num
          have hshare :
              0 < EXACT_INPUT_ADVERSE_FEE_SHARE *
                exactInputMinimumFeePowerValue idealExponent nominalRatio :=
            mul_pos hshare0 hfeePowerPositive
          linarith
        have hresult := swap_exact_amount_in_from_fixed_point_refinements_fee_share
          (inputBalance := inputBalance) (inputAmount := inputAmount)
          (feeRate := feeRate) (nominalRatio := nominalRatio)
          (adjustedRatio := adjustedRatio) (computedBase := computedBase)
          (idealExponent := idealExponent) (computedExponent := computedExponent)
          (computedPower := computedPower) (outputBalance := outputBalance)
          (scale := scale) (adjustedInput := run.adjustedIn)
          (computedBaseRaw := run.baseRaw)
          (computedExponentRaw := run.weightRatioStroop)
          (intermediate := run.intermediate) (output := run.output)
          hinputBalance hinputAmount.le (by rfl) hfeeUpperReal
          href.adjustedInputNonnegative (by rfl) href.adjustedFloor
          (by rfl) href.baseCeil href.weightRatioNonnegative (by rfl)
          href.exponentFloor hcpowBound houtputBalance hscale
          (by simpa [hcpowCase, computedPower] using href.intermediateFloor)
          href.outputFloor
        exact hresult
      · have hbaseNonunit : computedBase < 1 := by
          have hnotOne : computedBase ≠ 1 := by
            intro hcomputed
            dsimp [computedBase] at hcomputed
            have hB : (BONE : ℝ) ≠ 0 := by norm_num [BONE]
            have hrawReal : (run.baseRaw : ℝ) = BONE := by
              field_simp at hcomputed
              linarith
            have hraw : run.baseRaw = BONE := by exact_mod_cast hrawReal
            exact hunit hraw
          exact lt_of_le_of_ne hbaseFacts.2 hnotOne
        by_cases hfirst : approx.iterations = 1
        · have hxNonzero : approx.xRaw ≠ 0 := by
            rw [hxRaw]
            intro hx
            apply hunit
            omega
          have hpartialFirst :
              approx.partialRaw =
                BONE +
                  (exactInputApproxStateAt approx.xRaw remainRaw 1).term + 1 := by
            rw [hcorrected ⟨hfirst, hxNonzero⟩, hunadjusted]
            have hsum := exactInputApproxSteps_sum hn50 hsteps
            rw [hfirst] at hsum
            rw [hsum]
            simp
          have hcomposedCeil :
              IsCeil powerRaw
                (wholeComputed *
                  ((BONE : ℝ) +
                    ((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ) + 1)) := by
            have hpartialFirstReal :
                (approx.partialRaw : ℝ) =
                  (BONE : ℝ) +
                    ((exactInputApproxStateAt approx.xRaw remainRaw 1).term : ℝ) + 1 := by
              exact_mod_cast hpartialFirst
            rw [← hpartialFirstReal]
            dsimp [wholeComputed]
            convert hcomposedCeilRaw using 1
            all_goals push_cast
            all_goals ring
          have hresult :=
            baseline_swap_exact_amount_in_first_term_adverse_error_lt_precise_fee_share
              (integerPart := integerPart)
              (inputBalance := inputBalance) (inputAmount := inputAmount)
              (feeRate := feeRate) (nominalRatio := nominalRatio)
              (adjustedRatio := adjustedRatio) (computedBase := computedBase)
              (idealExponent := idealExponent) (computedExponent := computedExponent)
              (wholeComputed := wholeComputed) (computedPower := computedPower)
              (outputBalance := outputBalance) (scale := scale) (a := a)
              (adjustedInput := run.adjustedIn) (computedBaseRaw := run.baseRaw)
              (computedExponentRaw := run.weightRatioStroop)
              (firstRounded :=
                (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
              (computedPowerRaw := powerRaw) (intermediate := run.intermediate)
              (output := run.output) hinputBalance hinputAmount (by rfl)
              hfeeUpperReal href.adjustedInputNonnegative (by rfl)
              href.adjustedFloor (by rfl) href.baseCeil
              href.weightRatioNonnegative (by rfl) href.exponentFloor
              hidealExponentPositive ha0 ha1 hcomputedExponentSplit hfirstFloor
              hwholeTrace (by rfl) hcomposedCeil houtputBalance hscale
              (by simpa [hcpowCase, computedPower] using href.intermediateFloor)
              href.outputFloor
          exact hresult
        · have hn2 : 2 ≤ approx.iterations := by omega
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
            obtain ⟨stepState, hstep⟩ :=
              exactInputApproxExecution_prefix happExec (k + 1) (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw (k + 1) = stepState := by
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
                (((computedTerm k : ℤ) : ℝ) *
                  (coefficientProduct (k + 1) : ℝ) / BONE) := by
            intro k hk hkn
            obtain ⟨stepState, hstep⟩ :=
              exactInputApproxExecution_prefix happExec (k + 1) (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw (k + 1) = stepState := by
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
            obtain ⟨stepState, hstep⟩ :=
              exactInputApproxExecution_prefix happExec (k + 1) (by omega) (by omega)
            have hstepAt :
                exactInputApproxStateAt approx.xRaw remainRaw (k + 1) = stepState := by
              simp [exactInputApproxStateAt, hstep]
            have hstepFacts := exactInputApproxSteps_refinements
              (iteration := k + 1) (by omega) (by omega) hstep
            dsimp [computedTerm, multiplied]
            rw [hstepAt]
            simpa [Nat.cast_add, Nat.cast_one] using hstepFacts.2.2.1
          have hpartialUncorrected : approx.partialRaw = approx.unadjustedSumRaw :=
            huncorrected (by intro h; exact hfirst h.1)
          have hsumState := exactInputApproxSteps_sum hn50 hsteps
          have hcomputedFractional :
              (approx.partialRaw : ℝ) = (BONE : ℝ) +
                ∑ k ∈ Finset.range approx.iterations,
                  (computedTerm (k + 1) : ℝ) := by
            rw [hpartialUncorrected, hunadjusted, hsumState]
            push_cast
            rfl
          have hcomposedCeil :
              IsCeil powerRaw (wholeComputed * (approx.partialRaw : ℝ)) := by
            dsimp [wholeComputed]
            convert hcomposedCeilRaw using 1
            all_goals push_cast
            all_goals ring
          have hresult :=
            baseline_swap_exact_amount_in_multiterm_adverse_error_lt_precise_fee_share
              coefficientProduct multiplied computedTerm
              (n := approx.iterations) (integerPart := integerPart)
              (inputBalance := inputBalance) (inputAmount := inputAmount)
              (feeRate := feeRate) (nominalRatio := nominalRatio)
              (adjustedRatio := adjustedRatio) (computedBase := computedBase)
              (idealExponent := idealExponent) (computedExponent := computedExponent)
              (computedFractional := (approx.partialRaw : ℝ))
              (wholeComputed := wholeComputed) (computedPower := computedPower)
              (outputBalance := outputBalance) (scale := scale)
              (adjustedInput := run.adjustedIn) (computedBaseRaw := run.baseRaw)
              (computedExponentRaw := run.weightRatioStroop)
              (computedPowerRaw := powerRaw) (intermediate := run.intermediate)
              (output := run.output) hinputBalance hinputAmount (by rfl)
              hnominalMax hfeeLowerReal hfee0 hfeeUpperReal
              href.adjustedInputNonnegative (by rfl) href.adjustedFloor
              (by rfl) href.baseCeil href.weightRatioNonnegative (by rfl)
              href.exponentFloor hidealExponentPositive ha0 ha1
              hcomputedExponentSplit hbaseNonunit hn2 hn50
              (by
                intro k hk hkn
                exact_mod_cast hcontinued k hk hkn)
              (by
                rw [(exactInputBinomialTerm_one ha0 hbaseFacts.2).1]
                simpa [computedTerm] using hfirstFloor)
              hcoefficientFloor hmultiplyFloor hdivideFloor hcomputedFractional
              hwholeTrace (by rfl) hcomposedCeil houtputBalance hscale
              (by simpa [hcpowCase, computedPower] using href.intermediateFloor)
              href.outputFloor
          exact hresult

/--
Direct theorem for a successful executable `calc_token_out_given_token_in`
model result under the public swap's positive-input, ratio, fee, and weight
configuration invariants, at the precise `17/800` fee share.
-/
theorem calc_token_out_given_token_in_execution_adverse_error_lt_precise_fee_share
    {inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ} {output : ℤ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountIn : 0 < amountIn)
    (hinWeightLower : MIN_WEIGHT ≤ inWeight)
    (hinWeightUpper : inWeight ≤ MAX_WEIGHT)
    (houtWeightLower : MIN_WEIGHT ≤ outWeight)
    (houtWeightUpper : outWeight ≤ MAX_WEIGHT)
    (hinputRatio : amountIn * STROOP ≤ inBalance * MAX_IN_RATIO)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenOutGivenTokenInExecution inBalance inScalar
      outBalance outScalar amountIn inWeight outWeight fee = some output) :
    (output : ℝ) -
        exactInputIdealOutput (outBalance : ℝ)
          ((fee : ℝ) / STROOP) ((amountIn : ℝ) / inBalance)
          ((inWeight : ℝ) / outWeight) <
      EXACT_INPUT_ADVERSE_FEE_SHARE * exactInputMinimumFeeOutputValue (outBalance : ℝ)
          ((inWeight : ℝ) / outWeight) ((amountIn : ℝ) / inBalance) := by
  obtain ⟨run, houtput⟩ := successfulExactInputMathRun_of_execution hexec
  have hrun :=
    successfulExactInputMathRun_adverse_error_lt_precise_fee_share
      hinBalance hinScalar houtBalance houtScalar hamountIn hinWeightLower
      hinWeightUpper houtWeightLower houtWeightUpper hinputRatio hfeeLower
      hfeeUpper run
  have houtWeight : 0 < outWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) houtWeightLower
  have houtWeightMax : outWeight ≤ STROOP :=
    le_trans houtWeightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have href := successfulExactInputMathRun_refines hinBalance hinScalar
    houtBalance houtScalar hamountIn houtWeight houtWeightMax hfeeUpper run
  have houtputBalanceEq :
      (run.tokenBalanceOut : ℝ) / outScalar = outBalance := by
    rw [href.tokenBalanceOutEq]
    push_cast
    have hscalar : (outScalar : ℝ) ≠ 0 := by positivity
    field_simp
  have hnominalEq :
      (run.tokenAmountIn : ℝ) / run.tokenBalanceIn =
        (amountIn : ℝ) / inBalance := by
    rw [href.tokenAmountInEq, href.tokenBalanceInEq]
    push_cast
    have hscalar : (inScalar : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [houtputBalanceEq, hnominalEq] at hrun
  have houtputReal : (run.output : ℝ) = output := by exact_mod_cast houtput
  simpa [houtputReal] using hrun

end CometPool
