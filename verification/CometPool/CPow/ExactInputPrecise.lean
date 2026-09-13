import CometPool.CPow.BaselineFeeBound
import CometPool.CPow.BaselineRecurrence

namespace CometPool

/-!
Tighter pool-adverse error bounds for the below-one fractional path used by
`swap_exact_amount_in`.

Unlike the absolute `3k - 2` recurrence budget, this file retains the signs of
the production floors.  The coefficient floor is favorable on this path, and
the multiply-floor followed by division-floor is one floor at the combined
divisor.  Those facts reduce the limiting two-term accumulated budget from
five raw units to `17/8` raw units.
-/

/-- The certified fraction of the minimum fee consumed by exact-input adverse error. -/
noncomputable def EXACT_INPUT_ADVERSE_FEE_SHARE : ℝ := 17 / 800

/-- The same share expressed as a rate applied to the first fractional term. -/
noncomputable def EXACT_INPUT_ADVERSE_FEE_RATE : ℝ :=
  EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE

theorem exact_input_adverse_fee_share_value :
    EXACT_INPUT_ADVERSE_FEE_SHARE = (17 : ℝ) / 800 := by
  rfl

theorem exact_input_adverse_fee_rate_value :
    EXACT_INPUT_ADVERSE_FEE_RATE = (17 : ℝ) / 800000000 := by
  norm_num [EXACT_INPUT_ADVERSE_FEE_RATE, EXACT_INPUT_ADVERSE_FEE_SHARE,
    MIN_FEE_RATE, MIN_FEE, STROOP]

/-- Signed per-term budgets for the below-one exact-input recurrence. -/
noncomputable def exactInputSignedTermErrorBudget (k : ℕ) : ℝ :=
  if k = 1 then 1 else if k = 2 then 9 / 8 else (3 * (k : ℝ) - 1) / 4

/-- Accumulated signed error budget through term `n`. -/
noncomputable def exactInputSignedAccumulatedError (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, exactInputSignedTermErrorBudget (k + 1)

/-- Flooring before division by a positive integer is the same as flooring after it. -/
theorem floor_floor_div_nat
    {value : ℝ} {inner outer : ℤ} {divisor : ℕ}
    (hdivisor : 0 < divisor)
    (hinner : IsFloor inner value)
    (houter : IsFloor outer ((inner : ℝ) / divisor)) :
    IsFloor outer (value / divisor) := by
  constructor
  · have hdivisorReal : (0 : ℝ) < divisor := by exact_mod_cast hdivisor
    exact le_trans houter.le
      (div_le_div_of_nonneg_right hinner.le hdivisorReal.le)
  · have hdivisorReal : (0 : ℝ) < divisor := by exact_mod_cast hdivisor
    have hinnerInteger : inner < (divisor : ℤ) * (outer + 1) := by
      have hreal : (inner : ℝ) < divisor * ((outer : ℝ) + 1) := by
        simpa [mul_comm] using (div_lt_iff₀ hdivisorReal).1 houter.lt_add_one
      exact_mod_cast hreal
    have hsuccessor : inner + 1 ≤ (divisor : ℤ) * (outer + 1) := by omega
    have hsuccessorReal :
        ((inner : ℝ) + 1) / divisor ≤ (outer : ℝ) + 1 := by
      apply (div_le_iff₀ hdivisorReal).2
      simpa [mul_comm] using (show
        (inner : ℝ) + 1 ≤ (divisor : ℝ) * ((outer : ℝ) + 1) by
          exact_mod_cast hsuccessor)
    have hvalue : value / divisor < ((inner : ℝ) + 1) / divisor :=
      (div_lt_div_iff_of_pos_right hdivisorReal).2 hinner.lt_add_one
    exact lt_of_lt_of_le hvalue hsuccessorReal

/--
One below-one recurrence step has less than one new unit of adverse error.
The coefficient-floor contribution is non-positive and the two subsequent
floors collapse to a single floor.
-/
theorem below_one_recurrence_step_signed_error
    {S exactPrevious computedPrevious coefficient displacement : ℝ}
    {coefficientProduct multiplied nextComputed : ℤ} {divisor : ℕ}
    (hS : 0 < S) (hdivisor : 0 < divisor)
    (hcomputedPrevious : computedPrevious ≤ 0)
    (hcoefficientFloor :
      IsFloor coefficientProduct (S * coefficient * displacement))
    (hmultiplyFloor :
      IsFloor multiplied
        (computedPrevious * (coefficientProduct : ℝ) / S))
    (hdivideFloor :
      IsFloor nextComputed ((multiplied : ℝ) / divisor)) :
    exactPrevious * coefficient * displacement / divisor - (nextComputed : ℝ) <
      (exactPrevious - computedPrevious) * coefficient * displacement / divisor + 1 := by
  have hcombined := floor_floor_div_nat hdivisor hmultiplyFloor hdivideFloor
  have hdivisorReal : (0 : ℝ) < divisor := by exact_mod_cast hdivisor
  let coefficientError : ℝ :=
    S * coefficient * displacement - (coefficientProduct : ℝ)
  have hcoefficientError0 : 0 ≤ coefficientError := by
    dsimp [coefficientError]
    exact sub_nonneg.mpr hcoefficientFloor.le
  have hcomputedContribution :
      computedPrevious * coefficientError / (S * divisor) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hcomputedPrevious hcoefficientError0)
      (mul_nonneg hS.le hdivisorReal.le)
  have hrounding :
      computedPrevious * (coefficientProduct : ℝ) / (S * divisor) -
          (nextComputed : ℝ) < 1 := by
    have hcombinedRounding :
        computedPrevious * (coefficientProduct : ℝ) / S / divisor -
            (nextComputed : ℝ) < 1 := by
      linarith [hcombined.lt_add_one]
    convert hcombinedRounding using 1
    field_simp [ne_of_gt hS, ne_of_gt hdivisorReal]
  have hdecompose :
      exactPrevious * coefficient * displacement / divisor - (nextComputed : ℝ) =
        (exactPrevious - computedPrevious) * coefficient * displacement / divisor +
          computedPrevious * coefficientError / (S * divisor) +
          (computedPrevious * (coefficientProduct : ℝ) / (S * divisor) -
            (nextComputed : ℝ)) := by
    dsimp [coefficientError]
    field_simp [ne_of_gt hS, ne_of_gt hdivisorReal]
    ring
  rw [hdecompose]
  linarith

/-- The below-one fractional recurrence multiplier is non-negative and at most `1/4`. -/
theorem below_one_recurrence_factor_bounds
    {a displacement : ℝ} {k : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hdisplacement : displacement ≤ 0)
    (hdisplacementQuarter : |displacement| ≤ 1 / 4)
    (hk : 1 ≤ k) :
    0 ≤ (a - (k : ℝ)) * displacement / ((k : ℝ) + 1) ∧
      (a - (k : ℝ)) * displacement / ((k : ℝ) + 1) ≤ 1 / 4 := by
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoefficient : a - (k : ℝ) ≤ 0 := by linarith
  have hproduct0 : 0 ≤ (a - (k : ℝ)) * displacement :=
    mul_nonneg_of_nonpos_of_nonpos hcoefficient hdisplacement
  have hcoefficientMagnitude : |a - (k : ℝ)| ≤ k := by
    rw [abs_of_nonpos hcoefficient]
    linarith
  have hproductMagnitude :
      |(a - (k : ℝ)) * displacement| ≤ (k : ℝ) * (1 / 4) := by
    rw [abs_mul]
    exact mul_le_mul hcoefficientMagnitude hdisplacementQuarter
      (abs_nonneg _) (by positivity)
  have hproduct :
      (a - (k : ℝ)) * displacement ≤ (k : ℝ) * (1 / 4) := by
    rw [← abs_of_nonneg hproduct0]
    exact hproductMagnitude
  have hdenominator : 0 < (k : ℝ) + 1 := by positivity
  constructor
  · exact div_nonneg hproduct0 hdenominator.le
  · apply (div_le_iff₀ hdenominator).2
    calc
      (a - (k : ℝ)) * displacement ≤ (k : ℝ) * (1 / 4) := hproduct
      _ ≤ ((k : ℝ) + 1) * (1 / 4) := by nlinarith
      _ = (1 / 4) * ((k : ℝ) + 1) := by ring

/-- At the second term, the recurrence multiplier has the sharper `1/8` ceiling. -/
theorem below_one_second_term_factor_le_one_eighth
    {a displacement : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hdisplacement : displacement ≤ 0)
    (hdisplacementQuarter : |displacement| ≤ 1 / 4) :
    (a - 1) * displacement / 2 ≤ 1 / 8 := by
  have hbounds := below_one_recurrence_factor_bounds
    ha0 ha1 hdisplacement hdisplacementQuarter (k := 1) (by omega)
  have hcoefficient : a - 1 ≤ 0 := by linarith
  have hproduct0 : 0 ≤ (a - 1) * displacement :=
    mul_nonneg_of_nonpos_of_nonpos hcoefficient hdisplacement
  have hcoefficientMagnitude : |a - 1| ≤ 1 := by
    rw [abs_of_nonpos hcoefficient]
    linarith
  have hproductMagnitude : |(a - 1) * displacement| ≤ 1 / 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hcoefficientMagnitude hdisplacementQuarter
      (abs_nonneg displacement) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [abs_of_nonneg hproduct0] at hproductMagnitude
  nlinarith

/-- Every computed term on the below-one fractional path is non-positive. -/
theorem below_one_computed_terms_nonpositive
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n : ℕ} {S a displacement : ℝ}
    (hS : 0 < S) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hdisplacement : displacement ≤ 0)
    (hfirstFloor : IsFloor (computedTerm 1) (S * a * displacement))
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (coefficientProduct (k + 1))
        (S * (a - (k : ℝ)) * displacement))
    (hmultiplyFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) / S))
    (hdivideFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1))) :
    ∀ k, 1 ≤ k → k ≤ n → (computedTerm k : ℝ) ≤ 0 := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      intro hk1 hkn
      by_cases hk0 : k = 0
      · subst k
        have hexact0 : S * a * displacement ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hS.le ha0) hdisplacement
        exact le_trans hfirstFloor.le hexact0
      · have hkPrevious : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hklt : k < n := Nat.lt_of_succ_le hkn
        have hprevious : (computedTerm k : ℝ) ≤ 0 :=
          ih hkPrevious (le_trans (Nat.le_succ k) hkn)
        have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hkPrevious
        have hcoefficient : a - (k : ℝ) ≤ 0 := by linarith
        have hexactCoefficient0 :
            0 ≤ S * (a - (k : ℝ)) * displacement := by
          calc
            0 ≤ S * ((a - (k : ℝ)) * displacement) :=
              mul_nonneg hS.le
                (mul_nonneg_of_nonpos_of_nonpos hcoefficient hdisplacement)
            _ = S * (a - (k : ℝ)) * displacement := by ring
        have hcoefficientAt := hcoefficientFloor k hkPrevious hklt
        have hcoefficientGt :
            (-1 : ℝ) < coefficientProduct (k + 1) := by
          linarith [hcoefficientAt.lt_add_one]
        have hcoefficientGtInt :
            (-1 : ℤ) < coefficientProduct (k + 1) := by
          exact_mod_cast hcoefficientGt
        have hcoefficient0Int : 0 ≤ coefficientProduct (k + 1) := by omega
        have hcoefficient0 :
            (0 : ℝ) ≤ coefficientProduct (k + 1) := by
          exact_mod_cast hcoefficient0Int
        have hproduct0 :
            (computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) / S ≤ 0 := by
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg hprevious hcoefficient0) hS.le
        have hmultiplied0 : (multiplied (k + 1) : ℝ) ≤ 0 :=
          le_trans (hmultiplyFloor k hkPrevious hklt).le hproduct0
        have hdivisor0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
        exact le_trans (hdivideFloor k hkPrevious hklt).le
          (div_nonpos_of_nonpos_of_nonneg hmultiplied0 hdivisor0)

/-- Signed term errors satisfy the tighter below-one per-term budgets. -/
theorem exact_input_signed_term_error_lt_budget
    (T : ℕ → ℝ)
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n : ℕ} {a displacement : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hdisplacement : displacement ≤ 0)
    (hdisplacementQuarter : |displacement| ≤ 1 / 4)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * displacement / ((k : ℝ) + 1))
    (hfirstFloor : IsFloor (computedTerm 1) (T 1))
    (hfirstExact : T 1 = (BONE : ℝ) * a * displacement)
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (a - (k : ℝ)) * displacement))
    (hmultiplyFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (habsolute : ∀ k, 1 ≤ k → k ≤ n →
      |T k - (computedTerm k : ℝ)| < 3 * (k : ℝ) - 2) :
    ∀ k, 1 ≤ k → k ≤ n →
      T k - (computedTerm k : ℝ) < exactInputSignedTermErrorBudget k := by
  have hcomputedNonpos := below_one_computed_terms_nonpositive
    coefficientProduct multiplied computedTerm (n := n) (S := (BONE : ℝ))
    (by norm_num [BONE]) ha0 ha1 hdisplacement (by simpa [hfirstExact] using hfirstFloor)
    hcoefficientFloor hmultiplyFloor hdivideFloor
  intro k hk1 hkn
  by_cases hkFirst : k = 1
  · subst k
    rw [exactInputSignedTermErrorBudget, if_pos rfl]
    have hfirstAbsolute := habsolute 1 (by omega) hkn
    norm_num at hfirstAbsolute
    exact lt_of_le_of_lt (le_abs_self _) hfirstAbsolute
  · have hk2 : 2 ≤ k := by omega
    let previous := k - 1
    have hprevious1 : 1 ≤ previous := by dsimp [previous]; omega
    have hpreviousLt : previous < n := by dsimp [previous]; omega
    have hkEq : previous + 1 = k := by dsimp [previous]; omega
    have hstep := below_one_recurrence_step_signed_error
      (S := (BONE : ℝ)) (divisor := k) (exactPrevious := T previous)
      (computedPrevious := (computedTerm previous : ℝ))
      (coefficient := a - (previous : ℝ)) (displacement := displacement)
      (coefficientProduct := coefficientProduct k) (multiplied := multiplied k)
      (nextComputed := computedTerm k) (by norm_num [BONE]) (by omega)
      (hcomputedNonpos previous hprevious1 (by omega))
      (by simpa [hkEq] using hcoefficientFloor previous hprevious1 hpreviousLt)
      (by simpa [hkEq] using hmultiplyFloor previous hprevious1 hpreviousLt)
      (by
        have hkReal : (k : ℝ) = (previous : ℝ) + 1 := by
          exact_mod_cast hkEq.symm
        rw [hkReal]
        simpa [hkEq] using hdivideFloor previous hprevious1 hpreviousLt)
    have hstep' :
        T k - (computedTerm k : ℝ) <
          (T previous - (computedTerm previous : ℝ)) *
              ((a - (previous : ℝ)) * displacement / (k : ℝ)) + 1 := by
      have hTk := hrec previous
      rw [hkEq] at hTk
      have hkReal : (k : ℝ) = (previous : ℝ) + 1 := by
        exact_mod_cast hkEq.symm
      rw [← hkReal] at hTk
      rw [hTk]
      simpa [mul_assoc, div_eq_mul_inv] using hstep
    have hfactor := below_one_recurrence_factor_bounds
      ha0 ha1 hdisplacement hdisplacementQuarter hprevious1
    have hfactorEq :
        (a - (previous : ℝ)) * displacement / ((previous : ℝ) + 1) =
          (a - (previous : ℝ)) * displacement / (k : ℝ) := by
      have hkReal : (k : ℝ) = (previous : ℝ) + 1 := by
        exact_mod_cast hkEq.symm
      rw [hkReal]
    rw [hfactorEq] at hfactor
    have habsolutePrevious := habsolute previous hprevious1 (by omega)
    have hscaledQuarter :
        (T previous - (computedTerm previous : ℝ)) *
            ((a - (previous : ℝ)) * displacement / (k : ℝ)) <
          (3 * (previous : ℝ) - 2) / 4 := by
      calc
        (T previous - (computedTerm previous : ℝ)) *
              ((a - (previous : ℝ)) * displacement / (k : ℝ)) ≤
            |T previous - (computedTerm previous : ℝ)| *
              ((a - (previous : ℝ)) * displacement / (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hfactor.1
        _ ≤ |T previous - (computedTerm previous : ℝ)| * (1 / 4) :=
          mul_le_mul_of_nonneg_left hfactor.2 (abs_nonneg _)
        _ < (3 * (previous : ℝ) - 2) * (1 / 4) :=
          mul_lt_mul_of_pos_right habsolutePrevious (by norm_num)
        _ = (3 * (previous : ℝ) - 2) / 4 := by ring
    by_cases hkSecond : k = 2
    · have hstepSecond := hstep'
      rw [hkSecond] at hstepSecond
      have hpreviousEq : previous = 1 := by
        dsimp [previous]
        omega
      have hfactorEighth :
          (a - (previous : ℝ)) * displacement / (2 : ℝ) ≤ 1 / 8 := by
        rw [hpreviousEq]
        norm_num
        exact below_one_second_term_factor_le_one_eighth
          ha0 ha1 hdisplacement hdisplacementQuarter
      have habsoluteOne := habsolute 1 (by omega) (by omega)
      have hscaledEighth :
          (T previous - (computedTerm previous : ℝ)) *
              ((a - (previous : ℝ)) * displacement / (2 : ℝ)) < 1 / 8 := by
        calc
          _ ≤ |T previous - (computedTerm previous : ℝ)| *
                ((a - (previous : ℝ)) * displacement / (2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by
              rw [hpreviousEq]
              have hf := (below_one_recurrence_factor_bounds ha0 ha1 hdisplacement
                hdisplacementQuarter (k := 1) (by omega)).1
              norm_num at hf ⊢
              exact hf)
          _ ≤ |T previous - (computedTerm previous : ℝ)| * (1 / 8) :=
            mul_le_mul_of_nonneg_left hfactorEighth (abs_nonneg _)
          _ < 1 * (1 / 8) := by
            apply mul_lt_mul_of_pos_right
            · norm_num at habsoluteOne
              simpa [hpreviousEq] using habsoluteOne
            · norm_num
          _ = 1 / 8 := by ring
      have hbound : T 2 - (computedTerm 2 : ℝ) < 9 / 8 := by
        linarith [hstepSecond, hscaledEighth]
      simpa [hkSecond, exactInputSignedTermErrorBudget] using hbound
    · have hbound :
          T k - (computedTerm k : ℝ) < (3 * (k : ℝ) - 1) / 4 := by
        have hkReal : (k : ℝ) = previous + 1 := by
          exact_mod_cast hkEq.symm
        rw [hkReal]
        linarith [hstep', hscaledQuarter]
      simpa [exactInputSignedTermErrorBudget, hkFirst, hkSecond] using hbound
/-- The signed term budgets sum to the accumulated exact-input budget. -/
theorem exact_input_partial_sum_signed_error_lt
    (exactTerm computedTerm : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n)
    (hterm : ∀ k, 1 ≤ k → k ≤ n →
      exactTerm k - computedTerm k < exactInputSignedTermErrorBudget k) :
    (∑ k ∈ Finset.range n, exactTerm (k + 1)) -
        (∑ k ∈ Finset.range n, computedTerm (k + 1)) <
      exactInputSignedAccumulatedError n := by
  have hrange : (Finset.range n).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  calc
    (∑ k ∈ Finset.range n, exactTerm (k + 1)) -
          (∑ k ∈ Finset.range n, computedTerm (k + 1)) =
        ∑ k ∈ Finset.range n,
          (exactTerm (k + 1) - computedTerm (k + 1)) := by
      rw [Finset.sum_sub_distrib]
    _ < ∑ k ∈ Finset.range n, exactInputSignedTermErrorBudget (k + 1) :=
      Finset.sum_lt_sum_of_nonempty hrange (by
        intro k hk
        exact hterm (k + 1) (by omega)
          (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)))
    _ = exactInputSignedAccumulatedError n := rfl

/-- The signed accumulated budget has a simple closed form from term two onward. -/
theorem exact_input_signed_accumulated_error_value
    {n : ℕ} (hn2 : 2 ≤ n) :
    exactInputSignedAccumulatedError n = (3 * (n : ℝ) ^ 2 + n + 3) / 8 := by
  induction n, hn2 using Nat.le_induction with
  | base =>
      norm_num [exactInputSignedAccumulatedError, exactInputSignedTermErrorBudget,
        Finset.sum_range_succ]
  | succ n hn2 ih =>
      rw [exactInputSignedAccumulatedError, Finset.sum_range_succ]
      rw [← exactInputSignedAccumulatedError, ih]
      simp only [exactInputSignedTermErrorBudget]
      have hn1 : n + 1 ≠ 1 := by omega
      have hn2' : n + 1 ≠ 2 := by omega
      rw [if_neg hn1, if_neg hn2']
      push_cast
      ring

/--
Across every possible production stopping index, the signed exact-input
budget consumes less than `17/800` of the minimum-fee scale of the first term.
-/
theorem exact_input_signed_accumulated_error_lt_fee_rate
    {n : ℕ} {firstTerm : ℝ}
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hfirstIfSecond : n = 2 → (CPOW_PRECISION : ℝ) < firstTerm)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * (1 / 4 : ℝ) ^ (n - 2) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    exactInputSignedAccumulatedError n <
      EXACT_INPUT_ADVERSE_FEE_RATE * firstTerm := by
  rw [exact_input_signed_accumulated_error_value hn2,
    exact_input_adverse_fee_rate_value]
  interval_cases n <;>
    norm_num [CPOW_PRECISION] at hfirstIfSecond hcontinue ⊢ <;>
    linarith

/-- The minimum fee value dominates the corresponding first-term rate. -/
theorem exact_input_adverse_fee_value_dominates_first_term
    {S a fullExponent q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (ha0 : 0 ≤ a)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ nominalRatio)
    (hfirst : firstTerm = S * a * q)
    (hfee : feeValue = MIN_FEE_RATE * (S * fullExponent * nominalRatio)) :
    EXACT_INPUT_ADVERSE_FEE_RATE * firstTerm ≤
      EXACT_INPUT_ADVERSE_FEE_SHARE * feeValue := by
  have hSa0 : 0 ≤ S * a := mul_nonneg hS0 ha0
  have hdisplacement : S * a * q ≤ S * a * nominalRatio :=
    mul_le_mul_of_nonneg_left hqNominal hSa0
  have hscale0 : 0 ≤ S * nominalRatio := mul_nonneg hS0 hnominal0
  have hexponent : S * a * nominalRatio ≤ S * fullExponent * nominalRatio := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left haFull hscale0
  have hterm := le_trans hdisplacement hexponent
  have hshare0 : 0 ≤ EXACT_INPUT_ADVERSE_FEE_SHARE := by
    rw [exact_input_adverse_fee_share_value]
    norm_num
  have hrate0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  calc
    EXACT_INPUT_ADVERSE_FEE_RATE * firstTerm =
        (EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) * (S * a * q) := by
      rw [EXACT_INPUT_ADVERSE_FEE_RATE, hfirst]
    _ ≤ (EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (S * fullExponent * nominalRatio) :=
      mul_le_mul_of_nonneg_left hterm (mul_nonneg hshare0 hrate0)
    _ = EXACT_INPUT_ADVERSE_FEE_SHARE * feeValue := by rw [hfee]; ring

/--
The complete signed fractional comparison for a multi-term exact-input run.
-/
theorem baseline_exact_input_multiterm_adverse_error_lt_precise_fee_share
    (T : ℕ → ℝ)
    {n : ℕ} {a fullExponent x previous q nominalRatio : ℝ}
    {firstRounded : ℤ}
    {exactPower exactPartial computedPartial feeValue : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ 1 / 4)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirstPrevious : n = 2 → previous = (firstRounded : ℝ))
    (hfirstFloor : IsFloor firstRounded (T 1))
    (hfirstNonpos : T 1 ≤ 0)
    (hfirst : |T 1| = (BONE : ℝ) * a * q)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ nominalRatio)
    (hfeeValue :
      feeValue = MIN_FEE_RATE * ((BONE : ℝ) * fullExponent * nominalRatio))
    (hpower : exactPower ≤ exactPartial)
    (hsum :
      exactPartial - computedPartial < exactInputSignedAccumulatedError n) :
    exactPower - computedPartial < EXACT_INPUT_ADVERSE_FEE_SHARE * feeValue := by
  have hcontinue := continued_exact_input_loop_forces_first_term_scale
    T ha0 ha1 hx hrec hn2 hprevious htermError
  have hfirstIfSecond : n = 2 → (CPOW_PRECISION : ℝ) < |T 1| := by
    intro hn
    have hprevFirst := hfirstPrevious hn
    rw [hprevFirst] at hprevious
    exact negative_floor_above_integer_threshold
      hfirstFloor hfirstNonpos (by simpa [CPOW_PRECISION] using hprevious)
  have hbudget := exact_input_signed_accumulated_error_lt_fee_rate
    hn2 hn46 hfirstIfSecond hcontinue
  have hadverse : exactPower - computedPartial <
      exactInputSignedAccumulatedError n := by linarith
  have hfee := exact_input_adverse_fee_value_dominates_first_term
    (S := (BONE : ℝ)) (a := a) (fullExponent := fullExponent)
    (q := q) (nominalRatio := nominalRatio)
    (firstTerm := |T 1|) (feeValue := feeValue)
    (by norm_num [BONE]) ha0 haFull hnominal0 hqNominal hfirst hfeeValue
  linarith

end CometPool
