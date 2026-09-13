import CometPool.Config.GeneratedConstants

namespace CometPool

/-- The configured maximum input ratio keeps direct input bases at or below `1.6`. -/
theorem configured_input_ratio_margin : 5 * MAX_IN_RATIO ≤ 3 * STROOP := by
  norm_num [MAX_IN_RATIO, STROOP]

/-- The configured maximum output ratio keeps reciprocal output bases below `1.6`. -/
theorem configured_output_ratio_margin : 8 * MAX_OUT_RATIO < 3 * STROOP := by
  norm_num [MAX_OUT_RATIO, STROOP]

/-- The worst configured fee adjustment leaves withdrawals above base `0.5`. -/
theorem configured_withdrawal_fee_margin :
    2 * MAX_OUT_RATIO * STROOP <
      STROOP ^ 2 - (STROOP - MIN_WEIGHT) * MAX_FEE := by
  norm_num [MAX_OUT_RATIO, STROOP, MIN_WEIGHT, MAX_FEE]

/-- Configured normalized weights do not exceed one, so reciprocal exponents are at least one. -/
theorem configured_weight_margin : MAX_WEIGHT ≤ STROOP := by
  norm_num [MAX_WEIGHT, STROOP]

/-- The exact-input swap anchor remains above the lower operating-base bound. -/
theorem configured_exact_input_base_lower :
    (1 / 2 : ℝ) < 1 / (1 + (MAX_IN_RATIO : ℝ) / STROOP) := by
  norm_num [MAX_IN_RATIO, STROOP]

/-- The exact-output swap anchor remains below the upper operating-base bound. -/
theorem configured_exact_output_base_upper :
    1 / (1 - (MAX_OUT_RATIO : ℝ) / STROOP) < 8 / 5 := by
  norm_num [MAX_OUT_RATIO, STROOP]

/--
The mathematical exact-output base plus a complete raw ceiling unit remains
below `1.51`, so its computed displacement is below `0.51`.
-/
theorem configured_exact_output_rounded_base_upper :
    1 / (1 - (MAX_OUT_RATIO : ℝ) / STROOP) + 1 / BONE < 151 / 100 := by
  norm_num [MAX_OUT_RATIO, STROOP, BONE]

/-- The exact configured output limit sharpens that displacement below `0.500001`. -/
theorem configured_exact_output_computed_displacement_lt_precise
    {nominalRatio computedBase : ℝ}
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hbaseLower : 1 ≤ computedBase)
    (hceil :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ)) :
    |computedBase - 1| < 500001 / 1000000 := by
  have hmaxDenom : 0 < 1 - (MAX_OUT_RATIO : ℝ) / STROOP := by
    norm_num [MAX_OUT_RATIO, STROOP]
  have hdenomOrder :
      1 - (MAX_OUT_RATIO : ℝ) / STROOP ≤ 1 - nominalRatio := by
    linarith
  have hinverseOrder := one_div_le_one_div_of_le hmaxDenom hdenomOrder
  have hconfigured :
      1 / (1 - (MAX_OUT_RATIO : ℝ) / STROOP) + 1 / (BONE : ℝ) <
        1500001 / 1000000 := by
    norm_num [MAX_OUT_RATIO, STROOP, BONE]
  rw [abs_of_nonneg (sub_nonneg.mpr hbaseLower)]
  linarith

/-
The operation-level exact-output proof needs enough margin to absorb the
weight-ratio ceiling as well as the base ceiling.  Retaining the full
`CPOW_PRECISION / BONE` scale gives the sharp lower ratio used by the
entrypoint-specific bound.
-/

/-- Continuing past the first term forces a production exact-output ratio above `5e-11`. -/
theorem continued_exact_output_forces_nominal_ratio_lower_sharp
    {nominalRatio computedBase fractional firstTerm : ℝ}
    (hratio0 : 0 ≤ nominalRatio)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hbaseLower : 1 ≤ computedBase)
    (hceil :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ))
    (hfractional1 : fractional ≤ 1)
    (hfirst : firstTerm = (BONE : ℝ) * fractional * (computedBase - 1))
    (hfirstLarge : (CPOW_PRECISION : ℝ) < firstTerm) :
    1 / 20000000000 ≤ nominalRatio := by
  have hmaxBelow : (MAX_OUT_RATIO : ℝ) / STROOP < 17 / 50 := by
    norm_num [MAX_OUT_RATIO, STROOP]
  have hratioBelow : nominalRatio < 17 / 50 := lt_of_le_of_lt hratioUpper hmaxBelow
  have hdenom : 0 < 1 - nominalRatio := by linarith
  have hinverse : 1 / (1 - nominalRatio) < 50 / 33 := by
    apply (div_lt_iff₀ hdenom).2
    nlinarith
  have hq0 : 0 ≤ computedBase - 1 := sub_nonneg.mpr hbaseLower
  have hafrac : fractional * (computedBase - 1) ≤ computedBase - 1 := by
    simpa using mul_le_of_le_one_left hq0 hfractional1
  have hB0 : (0 : ℝ) ≤ BONE := by norm_num [BONE]
  have hfirstUpper : firstTerm ≤ (BONE : ℝ) * (computedBase - 1) := by
    rw [hfirst, mul_assoc]
    exact mul_le_mul_of_nonneg_left hafrac hB0
  have hdisplacement :
      computedBase - 1 < (50 / 33 : ℝ) * nominalRatio + 1 / BONE := by
    have hid : 1 / (1 - nominalRatio) - 1 =
        nominalRatio / (1 - nominalRatio) := by
      field_simp
    have hratioInverse :
        nominalRatio / (1 - nominalRatio) ≤ (50 / 33 : ℝ) * nominalRatio := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hinverse) hratio0
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  norm_num [CPOW_PRECISION, BONE] at hfirstLarge hfirstUpper hdisplacement ⊢
  linarith

/-- Under continuation, the rounded displacement is at most `1.500001 * ratio`. -/
theorem configured_continued_exact_output_displacement_le_precise
    {nominalRatio computedBase : ℝ}
    (hratioLower : 1 / 20000000000 ≤ nominalRatio)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hceil :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ)) :
    computedBase - 1 ≤ (1500001 / 1000000 : ℝ) * nominalRatio := by
  have hmaxDenom : 0 < 1 - (MAX_OUT_RATIO : ℝ) / STROOP := by
    norm_num [MAX_OUT_RATIO, STROOP]
  have hdenomOrder :
      1 - (MAX_OUT_RATIO : ℝ) / STROOP ≤ 1 - nominalRatio := by
    linarith
  have hinverseOrder := one_div_le_one_div_of_le hmaxDenom hdenomOrder
  have hinverseMax :
      1 / (1 - (MAX_OUT_RATIO : ℝ) / STROOP) <
        (7500001 / 5000000 : ℝ) := by
    norm_num [MAX_OUT_RATIO, STROOP]
  have hinverse : 1 / (1 - nominalRatio) < (7500001 / 5000000 : ℝ) :=
    lt_of_le_of_lt hinverseOrder hinverseMax
  have hratio0 : 0 < nominalRatio := lt_of_lt_of_le (by norm_num) hratioLower
  have hgap : 1 / (BONE : ℝ) ≤ (1 / 50000000 : ℝ) * nominalRatio := by
    calc
      1 / (BONE : ℝ) =
          (1 / 50000000 : ℝ) * (1 / 20000000000 : ℝ) := by
        norm_num [BONE]
      _ ≤ (1 / 50000000 : ℝ) * nominalRatio :=
        mul_le_mul_of_nonneg_left hratioLower (by norm_num)
  have hdisplacement :
      computedBase - 1 <
        (7500001 / 5000000 : ℝ) * nominalRatio + 1 / BONE := by
    have hdenom : 0 < 1 - nominalRatio :=
      lt_of_lt_of_le hmaxDenom hdenomOrder
    have hid : 1 / (1 - nominalRatio) - 1 =
        nominalRatio / (1 - nominalRatio) := by
      field_simp
    have hratioInverse :
        nominalRatio / (1 - nominalRatio) <
          (7500001 / 5000000 : ℝ) * nominalRatio := by
      have hmul := mul_lt_mul_of_pos_left hinverse hratio0
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  nlinarith

/-- Direct single-sided input displacement stays inside the common operating band. -/
theorem configured_direct_input_displacement_le_three_fifths :
    (MAX_IN_RATIO : ℝ) / STROOP ≤ 3 / 5 := by
  norm_num [MAX_IN_RATIO, STROOP]

/-- The direct-deposit anchor remains below the upper operating-base bound. -/
theorem configured_direct_deposit_base_upper :
    1 + (MAX_IN_RATIO : ℝ) / STROOP ≤ 8 / 5 := by
  norm_num [MAX_IN_RATIO, STROOP]

/-- The worst fee-adjusted direct-withdrawal anchor remains above the lower base bound. -/
theorem configured_direct_withdrawal_base_lower :
    (1 / 2 : ℝ) <
      1 - (MAX_OUT_RATIO : ℝ) / STROOP /
        (1 - (1 - (MIN_WEIGHT : ℝ) / STROOP) * ((MAX_FEE : ℝ) / STROOP)) := by
  norm_num [MAX_OUT_RATIO, STROOP, MIN_WEIGHT, MAX_FEE]

/-- Every normalized base in `[0.5, 1.6]` has `abs(base - 1) ≤ 3/5`. -/
theorem operating_base_implies_abs_x_le_three_fifths {base : ℝ}
    (hlo : 1 / 2 ≤ base) (hi : base ≤ 8 / 5) :
    |base - 1| ≤ 3 / 5 := by
  rw [abs_le]
  constructor <;> linarith

end CometPool
