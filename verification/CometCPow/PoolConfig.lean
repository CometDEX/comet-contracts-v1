import CometCPow.GeneratedConstants

namespace CometCPow

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

end CometCPow
