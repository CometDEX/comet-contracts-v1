import CometCPow.GeneratedConstants

namespace CometCPow

theorem configured_exponent_limit : MAX_CPOW_EXP = 10 * BONE := by
  norm_num [MAX_CPOW_EXP, BONE]

theorem term_error_at_iteration_cap : 3 * MAX_CPOW_ITERS - 2 = 148 := by
  norm_num [MAX_CPOW_ITERS]

theorem real_scale_exceeds_term_error_cap : (148 : ℝ) < (BONE : ℝ) := by
  norm_num [BONE]

theorem sum_error_at_iteration_cap :
    (3 * MAX_CPOW_ITERS ^ 2 - MAX_CPOW_ITERS) / 2 = 3725 := by
  norm_num [MAX_CPOW_ITERS]

/-- Every raw multiplication covered by the proof fits in a signed 256-bit integer. -/
theorem final_raw_product_fits_i256 :
    4096 * BONE ^ 2 ≤ 2 ^ 255 - 1 := by
  norm_num [BONE]

end CometCPow
