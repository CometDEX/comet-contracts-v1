import CometCPow.Constants

namespace CometCPow

/-!
This module records the application-specific numerical bounds that `c_pow`
supplies to the reusable checked-`I256` refinement proved in the
`soroban-fixed-point-math` repository.
-/

def CPOW_RAW_MAGNITUDE_BOUND : ℕ := 4096 * BONE ^ 2

def CPOW_DENOMINATOR_BOUND : ℕ := MAX_CPOW_ITERS * BONE

/-- The largest documented raw product fits below signed `I256::MAX`. -/
theorem cpow_raw_magnitude_bound_fits_i256 :
    CPOW_RAW_MAGNITUDE_BOUND ≤ 2 ^ 255 - 1 := by
  simpa [CPOW_RAW_MAGNITUDE_BOUND] using final_raw_product_fits_i256

/-- The largest denominator used by the recurrence fits below signed `I256::MAX`. -/
theorem cpow_denominator_bound_fits_i256 :
    CPOW_DENOMINATOR_BOUND ≤ 2 ^ 255 - 1 := by
  norm_num [CPOW_DENOMINATOR_BOUND, MAX_CPOW_ITERS, BONE]

/-- Every positive denominator used by the 50-step recurrence fits in `I256`. -/
theorem cpow_denominator_fits_i256 {d : ℕ}
    (hd : d ≤ CPOW_DENOMINATOR_BOUND) : d ≤ 2 ^ 255 - 1 :=
  le_trans hd cpow_denominator_bound_fits_i256

end CometCPow
