import Mathlib

namespace CometPool

/-- Products of non-negative upper bounds remain upper bounds. -/
theorem mul_upper_bound {wholeExact wholeUpper fracExact fracUpper : ℝ}
    (hwe0 : 0 ≤ wholeExact) (hfe0 : 0 ≤ fracExact)
    (hwhole : wholeExact ≤ wholeUpper) (hfrac : fracExact ≤ fracUpper) :
    wholeExact * fracExact ≤ wholeUpper * fracUpper := by
  exact mul_le_mul hwhole hfrac hfe0 (le_trans hwe0 hwhole)

end CometPool
