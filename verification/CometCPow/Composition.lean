import Mathlib

namespace CometCPow

/-- Products of non-negative lower bounds remain lower bounds. -/
theorem mul_lower_bound {wholeLower wholeExact fracLower fracExact : ℝ}
    (hwl0 : 0 ≤ wholeLower) (hfl0 : 0 ≤ fracLower)
    (hwhole : wholeLower ≤ wholeExact) (hfrac : fracLower ≤ fracExact) :
    wholeLower * fracLower ≤ wholeExact * fracExact := by
  exact mul_le_mul hwhole hfrac hfl0 (le_trans hwl0 hwhole)

/-- Products of non-negative upper bounds remain upper bounds. -/
theorem mul_upper_bound {wholeExact wholeUpper fracExact fracUpper : ℝ}
    (hwe0 : 0 ≤ wholeExact) (hfe0 : 0 ≤ fracExact)
    (hwhole : wholeExact ≤ wholeUpper) (hfrac : fracExact ≤ fracUpper) :
    wholeExact * fracExact ≤ wholeUpper * fracUpper := by
  exact mul_le_mul hwhole hfrac hfe0 (le_trans hwe0 hwhole)

/-- Taking the maximum of two lower bounds preserves a lower bound. -/
theorem max_lower_bound {a b exact : ℝ} (ha : a ≤ exact) (hb : b ≤ exact) :
    max a b ≤ exact := max_le ha hb

/-- Taking the minimum of two upper bounds preserves an upper bound. -/
theorem min_upper_bound {a b exact : ℝ} (ha : exact ≤ a) (hb : exact ≤ b) :
    exact ≤ min a b := le_min ha hb

end CometCPow
