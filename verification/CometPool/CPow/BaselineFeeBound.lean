import CometPool.CPow.OperatingBand
import CometPool.Math.FixedPoint

namespace CometPool

/-!
Supporting theorems for comparing the baseline exact-input `c_pow`
approximation error with the minimum swap fee in a common, dimensionless
output-value normalization.

These theorems cover the `base < 1`, `round_up = true` fractional path used by
`calc_token_out_given_token_in`. They deliberately distinguish the
approximation error from final token-unit rounding.
-/

/-- The configured minimum swap-fee rate. -/
noncomputable def MIN_FEE_RATE : ℝ := (MIN_FEE : ℝ) / STROOP

/-- The closed-form accumulated recurrence-rounding budget through term `n`. -/
noncomputable def accumulatedError (n : ℕ) : ℝ := (3 * (n : ℝ) ^ 2 - n) / 2

theorem minimum_fee_rate_value : MIN_FEE_RATE = (1 : ℝ) / 1000000 := by
  norm_num [MIN_FEE_RATE, MIN_FEE, STROOP]

/-- Exact fractional-binomial terms contract geometrically from term one. -/
theorem fractional_binomial_terms_from_first_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T (n + 1)| ≤ |T 1| * q ^ n := by
  apply geometric_term_bound (M := fun n ↦ |T (n + 1)|)
    (S := |T 1|) (q := q) (le_refl _) (le_trans (abs_nonneg x) hx)
  intro n
  rw [hrec (n + 1)]
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
    fractional_binomial_step_contracts
      (a := a) (x := x) (q := q) (term := T (n + 1)) ha0 ha1 hx (n + 1)

/-- Exact-input bases contract terms by the sharper configured factor `1/4`. -/
theorem continued_exact_input_loop_forces_first_term_scale
    (T : ℕ → ℝ) {a x previous : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : |x| ≤ 1 / 4)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      |T 1| * (1 / 4 : ℝ) ^ (n - 2) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_first_bound
    T ha0 ha1 hx0 hrec (n - 2)
  have hindex : n - 2 + 1 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  linarith

/--
If a negative exact first term is floored to an integer whose magnitude is
above an integer threshold, the exact magnitude is strictly above that same
threshold.
-/
theorem negative_floor_above_integer_threshold
    {rounded threshold : ℤ} {exact : ℝ}
    (hfloor : IsFloor rounded exact)
    (hexactNonpos : exact ≤ 0)
    (hrounded : (threshold : ℝ) < |(rounded : ℝ)|) :
    (threshold : ℝ) < |exact| := by
  have hroundedNonpos : (rounded : ℝ) ≤ 0 := le_trans hfloor.le hexactNonpos
  rw [abs_of_nonpos hroundedNonpos] at hrounded
  rw [abs_of_nonpos hexactNonpos]
  have hroundedInt : threshold < -rounded := by exact_mod_cast hrounded
  have hsuccessor : threshold + 1 ≤ -rounded := by omega
  have hsuccessorReal : (threshold : ℝ) + 1 ≤ (-rounded : ℤ) := by
    exact_mod_cast hsuccessor
  push_cast at hsuccessorReal
  linarith [hfloor.lt_add_one]

/-- The configured minimum fee keeps the maximum adjusted input ratio below one third. -/
theorem configured_min_fee_adjusted_input_ratio_lt_one_third :
    (1 - MIN_FEE_RATE) * ((MAX_IN_RATIO : ℝ) / STROOP) < 1 / 3 := by
  norm_num [MIN_FEE_RATE, MIN_FEE, MAX_IN_RATIO, STROOP]

/-- A minimum-fee exact-input swap has `abs(base - 1) < 1/4`. -/
theorem configured_exact_input_base_displacement_lt_one_fourth
    {computedBase adjustedRatio : ℝ}
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjustedMax :
      adjustedRatio ≤
        (1 - MIN_FEE_RATE) * ((MAX_IN_RATIO : ℝ) / STROOP))
    (hceil : 1 / (1 + adjustedRatio) ≤ computedBase)
    (hbaseUpper : computedBase ≤ 1) :
    |computedBase - 1| < 1 / 4 := by
  have hadjustedThird : adjustedRatio < 1 / 3 :=
    lt_of_le_of_lt hadjustedMax configured_min_fee_adjusted_input_ratio_lt_one_third
  have hdenom : 0 < 1 + adjustedRatio := by linarith
  have hratioQuarter : adjustedRatio / (1 + adjustedRatio) < 1 / 4 := by
    apply (div_lt_iff₀ hdenom).2
    linarith
  have hid : 1 - 1 / (1 + adjustedRatio) =
      adjustedRatio / (1 + adjustedRatio) := by
    field_simp
  have hdisplacement : 1 - computedBase < 1 / 4 := by
    calc
      1 - computedBase ≤ 1 - 1 / (1 + adjustedRatio) := by linarith
      _ = adjustedRatio / (1 + adjustedRatio) := hid
      _ < 1 / 4 := hratioQuarter
  rw [abs_of_nonpos (sub_nonpos.mpr hbaseUpper)]
  linarith

/--
The computed exact-input base displacement cannot exceed the nominal input to
balance ratio. This connects the first binomial term to the input amount on
which the swap fee is charged.
-/
theorem exact_input_base_displacement_le_nominal_ratio
    {computedBase adjustedRatio nominalRatio : ℝ}
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjustedNominal : adjustedRatio ≤ nominalRatio)
    (hceil : 1 / (1 + adjustedRatio) ≤ computedBase) :
    1 - computedBase ≤ nominalRatio := by
  have hdenom : 0 < 1 + adjustedRatio := by linarith
  have hratio : adjustedRatio / (1 + adjustedRatio) ≤ adjustedRatio := by
    apply (div_le_iff₀ hdenom).2
    nlinarith [sq_nonneg adjustedRatio]
  have hid : 1 - 1 / (1 + adjustedRatio) =
      adjustedRatio / (1 + adjustedRatio) := by
    field_simp
  calc
    1 - computedBase ≤ 1 - 1 / (1 + adjustedRatio) := by linarith
    _ = adjustedRatio / (1 + adjustedRatio) := hid
    _ ≤ adjustedRatio := hratio
    _ ≤ nominalRatio := hadjustedNominal

/--
For a below-one base, an upper-rounded integer factor in `[0, 1]` cannot
amplify an adverse fractional-factor error. An upper-rounded final product can
only improve the result further.
-/
theorem below_one_upper_composition_preserves_adverse_bound
    {wholeExact wholeComputed fracExact fracComputed composed error : ℝ}
    (hwhole0 : 0 ≤ wholeExact) (hwhole1 : wholeExact ≤ 1)
    (hfracComputed0 : 0 ≤ fracComputed)
    (hwholeUpper : wholeExact ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * fracComputed ≤ composed)
    (herror0 : 0 < error)
    (hfracError : fracExact - fracComputed < error) :
    wholeExact * fracExact - composed < error := by
  have hproduct : wholeExact * fracComputed ≤ composed := by
    calc
      wholeExact * fracComputed ≤ wholeComputed * fracComputed :=
        mul_le_mul_of_nonneg_right hwholeUpper hfracComputed0
      _ ≤ composed := hcomposedUpper
  have hreduce :
      wholeExact * fracExact - composed ≤
        wholeExact * (fracExact - fracComputed) := by
    linarith
  by_cases hdelta : 0 ≤ fracExact - fracComputed
  · have hscale :
        wholeExact * (fracExact - fracComputed) ≤
          fracExact - fracComputed :=
      mul_le_of_le_one_left hdelta hwhole1
    linarith
  · have hscale : wholeExact * (fracExact - fracComputed) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hwhole0 (le_of_not_ge hdelta)
    linarith

end CometPool
