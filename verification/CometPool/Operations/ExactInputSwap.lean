import CometPool.CPow.BaselineFeeBound
import CometPool.CPow.BinomialUpper
import CometPool.CPow.BaselineRecurrence
import CometPool.CPow.ExactInputPrecise
import CometPool.CPow.CPowiUpper
import CometPool.Math.Composition

namespace CometPool

/-!
Operation-level composition for `swap_exact_amount_in` and its
`calc_token_out_given_token_in` arithmetic. The definitions use real values
for the mathematical specification and `IsFloor`/`IsCeil` relations for the
fixed-point operations. Those relations are exactly the interface proved by
the companion `soroban-fixed-point-math` refinement project.
-/

/-- The fee-adjusted mathematical base before any fixed-point rounding. -/
noncomputable def exactInputIdealBase (feeRate nominalRatio : ℝ) : ℝ :=
  1 / (1 + (1 - feeRate) * nominalRatio)

/-- Exact fee-adjusted output, expressed in the output balance's unit. -/
noncomputable def exactInputIdealOutput
    (outputBalance feeRate nominalRatio exponent : ℝ) : ℝ :=
  outputBalance * (1 - exactInputIdealBase feeRate nominalRatio ^ exponent)

/-- The configured minimum fee's spot-normalized output value. -/
noncomputable def exactInputMinimumFeeOutputValue
    (outputBalance exponent nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE * (outputBalance * exponent * nominalRatio)

/-- The corresponding fee scale in raw `c_pow` units. -/
noncomputable def exactInputMinimumFeePowerValue
    (exponent nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE * ((BONE : ℝ) * exponent * nominalRatio)

/-- A larger configured fee makes the exact adjusted input ratio no larger. -/
theorem exact_input_adjusted_ratio_le_minimum_fee_ratio
    {feeRate nominalRatio adjustedRatio : ℝ}
    (hfee : MIN_FEE_RATE ≤ feeRate)
    (hnominal0 : 0 ≤ nominalRatio)
    (hadjusted : adjustedRatio ≤ (1 - feeRate) * nominalRatio) :
    adjustedRatio ≤ (1 - MIN_FEE_RATE) * nominalRatio := by
  have hmultiplier : 1 - feeRate ≤ 1 - MIN_FEE_RATE := by linarith
  exact le_trans hadjusted (mul_le_mul_of_nonneg_right hmultiplier hnominal0)

/-- Fee adjustment cannot increase the nominal input-to-balance ratio. -/
theorem exact_input_adjusted_ratio_le_nominal_ratio
    {feeRate nominalRatio adjustedRatio : ℝ}
    (hfee0 : 0 ≤ feeRate)
    (hnominal0 : 0 ≤ nominalRatio)
    (hadjusted : adjustedRatio ≤ (1 - feeRate) * nominalRatio) :
    adjustedRatio ≤ nominalRatio := by
  have hmultiplier : 1 - feeRate ≤ 1 := by linarith
  exact le_trans hadjusted (by
    simpa using mul_le_mul_of_nonneg_right hmultiplier hnominal0)

/--
The exact-input fixed-point base and exponent directions both increase the
power relative to the unrounded fee-adjusted formula, which can only reduce
the amount paid to the user.
-/
theorem exact_input_rounded_power_dominates_ideal
    {feeRate nominalRatio adjustedRatio computedBase
      computedExponent idealExponent : ℝ}
    (hfeeUpper : feeRate ≤ 1)
    (hnominal0 : 0 ≤ nominalRatio)
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjusted : adjustedRatio ≤ (1 - feeRate) * nominalRatio)
    (hbaseCeil : 1 / (1 + adjustedRatio) ≤ computedBase)
    (hcomputedExponent0 : 0 ≤ computedExponent)
    (hexponentFloor : computedExponent ≤ idealExponent) :
    exactInputIdealBase feeRate nominalRatio ^ idealExponent ≤
      computedBase ^ computedExponent := by
  have hidealAdjusted0 : 0 ≤ (1 - feeRate) * nominalRatio :=
    mul_nonneg (sub_nonneg.mpr hfeeUpper) hnominal0
  have hadjustedDenom : 0 < 1 + adjustedRatio := by linarith
  have hidealDenom : 0 < 1 + (1 - feeRate) * nominalRatio := by linarith
  have hbaseOrder :
      exactInputIdealBase feeRate nominalRatio ≤ computedBase := by
    have hinverse :
        1 / (1 + (1 - feeRate) * nominalRatio) ≤
          1 / (1 + adjustedRatio) := by
      exact one_div_le_one_div_of_le hadjustedDenom (by linarith)
    exact le_trans hinverse hbaseCeil
  have hidealBase0 : 0 < exactInputIdealBase feeRate nominalRatio := by
    exact one_div_pos.mpr hidealDenom
  have hidealBase1 : exactInputIdealBase feeRate nominalRatio ≤ 1 := by
    apply (div_le_one hidealDenom).2
    linarith
  calc
    exactInputIdealBase feeRate nominalRatio ^ idealExponent ≤
        exactInputIdealBase feeRate nominalRatio ^ computedExponent :=
      Real.rpow_le_rpow_of_exponent_ge hidealBase0 hidealBase1 hexponentFloor
    _ ≤ computedBase ^ computedExponent :=
      Real.rpow_le_rpow hidealBase0.le hbaseOrder hcomputedExponent0

/--
Production fee and input-ratio limits discharge both exact-input displacement
bounds consumed by the five-percent fractional theorem.
-/
theorem configured_exact_input_computed_base_bounds
    {feeRate nominalRatio adjustedRatio computedBase : ℝ}
    (hfeeLower : MIN_FEE_RATE ≤ feeRate)
    (hfee0 : 0 ≤ feeRate)
    (hnominal0 : 0 ≤ nominalRatio)
    (hnominalMax : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjusted : adjustedRatio ≤ (1 - feeRate) * nominalRatio)
    (hbaseCeil : 1 / (1 + adjustedRatio) ≤ computedBase)
    (hbaseUpper : computedBase ≤ 1) :
    |computedBase - 1| < 1 / 4 ∧ 1 - computedBase ≤ nominalRatio := by
  have hadjustedMax :
      adjustedRatio ≤
        (1 - MIN_FEE_RATE) * ((MAX_IN_RATIO : ℝ) / STROOP) := by
    exact le_trans
      (exact_input_adjusted_ratio_le_minimum_fee_ratio
        hfeeLower hnominal0 hadjusted)
      (mul_le_mul_of_nonneg_left hnominalMax (by
        rw [minimum_fee_rate_value]
        norm_num))
  have hadjustedNominal := exact_input_adjusted_ratio_le_nominal_ratio
    hfee0 hnominal0 hadjusted
  constructor
  · exact configured_exact_input_base_displacement_lt_one_fourth
      hadjusted0 hadjustedMax hbaseCeil hbaseUpper
  · exact exact_input_base_displacement_le_nominal_ratio
      hadjusted0 hadjustedNominal hbaseCeil

/-- Flooring the fee-adjusted input gives the ratio bound used by the base proof. -/
theorem exact_input_adjusted_floor_refines_ratio
    {inputBalance inputAmount feeRate nominalRatio adjustedRatio : ℝ}
    {adjustedInput : ℤ}
    (hbalance : 0 < inputBalance)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor :
      IsFloor adjustedInput (inputAmount * (1 - feeRate))) :
    adjustedRatio ≤ (1 - feeRate) * nominalRatio := by
  rw [hadjustedRatio, hnominal]
  calc
    (adjustedInput : ℝ) / inputBalance ≤
        (inputAmount * (1 - feeRate)) / inputBalance :=
      div_le_div_of_nonneg_right hadjustedFloor.le hbalance.le
    _ = (1 - feeRate) * (inputAmount / inputBalance) := by ring

/-- The raw fixed-point base ceiling normalizes to a value in `(exactBase, 1]`. -/
theorem exact_input_base_ceil_refines
    {adjustedRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 + adjustedRatio)))) :
    1 / (1 + adjustedRatio) ≤ computedBase ∧ computedBase ≤ 1 := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hdenom : 0 < 1 + adjustedRatio := by linarith
  have hinverse : 1 / (1 + adjustedRatio) ≤ 1 :=
    (div_le_one hdenom).2 (by linarith)
  have hexactUpper :
      (BONE : ℝ) * (1 / (1 + adjustedRatio)) ≤ (BONE : ℝ) :=
    by simpa using mul_le_mul_of_nonneg_left hinverse hB.le
  have hrawUpper : computedBaseRaw ≤ (BONE : ℤ) :=
    hbaseCeil.le_integer_upper (by exact_mod_cast hexactUpper)
  constructor
  · rw [hcomputedBase]
    exact hbaseCeil.le_normalized hB
  · rw [hcomputedBase]
    exact (div_le_one hB).2 (by exact_mod_cast hrawUpper)

/-- The raw weight-ratio floor normalizes to a non-negative exponent no larger than exact. -/
theorem exact_input_exponent_floor_refines
    {idealExponent computedExponent : ℝ} {computedExponentRaw : ℤ}
    (hraw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentFloor :
      IsFloor computedExponentRaw ((STROOP : ℝ) * idealExponent)) :
    0 ≤ computedExponent ∧ computedExponent ≤ idealExponent := by
  have hS : (0 : ℝ) < STROOP := by norm_num [STROOP]
  constructor
  · rw [hcomputedExponent]
    positivity
  · rw [hcomputedExponent]
    exact hexponentFloor.normalized_le hS

/-- Compose the signed `17/800` fractional bound through baseline `c_pow`. -/
theorem baseline_exact_input_cpow_multiterm_adverse_error_lt_precise_fee_share
    (T : ℕ → ℝ)
    {n integerPart : ℕ}
    {a computedExponent feeExponent computedBase nominalRatio previous : ℝ}
    {firstRounded : ℤ}
    {exactPartial computedFractional wholeComputed computedPower : ℝ}
    {feePowerValue : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponent : computedExponent = (integerPart : ℝ) + a)
    (hbase0 : 0 < computedBase) (hbase1 : computedBase ≤ 1)
    (hbaseBounds :
      |computedBase - 1| < 1 / 4 ∧ 1 - computedBase ≤ nominalRatio)
    (hrec : ∀ k,
      T (k + 1) =
        T k * (a - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirstPrevious : n = 2 → previous = (firstRounded : ℝ))
    (hfirstFloor : IsFloor firstRounded (T 1))
    (hfirstNonpos : T 1 ≤ 0)
    (hfirst : |T 1| = (BONE : ℝ) * a * (1 - computedBase))
    (haFee : a ≤ feeExponent)
    (hnominal0 : 0 ≤ nominalRatio)
    (hfeeValue :
      feePowerValue = exactInputMinimumFeePowerValue feeExponent nominalRatio)
    (hfeePowerPositive : 0 < feePowerValue)
    (hpartialUpper : (BONE : ℝ) * computedBase ^ a ≤ exactPartial)
    (hsum : exactPartial - computedFractional < exactInputSignedAccumulatedError n)
    (hcomputedFractional0 : 0 ≤ computedFractional)
    (hwholeUpper : computedBase ^ integerPart ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * computedFractional ≤ computedPower) :
    (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
      EXACT_INPUT_ADVERSE_FEE_SHARE * feePowerValue := by
  have hfractional :=
    baseline_exact_input_multiterm_adverse_error_lt_precise_fee_share
      T ha0 ha1 (le_of_lt hbaseBounds.1) hrec hn2 hn46 hprevious htermError
        hfirstPrevious hfirstFloor hfirstNonpos hfirst haFee hnominal0
        hbaseBounds.2 (by simpa [exactInputMinimumFeePowerValue] using hfeeValue)
        hpartialUpper hsum
  have hwhole0 : 0 ≤ computedBase ^ integerPart := by positivity
  have hwhole1 : computedBase ^ integerPart ≤ 1 := by
    simpa using Real.rpow_le_one hbase0.le hbase1
      (show (0 : ℝ) ≤ integerPart by positivity)
  have hshare0 : 0 < EXACT_INPUT_ADVERSE_FEE_SHARE := by
    rw [exact_input_adverse_fee_share_value]
    norm_num
  have herrorPositive : 0 < EXACT_INPUT_ADVERSE_FEE_SHARE * feePowerValue :=
    mul_pos hshare0 hfeePowerPositive
  have hcomposed := below_one_upper_composition_preserves_adverse_bound
    hwhole0 hwhole1 hcomputedFractional0 hwholeUpper hcomposedUpper
      herrorPositive hfractional
  have hexact :
      (BONE : ℝ) * computedBase ^ computedExponent =
        computedBase ^ integerPart * ((BONE : ℝ) * computedBase ^ a) := by
    rw [hcomputedExponent, Real.rpow_add hbase0]
    norm_num [Real.rpow_natCast]
    ring
  rw [hexact]
  exact hcomposed

/--
The one-term correction remains an upper bound after integer-power and final
fixed-point composition, so it has zero pool-adverse error.
-/
theorem baseline_exact_input_cpow_first_term_has_no_adverse_error
    {integerPart : ℕ}
    {a computedExponent computedBase exactPartial computedPartial
      computedFractional wholeComputed computedPower : ℝ}
    (hcomputedExponent : computedExponent = (integerPart : ℝ) + a)
    (hbase0 : 0 < computedBase)
    (hpartialUpper : (BONE : ℝ) * computedBase ^ a ≤ exactPartial)
    (hfirstFloor : exactPartial < computedPartial + 1)
    (hcomputedFractional : computedFractional = computedPartial + 1)
    (hwholeUpper : computedBase ^ integerPart ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * computedFractional ≤ computedPower) :
    (BONE : ℝ) * computedBase ^ computedExponent ≤ computedPower := by
  have hfractional : (BONE : ℝ) * computedBase ^ a ≤ computedFractional := by
    rw [hcomputedFractional]
    exact le_trans hpartialUpper (le_of_lt hfirstFloor)
  have hwhole0 : 0 ≤ computedBase ^ integerPart := by positivity
  have hfrac0 : 0 ≤ (BONE : ℝ) * computedBase ^ a := by positivity
  have hproduct := mul_upper_bound hwhole0 hfrac0 hwholeUpper hfractional
  have hexact :
      (BONE : ℝ) * computedBase ^ computedExponent =
        computedBase ^ integerPart * ((BONE : ℝ) * computedBase ^ a) := by
    rw [hcomputedExponent, Real.rpow_add hbase0]
    norm_num [Real.rpow_natCast]
    ring
  rw [hexact]
  exact le_trans hproduct hcomposedUpper

/-- An integer-only `c_pow` result has zero adverse error when `c_powi` rounds upward. -/
theorem baseline_exact_input_cpow_integer_has_no_adverse_error
    {integerPart : ℕ} {computedBase computedPower : ℝ}
    (hwholeUpper :
      (BONE : ℝ) * computedBase ^ integerPart ≤ computedPower) :
    (BONE : ℝ) * computedBase ^ (integerPart : ℝ) ≤ computedPower := by
  simpa [Real.rpow_natCast] using hwholeUpper

/-- The final upper-rounded fixed-point product supplies `c_pow`'s composition bound. -/
theorem exact_input_final_cpow_ceil_refines
    {computedPowerRaw : ℤ}
    {wholeComputed computedFractional computedPower : ℝ}
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw (wholeComputed * computedFractional)) :
    wholeComputed * computedFractional ≤ computedPower := by
  rw [hcomputedPower]
  exact hcomposedCeil.le

/-- A unit base is exact for every exponent, including the no-correction first-term branch. -/
theorem baseline_exact_input_cpow_unit_base_has_no_adverse_error
    {computedExponent computedBase computedPower : ℝ}
    (hbase : computedBase = 1)
    (hpower : (BONE : ℝ) ≤ computedPower) :
    (BONE : ℝ) * computedBase ^ computedExponent ≤ computedPower := by
  simpa [hbase] using hpower

/-- Two successive output floors cannot increase the user-visible amount. -/
theorem exact_input_output_floor_chain
    {intermediate output : ℤ}
    {outputBalance computedPower scale : ℝ}
    (hscale : 0 < scale)
    (hmulFloor :
      IsFloor intermediate
        (outputBalance * (1 - computedPower / (BONE : ℝ))))
    (hdownscaleFloor : IsFloor output ((intermediate : ℝ) / scale)) :
    (output : ℝ) ≤
      (outputBalance / scale) * (1 - computedPower / (BONE : ℝ)) := by
  have hdown := hdownscaleFloor.le
  have hmul := hmulFloor.le
  have hscaled := (div_le_div_iff_of_pos_right hscale).2 hmul
  calc
    (output : ℝ) ≤ (intermediate : ℝ) / scale := hdown
    _ ≤ outputBalance * (1 - computedPower / (BONE : ℝ)) / scale := hscaled
    _ = (outputBalance / scale) * (1 - computedPower / (BONE : ℝ)) := by ring

/--
Complete operation-level error composition for `swap_exact_amount_in` once
the selected baseline `c_pow` control-flow case supplies its checked bound.
-/
theorem swap_exact_amount_in_adverse_error_lt_fee_share
    {feeShare feeRate nominalRatio adjustedRatio computedBase
      computedExponent idealExponent computedExactPower computedPower
      outputBalance computedOutput : ℝ}
    (hfeeUpper : feeRate ≤ 1)
    (hnominal0 : 0 ≤ nominalRatio)
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjusted : adjustedRatio ≤ (1 - feeRate) * nominalRatio)
    (hbaseCeil : 1 / (1 + adjustedRatio) ≤ computedBase)
    (hcomputedExponent0 : 0 ≤ computedExponent)
    (hexponentFloor : computedExponent ≤ idealExponent)
    (hcomputedExactPower :
      computedExactPower = (BONE : ℝ) * computedBase ^ computedExponent)
    (hcpow :
      computedExactPower - computedPower <
        feeShare * exactInputMinimumFeePowerValue idealExponent nominalRatio)
    (houtputBalance : 0 < outputBalance)
    (houtputFloor :
      computedOutput ≤
        outputBalance * (1 - computedPower / (BONE : ℝ))) :
    computedOutput -
        exactInputIdealOutput outputBalance feeRate nominalRatio idealExponent <
      feeShare * exactInputMinimumFeeOutputValue
        outputBalance idealExponent nominalRatio := by
  have hpowerDirection := exact_input_rounded_power_dominates_ideal
    hfeeUpper hnominal0 hadjusted0 hadjusted hbaseCeil
      hcomputedExponent0 hexponentFloor
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hrawPowerDirection :
      (BONE : ℝ) * exactInputIdealBase feeRate nominalRatio ^ idealExponent ≤
        computedExactPower := by
    rw [hcomputedExactPower]
    exact mul_le_mul_of_nonneg_left hpowerDirection hB.le
  have hadversePower :
      (BONE : ℝ) * exactInputIdealBase feeRate nominalRatio ^ idealExponent -
          computedPower <
        feeShare * exactInputMinimumFeePowerValue idealExponent nominalRatio := by
    linarith
  have hscale : 0 < outputBalance / (BONE : ℝ) := div_pos houtputBalance hB
  have hscaled := mul_lt_mul_of_pos_left hadversePower hscale
  calc
    computedOutput -
          exactInputIdealOutput outputBalance feeRate nominalRatio idealExponent ≤
        outputBalance * (1 - computedPower / (BONE : ℝ)) -
          exactInputIdealOutput outputBalance feeRate nominalRatio idealExponent :=
      sub_le_sub_right houtputFloor _
    _ = (outputBalance / (BONE : ℝ)) *
        ((BONE : ℝ) * exactInputIdealBase feeRate nominalRatio ^ idealExponent -
          computedPower) := by
      rw [exactInputIdealOutput]
      field_simp [ne_of_gt hB]
      ring
    _ < (outputBalance / (BONE : ℝ)) *
        (feeShare * exactInputMinimumFeePowerValue idealExponent nominalRatio) := hscaled
    _ = feeShare * exactInputMinimumFeeOutputValue
        outputBalance idealExponent nominalRatio := by
      rw [exactInputMinimumFeePowerValue, exactInputMinimumFeeOutputValue]
      field_simp [ne_of_gt hB]
      ring

/--
Instantiate the operation theorem from the floor/ceiling refinements matching
the fixed-point calls in `calc_token_out_given_token_in`.
-/
theorem swap_exact_amount_in_from_fixed_point_refinements_fee_share
    {feeShare inputBalance inputAmount feeRate nominalRatio adjustedRatio computedBase
      idealExponent computedExponent computedPower outputBalance scale : ℝ}
    {adjustedInput computedBaseRaw computedExponentRaw intermediate output : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hinputAmount : 0 ≤ inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hfeeUpper : feeRate ≤ 1)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor :
      IsFloor adjustedInput (inputAmount * (1 - feeRate)))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 + adjustedRatio))))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentFloor :
      IsFloor computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        feeShare * exactInputMinimumFeePowerValue idealExponent nominalRatio)
    (houtputBalance : 0 < outputBalance)
    (hscale : 0 < scale)
    (hmulFloor :
      IsFloor intermediate
        (outputBalance * (1 - computedPower / (BONE : ℝ))))
    (hdownscaleFloor : IsFloor output ((intermediate : ℝ) / scale)) :
    (output : ℝ) -
        exactInputIdealOutput (outputBalance / scale) feeRate nominalRatio idealExponent <
      feeShare * exactInputMinimumFeeOutputValue
        (outputBalance / scale) idealExponent nominalRatio := by
  have hnominal0 : 0 ≤ nominalRatio := by
    rw [hnominal]
    positivity
  have hadjusted0 : 0 ≤ adjustedRatio := by
    rw [hadjustedRatio]
    positivity
  have hadjusted := exact_input_adjusted_floor_refines_ratio
    hinputBalance hnominal hadjustedRatio hadjustedFloor
  have hbase := exact_input_base_ceil_refines
    hadjusted0 hcomputedBase hbaseCeil
  have hexponent := exact_input_exponent_floor_refines
    hcomputedExponentRaw0 hcomputedExponent hexponentFloor
  have houtput := exact_input_output_floor_chain
    hscale hmulFloor hdownscaleFloor
  exact swap_exact_amount_in_adverse_error_lt_fee_share
    hfeeUpper hnominal0 hadjusted0 hadjusted hbase.1 hexponent.1
      hexponent.2 rfl hcpow (div_pos houtputBalance hscale) houtput

/-- The exact fractional power is below its first-order term on the below-one path. -/
theorem exact_input_fractional_first_order_upper
    {a computedBase : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hbase0 : 0 ≤ computedBase) :
    (BONE : ℝ) * computedBase ^ a ≤
      (BONE : ℝ) + (BONE : ℝ) * a * (computedBase - 1) := by
  have hbernoulli := rpow_one_add_le_one_add_mul_self
    (s := computedBase - 1) (by linarith) ha0 ha1
  have hB : (0 : ℝ) ≤ BONE := by norm_num [BONE]
  have hscaled := mul_le_mul_of_nonneg_left hbernoulli hB
  norm_num at hscaled
  nlinarith

/--
Full multi-term `swap_exact_amount_in` comparison with the signed `17/800`
minimum-fee bound for the modeled production fixed-point path.
-/
theorem baseline_swap_exact_amount_in_multiterm_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n integerPart : ℕ}
    {inputBalance inputAmount feeRate nominalRatio adjustedRatio computedBase
      idealExponent computedExponent computedFractional
      wholeComputed computedPower outputBalance scale : ℝ}
    {adjustedInput computedBaseRaw computedExponentRaw computedPowerRaw
      intermediate output : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalMax : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate)
    (hfee0 : 0 ≤ feeRate) (hfeeUpper : feeRate ≤ 1)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor :
      IsFloor adjustedInput (inputAmount * (1 - feeRate)))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 + adjustedRatio))))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponentRaw :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentFloor :
      IsFloor computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (hidealExponentPositive : 0 < idealExponent)
    {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hbaseNonunit : computedBase < 1)
    (hn2 : 2 ≤ n)
    (hn50 : n ≤ 50)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1) (exactInputBinomialTerm a computedBase 1))
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (a - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) +
        ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw (wholeComputed * computedFractional))
    (houtputBalance : 0 < outputBalance)
    (hscale : 0 < scale)
    (hmulFloor :
      IsFloor intermediate
        (outputBalance * (1 - computedPower / (BONE : ℝ))))
    (hdownscaleFloor : IsFloor output ((intermediate : ℝ) / scale)) :
    (output : ℝ) -
        exactInputIdealOutput (outputBalance / scale) feeRate nominalRatio idealExponent <
      EXACT_INPUT_ADVERSE_FEE_SHARE * exactInputMinimumFeeOutputValue
        (outputBalance / scale) idealExponent nominalRatio := by
  have hnominal0 : 0 ≤ nominalRatio := by
    rw [hnominal]
    positivity
  have hnominalPositive : 0 < nominalRatio := by
    rw [hnominal]
    positivity
  have hadjusted0 : 0 ≤ adjustedRatio := by
    rw [hadjustedRatio]
    positivity
  have hadjusted := exact_input_adjusted_floor_refines_ratio
    hinputBalance hnominal hadjustedRatio hadjustedFloor
  have hbase := exact_input_base_ceil_refines
    hadjusted0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le
    (one_div_pos.mpr (by linarith : 0 < 1 + adjustedRatio)) hbase.1
  have hbaseBounds := configured_exact_input_computed_base_bounds
    hfeeLower hfee0 hnominal0 hnominalMax hadjusted0 hadjusted hbase.1 hbase.2
  let T : ℕ → ℝ := exactInputBinomialTerm a computedBase
  let exactPartial : ℝ :=
    ∑ k ∈ Finset.range (n + 1), exactInputBinomialTerm a computedBase k
  have hrec : ∀ k,
      T (k + 1) =
        T k * (a - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactInputBinomialTerm_succ a computedBase k
  have hfirstFacts := exactInputBinomialTerm_one ha0 hbase.2
  have hfirstNonpos : T 1 ≤ 0 := by
    change exactInputBinomialTerm a computedBase 1 ≤ 0
    rw [hfirstFacts.1]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num [BONE]) ha0) (sub_nonpos.mpr hbase.2)
  have hfirst : |T 1| = (BONE : ℝ) * a * (1 - computedBase) :=
    hfirstFacts.2
  have hpartialUpper : (BONE : ℝ) * computedBase ^ a ≤ exactPartial := by
    exact exact_input_binomial_partial_upper ha0 ha1 hbase0 hbaseNonunit n
  have hexactPartial :
      exactPartial = (BONE : ℝ) +
        ∑ k ∈ Finset.range n, T (k + 1) := by
    dsimp [exactPartial, T]
    rw [Finset.sum_range_succ']
    simp
    ring
  have hexponent := exact_input_exponent_floor_refines
    hcomputedExponentRaw0 hcomputedExponentRaw hexponentFloor
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  have hBErrorScale : (148 : ℝ) < BONE := by norm_num [BONE]
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [U, T]
    exact hfirstFloor.abs_error_lt_one
  have hbaseDisplacementQuarter : 1 - computedBase < 1 / 4 := by
    have h := hbaseBounds.1
    rw [abs_of_nonpos (sub_nonpos.mpr hbase.2)] at h
    linarith
  have hfirstMagnitude : |T 1| < BONE := by
    rw [hfirst]
    have hproduct : a * (1 - computedBase) < 1 := by
      calc
        a * (1 - computedBase) ≤ 1 * (1 - computedBase) :=
          mul_le_mul_of_nonneg_right ha1 (by linarith)
        _ < 1 := by linarith
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    simpa only [mul_assoc, mul_one] using mul_lt_mul_of_pos_left hproduct hB
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T ha0 ha1 (le_of_lt hbaseBounds.1) hrec (k - 1)
    have hindex : k - 1 + 1 = k := by omega
    rw [hindex] at hterms
    have hpower0 : 0 ≤ (1 / 4 : ℝ) ^ (k - 1) := by positivity
    have hpower1 : (1 / 4 : ℝ) ^ (k - 1) ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hscale : |T 1| * (1 / 4 : ℝ) ^ (k - 1) ≤ |T 1| := by
      nlinarith [abs_nonneg (T 1)]
    exact lt_of_le_of_lt (le_trans hterms hscale) hfirstMagnitude
  have herrorRec : ∀ k, 1 ≤ k → k < n →
      |T (k + 1) - U (k + 1)| <
        (1 + 1 / (((k + 1 : ℕ) : ℝ) * (BONE : ℝ))) * |T k - U k| +
          1 / ((k + 1 : ℕ) : ℝ) + 1 / ((k + 1 : ℕ) : ℝ) + 1 := by
    intro k hk hkn
    have hcoefficientNonpos : a - (k : ℝ) ≤ 0 := by
      have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hcoefficientBound : |a - (k : ℝ)| ≤ (k : ℝ) + 1 := by
      rw [abs_of_nonpos hcoefficientNonpos]
      linarith
    have hdisplacementBound : |computedBase - 1| ≤ 1 :=
      le_trans (le_of_lt hbaseBounds.1) (by norm_num)
    have hstep := three_floor_recurrence_step_error
      (S := (BONE : ℝ)) (K := (k : ℝ) + 1)
      (exactPrevious := T k) (computedPrevious := U k)
      (coefficient := a - (k : ℝ)) (displacement := computedBase - 1)
      (coefficientProduct := coefficientProduct (k + 1))
      (multiplied := multiplied (k + 1))
      (nextComputed := computedTerm (k + 1))
      (by norm_num [BONE]) (by positivity) hcoefficientBound
      hdisplacementBound (hexactTermMagnitude k hk)
      (hcoefficientFloor k hk hkn)
      (by simpa [U] using hmultiplyTermFloor k hk hkn)
      (hdivideTermFloor k hk hkn)
    rw [hrec k]
    simpa [U, Nat.cast_add, Nat.cast_one, add_assoc] using hstep
  have htermBounds := recurrence_error_budget_until (BONE : ℝ)
    (fun k ↦ |T k - U k|) hn50 hBErrorScale hfirstError herrorRec
  have hdisplacementNonpos : computedBase - 1 ≤ 0 := sub_nonpos.mpr hbase.2
  have hsignedTermRaw := exact_input_signed_term_error_lt_budget
    T coefficientProduct multiplied computedTerm ha0 ha1 hdisplacementNonpos
      (le_of_lt hbaseBounds.1) hrec hfirstFloor (by
        dsimp [T]
        exact hfirstFacts.1)
      hcoefficientFloor hmultiplyTermFloor hdivideTermFloor
      (fun k hk hkn ↦ by simpa [U] using htermBounds k hk hkn)
  have hbaseLower : (1 / 2 : ℝ) ≤ computedBase := by
    have h := hbaseBounds.1
    rw [abs_of_nonpos (sub_nonpos.mpr hbase.2)] at h
    linarith
  have hbaseUpper : computedBase ≤ (8 / 5 : ℝ) := by linarith [hbase.2]
  have htermZero : |T 0| ≤ (BONE : ℝ) := by
    dsimp [T]
    simp
  have hn46 : n ≤ 46 := by
    by_contra hn
    have herror46 : |T 46 - U 46| < 3 * (46 : ℝ) - 2 :=
      htermBounds 46 (by norm_num) (by omega)
    have hstopsBy46 : |U 46| < (CPOW_PRECISION : ℝ) :=
      pool_operating_base_converges_by_iteration_46
        T ha0 ha1 hbaseLower hbaseUpper htermZero hrec herror46
    have hstillRunning := hcontinued 46 (by norm_num) (by omega)
    dsimp [U] at hstopsBy46
    linarith
  have hprevious :
      (CPOW_PRECISION : ℝ) < |(computedTerm (n - 1) : ℝ)| :=
    hcontinued (n - 1) (by omega) (by omega)
  have hnMinusOne1 : 1 ≤ n - 1 := by omega
  have hnMinusOneN : n - 1 ≤ n := by omega
  have htermError :
      |T (n - 1) - U (n - 1)| < 3 * ((n - 1 : ℕ) : ℝ) - 2 :=
    htermBounds (n - 1) hnMinusOne1 hnMinusOneN
  have hfirstPrevious : n = 2 → U (n - 1) = (computedTerm 1 : ℝ) := by
    intro hn
    subst n
    rfl
  have hn1 : 1 ≤ n := by omega
  have hsumSignedRaw := exact_input_partial_sum_signed_error_lt T U hn1
    (fun k hk hkn ↦ by simpa [U] using hsignedTermRaw k hk hkn)
  have hsumSigned :
      exactPartial - computedFractional < exactInputSignedAccumulatedError n := by
    rw [hexactPartial, hcomputedFractional]
    convert hsumSignedRaw using 1
    simp [U, Nat.add_comm]
  have hsumRaw := recurrence_implies_partial_sum_error_budget_until
    (BONE : ℝ) T U hn1 hn50 hBErrorScale hfirstError herrorRec
  have hsum : |exactPartial - computedFractional| < accumulatedError n := by
    rw [hexactPartial, hcomputedFractional, accumulatedError]
    convert hsumRaw using 1
    simp [U, Nat.add_comm]
  have hpowerLower : (1 / 2 : ℝ) ≤ computedBase ^ a := by
    have hexponentDirection :
        computedBase ^ (1 : ℝ) ≤ computedBase ^ a :=
      Real.rpow_le_rpow_of_exponent_ge hbase0 hbase.2 ha1
    have hexponentDirection' : computedBase ≤ computedBase ^ a := by
      simpa using hexponentDirection
    exact le_trans hbaseLower hexponentDirection'
  have hpartialLower : (BONE : ℝ) / 2 ≤ exactPartial := by
    have hscaled := mul_le_mul_of_nonneg_left hpowerLower
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
    calc
      (BONE : ℝ) / 2 = (BONE : ℝ) * (1 / 2 : ℝ) := by ring
      _ ≤ (BONE : ℝ) * computedBase ^ a := hscaled
      _ ≤ exactPartial := hpartialUpper
  have haccumulatedErrorMax : accumulatedError n ≤ 3151 := by
    have hnReal : (n : ℝ) ≤ 46 := by exact_mod_cast hn46
    have hsecond : 0 ≤ 3 * (46 + (n : ℝ)) - 1 := by
      calc
        (0 : ℝ) ≤ 137 + 3 * (n : ℝ) := by positivity
        _ = 3 * (46 + (n : ℝ)) - 1 := by ring
    have hgap :
        0 ≤ (46 - (n : ℝ)) * (3 * (46 + (n : ℝ)) - 1) := by
      exact mul_nonneg (sub_nonneg.mpr hnReal) hsecond
    rw [accumulatedError]
    nlinarith only [hgap]
  have hcomputedFractionalPositive : 0 < computedFractional := by
    have hpartialDifference :
        exactPartial - computedFractional < accumulatedError n :=
      lt_of_le_of_lt (le_abs_self _) hsum
    have hmargin : (3151 : ℝ) < (BONE : ℝ) / 2 := by norm_num [BONE]
    linarith only [hpartialLower, hpartialDifference, haccumulatedErrorMax, hmargin]
  have hcomputedFractional0 : 0 ≤ computedFractional :=
    le_of_lt hcomputedFractionalPositive
  have haComputed : a ≤ computedExponent := by
    rw [hcomputedExponentSplit]
    have hinteger : (0 : ℝ) ≤ integerPart := by positivity
    linarith
  have haIdeal : a ≤ idealExponent := le_trans haComputed hexponent.2
  have hfeePowerPositive :
      0 < exactInputMinimumFeePowerValue idealExponent nominalRatio := by
    have hrate : 0 < MIN_FEE_RATE := by rw [minimum_fee_rate_value]; norm_num
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    rw [exactInputMinimumFeePowerValue]
    exact mul_pos hrate (mul_pos (mul_pos hB hidealExponentPositive) hnominalPositive)
  have hcomposedUpper := exact_input_final_cpow_ceil_refines
    hcomputedPower hcomposedCeil
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hcpow :=
    baseline_exact_input_cpow_multiterm_adverse_error_lt_precise_fee_share
      T ha0 ha1 hcomputedExponentSplit hbase0 hbase.2 hbaseBounds hrec
        hn2 hn46 hprevious htermError hfirstPrevious hfirstFloor hfirstNonpos
        hfirst haIdeal hnominal0 rfl hfeePowerPositive hpartialUpper hsumSigned
        hcomputedFractional0 hwholeUpper hcomposedUpper
  exact swap_exact_amount_in_from_fixed_point_refinements_fee_share
    hinputBalance hinputAmount.le hnominal hfeeUpper hadjustedInput0
      hadjustedRatio hadjustedFloor hcomputedBase hbaseCeil
      hcomputedExponentRaw0 hcomputedExponentRaw hexponentFloor hcpow
      houtputBalance hscale hmulFloor hdownscaleFloor

/-- Positive exponent and input ratio make the minimum-fee power scale positive. -/
theorem exact_input_minimum_fee_power_value_positive
    {exponent nominalRatio : ℝ}
    (hexponent : 0 < exponent) (hnominal : 0 < nominalRatio) :
    0 < exactInputMinimumFeePowerValue exponent nominalRatio := by
  have hrate : 0 < MIN_FEE_RATE := by rw [minimum_fee_rate_value]; norm_num
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  rw [exactInputMinimumFeePowerValue]
  exact mul_pos hrate (mul_pos (mul_pos hB hexponent) hnominal)

/-- The one-term path has zero adverse error, hence satisfies the precise fee share. -/
theorem baseline_swap_exact_amount_in_first_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {inputBalance inputAmount feeRate nominalRatio adjustedRatio computedBase
      idealExponent computedExponent wholeComputed computedPower outputBalance scale a : ℝ}
    {adjustedInput computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      intermediate output : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hfeeUpper : feeRate ≤ 1)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * (1 - feeRate)))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 / (1 + adjustedRatio))))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponentRaw :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentFloor :
      IsFloor computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (hidealExponentPositive : 0 < idealExponent)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ) + 1)))
    (houtputBalance : 0 < outputBalance)
    (hscale : 0 < scale)
    (hmulFloor :
      IsFloor intermediate
        (outputBalance * (1 - computedPower / (BONE : ℝ))))
    (hdownscaleFloor : IsFloor output ((intermediate : ℝ) / scale)) :
    (output : ℝ) -
        exactInputIdealOutput (outputBalance / scale) feeRate nominalRatio idealExponent <
      EXACT_INPUT_ADVERSE_FEE_SHARE * exactInputMinimumFeeOutputValue
        (outputBalance / scale) idealExponent nominalRatio := by
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hadjusted0 : 0 ≤ adjustedRatio := by rw [hadjustedRatio]; positivity
  have hbase := exact_input_base_ceil_refines
    hadjusted0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le
    (one_div_pos.mpr (by linarith : 0 < 1 + adjustedRatio)) hbase.1
  have hfeePowerPositive := exact_input_minimum_fee_power_value_positive
    hidealExponentPositive hnominalPositive
  have hcomposedUpper := exact_input_final_cpow_ceil_refines
    hcomputedPower hcomposedCeil
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hpartialUpper := exact_input_fractional_first_order_upper ha0 ha1 hbase0.le
  have hpartialFloor :
      (BONE : ℝ) + (BONE : ℝ) * a * (computedBase - 1) <
        ((BONE : ℝ) + (firstRounded : ℝ)) + 1 := by
    linarith [hfirstFloor.lt_add_one]
  have hconservative := baseline_exact_input_cpow_first_term_has_no_adverse_error
    hcomputedExponentSplit hbase0 hpartialUpper hpartialFloor rfl
      hwholeUpper hcomposedUpper
  have hshare0 : 0 < EXACT_INPUT_ADVERSE_FEE_SHARE := by
    rw [exact_input_adverse_fee_share_value]
    norm_num
  have hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        EXACT_INPUT_ADVERSE_FEE_SHARE *
          exactInputMinimumFeePowerValue idealExponent nominalRatio := by
    have := mul_pos hshare0 hfeePowerPositive
    linarith
  exact swap_exact_amount_in_from_fixed_point_refinements_fee_share
    hinputBalance hinputAmount.le hnominal hfeeUpper hadjustedInput0
      hadjustedRatio hadjustedFloor hcomputedBase hbaseCeil
      hcomputedExponentRaw0 hcomputedExponentRaw hexponentFloor hcpow
      houtputBalance hscale hmulFloor hdownscaleFloor

/-- The integer path has zero adverse error, hence satisfies the precise fee share. -/
theorem baseline_swap_exact_amount_in_integer_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {inputBalance inputAmount feeRate nominalRatio adjustedRatio computedBase
      idealExponent computedPower outputBalance scale : ℝ}
    {adjustedInput computedBaseRaw computedExponentRaw intermediate output : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hfeeUpper : feeRate ≤ 1)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * (1 - feeRate)))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 / (1 + adjustedRatio))))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponentRaw :
      (integerPart : ℝ) = (computedExponentRaw : ℝ) / STROOP)
    (hexponentFloor :
      IsFloor computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (hidealExponentPositive : 0 < idealExponent)
    (hwholeTrace :
      UpperCPowiTrace computedBase integerPart
        (computedPower / (BONE : ℝ)))
    (houtputBalance : 0 < outputBalance)
    (hscale : 0 < scale)
    (hmulFloor :
      IsFloor intermediate
        (outputBalance * (1 - computedPower / (BONE : ℝ))))
    (hdownscaleFloor : IsFloor output ((intermediate : ℝ) / scale)) :
    (output : ℝ) -
        exactInputIdealOutput (outputBalance / scale) feeRate nominalRatio idealExponent <
      EXACT_INPUT_ADVERSE_FEE_SHARE * exactInputMinimumFeeOutputValue
        (outputBalance / scale) idealExponent nominalRatio := by
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hfeePowerPositive := exact_input_minimum_fee_power_value_positive
    hidealExponentPositive hnominalPositive
  have hadjusted0 : 0 ≤ adjustedRatio := by rw [hadjustedRatio]; positivity
  have hbase := exact_input_base_ceil_refines
    hadjusted0 hcomputedBase hbaseCeil
  have hwholeNormalized := hwholeTrace.upper_bound
    (lt_of_lt_of_le
      (one_div_pos.mpr (by linarith : 0 < 1 + adjustedRatio)) hbase.1).le
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hwholeUpper :
      (BONE : ℝ) * computedBase ^ integerPart ≤ computedPower := by
    have h := (le_div_iff₀ hB).mp hwholeNormalized
    simpa [mul_comm] using h
  have hconservative := baseline_exact_input_cpow_integer_has_no_adverse_error
    hwholeUpper
  have hshare0 : 0 < EXACT_INPUT_ADVERSE_FEE_SHARE := by
    rw [exact_input_adverse_fee_share_value]
    norm_num
  have hcpow :
      (BONE : ℝ) * computedBase ^ (integerPart : ℝ) - computedPower <
        EXACT_INPUT_ADVERSE_FEE_SHARE *
          exactInputMinimumFeePowerValue idealExponent nominalRatio := by
    have := mul_pos hshare0 hfeePowerPositive
    linarith
  exact swap_exact_amount_in_from_fixed_point_refinements_fee_share
    hinputBalance hinputAmount.le hnominal hfeeUpper hadjustedInput0
      hadjustedRatio hadjustedFloor hcomputedBase hbaseCeil
      hcomputedExponentRaw0 hcomputedExponentRaw hexponentFloor hcpow
      houtputBalance hscale hmulFloor hdownscaleFloor

end CometPool
