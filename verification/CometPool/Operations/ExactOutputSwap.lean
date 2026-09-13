import CometPool.CPow.BinomialAboveUpper
import CometPool.CPow.BaselineRecurrence
import CometPool.CPow.CPowiUpper
import CometPool.Math.Composition
import CometPool.Operations.OperationFeeBound

namespace CometPool

/-!
Operation-level composition for `swap_exact_amount_out` and its
`calc_token_in_given_token_out` arithmetic.  Real-valued definitions state
the ideal formula; `IsFloor`/`IsCeil` premises connect each fixed-point call to
that formula.
-/

/-- The exact-output mathematical base before fixed-point ceiling. -/
noncomputable def exactOutputIdealBase (nominalRatio : ℝ) : ℝ :=
  1 / (1 - nominalRatio)

/-- Exact fee-adjusted input, expressed in the input balance's unit. -/
noncomputable def exactOutputIdealInput
    (inputBalance feeRate nominalRatio exponent : ℝ) : ℝ :=
  inputBalance * (exactOutputIdealBase nominalRatio ^ exponent - 1) /
    (1 - feeRate)

/-- Minimum-fee spot value after applying the path's actual fee denominator. -/
noncomputable def exactOutputAdjustedMinimumFeeInputValue
    (inputBalance feeRate exponent nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE * (inputBalance * exponent * nominalRatio) / (1 - feeRate)

/-- The corresponding fee scale in raw `c_pow` units. -/
noncomputable def exactOutputMinimumFeePowerValue
    (exponent nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE * ((BONE : ℝ) * exponent * nominalRatio)

/--
The precise path factors compose below this `4.501%` strict rational ceiling
on exact-output swap adverse approximation error.
-/
noncomputable def EXACT_OUTPUT_ADVERSE_FEE_SHARE : ℝ :=
  4501 / 100000

/-- The path-specific fractional recurrence budget relative to the minimum fee. -/
noncomputable def EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE : ℝ :=
  MIN_FEE_RATE * (30001 / 1000000)

theorem exact_output_adverse_fee_share_value :
    EXACT_OUTPUT_ADVERSE_FEE_SHARE = (4501 : ℝ) / 100000 := by
  rfl

theorem exact_output_precise_fractional_fee_rate_value :
    EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE = (30001 : ℝ) / 1000000000000 := by
  norm_num [EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE,
    MIN_FEE_RATE, MIN_FEE, STROOP]

/-- A normalized exact-output base ceiling is above both the ideal base and one. -/
theorem exact_output_base_ceil_refines
    {nominalRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hratio0 : 0 ≤ nominalRatio) (hratio1 : nominalRatio < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio)))) :
    exactOutputIdealBase nominalRatio ≤ computedBase ∧ 1 ≤ computedBase := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hdenom : 0 < 1 - nominalRatio := by linarith
  have hidealOne : 1 ≤ exactOutputIdealBase nominalRatio := by
    rw [exactOutputIdealBase]
    exact (one_le_div hdenom).2 (by linarith)
  constructor
  · rw [exactOutputIdealBase, hcomputedBase]
    exact hbaseCeil.le_normalized hB
  · exact le_trans hidealOne (by
      rw [exactOutputIdealBase, hcomputedBase]
      exact hbaseCeil.le_normalized hB)

/-- A normalized raw ceiling is no smaller than the exact weight ratio. -/
theorem exact_output_exponent_ceil_refines
    {idealExponent computedExponent : ℝ} {computedExponentRaw : ℤ}
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent)) :
    idealExponent ≤ computedExponent ∧
      computedExponent < idealExponent + 1 / (STROOP : ℝ) := by
  have hS : (0 : ℝ) < STROOP := by norm_num [STROOP]
  constructor
  · rw [hcomputedExponent]
    exact hexponentCeil.le_normalized hS
  · rw [hcomputedExponent]
    exact normalized_ceil_lt_exact_add_inv_scale hS hexponentCeil

/-- Ceiling both an above-one base and its exponent can only increase its power. -/
theorem exact_output_rounded_power_dominates_ideal
    {nominalRatio computedBase computedExponent idealExponent : ℝ}
    (hidealExponent0 : 0 ≤ idealExponent)
    (hbase : exactOutputIdealBase nominalRatio ≤ computedBase)
    (hidealBaseOne : 1 ≤ exactOutputIdealBase nominalRatio)
    (hexponent : idealExponent ≤ computedExponent) :
    exactOutputIdealBase nominalRatio ^ idealExponent ≤
      computedBase ^ computedExponent := by
  have hbase0 : 0 ≤ exactOutputIdealBase nominalRatio :=
    le_trans (by norm_num) hidealBaseOne
  calc
    exactOutputIdealBase nominalRatio ^ idealExponent ≤
        computedBase ^ idealExponent :=
      Real.rpow_le_rpow hbase0 hbase hidealExponent0
    _ ≤ computedBase ^ computedExponent :=
      Real.rpow_le_rpow_of_exponent_le (le_trans hidealBaseOne hbase) hexponent

/-- Three exact ceilings in the caller never understate the input implied by `c_pow`. -/
theorem exact_output_input_ceil_chain
    {tokenAmountIn adjustedInput output : ℤ}
    {inputBalance computedPower feeRate scale : ℝ}
    (hfeeUpper : feeRate < 1) (hscale : 0 < scale)
    (hmulCeil :
      IsCeil tokenAmountIn
        (inputBalance * (computedPower / (BONE : ℝ) - 1)))
    (hfeeCeil :
      IsCeil adjustedInput ((tokenAmountIn : ℝ) / (1 - feeRate)))
    (hdownscaleCeil : IsCeil output ((adjustedInput : ℝ) / scale)) :
    inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
        (1 - feeRate) ≤ (output : ℝ) := by
  have hfeeDenom : 0 < 1 - feeRate := by linarith
  have hmul := hmulCeil.le
  have hfeeScaled := (div_le_div_iff_of_pos_right hfeeDenom).2 hmul
  have hfee := hfeeCeil.le
  have hdownScaled := (div_le_div_iff_of_pos_right hscale).2 hfee
  have hdown := hdownscaleCeil.le
  calc
    inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
          (1 - feeRate) =
        (inputBalance * (computedPower / (BONE : ℝ) - 1) /
          (1 - feeRate)) / scale := by ring
    _ ≤ ((tokenAmountIn : ℝ) / (1 - feeRate)) / scale :=
      div_le_div_of_nonneg_right hfeeScaled hscale.le
    _ ≤ (adjustedInput : ℝ) / scale := hdownScaled
    _ ≤ (output : ℝ) := hdown

/--
Compose a raw `c_pow` error bound with the ideal exact-output formula and all
caller ceilings.  The resulting comparison is in the token's downscaled
unit and uses the path's actual fee-adjustment denominator.
-/
theorem swap_exact_amount_out_adverse_error_lt_fee_share
    {feeShare feeRate nominalRatio computedBase computedExponent idealExponent
      computedPower inputBalance scale computedInput : ℝ}
    (hfeeUpper : feeRate < 1)
    (hratio0 : 0 ≤ nominalRatio) (hratio1 : nominalRatio < 1)
    (hidealExponent0 : 0 ≤ idealExponent)
    (hbase : exactOutputIdealBase nominalRatio ≤ computedBase)
    (hexponent : idealExponent ≤ computedExponent)
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        feeShare * exactOutputMinimumFeePowerValue idealExponent nominalRatio)
    (hinputBalance : 0 < inputBalance) (hscale : 0 < scale)
    (hcomputedInput :
      inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
        (1 - feeRate) ≤ computedInput) :
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
        computedInput <
      feeShare * exactOutputAdjustedMinimumFeeInputValue
        (inputBalance / scale) feeRate idealExponent nominalRatio := by
  have hdenom : 0 < 1 - feeRate := by linarith
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hidealBaseOne : 1 ≤ exactOutputIdealBase nominalRatio := by
    rw [exactOutputIdealBase]
    exact (one_le_div (by linarith)).2 (by linarith)
  have hpowerDirection := exact_output_rounded_power_dominates_ideal
    hidealExponent0 hbase hidealBaseOne hexponent
  have hrawDirection :
      (BONE : ℝ) * exactOutputIdealBase nominalRatio ^ idealExponent ≤
        (BONE : ℝ) * computedBase ^ computedExponent := by
    exact mul_le_mul_of_nonneg_left hpowerDirection hB.le
  have hadversePower :
      (BONE : ℝ) * exactOutputIdealBase nominalRatio ^ idealExponent -
          computedPower <
        feeShare * exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
    linarith
  have hcallerScale : 0 < inputBalance / scale / (BONE : ℝ) / (1 - feeRate) :=
    div_pos (div_pos (div_pos hinputBalance hscale) hB) hdenom
  have hscaled := mul_lt_mul_of_pos_left hadversePower hcallerScale
  calc
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
          computedInput ≤
        exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
          (inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
            (1 - feeRate)) := sub_le_sub_left hcomputedInput _
    _ = (inputBalance / scale / (BONE : ℝ) / (1 - feeRate)) *
        ((BONE : ℝ) * exactOutputIdealBase nominalRatio ^ idealExponent -
          computedPower) := by
      rw [exactOutputIdealInput]
      field_simp [ne_of_gt hB, ne_of_gt hdenom, ne_of_gt hscale]
      ring
    _ < (inputBalance / scale / (BONE : ℝ) / (1 - feeRate)) *
        (feeShare * exactOutputMinimumFeePowerValue idealExponent nominalRatio) := hscaled
    _ = feeShare * exactOutputAdjustedMinimumFeeInputValue
          (inputBalance / scale) feeRate idealExponent nominalRatio := by
      rw [exactOutputMinimumFeePowerValue,
        exactOutputAdjustedMinimumFeeInputValue]
      field_simp [ne_of_gt hB, ne_of_gt hdenom, ne_of_gt hscale]
      ring

/-- Instantiate the operation theorem from the exact-output caller refinements. -/
theorem swap_exact_amount_out_from_fixed_point_refinements_fee_share
    {feeShare inputBalance outputBalance outputAmount nominalRatio feeRate computedBase
      idealExponent computedExponent computedPower scale : ℝ}
    {computedBaseRaw computedExponentRaw tokenAmountIn adjustedInput output : ℤ}
    (hinputBalance : 0 < inputBalance) (houtputBalance : 0 < outputBalance)
    (houtputAmount0 : 0 ≤ outputAmount)
    (hnominal : nominalRatio = outputAmount / outputBalance)
    (hratio1 : nominalRatio < 1) (hfeeUpper : feeRate < 1)
    (hidealExponent0 : 0 ≤ idealExponent)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        feeShare * exactOutputMinimumFeePowerValue idealExponent nominalRatio)
    (hscale : 0 < scale)
    (hmulCeil :
      IsCeil tokenAmountIn
        (inputBalance * (computedPower / (BONE : ℝ) - 1)))
    (hfeeCeil :
      IsCeil adjustedInput ((tokenAmountIn : ℝ) / (1 - feeRate)))
    (hdownscaleCeil : IsCeil output ((adjustedInput : ℝ) / scale)) :
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
        (output : ℝ) <
      feeShare * exactOutputAdjustedMinimumFeeInputValue
        (inputBalance / scale) feeRate idealExponent nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by
    rw [hnominal]
    positivity
  have hbase := exact_output_base_ceil_refines
    hratio0 hratio1 hcomputedBase hbaseCeil
  have hexponent := exact_output_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hinput := exact_output_input_ceil_chain
    hfeeUpper hscale hmulCeil hfeeCeil hdownscaleCeil
  exact swap_exact_amount_out_adverse_error_lt_fee_share
    hfeeUpper hratio0 hratio1 hidealExponent0 hbase.1 hexponent.1 hcpow
      hinputBalance hscale hinput

/-- The production exponent ceiling and maximum ideal ratio keep the integer part at most nine. -/
theorem exact_output_integer_part_le_nine
    {integerPart : ℕ} {a computedExponent idealExponent : ℝ}
    (ha0 : 0 ≤ a)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper :
      computedExponent < idealExponent + 1 / (STROOP : ℝ))
    (hidealExponentUpper : idealExponent ≤ 9) :
    integerPart ≤ 9 := by
  by_contra hnot
  have hm10 : 10 ≤ integerPart := by omega
  have hm10Real : (10 : ℝ) ≤ integerPart := by exact_mod_cast hm10
  rw [hcomputedExponentSplit] at hcomputedExponentUpper
  norm_num [STROOP] at hcomputedExponentUpper
  linarith

/-- The one-raw-unit exponent ceiling is below a one-millionth relative adjustment. -/
theorem exact_output_fractional_exponent_le_adjusted_ideal
    {integerPart : ℕ} {a computedExponent idealExponent : ℝ}
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper :
      computedExponent < idealExponent + 1 / (STROOP : ℝ))
    (hidealExponentLower : 1 / 9 ≤ idealExponent) :
    a < (1000001 / 1000000 : ℝ) * idealExponent := by
  have hinteger0 : (0 : ℝ) ≤ integerPart := by positivity
  have haComputed : a ≤ computedExponent := by
    rw [hcomputedExponentSplit]
    linarith
  have hceilingRelative :
      1 / (STROOP : ℝ) ≤ idealExponent / 1000000 := by
    norm_num [STROOP] at ⊢
    linarith
  calc
    a ≤ computedExponent := haComputed
    _ < idealExponent + 1 / (STROOP : ℝ) := hcomputedExponentUpper
    _ ≤ idealExponent + idealExponent / 1000000 := by linarith
    _ = (1000001 / 1000000 : ℝ) * idealExponent := by ring

/-- A base below `1.51` raised to a production integer part is below `64`. -/
theorem exact_output_whole_power_lt_sixty_four
    {integerPart : ℕ} {computedBase : ℝ}
    (hbase0 : 0 ≤ computedBase) (hbaseUpper : computedBase < 151 / 100)
    (hintegerPart : integerPart ≤ 9) :
    computedBase ^ integerPart < 64 := by
  have hbasePower : computedBase ^ integerPart ≤
      (151 / 100 : ℝ) ^ integerPart :=
    pow_le_pow_left₀ hbase0 (le_of_lt hbaseUpper) integerPart
  have hexponentPower : (151 / 100 : ℝ) ^ integerPart ≤
      (151 / 100 : ℝ) ^ 9 :=
    pow_le_pow_right₀ (by norm_num) hintegerPart
  calc
    computedBase ^ integerPart ≤ (151 / 100 : ℝ) ^ integerPart := hbasePower
    _ ≤ (151 / 100 : ℝ) ^ 9 := hexponentPower
    _ < 64 := by norm_num

/-- At ratios below `1e-5`, the rounded exact-output base remains below `1.02`. -/
theorem exact_output_small_ratio_computed_base_lt
    {nominalRatio computedBase : ℝ}
    (hratioSmall : nominalRatio < 1 / 100000)
    (hceil :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ)) :
    computedBase < 51 / 50 := by
  have hdenom : 99 / 100 < 1 - nominalRatio := by linarith
  have hdenom0 : 0 < 1 - nominalRatio := lt_trans (by norm_num) hdenom
  have hinverse : 1 / (1 - nominalRatio) < 100 / 99 := by
    apply (div_lt_iff₀ hdenom0).2
    nlinarith
  have hunit : 1 / (BONE : ℝ) < 1 / 1000 := by norm_num [BONE]
  linarith

/-- A base below `1.02` raised to a production integer part is below two. -/
theorem exact_output_small_whole_power_lt_two
    {integerPart : ℕ} {computedBase : ℝ}
    (hbase0 : 0 ≤ computedBase) (hbaseUpper : computedBase < 51 / 50)
    (hintegerPart : integerPart ≤ 9) :
    computedBase ^ integerPart < 2 := by
  have hbasePower : computedBase ^ integerPart ≤
      (51 / 50 : ℝ) ^ integerPart :=
    pow_le_pow_left₀ hbase0 (le_of_lt hbaseUpper) integerPart
  have hexponentPower : (51 / 50 : ℝ) ^ integerPart ≤
      (51 / 50 : ℝ) ^ 9 :=
    pow_le_pow_right₀ (by norm_num) hintegerPart
  calc
    computedBase ^ integerPart ≤ (51 / 50 : ℝ) ^ integerPart := hbasePower
    _ ≤ (51 / 50 : ℝ) ^ 9 := hexponentPower
    _ < 2 := by norm_num

/-- Upper-rounded whole-power and final multiplication composition. -/
theorem exact_output_upper_composition_adverse_le
    {wholeExact exactFractional wholeComputed computedFractional computedPower : ℝ}
    (hcomputedFractional0 : 0 ≤ computedFractional)
    (hwholeUpper : wholeExact ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * computedFractional ≤ computedPower) :
    wholeExact * exactFractional - computedPower ≤
      wholeExact * (exactFractional - computedFractional) := by
  have hproduct :
      wholeExact * computedFractional ≤ wholeComputed * computedFractional :=
    mul_le_mul_of_nonneg_right hwholeUpper hcomputedFractional0
  calc
    wholeExact * exactFractional - computedPower ≤
        wholeExact * exactFractional - wholeComputed * computedFractional :=
      sub_le_sub_left hcomposedUpper _
    _ ≤ wholeExact * exactFractional - wholeExact * computedFractional :=
      sub_le_sub_left hproduct _
    _ = wholeExact * (exactFractional - computedFractional) := by ring

/-- The precise output displacement leaves a `3.0001%` fractional fee-rate budget. -/
theorem accumulated_error_lt_exact_output_precise_fractional_fee_of_later_terms
    {n : ℕ} {firstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * ((500001 : ℝ) / 1000000 / 2) *
            ((500001 : ℝ) / 1000000) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n <
      EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE * firstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE,
      MIN_FEE_RATE, MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- The same precise continuation estimate forces the first term above precision. -/
theorem exact_output_precise_continuation_forces_first_term_above_precision
    {n : ℕ} {firstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * ((500001 : ℝ) / 1000000 / 2) *
            ((500001 : ℝ) / 1000000) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    (CPOW_PRECISION : ℝ) < firstTerm := by
  interval_cases n <;>
    norm_num [CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- The precise base and exponent ceilings retain the `4.501%` margin. -/
theorem exact_output_weighted_first_term_fee_scale_lt_precise_share
    {weightedFraction idealExponent displacement nominalRatio : ℝ}
    (hweighted :
      weightedFraction ≤ (1000001 / 1000000 : ℝ) * idealExponent)
    (hidealPositive : 0 < idealExponent)
    (hratioPositive : 0 < nominalRatio)
    (hdisplacement0 : 0 ≤ displacement)
    (hdisplacement :
      displacement ≤ (1500001 / 1000000 : ℝ) * nominalRatio) :
    EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
        ((BONE : ℝ) * weightedFraction * displacement) <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
  have hproduct :
      weightedFraction * displacement ≤
        ((1000001 / 1000000 : ℝ) * idealExponent) *
          ((1500001 / 1000000 : ℝ) * nominalRatio) :=
    mul_le_mul hweighted hdisplacement hdisplacement0
      (mul_nonneg (by norm_num) (le_of_lt hidealPositive))
  have hB0 : (0 : ℝ) ≤ BONE := by norm_num [BONE]
  have hscaled :
      (BONE : ℝ) * weightedFraction * displacement ≤
        (BONE : ℝ) *
          (((1000001 / 1000000 : ℝ) * idealExponent) *
            ((1500001 / 1000000 : ℝ) * nominalRatio)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hproduct hB0]
  have hrate0 : 0 ≤ EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE := by
    rw [exact_output_precise_fractional_fee_rate_value]
    norm_num
  have hscaleUpper := mul_le_mul_of_nonneg_left hscaled hrate0
  have hpositive : 0 < (BONE : ℝ) * idealExponent * nominalRatio :=
    mul_pos (mul_pos (by norm_num [BONE]) hidealPositive) hratioPositive
  have hconstant :
      EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((1000001 / 1000000 : ℝ) * (1500001 / 1000000 : ℝ)) <
        EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
    rw [exact_output_precise_fractional_fee_rate_value,
      exact_output_adverse_fee_share_value, minimum_fee_rate_value]
    norm_num
  have hstrict := mul_lt_mul_of_pos_right hconstant hpositive
  rw [exactOutputMinimumFeePowerValue]
  calc
    EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((BONE : ℝ) * weightedFraction * displacement) ≤
        EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((BONE : ℝ) *
            (((1000001 / 1000000 : ℝ) * idealExponent) *
              ((1500001 / 1000000 : ℝ) * nominalRatio))) := hscaleUpper
    _ = (EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((1000001 / 1000000 : ℝ) * (1500001 / 1000000 : ℝ))) *
        ((BONE : ℝ) * idealExponent * nominalRatio) := by ring
    _ < (EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
        ((BONE : ℝ) * idealExponent * nominalRatio) := hstrict
    _ = EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        (MIN_FEE_RATE * ((BONE : ℝ) * idealExponent * nominalRatio)) := by ring

/-
For small output ratios the whole power is below two, and `whole * a` is
bounded by the full exponent. For larger ratios the universal raw rounding
cap (`3151`) is already below the precise fee share.
-/

/-- Compose a later fractional exact-output bound through the whole baseline `c_pow`. -/
theorem baseline_exact_output_cpow_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {a computedExponent idealExponent computedBase nominalRatio
      computedFractional wholeComputed computedPower : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hcomputedExponentUpper :
      computedExponent < idealExponent + 1 / (STROOP : ℝ))
    (hintegerPart : integerPart ≤ 9)
    (hratioPositive : 0 < nominalRatio)
    (hbaseOne : 1 ≤ computedBase)
    (hbaseUpper : computedBase < 151 / 100)
    (hbaseCeilUpper :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ))
    (hdisplacement :
      computedBase - 1 ≤ (1500001 / 1000000 : ℝ) * nominalRatio)
    (hcomputedFractional0 : 0 ≤ computedFractional)
    (hwholeUpper : computedBase ^ integerPart ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * computedFractional ≤ computedPower)
    (hfractionalFee :
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((BONE : ℝ) * a * (computedBase - 1)))
    (hfractionalCap :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 3151) :
    (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
  let wholeExact : ℝ := computedBase ^ integerPart
  let exactFractional : ℝ := (BONE : ℝ) * computedBase ^ a
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbaseOne
  have hwhole0 : 0 < wholeExact := by
    dsimp [wholeExact]
    positivity
  have hcomposition :
      wholeExact * exactFractional - computedPower ≤
        wholeExact * (exactFractional - computedFractional) :=
    exact_output_upper_composition_adverse_le hcomputedFractional0
      hwholeUpper hcomposedUpper
  have hexact :
      (BONE : ℝ) * computedBase ^ computedExponent =
        wholeExact * exactFractional := by
    dsimp [wholeExact, exactFractional]
    rw [hcomputedExponentSplit, Real.rpow_add hbase0]
    norm_num [Real.rpow_natCast]
    ring
  rw [hexact]
  have hidealPositive : 0 < idealExponent := lt_of_lt_of_le (by norm_num) hidealExponentLower
  have hdisplacement0 : 0 ≤ computedBase - 1 := sub_nonneg.mpr hbaseOne
  by_cases hintegerZero : integerPart = 0
  · subst integerPart
    have hwhole : wholeExact = 1 := by simp [wholeExact]
    have haAdjusted := exact_output_fractional_exponent_le_adjusted_ideal
      hcomputedExponentSplit hcomputedExponentUpper hidealExponentLower
    have hfeeScale := exact_output_weighted_first_term_fee_scale_lt_precise_share
      (le_of_lt haAdjusted) hidealPositive hratioPositive
        hdisplacement0 hdisplacement
    have hscaledFractional :
        wholeExact * (exactFractional - computedFractional) <
          EXACT_OUTPUT_ADVERSE_FEE_SHARE *
            exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
      rw [hwhole]
      norm_num
      exact lt_trans hfractionalFee hfeeScale
    exact lt_of_le_of_lt hcomposition hscaledFractional
  · have hintegerOne : 1 ≤ integerPart := Nat.one_le_iff_ne_zero.mpr hintegerZero
    by_cases hratioSmall : nominalRatio < 1 / 100000
    · have hsmallBase := exact_output_small_ratio_computed_base_lt
        hratioSmall hbaseCeilUpper
      have hwholeTwo := exact_output_small_whole_power_lt_two
        hbase0.le hsmallBase hintegerPart
      have hintegerReal : (1 : ℝ) ≤ integerPart := by exact_mod_cast hintegerOne
      have htwoA : 2 * a ≤ (integerPart : ℝ) + a := by linarith
      have hwholeA : wholeExact * a ≤ (integerPart : ℝ) + a := by
        have haNonneg := ha0
        have hmul : wholeExact * a ≤ 2 * a :=
          mul_le_mul_of_nonneg_right (le_of_lt hwholeTwo) haNonneg
        exact le_trans hmul htwoA
      have hweightedAdjusted :
          wholeExact * a ≤ (1000001 / 1000000 : ℝ) * idealExponent := by
        have hcomputedAdjusted :
            computedExponent < (1000001 / 1000000 : ℝ) * idealExponent := by
          have hceilingRelative :
              1 / (STROOP : ℝ) ≤ idealExponent / 1000000 := by
            norm_num [STROOP] at ⊢
            linarith
          calc
            computedExponent < idealExponent + 1 / (STROOP : ℝ) :=
              hcomputedExponentUpper
            _ ≤ idealExponent + idealExponent / 1000000 := by linarith
            _ = (1000001 / 1000000 : ℝ) * idealExponent := by ring
        rw [← hcomputedExponentSplit] at hwholeA
        exact le_trans hwholeA (le_of_lt hcomputedAdjusted)
      have hfeeScale := exact_output_weighted_first_term_fee_scale_lt_precise_share
        hweightedAdjusted hidealPositive hratioPositive
          hdisplacement0 hdisplacement
      have hscaledFractional := mul_lt_mul_of_pos_left hfractionalFee hwhole0
      have hrearrange :
          wholeExact *
              (EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
                ((BONE : ℝ) * a * (computedBase - 1))) =
            EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
              ((BONE : ℝ) * (wholeExact * a) * (computedBase - 1)) := by ring
      rw [hrearrange] at hscaledFractional
      exact lt_of_le_of_lt hcomposition (lt_trans hscaledFractional hfeeScale)
    · have hratioLarge : 1 / 100000 ≤ nominalRatio := le_of_not_gt hratioSmall
      have hwhole64 := exact_output_whole_power_lt_sixty_four
        hbase0.le hbaseUpper hintegerPart
      have hscaledCap := mul_lt_mul_of_pos_left hfractionalCap hwhole0
      have hcap : wholeExact * (exactFractional - computedFractional) < 64 * 3151 := by
        have hsecond : wholeExact * 3151 < 64 * 3151 :=
          mul_lt_mul_of_pos_right hwhole64 (by norm_num)
        exact lt_trans hscaledCap hsecond
      have hintegerReal : (1 : ℝ) ≤ integerPart := by exact_mod_cast hintegerOne
      have hcomputedAtLeastOne : (1 : ℝ) ≤ computedExponent := by
        rw [hcomputedExponentSplit]
        exact le_add_of_le_of_nonneg hintegerReal ha0
      have hidealNineTenths : (9 / 10 : ℝ) < idealExponent := by
        norm_num [STROOP] at hcomputedExponentUpper
        linarith
      have hproductLower :
          (9 / 10 : ℝ) * (1 / 100000 : ℝ) <
            idealExponent * nominalRatio := by
        have hfirst := mul_lt_mul_of_pos_right hidealNineTenths (by norm_num : (0 : ℝ) < 1 / 100000)
        have hsecond := mul_le_mul_of_nonneg_left hratioLarge (le_of_lt hidealPositive)
        nlinarith
      have hfeeLarge :
          (400000 : ℝ) <
            EXACT_OUTPUT_ADVERSE_FEE_SHARE *
              exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
        rw [exact_output_adverse_fee_share_value,
          exactOutputMinimumFeePowerValue, minimum_fee_rate_value]
        norm_num [BONE] at ⊢
        nlinarith
      have hnumeric : (64 : ℝ) * 3151 < 400000 := by norm_num
      exact lt_of_le_of_lt hcomposition
        (lt_trans hcap (lt_trans hnumeric hfeeLarge))

/-- The accumulated raw recurrence budget is at most `3151` through iteration 46. -/
theorem accumulated_error_le_3151 {n : ℕ} (hn : n ≤ 46) :
    accumulatedError n ≤ 3151 := by
  have hnReal : (n : ℝ) ≤ 46 := by exact_mod_cast hn
  have hsecond : 0 ≤ 3 * (46 + (n : ℝ)) - 1 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hgap : 0 ≤ (46 - (n : ℝ)) * (3 * (46 + (n : ℝ)) - 1) :=
    mul_nonneg (sub_nonneg.mpr hnReal) hsecond
  rw [accumulatedError]
  nlinarith only [hgap]

/-- The closed-form recurrence budget is monotone from the first term onward. -/
theorem accumulated_error_mono
    {degree n : ℕ} (hdegree1 : 1 ≤ degree) (hdegreeN : degree ≤ n) :
    accumulatedError degree ≤ accumulatedError n := by
  have hdegreeReal : (1 : ℝ) ≤ degree := by exact_mod_cast hdegree1
  have horderReal : (degree : ℝ) ≤ n := by exact_mod_cast hdegreeN
  have hfactor : 0 ≤ 3 * ((n : ℝ) + degree) - 1 := by linarith
  have hgap :
      0 ≤ ((n : ℝ) - degree) * (3 * ((n : ℝ) + degree) - 1) :=
    mul_nonneg (sub_nonneg.mpr horderReal) hfactor
  rw [accumulatedError, accumulatedError]
  nlinarith only [hgap]

/-
This theorem instantiates the baseline recurrence for every later exact-output
stop.  `degree = n` models an odd final term.  `degree + 1 = n` models an
even final term that the implementation removes, leaving the preceding odd
Taylor partial.
-/

/-- Full later-term baseline `c_pow` bound for the exact-output configuration. -/
theorem baseline_exact_output_cpow_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n degree oddIndex integerPart : ℕ}
    {nominalRatio computedBase idealExponent computedExponent a
      computedFractional wholeComputed computedPower : ℝ}
    {computedBaseRaw computedExponentRaw computedPowerRaw : ℤ}
    (hratio0 : 0 ≤ nominalRatio)
    (hratioPositive : 0 < nominalRatio)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hidealExponentUpper : idealExponent ≤ 9)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hn3 : 3 ≤ n)
    (hn50 : n ≤ 50)
    (hdegreeOdd : degree = 2 * oddIndex + 1)
    (hdegreeStop : degree = n ∨ degree + 1 = n)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1) (exactOutputBinomialTerm a computedBase 1))
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
        ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw (wholeComputed * computedFractional)) :
    (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hbase := exact_output_base_ceil_refines
    hratio0 hratio1 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbase.2
  have hceilUpper :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ) := by
    rw [hcomputedBase]
    exact normalized_ceil_lt_exact_add_inv_scale
      (by norm_num [BONE]) hbaseCeil
  have hbaseDisplacement := configured_exact_output_computed_displacement_lt_precise
    hratioUpper hbase.2 hceilUpper
  let T : ℕ → ℝ := exactOutputBinomialTerm a computedBase
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  have hrec : ∀ k,
      T (k + 1) =
        T k * (a - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactOutputBinomialTerm_succ a computedBase k
  have hfirstExact : T 1 = (BONE : ℝ) * a * (computedBase - 1) := by
    exact exactOutputBinomialTerm_one a computedBase
  have hfirstNonnegative : 0 ≤ T 1 := by
    rw [hfirstExact]
    exact mul_nonneg (mul_nonneg (by norm_num [BONE]) ha0)
      (sub_nonneg.mpr hbase.2)
  have hfirstMagnitude : |T 1| = (BONE : ℝ) * a * (computedBase - 1) := by
    rw [abs_of_nonneg hfirstNonnegative, hfirstExact]
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [T, U]
    exact hfirstFloor.abs_error_lt_one
  have hfirstBelowScale : |T 1| < BONE := by
    rw [hfirstMagnitude]
    have hproduct : a * (computedBase - 1) < 1 := by
      have hq : computedBase - 1 < 500001 / 1000000 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hbase.2)] at hbaseDisplacement
        exact hbaseDisplacement
      have hmul : a * (computedBase - 1) ≤ 1 * (computedBase - 1) :=
        mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr hbase.2)
      linarith
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    simpa only [mul_assoc, mul_one] using mul_lt_mul_of_pos_left hproduct hB
  have hx : |computedBase - 1| ≤ (500001 / 1000000 : ℝ) :=
    le_of_lt hbaseDisplacement
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T ha0 ha1 hx hrec (k - 1)
    have hindex : k - 1 + 1 = k := by omega
    rw [hindex] at hterms
    have hpower1 : (500001 / 1000000 : ℝ) ^ (k - 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hscale : |T 1| * (500001 / 1000000 : ℝ) ^ (k - 1) ≤ |T 1| := by
      nlinarith [abs_nonneg (T 1)]
    exact lt_of_le_of_lt (le_trans hterms hscale) hfirstBelowScale
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
    have hstep := three_floor_recurrence_step_error
      (S := (BONE : ℝ)) (K := (k : ℝ) + 1)
      (exactPrevious := T k) (computedPrevious := U k)
      (coefficient := a - (k : ℝ)) (displacement := computedBase - 1)
      (coefficientProduct := coefficientProduct (k + 1))
      (multiplied := multiplied (k + 1))
      (nextComputed := computedTerm (k + 1))
      (by norm_num [BONE]) (by positivity) hcoefficientBound
      (le_trans hx (by norm_num)) (hexactTermMagnitude k hk)
      (hcoefficientFloor k hk hkn)
      (by simpa [U] using hmultiplyTermFloor k hk hkn)
      (hdivideTermFloor k hk hkn)
    rw [hrec k]
    simpa [U, Nat.cast_add, Nat.cast_one, add_assoc] using hstep
  have htermBounds := recurrence_error_budget_until (BONE : ℝ)
    (fun k ↦ |T k - U k|) hn50 (by norm_num [BONE]) hfirstError herrorRec
  have htermZero : |T 0| ≤ (BONE : ℝ) := by
    dsimp [T]
    simp
  have hbaseUpperOperating : computedBase ≤ (8 / 5 : ℝ) := by
    have hq : computedBase - 1 < 500001 / 1000000 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbase.2)] at hbaseDisplacement
      exact hbaseDisplacement
    linarith
  have hn46 : n ≤ 46 := by
    by_contra hn
    have herror46 : |T 46 - U 46| < 3 * (46 : ℝ) - 2 :=
      htermBounds 46 (by norm_num) (by omega)
    have hstopsBy46 : |U 46| < (CPOW_PRECISION : ℝ) :=
      pool_operating_base_converges_by_iteration_46
        T ha0 ha1 (by linarith : (1 / 2 : ℝ) ≤ computedBase)
          hbaseUpperOperating
          htermZero hrec herror46
    have hstillRunning := hcontinued 46 (by norm_num) (by omega)
    dsimp [U] at hstopsBy46
    linarith
  have hprevious :
      (CPOW_PRECISION : ℝ) < |U (n - 1)| := by
    simpa [U] using hcontinued (n - 1) (by omega) (by omega)
  have htermError :
      |T (n - 1) - U (n - 1)| < 3 * ((n - 1 : ℕ) : ℝ) - 2 :=
    htermBounds (n - 1) (by omega) (by omega)
  have hcontinue := continued_loop_forces_sharp_first_term_scale
    T ha0 ha1 hx (by norm_num) hrec hn3 hprevious htermError
  have hfirstLarge : (CPOW_PRECISION : ℝ) < |T 1| :=
    exact_output_precise_continuation_forces_first_term_above_precision
      hn3 hn46 (by simpa using hcontinue)
  have hbaseStrict : 1 < computedBase := by
    have hpositiveProduct : 0 < a * (computedBase - 1) := by
      rw [hfirstMagnitude] at hfirstLarge
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      have hprecision : (0 : ℝ) ≤ CPOW_PRECISION := by positivity
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hbase.2)]
    by_contra hnot
    have hbaseLe : computedBase ≤ 1 := le_of_not_gt hnot
    have hproductNonpos : a * (computedBase - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha0 (sub_nonpos.mpr hbaseLe)
    linarith
  let exactPartial : ℝ :=
    ∑ k ∈ Finset.range (degree + 1), exactOutputBinomialTerm a computedBase k
  have hpartialUpper : (BONE : ℝ) * computedBase ^ a ≤ exactPartial := by
    dsimp [exactPartial]
    rw [hdegreeOdd]
    exact exact_output_binomial_odd_partial_upper ha0 ha1 hbaseStrict oddIndex
  have hexactPartial :
      exactPartial = (BONE : ℝ) + ∑ k ∈ Finset.range degree, T (k + 1) := by
    dsimp [exactPartial, T]
    rw [Finset.sum_range_succ']
    simp
    ring
  have hdegree1 : 1 ≤ degree := by rw [hdegreeOdd]; omega
  have hdegreeN : degree ≤ n := by rcases hdegreeStop with h | h <;> omega
  have hdegree50 : degree ≤ 50 := le_trans hdegreeN hn50
  have hsumRaw := recurrence_implies_partial_sum_error_budget_until
    (BONE : ℝ) T U hdegree1 hdegree50 (by norm_num [BONE]) hfirstError
      (fun k hk hdegree ↦ herrorRec k hk (lt_of_lt_of_le hdegree hdegreeN))
  have hsum : |exactPartial - computedFractional| < accumulatedError degree := by
    rw [hexactPartial, hcomputedFractional, accumulatedError]
    convert hsumRaw using 1
    simp [U, Nat.add_comm]
  have herrorMono := accumulated_error_mono hdegree1 hdegreeN
  have hbudget := accumulated_error_lt_exact_output_precise_fractional_fee_of_later_terms
    hn3 hn46 (by simpa using hcontinue)
  have hfractionalFee :
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((BONE : ℝ) * a * (computedBase - 1)) := by
    have hadverse :
        (BONE : ℝ) * computedBase ^ a - computedFractional <
          accumulatedError degree := by
      have hpartialDifference :
          exactPartial - computedFractional < accumulatedError degree :=
        lt_of_le_of_lt (le_abs_self _) hsum
      linarith
    rw [← hfirstMagnitude]
    exact lt_of_lt_of_le hadverse (le_trans herrorMono (le_of_lt hbudget))
  have hfractionalCap :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 3151 := by
    have hadverse :
        (BONE : ℝ) * computedBase ^ a - computedFractional <
          accumulatedError degree := by
      have hpartialDifference :
          exactPartial - computedFractional < accumulatedError degree :=
        lt_of_le_of_lt (le_abs_self _) hsum
      linarith
    exact lt_of_lt_of_le hadverse
      (le_trans herrorMono (accumulated_error_le_3151 hn46))
  have hpartialLower : (BONE : ℝ) ≤ exactPartial := by
    have hpowerOne : 1 ≤ computedBase ^ a :=
      Real.one_le_rpow hbase.2 ha0
    have hscaled := mul_le_mul_of_nonneg_left hpowerOne
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
    exact le_trans (by simpa using hscaled) hpartialUpper
  have hcomputedFractional0 : 0 ≤ computedFractional := by
    have hpartialDifference :
        exactPartial - computedFractional < accumulatedError degree :=
      lt_of_le_of_lt (le_abs_self _) hsum
    have hdegreeCap := le_trans herrorMono (accumulated_error_le_3151 hn46)
    have hmargin : (3151 : ℝ) < BONE := by norm_num [BONE]
    linarith
  have hratioLower := continued_exact_output_forces_nominal_ratio_lower_sharp
    hratio0 hratioUpper hbase.2 hceilUpper ha1 hfirstMagnitude hfirstLarge
  have hdisplacement := configured_continued_exact_output_displacement_le_precise
    hratioLower hratioUpper hceilUpper
  have hbaseUpper : computedBase < 151 / 100 := by
    have hq := hbaseDisplacement
    rw [abs_of_nonneg (sub_nonneg.mpr hbase.2)] at hq
    linarith only [hq]
  have hexponent := exact_output_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hintegerPart := exact_output_integer_part_le_nine
    ha0 hcomputedExponentSplit hexponent.2 hidealExponentUpper
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hcomposedUpper : wholeComputed * computedFractional ≤ computedPower := by
    rw [hcomputedPower]
    exact hcomposedCeil.le
  exact baseline_exact_output_cpow_adverse_error_lt_precise_fee_share
    ha0 ha1 hcomputedExponentSplit hidealExponentLower hexponent.2
      hintegerPart hratioPositive hbase.2 hbaseUpper hceilUpper hdisplacement
      hcomputedFractional0 hwholeUpper hcomposedUpper hfractionalFee hfractionalCap

/-- Complete later-term `swap_exact_amount_out` comparison for the modeled caller. -/
theorem baseline_swap_exact_amount_out_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n degree oddIndex integerPart : ℕ}
    {inputBalance outputBalance outputAmount nominalRatio feeRate computedBase
      idealExponent computedExponent a computedFractional wholeComputed
      computedPower scale : ℝ}
    {computedBaseRaw computedExponentRaw computedPowerRaw tokenAmountIn
      adjustedInput output : ℤ}
    (hinputBalance : 0 < inputBalance) (houtputBalance : 0 < outputBalance)
    (houtputAmount : 0 < outputAmount)
    (hnominal : nominalRatio = outputAmount / outputBalance)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hfeeUpper : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hidealExponentUpper : idealExponent ≤ 9)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hn3 : 3 ≤ n)
    (hn50 : n ≤ 50)
    (hdegreeOdd : degree = 2 * oddIndex + 1)
    (hdegreeStop : degree = n ∨ degree + 1 = n)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1) (exactOutputBinomialTerm a computedBase 1))
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
        ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw (wholeComputed * computedFractional))
    (hscale : 0 < scale)
    (hmulCeil :
      IsCeil tokenAmountIn
        (inputBalance * (computedPower / (BONE : ℝ) - 1)))
    (hfeeCeil :
      IsCeil adjustedInput ((tokenAmountIn : ℝ) / (1 - feeRate)))
    (hdownscaleCeil : IsCeil output ((adjustedInput : ℝ) / scale)) :
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
        (output : ℝ) <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputAdjustedMinimumFeeInputValue
          (inputBalance / scale) feeRate idealExponent nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hcpow := baseline_exact_output_cpow_later_adverse_error_lt_precise_fee_share
    coefficientProduct multiplied computedTerm hratio0 hratioPositive
      hratioUpper hcomputedBase hbaseCeil hidealExponentLower
      hidealExponentUpper hcomputedExponent hexponentCeil ha0 ha1
      hcomputedExponentSplit hn3 hn50 hdegreeOdd hdegreeStop hcontinued
      hfirstFloor hcoefficientFloor hmultiplyTermFloor hdivideTermFloor
      hcomputedFractional hwholeTrace hcomputedPower hcomposedCeil
  exact swap_exact_amount_out_from_fixed_point_refinements_fee_share
    (feeShare := EXACT_OUTPUT_ADVERSE_FEE_SHARE)
    hinputBalance houtputBalance houtputAmount.le hnominal hratio1 hfeeUpper
      (lt_of_lt_of_le (by norm_num) hidealExponentLower).le hcomputedBase
      hbaseCeil hcomputedExponent hexponentCeil hcpow hscale hmulCeil
      hfeeCeil hdownscaleCeil

/-- Concavity makes the positive linear term an upper bound for the fractional power. -/
theorem exact_output_fractional_first_order_upper
    {a computedBase : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hbase0 : 0 ≤ computedBase) :
    (BONE : ℝ) * computedBase ^ a ≤
      (BONE : ℝ) + (BONE : ℝ) * a * (computedBase - 1) := by
  have hbernoulli := rpow_one_add_le_one_add_mul_self
    (s := computedBase - 1) (by linarith) ha0 ha1
  have hscaled := mul_le_mul_of_nonneg_left hbernoulli
    (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  norm_num at hscaled
  nlinarith

/-- The first-term `+1` correction remains conservative through full `c_pow` composition. -/
theorem baseline_exact_output_cpow_first_term_has_no_adverse_error
    {integerPart : ℕ}
    {a computedExponent computedBase wholeComputed computedPower : ℝ}
    {firstRounded computedPowerRaw : ℤ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hbase0 : 0 < computedBase)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ) + 1))) :
    (BONE : ℝ) * computedBase ^ computedExponent ≤ computedPower := by
  have hpartialUpper := exact_output_fractional_first_order_upper
    ha0 ha1 hbase0.le
  have hfractional :
      (BONE : ℝ) * computedBase ^ a ≤
        (BONE : ℝ) + (firstRounded : ℝ) + 1 := by
    calc
      (BONE : ℝ) * computedBase ^ a ≤
          (BONE : ℝ) + (BONE : ℝ) * a * (computedBase - 1) :=
        hpartialUpper
      _ ≤ (BONE : ℝ) + (firstRounded : ℝ) + 1 := by
        exact le_of_lt (by linarith [hfirstFloor.lt_add_one])
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hproduct := mul_upper_bound
    (pow_nonneg hbase0.le integerPart)
    (mul_nonneg (by norm_num [BONE]) (Real.rpow_nonneg hbase0.le a))
    hwholeUpper hfractional
  have hcomposed :
      wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ) + 1) ≤
        computedPower := by
    rw [hcomputedPower]
    exact hcomposedCeil.le
  have hexact :
      (BONE : ℝ) * computedBase ^ computedExponent =
        computedBase ^ integerPart * ((BONE : ℝ) * computedBase ^ a) := by
    rw [hcomputedExponentSplit, Real.rpow_add hbase0]
    norm_num [Real.rpow_natCast]
    ring
  rw [hexact]
  exact le_trans hproduct hcomposed

/-- At the second stop, removal of the negative term leaves less than the first floor unit. -/
theorem baseline_exact_output_cpow_second_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {nominalRatio computedBase idealExponent computedExponent a
      wholeComputed computedPower : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw : ℤ}
    (hratio0 : 0 ≤ nominalRatio)
    (hratioPositive : 0 < nominalRatio)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hidealExponentUpper : idealExponent ≤ 9)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hcontinued : (CPOW_PRECISION : ℝ) < (firstRounded : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ)))) :
    (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hbase := exact_output_base_ceil_refines
    hratio0 hratio1 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbase.2
  have hceilUpper :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ) := by
    rw [hcomputedBase]
    exact normalized_ceil_lt_exact_add_inv_scale
      (by norm_num [BONE]) hbaseCeil
  have hfirstLarge :
      (CPOW_PRECISION : ℝ) < (BONE : ℝ) * a * (computedBase - 1) :=
    positive_floor_above_threshold hfirstFloor hcontinued
  have hratioLower := continued_exact_output_forces_nominal_ratio_lower_sharp
    hratio0 hratioUpper hbase.2 hceilUpper ha1 rfl hfirstLarge
  have hdisplacement := configured_continued_exact_output_displacement_le_precise
    hratioLower hratioUpper hceilUpper
  have hbaseDisplacement := configured_exact_output_computed_displacement_lt_precise
    hratioUpper hbase.2 hceilUpper
  have hbaseUpper : computedBase < 151 / 100 := by
    have hq := hbaseDisplacement
    rw [abs_of_nonneg (sub_nonneg.mpr hbase.2)] at hq
    linarith only [hq]
  have hpartialUpper := exact_output_fractional_first_order_upper
    ha0 ha1 hbase0.le
  let computedFractional : ℝ := (BONE : ℝ) + (firstRounded : ℝ)
  have hfractionalOne :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 1 := by
    dsimp [computedFractional]
    have hrounding :
        (BONE : ℝ) + (BONE : ℝ) * a * (computedBase - 1) -
          ((BONE : ℝ) + (firstRounded : ℝ)) < 1 := by
      linarith [hfirstFloor.lt_add_one]
    linarith
  have honeFee :
      (1 : ℝ) < EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
        ((BONE : ℝ) * a * (computedBase - 1)) := by
    rw [exact_output_precise_fractional_fee_rate_value]
    norm_num [CPOW_PRECISION] at hfirstLarge ⊢
    linarith
  have hfractionalFee :
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        EXACT_OUTPUT_PRECISE_FRACTIONAL_FEE_RATE *
          ((BONE : ℝ) * a * (computedBase - 1)) :=
    lt_trans hfractionalOne honeFee
  have hfractionalCap :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 3151 :=
    lt_trans hfractionalOne (by norm_num)
  have hcomputedFractional0 : 0 ≤ computedFractional := by
    dsimp [computedFractional]
    have hrounded0 : (0 : ℝ) ≤ firstRounded := by
      linarith [show (0 : ℝ) ≤ CPOW_PRECISION by positivity]
    positivity
  have hexponent := exact_output_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hintegerPart := exact_output_integer_part_le_nine
    ha0 hcomputedExponentSplit hexponent.2 hidealExponentUpper
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hcomposedUpper : wholeComputed * computedFractional ≤ computedPower := by
    dsimp [computedFractional]
    rw [hcomputedPower]
    exact hcomposedCeil.le
  exact baseline_exact_output_cpow_adverse_error_lt_precise_fee_share
    ha0 ha1 hcomputedExponentSplit hidealExponentLower hexponent.2
      hintegerPart hratioPositive hbase.2 hbaseUpper hceilUpper hdisplacement
      hcomputedFractional0 hwholeUpper hcomposedUpper hfractionalFee hfractionalCap

/-- An integer-only upper-rounded `c_powi` exact-output result has no adverse error. -/
theorem baseline_exact_output_cpow_integer_has_no_adverse_error
    {integerPart : ℕ} {computedBase computedPower : ℝ}
    (hbase0 : 0 ≤ computedBase)
    (hwholeTrace :
      UpperCPowiTrace computedBase integerPart (computedPower / (BONE : ℝ))) :
    (BONE : ℝ) * computedBase ^ (integerPart : ℝ) ≤ computedPower := by
  have hwhole := hwholeTrace.upper_bound hbase0
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hscaled := (le_div_iff₀ hB).mp hwhole
  simpa [Real.rpow_natCast, mul_comm] using hscaled

/-- Positive exponent and output ratio make the exact-output fee power scale positive. -/
theorem exact_output_minimum_fee_power_value_positive
    {exponent nominalRatio : ℝ}
    (hexponent : 0 < exponent) (hratio : 0 < nominalRatio) :
    0 < exactOutputMinimumFeePowerValue exponent nominalRatio := by
  rw [exactOutputMinimumFeePowerValue, minimum_fee_rate_value]
  exact mul_pos (by norm_num)
    (mul_pos (mul_pos (by norm_num [BONE]) hexponent) hratio)

/-- Complete first-term exact-output comparison; its corrected `c_pow` is conservative. -/
theorem baseline_swap_exact_amount_out_first_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {inputBalance outputBalance outputAmount nominalRatio feeRate computedBase
      idealExponent computedExponent a wholeComputed computedPower scale : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      tokenAmountIn adjustedInput output : ℤ}
    (hinputBalance : 0 < inputBalance) (houtputBalance : 0 < outputBalance)
    (houtputAmount : 0 < outputAmount)
    (hnominal : nominalRatio = outputAmount / outputBalance)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hfeeUpper : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ) + 1)))
    (hscale : 0 < scale)
    (hmulCeil :
      IsCeil tokenAmountIn
        (inputBalance * (computedPower / (BONE : ℝ) - 1)))
    (hfeeCeil :
      IsCeil adjustedInput ((tokenAmountIn : ℝ) / (1 - feeRate)))
    (hdownscaleCeil : IsCeil output ((adjustedInput : ℝ) / scale)) :
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
        (output : ℝ) <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputAdjustedMinimumFeeInputValue
          (inputBalance / scale) feeRate idealExponent nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hbase := exact_output_base_ceil_refines
    hratio0 hratio1 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbase.2
  have hconservative := baseline_exact_output_cpow_first_term_has_no_adverse_error
    ha0 ha1 hcomputedExponentSplit hbase0 hfirstFloor hwholeTrace
      hcomputedPower hcomposedCeil
  have hidealPositive : 0 < idealExponent :=
    lt_of_lt_of_le (by norm_num) hidealExponentLower
  have hfeePositive := exact_output_minimum_fee_power_value_positive
    hidealPositive hratioPositive
  have hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        EXACT_OUTPUT_ADVERSE_FEE_SHARE *
          exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
    have hshare :
        0 < EXACT_OUTPUT_ADVERSE_FEE_SHARE *
          exactOutputMinimumFeePowerValue idealExponent nominalRatio :=
      mul_pos (by rw [exact_output_adverse_fee_share_value]; norm_num) hfeePositive
    linarith
  exact swap_exact_amount_out_from_fixed_point_refinements_fee_share
    (feeShare := EXACT_OUTPUT_ADVERSE_FEE_SHARE)
    hinputBalance houtputBalance houtputAmount.le hnominal hratio1 hfeeUpper
      hidealPositive.le hcomputedBase hbaseCeil hcomputedExponent hexponentCeil
      hcpow hscale hmulCeil hfeeCeil hdownscaleCeil

/-- Complete second-term exact-output comparison after removing the negative term. -/
theorem baseline_swap_exact_amount_out_second_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {inputBalance outputBalance outputAmount nominalRatio feeRate computedBase
      idealExponent computedExponent a wholeComputed computedPower scale : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      tokenAmountIn adjustedInput output : ℤ}
    (hinputBalance : 0 < inputBalance) (houtputBalance : 0 < outputBalance)
    (houtputAmount : 0 < outputAmount)
    (hnominal : nominalRatio = outputAmount / outputBalance)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hfeeUpper : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hidealExponentUpper : idealExponent ≤ 9)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hcontinued : (CPOW_PRECISION : ℝ) < (firstRounded : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ))))
    (hscale : 0 < scale)
    (hmulCeil :
      IsCeil tokenAmountIn
        (inputBalance * (computedPower / (BONE : ℝ) - 1)))
    (hfeeCeil :
      IsCeil adjustedInput ((tokenAmountIn : ℝ) / (1 - feeRate)))
    (hdownscaleCeil : IsCeil output ((adjustedInput : ℝ) / scale)) :
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
        (output : ℝ) <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputAdjustedMinimumFeeInputValue
          (inputBalance / scale) feeRate idealExponent nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hcpow := baseline_exact_output_cpow_second_term_adverse_error_lt_precise_fee_share
    hratio0 hratioPositive hratioUpper hcomputedBase hbaseCeil
      hidealExponentLower hidealExponentUpper hcomputedExponent hexponentCeil
      ha0 ha1 hcomputedExponentSplit hfirstFloor hcontinued hwholeTrace
      hcomputedPower hcomposedCeil
  exact swap_exact_amount_out_from_fixed_point_refinements_fee_share
    (feeShare := EXACT_OUTPUT_ADVERSE_FEE_SHARE)
    hinputBalance houtputBalance houtputAmount.le hnominal hratio1 hfeeUpper
      (lt_of_lt_of_le (by norm_num) hidealExponentLower).le hcomputedBase
      hbaseCeil hcomputedExponent hexponentCeil hcpow hscale hmulCeil
      hfeeCeil hdownscaleCeil

/-- Complete integer-exponent exact-output comparison; upper-rounded `c_powi` is conservative. -/
theorem baseline_swap_exact_amount_out_integer_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {inputBalance outputBalance outputAmount nominalRatio feeRate computedBase
      idealExponent computedPower scale : ℝ}
    {computedBaseRaw computedExponentRaw tokenAmountIn adjustedInput output : ℤ}
    (hinputBalance : 0 < inputBalance) (houtputBalance : 0 < outputBalance)
    (houtputAmount : 0 < outputAmount)
    (hnominal : nominalRatio = outputAmount / outputBalance)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hfeeUpper : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hidealExponentLower : 1 / 9 ≤ idealExponent)
    (hcomputedExponent :
      (integerPart : ℝ) = (computedExponentRaw : ℝ) / STROOP)
    (hexponentCeil :
      IsCeil computedExponentRaw ((STROOP : ℝ) * idealExponent))
    (hwholeTrace :
      UpperCPowiTrace computedBase integerPart (computedPower / (BONE : ℝ)))
    (hscale : 0 < scale)
    (hmulCeil :
      IsCeil tokenAmountIn
        (inputBalance * (computedPower / (BONE : ℝ) - 1)))
    (hfeeCeil :
      IsCeil adjustedInput ((tokenAmountIn : ℝ) / (1 - feeRate)))
    (hdownscaleCeil : IsCeil output ((adjustedInput : ℝ) / scale)) :
    exactOutputIdealInput (inputBalance / scale) feeRate nominalRatio idealExponent -
        (output : ℝ) <
      EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputAdjustedMinimumFeeInputValue
          (inputBalance / scale) feeRate idealExponent nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hratio1 : nominalRatio < 1 := by
    have hmax : (MAX_OUT_RATIO : ℝ) / STROOP < 1 := by
      norm_num [MAX_OUT_RATIO, STROOP]
    exact lt_of_le_of_lt hratioUpper hmax
  have hbase := exact_output_base_ceil_refines
    hratio0 hratio1 hcomputedBase hbaseCeil
  have hconservative := baseline_exact_output_cpow_integer_has_no_adverse_error
    (le_trans (by norm_num) hbase.2) hwholeTrace
  have hidealPositive : 0 < idealExponent :=
    lt_of_lt_of_le (by norm_num) hidealExponentLower
  have hfeePositive := exact_output_minimum_fee_power_value_positive
    hidealPositive hratioPositive
  have hcpow :
      (BONE : ℝ) * computedBase ^ (integerPart : ℝ) - computedPower <
        EXACT_OUTPUT_ADVERSE_FEE_SHARE *
          exactOutputMinimumFeePowerValue idealExponent nominalRatio := by
    have hshare :
        0 < EXACT_OUTPUT_ADVERSE_FEE_SHARE *
          exactOutputMinimumFeePowerValue idealExponent nominalRatio :=
      mul_pos (by rw [exact_output_adverse_fee_share_value]; norm_num) hfeePositive
    linarith
  exact swap_exact_amount_out_from_fixed_point_refinements_fee_share
    (feeShare := EXACT_OUTPUT_ADVERSE_FEE_SHARE)
    hinputBalance houtputBalance houtputAmount.le hnominal hratio1 hfeeUpper
      hidealPositive.le hcomputedBase hbaseCeil hcomputedExponent hexponentCeil
      hcpow hscale hmulCeil hfeeCeil hdownscaleCeil

end CometPool
