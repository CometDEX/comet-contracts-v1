import CometPool.Operations.SingleSidedWithdrawal
import CometPool.Operations.ExactOutputSwap

namespace CometPool

/-!
Operation-level model for `dep_lp_tokn_amt_out_get_tokn_in`, the
single-sided deposit that mints an exact LP-token amount and charges one
underlying token. Its `c_pow` path has an above-one base, a ceiled reciprocal
weight exponent, and `round_up = true`.
-/

/-- The ideal enlarged-pool-supply ratio after minting LP tokens. -/
noncomputable def singleSidedDepositIdealBase (nominalRatio : ℝ) : ℝ :=
  1 + nominalRatio

/-- Exact fee-adjusted token input in the input balance's unit. -/
noncomputable def singleSidedDepositIdealInput
    (inputBalance weight feeRate nominalRatio : ℝ) : ℝ :=
  inputBalance *
      (singleSidedDepositIdealBase nominalRatio ^ (1 / weight) - 1) /
    (1 - singleSidedWithdrawalFeeRate weight feeRate)

/-- Minimum weighted-fee spot value in raw `c_pow` units. -/
noncomputable def singleSidedDepositMinimumFeePowerValue
    (weight nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
    ((BONE : ℝ) * ((1 - weight) / weight) * nominalRatio)

/-- Minimum weighted-fee spot value after the actual weighted-fee denominator. -/
noncomputable def singleSidedDepositAdjustedMinimumFeeInputValue
    (inputBalance weight feeRate nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
      (inputBalance * ((1 - weight) / weight) * nominalRatio) /
    (1 - singleSidedWithdrawalFeeRate weight feeRate)

/--
The certified adverse-error share of the adjusted weighted minimum fee. The
small-ratio second-stop composition approaches `1.10696%`; `1.107%` is a
simple strict rational ceiling.
-/
noncomputable def SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE : ℝ :=
  1107 / 100000

/-- One percent of the configured minimum fee rate for the small-ratio branch. -/
noncomputable def SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE : ℝ :=
  MIN_FEE_RATE / 100

theorem single_sided_deposit_adverse_fee_share_value :
    SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE = (1107 : ℝ) / 100000 := by
  rfl

theorem single_sided_deposit_small_ratio_fee_rate_value :
    SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE = (1 : ℝ) / 100000000 := by
  norm_num [SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE,
    MIN_FEE_RATE, MIN_FEE, STROOP]

/-- The normalized supply-ratio ceiling is above both the ideal base and one. -/
theorem single_sided_deposit_base_ceil_refines
    {nominalRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hratio0 : 0 ≤ nominalRatio)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio))) :
    singleSidedDepositIdealBase nominalRatio ≤ computedBase ∧
      1 ≤ computedBase := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hideal := hbaseCeil.le_normalized hB
  constructor
  · rw [singleSidedDepositIdealBase, hcomputedBase]
    exact hideal
  · rw [hcomputedBase]
    exact le_trans (by linarith) hideal

/-- A normalized reciprocal ceiling is no smaller than the ideal reciprocal. -/
theorem single_sided_deposit_exponent_ceil_refines
    {weight computedExponent : ℝ} {computedExponentRaw : ℤ}
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight))) :
    1 / weight ≤ computedExponent ∧
      computedExponent < 1 / weight + 1 / (BONE : ℝ) := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  constructor
  · rw [hcomputedExponent]
    exact hexponentCeil.le_normalized hB
  · rw [hcomputedExponent]
    exact normalized_ceil_lt_exact_add_inv_scale hB hexponentCeil

/-- Ceiling an above-one base and reciprocal exponent can only increase its power. -/
theorem single_sided_deposit_rounded_power_dominates_ideal
    {nominalRatio weight computedBase computedExponent : ℝ}
    (hratio0 : 0 ≤ nominalRatio) (hweight0 : 0 < weight)
    (hbase : singleSidedDepositIdealBase nominalRatio ≤ computedBase)
    (hexponent : 1 / weight ≤ computedExponent) :
    singleSidedDepositIdealBase nominalRatio ^ (1 / weight) ≤
      computedBase ^ computedExponent := by
  have hidealBaseOne : 1 ≤ singleSidedDepositIdealBase nominalRatio := by
    rw [singleSidedDepositIdealBase]
    linarith
  have hexponent0 : 0 ≤ 1 / weight := (one_div_pos.mpr hweight0).le
  calc
    singleSidedDepositIdealBase nominalRatio ^ (1 / weight) ≤
        computedBase ^ (1 / weight) :=
      Real.rpow_le_rpow (le_trans (by norm_num) hidealBaseOne) hbase hexponent0
    _ ≤ computedBase ^ computedExponent :=
      Real.rpow_le_rpow_of_exponent_le (le_trans hidealBaseOne hbase) hexponent

/-- The weighted-fee denominator is positive throughout the configured domain. -/
theorem single_sided_deposit_fee_denominator_positive
    {weight feeRate : ℝ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1) :
    0 < 1 - singleSidedWithdrawalFeeRate weight feeRate := by
  rw [singleSidedWithdrawalFeeRate]
  have hweighted : (1 - weight) * feeRate < 1 := by
    have hleft : 0 ≤ 1 - weight := sub_nonneg.mpr hweight1
    calc
      (1 - weight) * feeRate ≤ 1 * feeRate :=
        mul_le_mul_of_nonneg_right (by linarith) hfee0
      _ < 1 := by simpa using hfee1
  linarith

/-- The new-balance ceiling followed by subtraction is an input lower bound. -/
theorem single_sided_deposit_balance_ceil_chain
    {newBalance tokenAmountAfterFee : ℤ}
    {inputBalance computedPower : ℝ}
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance) :
    inputBalance * (computedPower / (BONE : ℝ) - 1) ≤
      (tokenAmountAfterFee : ℝ) := by
  have hnew := hnewBalanceCeil.le
  rw [htokenAmount]
  linarith

/-- Caller ceilings cannot understate the fee-adjusted token input. -/
theorem single_sided_deposit_input_ceil_chain
    {newBalance tokenAmountAfterFee result output : ℤ}
    {inputBalance computedPower feeMultiplier scale : ℝ}
    (hfeeMultiplier : 0 < feeMultiplier) (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance)
    (hfeeCeil :
      IsCeil result ((tokenAmountAfterFee : ℝ) / feeMultiplier))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
        feeMultiplier ≤ (output : ℝ) := by
  have htoken := single_sided_deposit_balance_ceil_chain
    hnewBalanceCeil htokenAmount
  have hfeeScaled := (div_le_div_iff_of_pos_right hfeeMultiplier).2 htoken
  have hfee := hfeeCeil.le
  have hdownScaled := (div_le_div_iff_of_pos_right hscale).2 hfee
  calc
    inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
          feeMultiplier =
        (inputBalance * (computedPower / (BONE : ℝ) - 1) /
          feeMultiplier) / scale := by ring
    _ ≤ ((tokenAmountAfterFee : ℝ) / feeMultiplier) / scale :=
      div_le_div_of_nonneg_right hfeeScaled hscale.le
    _ ≤ (result : ℝ) / scale := hdownScaled
    _ ≤ (output : ℝ) := hdownscaleCeil.le

/-- Compose a raw power bound with the ideal deposit and all caller ceilings. -/
theorem single_sided_deposit_adverse_error_lt_fee_share
    {feeShare inputBalance weight feeRate nominalRatio computedBase computedExponent
      computedPower computedInput scale : ℝ}
    (hinputBalance : 0 < inputBalance) (hscale : 0 < scale)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1)
    (hratio0 : 0 ≤ nominalRatio)
    (hbase : singleSidedDepositIdealBase nominalRatio ≤ computedBase)
    (hexponent : 1 / weight ≤ computedExponent)
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        feeShare * singleSidedDepositMinimumFeePowerValue weight nominalRatio)
    (hcomputedInput :
      inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) ≤ computedInput) :
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio -
        computedInput <
      feeShare * singleSidedDepositAdjustedMinimumFeeInputValue
        (inputBalance / scale) weight feeRate nominalRatio := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hdenom := single_sided_deposit_fee_denominator_positive
    hweight0.le hweight1.le hfee0 hfee1
  have hpowerDirection := single_sided_deposit_rounded_power_dominates_ideal
    hratio0 hweight0 hbase hexponent
  have hrawDirection :
      (BONE : ℝ) * singleSidedDepositIdealBase nominalRatio ^ (1 / weight) ≤
        (BONE : ℝ) * computedBase ^ computedExponent :=
    mul_le_mul_of_nonneg_left hpowerDirection hB.le
  have hadversePower :
      (BONE : ℝ) * singleSidedDepositIdealBase nominalRatio ^ (1 / weight) -
          computedPower <
        feeShare * singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
    linarith
  have hcallerScale :
      0 < inputBalance / scale / (BONE : ℝ) /
        (1 - singleSidedWithdrawalFeeRate weight feeRate) :=
    div_pos (div_pos (div_pos hinputBalance hscale) hB) hdenom
  have hscaled := mul_lt_mul_of_pos_left hadversePower hcallerScale
  calc
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio - computedInput ≤
        singleSidedDepositIdealInput
            (inputBalance / scale) weight feeRate nominalRatio -
          (inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate)) :=
      sub_le_sub_left hcomputedInput _
    _ = (inputBalance / scale / (BONE : ℝ) /
          (1 - singleSidedWithdrawalFeeRate weight feeRate)) *
        ((BONE : ℝ) *
            singleSidedDepositIdealBase nominalRatio ^ (1 / weight) -
          computedPower) := by
      rw [singleSidedDepositIdealInput]
      field_simp [ne_of_gt hB, ne_of_gt hdenom, ne_of_gt hscale]
      ring
    _ < (inputBalance / scale / (BONE : ℝ) /
          (1 - singleSidedWithdrawalFeeRate weight feeRate)) *
        (feeShare * singleSidedDepositMinimumFeePowerValue weight nominalRatio) :=
      hscaled
    _ = feeShare * singleSidedDepositAdjustedMinimumFeeInputValue
          (inputBalance / scale) weight feeRate nominalRatio := by
      rw [singleSidedDepositMinimumFeePowerValue,
        singleSidedDepositAdjustedMinimumFeeInputValue]
      field_simp [ne_of_gt hB, ne_of_gt hdenom, ne_of_gt hscale,
        ne_of_gt hweight0]
      ring

/-- Instantiate the operation theorem from the fixed-point caller refinements. -/
theorem single_sided_deposit_from_fixed_point_refinements_fee_share
    {feeShare poolSupply poolAmountOut nominalRatio inputBalance weight feeRate
      computedBase computedExponent computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw newBalance tokenAmountAfterFee result
      output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hnominal : nominalRatio = poolAmountOut / poolSupply)
    (hinputBalance : 0 < inputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        feeShare * singleSidedDepositMinimumFeePowerValue weight nominalRatio)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance)
    (hfeeCeil :
      IsCeil result ((tokenAmountAfterFee : ℝ) / feeMultiplier))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio - (output : ℝ) <
      feeShare * singleSidedDepositAdjustedMinimumFeeInputValue
        (inputBalance / scale) weight feeRate nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hexponent := single_sided_deposit_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hdenom := single_sided_deposit_fee_denominator_positive
    hweight0.le hweight1.le hfee0 hfee1
  have hinput := single_sided_deposit_input_ceil_chain
    (by rw [hfeeMultiplier]; exact hdenom) hscale hnewBalanceCeil
      htokenAmount hfeeCeil hdownscaleCeil
  rw [hfeeMultiplier] at hinput
  exact single_sided_deposit_adverse_error_lt_fee_share
    hinputBalance hscale hweight0 hweight1 hfee0 hfee1 hratio0
      hbase.1 hexponent.1 hcpow hinput

/-- Production weights bound the reciprocal and weighted-fee exponents. -/
theorem single_sided_deposit_reciprocal_weight_bounds
    {weight : ℝ}
    (hweight0 : 0 < weight)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP) :
    1 / weight ≤ 10 ∧ 1 / 9 ≤ (1 - weight) / weight := by
  have hmin : (MIN_WEIGHT : ℝ) / STROOP = 1 / 10 := by
    norm_num [MIN_WEIGHT, STROOP]
  have hmax : (MAX_WEIGHT : ℝ) / STROOP = 9 / 10 := by
    norm_num [MAX_WEIGHT, STROOP]
  rw [hmin] at hweightLower
  rw [hmax] at hweightUpper
  constructor
  · apply (div_le_iff₀ hweight0).2
    nlinarith
  · apply (le_div_iff₀ hweight0).2
    nlinarith

/-- The BONE-scaled reciprocal ceiling remains at most ten. -/
theorem single_sided_deposit_computed_exponent_le_ten
    {weight computedExponent : ℝ} {computedExponentRaw : ℤ}
    (hidealUpper : 1 / weight ≤ 10)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight))) :
    computedExponent ≤ 10 := by
  have hexactUpper :
      (BONE : ℝ) * (1 / weight) ≤ (10 * BONE : ℤ) := by
    exact_mod_cast mul_le_mul_of_nonneg_left hidealUpper
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  have hrawUpper : computedExponentRaw ≤ (10 * BONE : ℤ) :=
    hexponentCeil.le_integer_upper hexactUpper
  rw [hcomputedExponent]
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  apply (div_le_iff₀ hB).2
  exact_mod_cast hrawUpper

/-- The reciprocal ceiling's fractional part is within `0.1%` of the fee exponent. -/
theorem single_sided_deposit_fractional_le_adjusted_fee_exponent
    {integerPart : ℕ} {weight a computedExponent : ℝ}
    (hweight0 : 0 < weight)
    (hfeeExponentLower : 1 / 9 ≤ (1 - weight) / weight)
    (hintegerPart : 1 ≤ integerPart)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper :
      computedExponent < 1 / weight + 1 / (BONE : ℝ)) :
    a ≤ (1001 / 1000 : ℝ) * ((1 - weight) / weight) := by
  have hintegerReal : (1 : ℝ) ≤ integerPart := by exact_mod_cast hintegerPart
  have haUpper : a < (1 - weight) / weight + 1 / (BONE : ℝ) := by
    rw [hcomputedExponentSplit] at hcomputedExponentUpper
    have hid : 1 / weight - 1 = (1 - weight) / weight := by
      field_simp
    linarith
  have hunit :
      1 / (BONE : ℝ) ≤ ((1 - weight) / weight) / 1000 := by
    have hnumeric : (1 : ℝ) / BONE ≤ (1 / 9 : ℝ) / 1000 := by
      norm_num [BONE]
    exact le_trans hnumeric
      (div_le_div_of_nonneg_right hfeeExponentLower (by norm_num))
  nlinarith

/-- A positive fractional part and an exponent at most ten force integer part at most nine. -/
theorem single_sided_deposit_fractional_integer_part_le_nine
    {integerPart : ℕ} {a computedExponent : ℝ}
    (haPositive : 0 < a)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper : computedExponent ≤ 10) :
    integerPart ≤ 9 := by
  by_contra hnot
  have hintegerTen : 10 ≤ integerPart := by omega
  have hintegerReal : (10 : ℝ) ≤ integerPart := by exact_mod_cast hintegerTen
  rw [hcomputedExponentSplit] at hcomputedExponentUpper
  linarith

/-- The direct supply-ratio ceiling is less than the ideal base plus one raw unit. -/
theorem single_sided_deposit_base_ceil_upper
    {nominalRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio))) :
    computedBase < 1 + nominalRatio + 1 / (BONE : ℝ) := by
  rw [hcomputedBase]
  have h := normalized_ceil_lt_exact_add_inv_scale
    (exact := 1 + nominalRatio) (by norm_num [BONE]) hbaseCeil
  linarith

/-- Continuation makes the nominal mint ratio large enough to absorb a base ceiling unit. -/
theorem single_sided_deposit_continuation_forces_ratio_lower
    {a nominalRatio computedBase firstTerm : ℝ}
    (ha1 : a ≤ 1)
    (hbaseOne : 1 ≤ computedBase)
    (hbaseCeilUpper :
      computedBase < 1 + nominalRatio + 1 / (BONE : ℝ))
    (hfirst : firstTerm = (BONE : ℝ) * a * (computedBase - 1))
    (hfirstLarge : (CPOW_PRECISION : ℝ) < firstTerm) :
    1 / 10000000000000000 ≤ nominalRatio := by
  have hq0 : 0 ≤ computedBase - 1 := sub_nonneg.mpr hbaseOne
  have haProduct : a * (computedBase - 1) ≤ computedBase - 1 := by
    simpa using mul_le_of_le_one_left hq0 ha1
  have hfirstUpper : firstTerm ≤ (BONE : ℝ) * (computedBase - 1) := by
    rw [hfirst, mul_assoc]
    exact mul_le_mul_of_nonneg_left haProduct (by norm_num [BONE])
  norm_num [BONE, CPOW_PRECISION] at hfirstLarge hfirstUpper
  norm_num [BONE] at hbaseCeilUpper ⊢
  linarith

/-- Once continuation occurs, base displacement is within `1.01` of the nominal ratio. -/
theorem single_sided_deposit_continued_displacement_le
    {nominalRatio computedBase : ℝ}
    (hratioLower : 1 / 10000000000000000 ≤ nominalRatio)
    (hbaseCeilUpper :
      computedBase < 1 + nominalRatio + 1 / (BONE : ℝ)) :
    computedBase - 1 ≤ (101 / 100 : ℝ) * nominalRatio := by
  have hunit : 1 / (BONE : ℝ) ≤ nominalRatio / 100 := by
    have hnumeric :
        1 / (BONE : ℝ) ≤ (1 / 10000000000000000 : ℝ) / 100 := by
      norm_num [BONE]
    exact le_trans hnumeric
      (div_le_div_of_nonneg_right hratioLower (by norm_num))
  nlinarith

/-- A small mint ratio keeps the rounded direct base below `1.01`. -/
theorem single_sided_deposit_small_computed_base_lt
    {nominalRatio computedBase : ℝ}
    (hratioSmall : nominalRatio < 1 / 200)
    (hbaseCeilUpper :
      computedBase < 1 + nominalRatio + 1 / (BONE : ℝ)) :
    computedBase < 101 / 100 := by
  have hunit : 1 / (BONE : ℝ) < 1 / 10000 := by norm_num [BONE]
  linarith

/-- A base below `1.01` to a production fractional-case integer part is below `1.094`. -/
theorem single_sided_deposit_small_whole_power_lt
    {integerPart : ℕ} {computedBase : ℝ}
    (hbase0 : 0 ≤ computedBase) (hbaseUpper : computedBase < 101 / 100)
    (hintegerPart : integerPart ≤ 9) :
    computedBase ^ integerPart < 547 / 500 := by
  have hbasePower : computedBase ^ integerPart ≤
      (101 / 100 : ℝ) ^ integerPart :=
    pow_le_pow_left₀ hbase0 (le_of_lt hbaseUpper) integerPart
  have hexponentPower : (101 / 100 : ℝ) ^ integerPart ≤
      (101 / 100 : ℝ) ^ 9 :=
    pow_le_pow_right₀ (by norm_num) hintegerPart
  calc
    computedBase ^ integerPart ≤ (101 / 100 : ℝ) ^ integerPart := hbasePower
    _ ≤ (101 / 100 : ℝ) ^ 9 := hexponentPower
    _ < 547 / 500 := by norm_num

/-- A base at most `1.6` to an integer part at most nine is below `68.72`. -/
theorem single_sided_deposit_whole_power_lt_1718_div_25
    {integerPart : ℕ} {computedBase : ℝ}
    (hbase0 : 0 ≤ computedBase) (hbaseUpper : computedBase ≤ 8 / 5)
    (hintegerPart : integerPart ≤ 9) :
    computedBase ^ integerPart < 1718 / 25 := by
  have hbasePower : computedBase ^ integerPart ≤
      (8 / 5 : ℝ) ^ integerPart :=
    pow_le_pow_left₀ hbase0 hbaseUpper integerPart
  have hexponentPower : (8 / 5 : ℝ) ^ integerPart ≤
      (8 / 5 : ℝ) ^ 9 :=
    pow_le_pow_right₀ (by norm_num) hintegerPart
  calc
    computedBase ^ integerPart ≤ (8 / 5 : ℝ) ^ integerPart := hbasePower
    _ ≤ (8 / 5 : ℝ) ^ 9 := hexponentPower
    _ < 1718 / 25 := by norm_num

/-- The small-ratio displacement leaves a one-percent fee-rate budget. -/
theorem accumulated_error_lt_small_ratio_fee_rate_of_later_terms
    {n : ℕ} {firstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * ((101 : ℝ) / 20000 / 2) *
            ((101 : ℝ) / 20000) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n <
      SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE * firstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE,
      MIN_FEE_RATE, MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- Continuation in the full operating band forces the first term above precision. -/
theorem operating_band_continuation_forces_first_term_above_precision
    {n : ℕ} {firstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * ((3 : ℝ) / 5 / 2) * ((3 : ℝ) / 5) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    (CPOW_PRECISION : ℝ) < firstTerm := by
  interval_cases n <;>
    norm_num [CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- The small-ratio whole power and ceiling units retain the `1.107%` margin. -/
theorem single_sided_deposit_small_ratio_fee_scale_lt_precise_share
    {weightedFraction feeExponent displacement nominalRatio : ℝ}
    (hweighted : weightedFraction ≤ (137 / 125 : ℝ) * feeExponent)
    (hfeeExponentPositive : 0 < feeExponent)
    (hratioPositive : 0 < nominalRatio)
    (hdisplacement0 : 0 ≤ displacement)
    (hdisplacement : displacement ≤ (101 / 100 : ℝ) * nominalRatio) :
    SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
        ((BONE : ℝ) * weightedFraction * displacement) <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        (MIN_FEE_RATE * ((BONE : ℝ) * feeExponent * nominalRatio)) := by
  have hproduct :
      weightedFraction * displacement ≤
        ((137 / 125 : ℝ) * feeExponent) *
          ((101 / 100 : ℝ) * nominalRatio) :=
    mul_le_mul hweighted hdisplacement hdisplacement0
      (mul_nonneg (by norm_num) hfeeExponentPositive.le)
  have hscaled := mul_le_mul_of_nonneg_left hproduct
    (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  have hrate0 : 0 ≤ SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE := by
    rw [single_sided_deposit_small_ratio_fee_rate_value]
    norm_num
  have hscaledRate := mul_le_mul_of_nonneg_left hscaled hrate0
  have hpositive : 0 < (BONE : ℝ) * feeExponent * nominalRatio :=
    mul_pos (mul_pos (by norm_num [BONE]) hfeeExponentPositive) hratioPositive
  have hconstant :
      SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
          ((137 / 125 : ℝ) * (101 / 100 : ℝ)) <
        SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
    rw [single_sided_deposit_small_ratio_fee_rate_value,
      single_sided_deposit_adverse_fee_share_value, minimum_fee_rate_value]
    norm_num
  have hstrict := mul_lt_mul_of_pos_right hconstant hpositive
  calc
    SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
          ((BONE : ℝ) * weightedFraction * displacement) ≤
        SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
          ((BONE : ℝ) * (((137 / 125 : ℝ) * feeExponent) *
            ((101 / 100 : ℝ) * nominalRatio))) := by
      simpa [mul_assoc] using hscaledRate
    _ = (SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
          ((137 / 125 : ℝ) * (101 / 100 : ℝ))) *
        ((BONE : ℝ) * feeExponent * nominalRatio) := by ring
    _ < (SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
        ((BONE : ℝ) * feeExponent * nominalRatio) := hstrict
    _ = SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        (MIN_FEE_RATE * ((BONE : ℝ) * feeExponent * nominalRatio)) := by ring

/--
Compose an above-one fractional bound through the reciprocal whole power and
compare it with the weighted minimum fee.
-/
theorem baseline_single_sided_deposit_cpow_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {weight nominalRatio a computedExponent computedBase computedFractional
      wholeComputed computedPower : ℝ}
    (hweight0 : 0 < weight)
    (hfeeExponentLower : 1 / 9 ≤ (1 - weight) / weight)
    (ha0 : 0 ≤ a)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper :
      computedExponent < 1 / weight + 1 / (BONE : ℝ))
    (hintegerPartOne : 1 ≤ integerPart)
    (hintegerPart : integerPart ≤ 9)
    (hratioPositive : 0 < nominalRatio)
    (hbaseOne : 1 ≤ computedBase) (hbaseUpper : computedBase ≤ 8 / 5)
    (hbaseCeilUpper :
      computedBase < 1 + nominalRatio + 1 / (BONE : ℝ))
    (hdisplacement :
      computedBase - 1 ≤ (101 / 100 : ℝ) * nominalRatio)
    (hcomputedFractional0 : 0 ≤ computedFractional)
    (hwholeUpper : computedBase ^ integerPart ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * computedFractional ≤ computedPower)
    (hfractionalSmallFee :
      nominalRatio < 1 / 200 →
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
          ((BONE : ℝ) * a * (computedBase - 1)))
    (hfractionalCap :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 3151) :
    (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
  let wholeExact : ℝ := computedBase ^ integerPart
  let exactFractional : ℝ := (BONE : ℝ) * computedBase ^ a
  let feeExponent : ℝ := (1 - weight) / weight
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbaseOne
  have hwhole0 : 0 < wholeExact := by dsimp [wholeExact]; positivity
  have hfeeExponentPositive : 0 < feeExponent :=
    lt_of_lt_of_le (by norm_num) hfeeExponentLower
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
  have hdisplacement0 : 0 ≤ computedBase - 1 := sub_nonneg.mpr hbaseOne
  have haAdjusted := single_sided_deposit_fractional_le_adjusted_fee_exponent
    hweight0 hfeeExponentLower hintegerPartOne
      hcomputedExponentSplit hcomputedExponentUpper
  by_cases hratioSmall : nominalRatio < 1 / 200
  · have hsmallBase := single_sided_deposit_small_computed_base_lt
      hratioSmall hbaseCeilUpper
    have hwholeSmall := single_sided_deposit_small_whole_power_lt
      hbase0.le hsmallBase hintegerPart
    have hwholeA : wholeExact * a ≤ (137 / 125 : ℝ) * feeExponent := by
      have hmul := mul_le_mul hwholeSmall.le haAdjusted ha0
        (by positivity : 0 ≤ (547 / 500 : ℝ))
      dsimp [feeExponent] at haAdjusted ⊢
      dsimp [wholeExact] at hmul ⊢
      have hconstant :
          (547 / 500 : ℝ) * (1001 / 1000) < 137 / 125 := by
        norm_num
      have hstrict := mul_lt_mul_of_pos_right hconstant hfeeExponentPositive
      nlinarith
    have hfeeScale := single_sided_deposit_small_ratio_fee_scale_lt_precise_share
      hwholeA hfeeExponentPositive hratioPositive hdisplacement0 hdisplacement
    have hscaledFractional :=
      mul_lt_mul_of_pos_left (hfractionalSmallFee hratioSmall) hwhole0
    have hrearrange :
        wholeExact *
            (SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
              ((BONE : ℝ) * a * (computedBase - 1))) =
          SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
            ((BONE : ℝ) * (wholeExact * a) * (computedBase - 1)) := by ring
    rw [hrearrange] at hscaledFractional
    rw [singleSidedDepositMinimumFeePowerValue]
    exact lt_of_le_of_lt hcomposition (lt_trans hscaledFractional hfeeScale)
  · have hratioLarge : 1 / 200 ≤ nominalRatio := le_of_not_gt hratioSmall
    have hwholeCap := single_sided_deposit_whole_power_lt_1718_div_25
      hbase0.le hbaseUpper hintegerPart
    have hscaledCap := mul_lt_mul_of_pos_left hfractionalCap hwhole0
    have hcap : wholeExact * (exactFractional - computedFractional) <
        (1718 / 25 : ℝ) * 3151 := by
      exact lt_trans hscaledCap
        (mul_lt_mul_of_pos_right hwholeCap (by norm_num))
    have hfeeLarge :
        (1718 / 25 : ℝ) * 3151 <
          SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
            singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
      rw [single_sided_deposit_adverse_fee_share_value,
        singleSidedDepositMinimumFeePowerValue, minimum_fee_rate_value]
      have hproduct :
          (1 / 9 : ℝ) * (1 / 200) ≤
            feeExponent * nominalRatio :=
        mul_le_mul hfeeExponentLower hratioLarge (by norm_num)
          hfeeExponentPositive.le
      dsimp [feeExponent] at hproduct ⊢
      norm_num [BONE] at ⊢
      nlinarith
    exact lt_of_le_of_lt hcomposition
      (lt_trans hcap hfeeLarge)

/-- A fractional reciprocal exponent always leaves a positive whole exponent. -/
theorem single_sided_deposit_fractional_integer_part_positive
    {integerPart : ℕ} {weight computedExponent a : ℝ}
    (hweight0 : 0 < weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hcomputedExponentLower : 1 / weight ≤ computedExponent)
    (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a) :
    1 ≤ integerPart := by
  by_contra hnot
  have hzero : integerPart = 0 := Nat.eq_zero_of_not_pos hnot
  have hcomputedEq : computedExponent = a := by
    simpa [hzero] using hcomputedExponentSplit
  have hweightStrict : weight < 1 := by
    have hmax : (MAX_WEIGHT : ℝ) / STROOP < 1 := by
      norm_num [MAX_WEIGHT, STROOP]
    exact lt_of_le_of_lt hweightUpper hmax
  have hidealOne : 1 < 1 / weight := (one_lt_div hweight0).2 hweightStrict
  linarith

/--
Across the full successful `c_pow` base domain, a retained odd fractional
partial stays within the iteration-cap floor budget below `BONE`.
-/
theorem single_sided_deposit_later_fractional_gt_bone_sub_cap
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {degree oddIndex : ℕ}
    {a computedBase computedFractional : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbaseStrict : 1 < computedBase) (hbaseTwo : computedBase < 2)
    (hdegreeOdd : degree = 2 * oddIndex + 1)
    (hdegree50 : degree ≤ 50)
    (hfirstFloor :
      IsFloor (computedTerm 1) (exactOutputBinomialTerm a computedBase 1))
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < degree →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (a - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < degree →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < degree →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) +
        ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ)) :
    (BONE : ℝ) - 3725 < computedFractional := by
  have hx : |computedBase - 1| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hbaseStrict.le)]
    linarith
  let T : ℕ → ℝ := exactOutputBinomialTerm a computedBase
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  have hrec : ∀ k,
      T (k + 1) =
        T k * (a - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactOutputBinomialTerm_succ a computedBase k
  have hfirstExact : T 1 = (BONE : ℝ) * a * (computedBase - 1) := by
    exact exactOutputBinomialTerm_one a computedBase
  have hfirst0 : 0 ≤ T 1 := by
    rw [hfirstExact]
    exact mul_nonneg (mul_nonneg (by norm_num [BONE]) ha0)
      (sub_nonneg.mpr hbaseStrict.le)
  have hfirstMagnitude : |T 1| = (BONE : ℝ) * a * (computedBase - 1) := by
    rw [abs_of_nonneg hfirst0, hfirstExact]
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [T, U]
    exact hfirstFloor.abs_error_lt_one
  have hfirstBelowScale : |T 1| < BONE := by
    rw [hfirstMagnitude]
    have hproduct : a * (computedBase - 1) < 1 := by
      have hmul : a * (computedBase - 1) ≤ 1 * (computedBase - 1) :=
        mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr hbaseStrict.le)
      linarith
    have hscaled := mul_lt_mul_of_pos_left hproduct
      (show (0 : ℝ) < BONE by norm_num [BONE])
    simpa [mul_assoc] using hscaled
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T ha0 ha1 hx hrec (k - 1)
    have hindex : k - 1 + 1 = k := by omega
    rw [hindex] at hterms
    have hscale : |T 1| * (1 : ℝ) ^ (k - 1) = |T 1| := by simp
    rw [hscale] at hterms
    exact lt_of_le_of_lt hterms hfirstBelowScale
  have herrorRec : ∀ k, 1 ≤ k → k < degree →
      |T (k + 1) - U (k + 1)| <
        (1 + 1 / (((k + 1 : ℕ) : ℝ) * (BONE : ℝ))) * |T k - U k| +
          1 / ((k + 1 : ℕ) : ℝ) + 1 / ((k + 1 : ℕ) : ℝ) + 1 := by
    intro k hk hkdegree
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
      (by norm_num [BONE]) (by positivity) hcoefficientBound hx
      (hexactTermMagnitude k hk) (hcoefficientFloor k hk hkdegree)
      (by simpa [U] using hmultiplyTermFloor k hk hkdegree)
      (hdivideTermFloor k hk hkdegree)
    rw [hrec k]
    simpa [U, Nat.cast_add, Nat.cast_one, add_assoc] using hstep
  let exactPartial : ℝ :=
    ∑ k ∈ Finset.range (degree + 1), exactOutputBinomialTerm a computedBase k
  have hpartialUpper : (BONE : ℝ) * computedBase ^ a ≤ exactPartial := by
    dsimp [exactPartial]
    rw [hdegreeOdd]
    exact exact_output_binomial_odd_partial_upper ha0 ha1 hbaseStrict oddIndex
  have hpartialLower : (BONE : ℝ) ≤ exactPartial := by
    have hpowerOne : 1 ≤ computedBase ^ a := Real.one_le_rpow hbaseStrict.le ha0
    have hscaled := mul_le_mul_of_nonneg_left hpowerOne
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
    exact le_trans (by simpa using hscaled) hpartialUpper
  have hexactPartial :
      exactPartial = (BONE : ℝ) + ∑ k ∈ Finset.range degree, T (k + 1) := by
    dsimp [exactPartial, T]
    rw [Finset.sum_range_succ']
    simp
    ring
  have hdegree1 : 1 ≤ degree := by rw [hdegreeOdd]; omega
  have hsumRaw := recurrence_implies_partial_sum_error_budget_until
    (BONE : ℝ) T U hdegree1 hdegree50 (by norm_num [BONE]) hfirstError
      herrorRec
  have hsum : |exactPartial - computedFractional| < accumulatedError degree := by
    rw [hexactPartial, hcomputedFractional, accumulatedError]
    convert hsumRaw using 1
    simp [U, Nat.add_comm]
  have herrorCap : accumulatedError degree ≤ 3725 := by
    have hmono := accumulated_error_mono hdegree1 hdegree50
    have hcap : accumulatedError 50 = 3725 := by
      norm_num [accumulatedError]
    linarith
  have hdifference : exactPartial - computedFractional < accumulatedError degree :=
    lt_of_le_of_lt (le_abs_self _) hsum
  linarith

/-- A positive whole exponent composes a coarse fractional lower bound. -/
theorem single_sided_deposit_composed_power_lower
    {integerPart : ℕ}
    {computedBase computedFractional wholeComputed computedPower : ℝ}
    (hbaseOne : 1 ≤ computedBase) (hintegerPartOne : 1 ≤ integerPart)
    (hfractionalLower : (BONE : ℝ) - 3725 ≤ computedFractional)
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomposedUpper : wholeComputed * computedFractional ≤ computedPower) :
    computedBase * ((BONE : ℝ) - 3725) ≤ computedPower := by
  have hbasePower : computedBase ≤ computedBase ^ integerPart := by
    have hpower := pow_le_pow_right₀ hbaseOne hintegerPartOne
    simpa using hpower
  have hwholeBound := hwholeTrace.upper_bound (le_trans (by norm_num) hbaseOne)
  have hwhole0 : 0 ≤ wholeComputed :=
    le_trans (pow_nonneg (le_trans (by norm_num) hbaseOne) _) hwholeBound
  have hcap0 : (0 : ℝ) ≤ BONE - 3725 := by norm_num [BONE]
  calc
    computedBase * ((BONE : ℝ) - 3725) ≤
        computedBase ^ integerPart * ((BONE : ℝ) - 3725) :=
      mul_le_mul_of_nonneg_right hbasePower hcap0
    _ ≤ wholeComputed * ((BONE : ℝ) - 3725) :=
      mul_le_mul_of_nonneg_right hwholeBound hcap0
    _ ≤ wholeComputed * computedFractional :=
      mul_le_mul_of_nonneg_left hfractionalLower hwhole0
    _ ≤ computedPower := hcomposedUpper

/--
If the caller's post-calculation maximum-input guard succeeds, the coarse
`c_pow` lower bound forces the rounded supply base into the proven band.
-/
theorem successful_single_sided_deposit_implies_base_upper
    {inputBalance scale feeMultiplier computedBase computedPower output : ℝ}
    (hinputBalance : 0 < inputBalance) (hscale : 0 < scale)
    (hfeeMultiplier0 : 0 < feeMultiplier) (hfeeMultiplier1 : feeMultiplier ≤ 1)
    (hpowerLower : computedBase * ((BONE : ℝ) - 3725) ≤ computedPower)
    (hcomputedInput :
      inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
          feeMultiplier ≤ output)
    (hmaxInput :
      output ≤ inputBalance / scale * ((MAX_IN_RATIO : ℝ) / STROOP)) :
    computedBase ≤ 8 / 5 := by
  by_contra hnot
  have hbaseLarge : (8 / 5 : ℝ) < computedBase := lt_of_not_ge hnot
  have hcap0 : (0 : ℝ) < BONE - 3725 := by norm_num [BONE]
  have hbaseProduct :
      (8 / 5 : ℝ) * ((BONE : ℝ) - 3725) <
        computedBase * ((BONE : ℝ) - 3725) :=
    mul_lt_mul_of_pos_right hbaseLarge hcap0
  have hnumeric :
      (3 / 2 : ℝ) * BONE < (8 / 5 : ℝ) * ((BONE : ℝ) - 3725) := by
    norm_num [BONE]
  have hpower : (3 / 2 : ℝ) * BONE < computedPower :=
    lt_of_lt_of_le (lt_trans hnumeric hbaseProduct) hpowerLower
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hgrowth : (1 / 2 : ℝ) < computedPower / (BONE : ℝ) - 1 := by
    apply (lt_sub_iff_add_lt).2
    apply (lt_div_iff₀ hB).2
    nlinarith
  have hnative0 : 0 < inputBalance / scale := div_pos hinputBalance hscale
  have hrawInput0 :
      0 ≤ inputBalance / scale * (computedPower / (BONE : ℝ) - 1) :=
    mul_nonneg hnative0.le (le_trans (by norm_num) hgrowth.le)
  have hfeeDirection :
      inputBalance / scale * (computedPower / (BONE : ℝ) - 1) ≤
        inputBalance / scale * (computedPower / (BONE : ℝ) - 1) /
          feeMultiplier := by
    apply (le_div_iff₀ hfeeMultiplier0).2
    nlinarith
  have hlower : inputBalance / scale * (1 / 2 : ℝ) < output := by
    have hscaledGrowth := mul_lt_mul_of_pos_left hgrowth hnative0
    exact lt_of_lt_of_le hscaledGrowth (le_trans hfeeDirection hcomputedInput)
  have hratioHalf : (MAX_IN_RATIO : ℝ) / STROOP < 1 / 2 := by
    norm_num [MAX_IN_RATIO, STROOP]
  have hupper : output < inputBalance / scale * (1 / 2 : ℝ) := by
    exact lt_of_le_of_lt hmaxInput (mul_lt_mul_of_pos_left hratioHalf hnative0)
  linarith

/-- Full later-term baseline `c_pow` bound for the exact-LP-output deposit. -/
theorem baseline_single_sided_deposit_cpow_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n degree oddIndex integerPart : ℕ}
    {weight nominalRatio computedBase computedExponent a computedFractional
      wholeComputed computedPower : ℝ}
    {computedBaseRaw computedExponentRaw computedPowerRaw : ℤ}
    (hweight0 : 0 < weight)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hratio0 : 0 ≤ nominalRatio) (hratioPositive : 0 < nominalRatio)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hbaseUpper : computedBase ≤ 8 / 5)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
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
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
  have hweightBounds := single_sided_deposit_reciprocal_weight_bounds
    hweight0 hweightLower hweightUpper
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbase.2
  have hbaseStrict : 1 < computedBase := by
    have hidealStrict : 1 < singleSidedDepositIdealBase nominalRatio := by
      rw [singleSidedDepositIdealBase]
      linarith
    exact lt_of_lt_of_le hidealStrict hbase.1
  have hbaseCeilUpper := single_sided_deposit_base_ceil_upper
    hcomputedBase hbaseCeil
  have hx : |computedBase - 1| ≤ (3 / 5 : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hbase.2)]
    linarith
  let T : ℕ → ℝ := exactOutputBinomialTerm a computedBase
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  have hrec : ∀ k,
      T (k + 1) =
        T k * (a - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactOutputBinomialTerm_succ a computedBase k
  have hfirstExact : T 1 = (BONE : ℝ) * a * (computedBase - 1) := by
    exact exactOutputBinomialTerm_one a computedBase
  have hfirst0 : 0 ≤ T 1 := by
    rw [hfirstExact]
    exact mul_nonneg (mul_nonneg (by norm_num [BONE]) ha0)
      (sub_nonneg.mpr hbase.2)
  have hfirstMagnitude : |T 1| = (BONE : ℝ) * a * (computedBase - 1) := by
    rw [abs_of_nonneg hfirst0, hfirstExact]
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [T, U]
    exact hfirstFloor.abs_error_lt_one
  have hfirstBelowScale : |T 1| < BONE := by
    rw [hfirstMagnitude]
    have hproduct : a * (computedBase - 1) < 1 := by
      have hmul : a * (computedBase - 1) ≤ 1 * (computedBase - 1) :=
        mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr hbase.2)
      linarith
    have hscaled := mul_lt_mul_of_pos_left hproduct
      (show (0 : ℝ) < BONE by norm_num [BONE])
    simpa [mul_assoc] using hscaled
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T ha0 ha1 hx hrec (k - 1)
    have hindex : k - 1 + 1 = k := by omega
    rw [hindex] at hterms
    have hpower1 : (3 / 5 : ℝ) ^ (k - 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hscale : |T 1| * (3 / 5 : ℝ) ^ (k - 1) ≤ |T 1| := by
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
  have htermZero : |T 0| ≤ (BONE : ℝ) := by dsimp [T]; simp
  have hn46 : n ≤ 46 := by
    by_contra hn
    have herror46 : |T 46 - U 46| < 3 * (46 : ℝ) - 2 :=
      htermBounds 46 (by norm_num) (by omega)
    have hstopsBy46 : |U 46| < (CPOW_PRECISION : ℝ) :=
      pool_operating_base_converges_by_iteration_46
        T ha0 ha1 (by linarith : (1 / 2 : ℝ) ≤ computedBase) hbaseUpper
          htermZero hrec herror46
    have hstillRunning := hcontinued 46 (by norm_num) (Nat.lt_of_not_ge hn)
    dsimp [U] at hstopsBy46
    linarith
  have hprevious : (CPOW_PRECISION : ℝ) < |U (n - 1)| := by
    simpa [U] using hcontinued (n - 1) (by omega) (by omega)
  have htermError :
      |T (n - 1) - U (n - 1)| < 3 * ((n - 1 : ℕ) : ℝ) - 2 :=
    htermBounds (n - 1) (by omega) (by omega)
  have hcontinue := continued_loop_forces_sharp_first_term_scale
    T ha0 ha1 hx (by norm_num) hrec hn3 hprevious htermError
  have hfirstLarge : (CPOW_PRECISION : ℝ) < |T 1| :=
    operating_band_continuation_forces_first_term_above_precision
      hn3 hn46 (by simpa using hcontinue)
  have haPositive : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := le_antisymm (le_of_not_gt hnot) ha0
    rw [hfirstMagnitude, haZero] at hfirstLarge
    norm_num [CPOW_PRECISION] at hfirstLarge
  have hratioLower := single_sided_deposit_continuation_forces_ratio_lower
    ha1 hbase.2 hbaseCeilUpper hfirstMagnitude hfirstLarge
  have hdisplacement := single_sided_deposit_continued_displacement_le
    hratioLower hbaseCeilUpper
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
  have hfractionalSmallFee (hratioSmall : nominalRatio < 1 / 200) :
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
          ((BONE : ℝ) * a * (computedBase - 1)) := by
    have hxSmall : |computedBase - 1| ≤ (101 : ℝ) / 20000 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbase.2)]
      have hscaled := mul_lt_mul_of_pos_left hratioSmall
        (show (0 : ℝ) < 101 / 100 by norm_num)
      exact le_trans hdisplacement (le_of_lt (by
        norm_num at hscaled ⊢
        linarith))
    have hcontinueSmall := continued_loop_forces_sharp_first_term_scale
      T ha0 ha1 hxSmall (by norm_num) hrec hn3 hprevious htermError
    have hbudget := accumulated_error_lt_small_ratio_fee_rate_of_later_terms
      hn3 hn46 (by simpa using hcontinueSmall)
    have hadverse :
        (BONE : ℝ) * computedBase ^ a - computedFractional <
          accumulatedError degree := by
      have hdifference : exactPartial - computedFractional < accumulatedError degree :=
        lt_of_le_of_lt (le_abs_self _) hsum
      linarith
    rw [← hfirstMagnitude]
    exact lt_of_lt_of_le hadverse (le_trans herrorMono (le_of_lt hbudget))
  have hfractionalCap :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 3151 := by
    have hadverse :
        (BONE : ℝ) * computedBase ^ a - computedFractional <
          accumulatedError degree := by
      have hdifference : exactPartial - computedFractional < accumulatedError degree :=
        lt_of_le_of_lt (le_abs_self _) hsum
      linarith
    exact lt_of_lt_of_le hadverse
      (le_trans herrorMono (accumulated_error_le_3151 hn46))
  have hpartialLower : (BONE : ℝ) ≤ exactPartial := by
    have hpowerOne : 1 ≤ computedBase ^ a := Real.one_le_rpow hbase.2 ha0
    have hscaled := mul_le_mul_of_nonneg_left hpowerOne
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
    exact le_trans (by simpa using hscaled) hpartialUpper
  have hcomputedFractional0 : 0 ≤ computedFractional := by
    have hdifference : exactPartial - computedFractional < accumulatedError degree :=
      lt_of_le_of_lt (le_abs_self _) hsum
    have hdegreeCap := le_trans herrorMono (accumulated_error_le_3151 hn46)
    have hmargin : (3151 : ℝ) < BONE := by norm_num [BONE]
    linarith
  have hexponent := single_sided_deposit_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hcomputedExponentTen := single_sided_deposit_computed_exponent_le_ten
    hweightBounds.1 hcomputedExponent hexponentCeil
  have hintegerPart := single_sided_deposit_fractional_integer_part_le_nine
    haPositive hcomputedExponentSplit hcomputedExponentTen
  have hintegerPartOne : 1 ≤ integerPart := by
    by_contra hnot
    have hzero : integerPart = 0 := Nat.eq_zero_of_not_pos hnot
    have hcomputedEq : computedExponent = a := by
      simpa [hzero] using hcomputedExponentSplit
    have hidealOne : 1 < 1 / weight := by
      have hweightStrict : weight < 1 := by
        have hmax : (MAX_WEIGHT : ℝ) / STROOP < 1 := by
          norm_num [MAX_WEIGHT, STROOP]
        exact lt_of_le_of_lt hweightUpper hmax
      exact (one_lt_div hweight0).2 hweightStrict
    linarith [hexponent.1, ha1]
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hcomposedUpper : wholeComputed * computedFractional ≤ computedPower := by
    rw [hcomputedPower]
    exact hcomposedCeil.le
  exact baseline_single_sided_deposit_cpow_adverse_error_lt_precise_fee_share
    hweight0 hweightBounds.2 ha0 hcomputedExponentSplit hexponent.2
      hintegerPartOne hintegerPart hratioPositive hbase.2 hbaseUpper
      hbaseCeilUpper hdisplacement hcomputedFractional0 hwholeUpper
      hcomposedUpper hfractionalSmallFee hfractionalCap

/-- The second stop removes its negative term and leaves only the first floor unit. -/
theorem baseline_single_sided_deposit_cpow_second_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {weight nominalRatio computedBase computedExponent a wholeComputed
      computedPower : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw : ℤ}
    (hweight0 : 0 < weight)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hratio0 : 0 ≤ nominalRatio) (hratioPositive : 0 < nominalRatio)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hbaseUpper : computedBase ≤ 8 / 5)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
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
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
  have hweightBounds := single_sided_deposit_reciprocal_weight_bounds
    hweight0 hweightLower hweightUpper
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbase.2
  have hbaseCeilUpper := single_sided_deposit_base_ceil_upper
    hcomputedBase hbaseCeil
  have hfirstLarge :
      (CPOW_PRECISION : ℝ) < (BONE : ℝ) * a * (computedBase - 1) :=
    positive_floor_above_threshold hfirstFloor hcontinued
  have haPositive : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := le_antisymm (le_of_not_gt hnot) ha0
    rw [haZero] at hfirstLarge
    norm_num [CPOW_PRECISION] at hfirstLarge
  have hratioLower := single_sided_deposit_continuation_forces_ratio_lower
    ha1 hbase.2 hbaseCeilUpper rfl hfirstLarge
  have hdisplacement := single_sided_deposit_continued_displacement_le
    hratioLower hbaseCeilUpper
  have hexponent := single_sided_deposit_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hcomputedExponentTen := single_sided_deposit_computed_exponent_le_ten
    hweightBounds.1 hcomputedExponent hexponentCeil
  have hintegerPart := single_sided_deposit_fractional_integer_part_le_nine
    haPositive hcomputedExponentSplit hcomputedExponentTen
  have hintegerPartOne : 1 ≤ integerPart := by
    by_contra hnot
    have hzero : integerPart = 0 := Nat.eq_zero_of_not_pos hnot
    have hcomputedEq : computedExponent = a := by
      simpa [hzero] using hcomputedExponentSplit
    have hweightStrict : weight < 1 := by
      have hmax : (MAX_WEIGHT : ℝ) / STROOP < 1 := by
        norm_num [MAX_WEIGHT, STROOP]
      exact lt_of_le_of_lt hweightUpper hmax
    have hidealOne : 1 < 1 / weight := (one_lt_div hweight0).2 hweightStrict
    linarith [hexponent.1, ha1]
  let computedFractional : ℝ := (BONE : ℝ) + (firstRounded : ℝ)
  have hpartialUpper := exact_output_fractional_first_order_upper
    ha0 ha1 hbase0.le
  have hfractionalOne :
      (BONE : ℝ) * computedBase ^ a - computedFractional < 1 := by
    dsimp [computedFractional]
    have hrounding :
        (BONE : ℝ) + (BONE : ℝ) * a * (computedBase - 1) -
          ((BONE : ℝ) + (firstRounded : ℝ)) < 1 := by
      linarith [hfirstFloor.lt_add_one]
    linarith
  have honeFee :
      (1 : ℝ) < SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
        ((BONE : ℝ) * a * (computedBase - 1)) := by
    rw [single_sided_deposit_small_ratio_fee_rate_value]
    norm_num [CPOW_PRECISION] at hfirstLarge ⊢
    linarith
  have hfractionalSmallFee (_ : nominalRatio < 1 / 200) :
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        SINGLE_SIDED_DEPOSIT_SMALL_RATIO_FEE_RATE *
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
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hcomposedUpper : wholeComputed * computedFractional ≤ computedPower := by
    dsimp [computedFractional]
    rw [hcomputedPower]
    exact hcomposedCeil.le
  exact baseline_single_sided_deposit_cpow_adverse_error_lt_precise_fee_share
    hweight0 hweightBounds.2 ha0 hcomputedExponentSplit hexponent.2
      hintegerPartOne hintegerPart hratioPositive hbase.2 hbaseUpper
      hbaseCeilUpper hdisplacement hcomputedFractional0 hwholeUpper
      hcomposedUpper hfractionalSmallFee hfractionalCap

/-- Positive weight complement and mint ratio make the deposit fee scale positive. -/
theorem single_sided_deposit_minimum_fee_power_value_positive
    {weight nominalRatio : ℝ}
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hratioPositive : 0 < nominalRatio) :
    0 < singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
  rw [singleSidedDepositMinimumFeePowerValue, minimum_fee_rate_value]
  exact mul_pos (by norm_num)
    (mul_pos
      (mul_pos (by norm_num [BONE]) (div_pos (by linarith) hweight0))
      hratioPositive)

/-- Complete corrected-first-term comparison for the modeled deposit caller. -/
theorem baseline_single_sided_deposit_first_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {poolSupply poolAmountOut nominalRatio inputBalance weight feeRate
      computedBase computedExponent a wholeComputed computedPower feeMultiplier
      scale : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      newBalance tokenAmountAfterFee result output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hnominal : nominalRatio = poolAmountOut / poolSupply)
    (hinputBalance : 0 < inputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ) + 1)))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance)
    (hfeeCeil :
      IsCeil result ((tokenAmountAfterFee : ℝ) / feeMultiplier))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositAdjustedMinimumFeeInputValue
          (inputBalance / scale) weight feeRate nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbase.2
  have hconservative := baseline_exact_output_cpow_first_term_has_no_adverse_error
    ha0 ha1 hcomputedExponentSplit hbase0 hfirstFloor hwholeTrace
      hcomputedPower hcomposedCeil
  have hfeePositive := single_sided_deposit_minimum_fee_power_value_positive
    hweight0 hweight1 hratioPositive
  have hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
    have hshare :
        0 < SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedDepositMinimumFeePowerValue weight nominalRatio :=
      mul_pos (by
        rw [single_sided_deposit_adverse_fee_share_value]
        norm_num) hfeePositive
    linarith
  exact single_sided_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE)
      hpoolSupply hpoolAmountOut hnominal hinputBalance hweight0 hweight1
      hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponent hexponentCeil
      hcpow hfeeMultiplier hscale hnewBalanceCeil htokenAmount hfeeCeil
      hdownscaleCeil

/-- Complete integer-only comparison for the modeled deposit caller. -/
theorem baseline_single_sided_deposit_integer_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {poolSupply poolAmountOut nominalRatio inputBalance weight feeRate
      computedBase computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw newBalance tokenAmountAfterFee result
      output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hnominal : nominalRatio = poolAmountOut / poolSupply)
    (hinputBalance : 0 < inputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hcomputedExponent :
      (integerPart : ℝ) = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (hwholeTrace :
      UpperCPowiTrace computedBase integerPart
        (computedPower / (BONE : ℝ)))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance)
    (hfeeCeil :
      IsCeil result ((tokenAmountAfterFee : ℝ) / feeMultiplier))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositAdjustedMinimumFeeInputValue
          (inputBalance / scale) weight feeRate nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hconservative := baseline_exact_output_cpow_integer_has_no_adverse_error
    (le_trans (by norm_num) hbase.2) hwholeTrace
  have hfeePositive := single_sided_deposit_minimum_fee_power_value_positive
    hweight0 hweight1 hratioPositive
  have hcpow :
      (BONE : ℝ) * computedBase ^ (integerPart : ℝ) - computedPower <
        SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedDepositMinimumFeePowerValue weight nominalRatio := by
    have hshare :
        0 < SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedDepositMinimumFeePowerValue weight nominalRatio :=
      mul_pos (by
        rw [single_sided_deposit_adverse_fee_share_value]
        norm_num) hfeePositive
    linarith
  exact single_sided_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE)
      hpoolSupply hpoolAmountOut hnominal hinputBalance hweight0 hweight1
      hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponent hexponentCeil
      hcpow hfeeMultiplier hscale hnewBalanceCeil htokenAmount hfeeCeil
      hdownscaleCeil

/-- Complete second-term comparison for the modeled deposit caller. -/
theorem baseline_single_sided_deposit_second_term_adverse_error_lt_precise_fee_share
    {integerPart : ℕ}
    {poolSupply poolAmountOut nominalRatio inputBalance weight feeRate
      computedBase computedExponent a wholeComputed computedPower feeMultiplier
      scale : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      newBalance tokenAmountAfterFee result output maxInput : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hnominal : nominalRatio = poolAmountOut / poolSupply)
    (hinputBalance : 0 < inputBalance)
    (hweight0 : 0 < weight)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
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
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance)
    (hfeeCeil :
      IsCeil result ((tokenAmountAfterFee : ℝ) / feeMultiplier))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale))
    (hmaxInputFloor :
      IsFloor maxInput
        (inputBalance / scale * ((MAX_IN_RATIO : ℝ) / STROOP)))
    (hmaxInputGuard : output ≤ maxInput) :
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositAdjustedMinimumFeeInputValue
          (inputBalance / scale) weight feeRate nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hexponent := single_sided_deposit_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hintegerPartOne := single_sided_deposit_fractional_integer_part_positive
    hweight0 hweightUpper hexponent.1 ha1 hcomputedExponentSplit
  have hfirstRounded0 : (0 : ℝ) ≤ firstRounded := by
    have hprecision0 : (0 : ℝ) ≤ CPOW_PRECISION := by positivity
    linarith
  have hfractionalLower :
      (BONE : ℝ) - 3725 ≤ (BONE : ℝ) + (firstRounded : ℝ) := by
    linarith
  have hcomposedUpper :
      wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ)) ≤ computedPower := by
    rw [hcomputedPower]
    exact hcomposedCeil.le
  have hpowerLower := single_sided_deposit_composed_power_lower
    hbase.2 hintegerPartOne hfractionalLower hwholeTrace hcomposedUpper
  have hfeeMultiplier0 : 0 < feeMultiplier := by
    rw [hfeeMultiplier]
    exact single_sided_deposit_fee_denominator_positive
      hweight0.le hweight1.le hfee0 hfee1
  have hfeeMultiplier1 : feeMultiplier ≤ 1 := by
    rw [hfeeMultiplier, singleSidedWithdrawalFeeRate]
    have hweighted0 : 0 ≤ (1 - weight) * feeRate :=
      mul_nonneg (sub_nonneg.mpr hweight1.le) hfee0
    linarith
  have hcomputedInput := single_sided_deposit_input_ceil_chain
    hfeeMultiplier0 hscale hnewBalanceCeil htokenAmount hfeeCeil hdownscaleCeil
  have hmaxInputGuardReal : (output : ℝ) ≤ (maxInput : ℝ) := by
    exact_mod_cast hmaxInputGuard
  have hmaxInput := le_trans hmaxInputGuardReal hmaxInputFloor.le
  have hbaseUpper := successful_single_sided_deposit_implies_base_upper
    hinputBalance hscale hfeeMultiplier0 hfeeMultiplier1 hpowerLower
      hcomputedInput hmaxInput
  have hcpow :=
    baseline_single_sided_deposit_cpow_second_term_adverse_error_lt_precise_fee_share
      hweight0 hweightLower hweightUpper hratio0 hratioPositive hcomputedBase
        hbaseCeil hbaseUpper hcomputedExponent hexponentCeil ha0 ha1
        hcomputedExponentSplit hfirstFloor hcontinued hwholeTrace
        hcomputedPower hcomposedCeil
  exact single_sided_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE)
      hpoolSupply hpoolAmountOut hnominal hinputBalance hweight0 hweight1
      hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponent hexponentCeil
      hcpow hfeeMultiplier hscale hnewBalanceCeil htokenAmount hfeeCeil
      hdownscaleCeil

/-- Complete later-term comparison for the modeled deposit caller. -/
theorem baseline_single_sided_deposit_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n degree oddIndex integerPart : ℕ}
    {poolSupply poolAmountOut nominalRatio inputBalance weight feeRate
      computedBase computedExponent a computedFractional wholeComputed
      computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw computedPowerRaw newBalance
      tokenAmountAfterFee result output maxInput : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hnominal : nominalRatio = poolAmountOut / poolSupply)
    (hinputBalance : 0 < inputBalance)
    (hweight0 : 0 < weight)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate < 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 + nominalRatio)))
    (hbaseTwo : computedBase < 2)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentCeil :
      IsCeil computedExponentRaw ((BONE : ℝ) * (1 / weight)))
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
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (inputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountAfterFee : ℝ) = (newBalance : ℝ) - inputBalance)
    (hfeeCeil :
      IsCeil result ((tokenAmountAfterFee : ℝ) / feeMultiplier))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale))
    (hmaxInputFloor :
      IsFloor maxInput
        (inputBalance / scale * ((MAX_IN_RATIO : ℝ) / STROOP)))
    (hmaxInputGuard : output ≤ maxInput) :
    singleSidedDepositIdealInput
          (inputBalance / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositAdjustedMinimumFeeInputValue
          (inputBalance / scale) weight feeRate nominalRatio := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hratioPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_deposit_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hbaseStrict : 1 < computedBase := by
    have hidealStrict : 1 < singleSidedDepositIdealBase nominalRatio := by
      rw [singleSidedDepositIdealBase]
      linarith
    exact lt_of_lt_of_le hidealStrict hbase.1
  have hexponent := single_sided_deposit_exponent_ceil_refines
    hcomputedExponent hexponentCeil
  have hintegerPartOne := single_sided_deposit_fractional_integer_part_positive
    hweight0 hweightUpper hexponent.1 ha1 hcomputedExponentSplit
  have hdegreeN : degree ≤ n := by
    rcases hdegreeStop with h | h <;> omega
  have hdegree50 : degree ≤ 50 := le_trans hdegreeN hn50
  have hfractionalLowerStrict :=
    single_sided_deposit_later_fractional_gt_bone_sub_cap
      coefficientProduct multiplied computedTerm ha0 ha1 hbaseStrict hbaseTwo
        hdegreeOdd hdegree50 hfirstFloor
        (fun k hk hdegree ↦ hcoefficientFloor k hk
          (lt_of_lt_of_le hdegree hdegreeN))
        (fun k hk hdegree ↦ hmultiplyTermFloor k hk
          (lt_of_lt_of_le hdegree hdegreeN))
        (fun k hk hdegree ↦ hdivideTermFloor k hk
          (lt_of_lt_of_le hdegree hdegreeN))
        hcomputedFractional
  have hfractionalLower :
      (BONE : ℝ) - 3725 ≤ computedFractional := hfractionalLowerStrict.le
  have hcomposedUpper : wholeComputed * computedFractional ≤ computedPower := by
    rw [hcomputedPower]
    exact hcomposedCeil.le
  have hpowerLower := single_sided_deposit_composed_power_lower
    hbase.2 hintegerPartOne hfractionalLower hwholeTrace hcomposedUpper
  have hfeeMultiplier0 : 0 < feeMultiplier := by
    rw [hfeeMultiplier]
    exact single_sided_deposit_fee_denominator_positive
      hweight0.le hweight1.le hfee0 hfee1
  have hfeeMultiplier1 : feeMultiplier ≤ 1 := by
    rw [hfeeMultiplier, singleSidedWithdrawalFeeRate]
    have hweighted0 : 0 ≤ (1 - weight) * feeRate :=
      mul_nonneg (sub_nonneg.mpr hweight1.le) hfee0
    linarith
  have hcomputedInput := single_sided_deposit_input_ceil_chain
    hfeeMultiplier0 hscale hnewBalanceCeil htokenAmount hfeeCeil hdownscaleCeil
  have hmaxInputGuardReal : (output : ℝ) ≤ (maxInput : ℝ) := by
    exact_mod_cast hmaxInputGuard
  have hmaxInput := le_trans hmaxInputGuardReal hmaxInputFloor.le
  have hbaseUpper := successful_single_sided_deposit_implies_base_upper
    hinputBalance hscale hfeeMultiplier0 hfeeMultiplier1 hpowerLower
      hcomputedInput hmaxInput
  have hcpow :=
    baseline_single_sided_deposit_cpow_later_adverse_error_lt_precise_fee_share
      coefficientProduct multiplied computedTerm hweight0 hweightLower
        hweightUpper hratio0 hratioPositive hcomputedBase hbaseCeil
        hbaseUpper hcomputedExponent hexponentCeil ha0 ha1
        hcomputedExponentSplit hn3 hn50 hdegreeOdd hdegreeStop hcontinued
        hfirstFloor hcoefficientFloor hmultiplyTermFloor hdivideTermFloor
        hcomputedFractional hwholeTrace hcomputedPower hcomposedCeil
  exact single_sided_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE)
      hpoolSupply hpoolAmountOut hnominal hinputBalance hweight0 hweight1
      hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponent hexponentCeil
      hcpow hfeeMultiplier hscale hnewBalanceCeil htokenAmount hfeeCeil
      hdownscaleCeil

end CometPool
