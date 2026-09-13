import CometPool.CPow.BinomialBelowLower
import CometPool.Operations.OperationFeeBound
import CometPool.Operations.SingleSidedTokenDeposit
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv

namespace CometPool

/-!
Operation-level model for `wdr_tokn_amt_out_get_lp_tokns_in`, the
single-sided withdrawal that returns an exact underlying-token amount and
charges LP tokens. Its `c_pow` path has a below-one base, the direct
normalized weight as exponent, and `round_up = false`.
-/

/-- The exact fee-adjusted remaining-token-balance ratio. -/
noncomputable def singleSidedTokenWithdrawalIdealBase
    (weight feeRate nominalRatio : ℝ) : ℝ :=
  1 - nominalRatio / (1 - singleSidedWithdrawalFeeRate weight feeRate)

/-- Exact LP-token input in the pool supply's unit. -/
noncomputable def singleSidedTokenWithdrawalIdealInput
    (poolSupply weight feeRate nominalRatio : ℝ) : ℝ :=
  poolSupply *
    (1 - singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight)

/-- Minimum weighted-fee spot value after the path's actual fee denominator. -/
noncomputable def singleSidedTokenWithdrawalAdjustedMinimumFeePowerValue
    (weight feeRate nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
    ((BONE : ℝ) * weight * (1 - weight) * nominalRatio) /
      (1 - singleSidedWithdrawalFeeRate weight feeRate)

/-- The same adjusted minimum-fee value in the LP token's unit. -/
noncomputable def singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
    (poolSupply weight feeRate nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
    (poolSupply * weight * (1 - weight) * nominalRatio) /
      (1 - singleSidedWithdrawalFeeRate weight feeRate)

/-- The weighted fee scale associated with the rounded base displacement. -/
noncomputable def singleSidedTokenWithdrawalComputedMinimumFeePowerValue
    (weight computedBase : ℝ) : ℝ :=
  MIN_FEE_RATE *
    ((BONE : ℝ) * weight * (1 - weight) * (1 - computedBase))

/-- A strict rational ceiling on exact-token-output withdrawal adverse error. -/
noncomputable def SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE : ℝ :=
  HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE

/-- The precise later recurrence budget relative to the minimum fee rate. -/
noncomputable def SINGLE_SIDED_TOKEN_WITHDRAWAL_LATER_FEE_RATE : ℝ :=
  HALF_AUGMENTED_LATER_FEE_RATE

theorem single_sided_token_withdrawal_adverse_fee_share_value :
    SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE =
      (4751 : ℝ) / 100000 := by
  rw [SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE,
    half_augmented_later_adverse_fee_share_value]

/--
For a fractional exponent, reducing a base in `[0,1]` by `q - r` reduces its
power by at least `weight * (q - r)`. This is the favorable-rounding margin
used to absorb fee-division and base-floor units.
-/
theorem fractional_power_drop_ge_linear
    {weight r q : ℝ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hr0 : 0 ≤ r) (hrq : r ≤ q) (hq1 : q < 1) :
    weight * (q - r) ≤ (1 - r) ^ weight - (1 - q) ^ weight := by
  let f : ℝ → ℝ := fun x ↦ x ^ weight
  have hx0 : 0 < 1 - q := by linarith
  have hy0 : 0 < 1 - r := by linarith
  have hy1 : 1 - r ≤ 1 := by linarith
  by_cases heq : r = q
  · subst q
    simp
  have hrlt : r < q := lt_of_le_of_ne hrq heq
  have hxy : 1 - q < 1 - r := by linarith
  have hconcave : ConcaveOn ℝ (Set.Ici 0) f := Real.concaveOn_rpow hweight0 hweight1
  have hderiv : HasDerivAt f (weight * (1 - r) ^ (weight - 1)) (1 - r) := by
    exact Real.hasDerivAt_rpow_const (Or.inl hy0.ne')
  have hslope := hconcave.le_slope_of_hasDerivAt hx0.le hy0.le hxy hderiv
  have hpowFactor : 1 ≤ (1 - r) ^ (weight - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by linarith)
  have hderivLower : weight ≤ weight * (1 - r) ^ (weight - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hpowFactor hweight0]
  have hslopeLower : weight ≤
      ((1 - r) ^ weight - (1 - q) ^ weight) / ((1 - r) - (1 - q)) :=
    le_trans hderivLower (by
      simpa [f, slope, div_eq_mul_inv, mul_comm] using hslope)
  have hdenom : 0 < (1 - r) - (1 - q) := by linarith
  have hmul := (le_div_iff₀ hdenom).mp hslopeLower
  nlinarith

/-- The before-fee ceiling cannot understate the exact adjusted output ratio. -/
theorem single_sided_token_withdrawal_before_fee_ceil_refines
    {inputBalance inputAmount nominalRatio feeMultiplier beforeFeeRatio : ℝ}
    {beforeFee : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hbeforeFeeRatio : beforeFeeRatio = (beforeFee : ℝ) / inputBalance)
    (hbeforeFeeCeil : IsCeil beforeFee (inputAmount / feeMultiplier)) :
    nominalRatio / feeMultiplier ≤ beforeFeeRatio := by
  rw [hnominal, hbeforeFeeRatio]
  have hceilScaled := div_le_div_of_nonneg_right hbeforeFeeCeil.le hinputBalance.le
  calc
    (inputAmount / inputBalance) / feeMultiplier =
        (inputAmount / feeMultiplier) / inputBalance := by ring
    _ ≤ (beforeFee : ℝ) / inputBalance := hceilScaled

/-- The normalized remaining-balance floor cannot exceed its exact ratio. -/
theorem single_sided_token_withdrawal_base_floor_refines
    {beforeFeeRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 - beforeFeeRatio))) :
    computedBase ≤ 1 - beforeFeeRatio := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  rw [hcomputedBase]
  exact hbaseFloor.normalized_le hB

/-- Fee division and base flooring can only reduce the base from the ideal formula. -/
theorem single_sided_token_withdrawal_computed_base_le_ideal
    {weight feeRate nominalRatio feeMultiplier beforeFeeRatio computedBase : ℝ}
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjusted : nominalRatio / feeMultiplier ≤ beforeFeeRatio)
    (hbase : computedBase ≤ 1 - beforeFeeRatio) :
    computedBase ≤
      singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio := by
  rw [singleSidedTokenWithdrawalIdealBase, ← hfeeMultiplier]
  linarith

/-- Caller floors and the final ceiling cannot reduce the LP amount charged. -/
theorem single_sided_token_withdrawal_input_ceil_chain
    {newPoolSupply result output : ℤ}
    {poolSupply computedPower scale : ℝ}
    (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hresult : (result : ℝ) = poolSupply - (newPoolSupply : ℝ))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    poolSupply / scale * (1 - computedPower / (BONE : ℝ)) ≤
      (output : ℝ) := by
  have hraw :
      poolSupply * (1 - computedPower / (BONE : ℝ)) ≤ (result : ℝ) := by
    rw [hresult]
    linarith [hnewSupplyFloor.le]
  have hscaled := (div_le_div_iff_of_pos_right hscale).2 hraw
  calc
    poolSupply / scale * (1 - computedPower / (BONE : ℝ)) =
        (poolSupply * (1 - computedPower / (BONE : ℝ))) / scale := by ring
    _ ≤ (result : ℝ) / scale := hscaled
    _ ≤ (output : ℝ) := hdownscaleCeil.le

/--
The power margin created by fee division and base flooring absorbs the part
of a rounded-base approximation budget attributable to their extra
displacement.
-/
theorem single_sided_token_withdrawal_absorb_base_rounding
    {weight feeRate nominalRatio computedBase computedPower : ℝ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hadjusted0 : 0 ≤
      nominalRatio / (1 - singleSidedWithdrawalFeeRate weight feeRate))
    (hbasePositive : 0 < computedBase)
    (hbase : computedBase ≤
      singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio)
    (hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalComputedMinimumFeePowerValue
            weight computedBase) :
    computedPower - (BONE : ℝ) *
        singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeePowerValue
          weight feeRate nominalRatio := by
  let r : ℝ := nominalRatio /
    (1 - singleSidedWithdrawalFeeRate weight feeRate)
  let q : ℝ := 1 - computedBase
  have hrq : r ≤ q := by
    dsimp [r, q]
    rw [singleSidedTokenWithdrawalIdealBase] at hbase
    linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hdrop := fractional_power_drop_ge_linear
    hweight0 hweight1 hadjusted0 hrq hq1
  have hB0 : (0 : ℝ) ≤ BONE := by norm_num [BONE]
  have hdropScaled := mul_le_mul_of_nonneg_left hdrop hB0
  have hrate0 :
      0 ≤ SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
    rw [single_sided_token_withdrawal_adverse_fee_share_value,
      minimum_fee_rate_value]
    norm_num
  have hcoefficient :
      (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (1 - weight) ≤ 1 := by
    rw [single_sided_token_withdrawal_adverse_fee_share_value,
      minimum_fee_rate_value]
    nlinarith
  have hroundingAbsorbed :
      (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          ((BONE : ℝ) * weight * (1 - weight) * q) -
        (BONE : ℝ) * weight * (q - r) ≤
      (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          ((BONE : ℝ) * weight * (1 - weight) * r) := by
    have hBw0 : 0 ≤ (BONE : ℝ) * weight := mul_nonneg hB0 hweight0
    have hgap0 : 0 ≤ q - r := sub_nonneg.mpr hrq
    have hscaledGap := mul_le_mul_of_nonneg_right hcoefficient
      (mul_nonneg hBw0 hgap0)
    nlinarith
  rw [singleSidedTokenWithdrawalComputedMinimumFeePowerValue] at hcpow
  rw [singleSidedTokenWithdrawalAdjustedMinimumFeePowerValue]
  dsimp [q, r] at hcpow hdropScaled hroundingAbsorbed ⊢
  have hdecompose :
      computedPower - (BONE : ℝ) *
          singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight =
        (computedPower - (BONE : ℝ) * computedBase ^ weight) -
          (BONE : ℝ) *
            (singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight -
              computedBase ^ weight) := by ring
  have hpowerGap :
      (BONE : ℝ) * weight *
          (1 - computedBase -
            nominalRatio / (1 - singleSidedWithdrawalFeeRate weight feeRate)) ≤
        (BONE : ℝ) *
          (singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight -
            computedBase ^ weight) := by
    rw [singleSidedTokenWithdrawalIdealBase]
    ring_nf at hdropScaled ⊢
    exact hdropScaled
  have hraw :
      computedPower - (BONE : ℝ) *
          singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight <
        (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
            ((BONE : ℝ) * weight * (1 - weight) * (1 - computedBase)) -
          (BONE : ℝ) * weight *
            (1 - computedBase -
              nominalRatio /
                (1 - singleSidedWithdrawalFeeRate weight feeRate)) := by
    rw [hdecompose]
    linarith
  calc
    computedPower - (BONE : ℝ) *
          singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight <
        (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
            ((BONE : ℝ) * weight * (1 - weight) * (1 - computedBase)) -
          (BONE : ℝ) * weight *
            (1 - computedBase -
              nominalRatio /
                (1 - singleSidedWithdrawalFeeRate weight feeRate)) := hraw
    _ ≤ (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
        ((BONE : ℝ) * weight * (1 - weight) *
          (nominalRatio /
            (1 - singleSidedWithdrawalFeeRate weight feeRate))) := hroundingAbsorbed
    _ = SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        (MIN_FEE_RATE *
          ((BONE : ℝ) * weight * (1 - weight) * nominalRatio) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate)) := by ring

/-- Compose the raw power bound with the LP-supply floor and output ceiling. -/
theorem single_sided_token_withdrawal_adverse_error_lt_precise_fee_share
    {poolSupply weight feeRate nominalRatio computedBase computedPower
      computedInput scale : ℝ}
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hfeeDenom : 0 < 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjusted0 : 0 ≤
      nominalRatio / (1 - singleSidedWithdrawalFeeRate weight feeRate))
    (hbasePositive : 0 < computedBase)
    (hbase : computedBase ≤
      singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio)
    (hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalComputedMinimumFeePowerValue
            weight computedBase)
    (hcomputedInput :
      poolSupply / scale * (1 - computedPower / (BONE : ℝ)) ≤
        computedInput) :
    singleSidedTokenWithdrawalIdealInput
        (poolSupply / scale) weight feeRate nominalRatio - computedInput <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hraw := single_sided_token_withdrawal_absorb_base_rounding
    hweight0 hweight1 hadjusted0 hbasePositive hbase hcpow
  have hcallerScale : 0 < poolSupply / scale / (BONE : ℝ) :=
    div_pos (div_pos hpoolSupply hscale) hB
  have hscaled := mul_lt_mul_of_pos_left hraw hcallerScale
  calc
    singleSidedTokenWithdrawalIdealInput
          (poolSupply / scale) weight feeRate nominalRatio - computedInput ≤
        singleSidedTokenWithdrawalIdealInput
            (poolSupply / scale) weight feeRate nominalRatio -
          poolSupply / scale * (1 - computedPower / (BONE : ℝ)) :=
      sub_le_sub_left hcomputedInput _
    _ = (poolSupply / scale / (BONE : ℝ)) *
        (computedPower - (BONE : ℝ) *
          singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight) := by
      rw [singleSidedTokenWithdrawalIdealInput]
      field_simp [ne_of_gt hB, ne_of_gt hscale]
      ring
    _ < (poolSupply / scale / (BONE : ℝ)) *
        (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalAdjustedMinimumFeePowerValue
            weight feeRate nominalRatio) := hscaled
    _ = SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
      rw [singleSidedTokenWithdrawalAdjustedMinimumFeePowerValue,
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue]
      field_simp [ne_of_gt hB, ne_of_gt hscale, ne_of_gt hfeeDenom]
      ring

/-- A first-stop below-one tail is smaller than the one-unit correction. -/
theorem single_sided_token_withdrawal_first_tail_lt_one
    {weight computedBase : ℝ} {firstRounded : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hbasePositive : 0 < computedBase) (hbaseStrict : computedBase < 1)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm weight computedBase 1))
    (hstop : |(firstRounded : ℝ)| ≤ CPOW_PRECISION) :
    |exactInputBinomialTerm weight computedBase 1| *
        (1 - computedBase) / computedBase < 1 := by
  have hweight0 : 0 ≤ weight := by
    have hmin : (0 : ℝ) < (MIN_WEIGHT : ℝ) / STROOP := by
      norm_num [MIN_WEIGHT, STROOP]
    linarith
  have hq0 : 0 < 1 - computedBase := by linarith
  have hfirstFacts := exactInputBinomialTerm_one hweight0 hbaseStrict.le
  have hfirstNonpos : exactInputBinomialTerm weight computedBase 1 ≤ 0 := by
    rw [hfirstFacts.1]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num [BONE]) hweight0) (by linarith)
  have hroundedNonpos : (firstRounded : ℝ) ≤ 0 :=
    le_trans hfirstFloor.le hfirstNonpos
  have hmagnitude :
      |exactInputBinomialTerm weight computedBase 1| ≤
        |(firstRounded : ℝ)| := by
    rw [abs_of_nonpos hfirstNonpos, abs_of_nonpos hroundedNonpos]
    linarith [hfirstFloor.le]
  have hexactStop :
      |exactInputBinomialTerm weight computedBase 1| ≤ CPOW_PRECISION :=
    le_trans hmagnitude hstop
  have hqSmall : 1 - computedBase ≤ 1 / 1000000000 := by
    rw [hfirstFacts.2] at hexactStop
    norm_num [BONE, CPOW_PRECISION, MIN_WEIGHT, STROOP] at hweightLower hexactStop ⊢
    nlinarith
  have hbaseHalf : 1 / 2 ≤ computedBase := by linarith
  apply (div_lt_iff₀ hbasePositive).2
  calc
    |exactInputBinomialTerm weight computedBase 1| * (1 - computedBase) ≤
        (CPOW_PRECISION : ℝ) * (1 - computedBase) :=
      mul_le_mul_of_nonneg_right hexactStop hq0.le
    _ ≤ (CPOW_PRECISION : ℝ) * (1 / 1000000000 : ℝ) :=
      mul_le_mul_of_nonneg_left hqSmall (by positivity)
    _ < 1 * computedBase := by
      norm_num [CPOW_PRECISION] at hbaseHalf ⊢
      linarith

/-- The one-unit first-stop correction is strictly pool-favoring. -/
theorem baseline_single_sided_token_withdrawal_cpow_first_term_has_no_adverse_error
    {weight computedBase computedFractional computedPower : ℝ}
    {firstRounded computedPowerRaw : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hbasePositive : 0 < computedBase) (hbaseStrict : computedBase < 1)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm weight computedBase 1))
    (hstop : |(firstRounded : ℝ)| ≤ CPOW_PRECISION)
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) + (firstRounded : ℝ) - 1)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional) :
    computedPower ≤ (BONE : ℝ) * computedBase ^ weight := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have htail := exact_input_binomial_partial_tail_le
    hweights.1.le hweights.2.le
      hbasePositive hbaseStrict (n := 1) (by norm_num)
  have htailSmall := single_sided_token_withdrawal_first_tail_lt_one
    hweightLower hbasePositive hbaseStrict hfirstFloor hstop
  have hpartial :
      ∑ k ∈ Finset.range 2, exactInputBinomialTerm weight computedBase k =
        (BONE : ℝ) + exactInputBinomialTerm weight computedBase 1 := by
    norm_num [Finset.sum_range_succ]
  have hcomputedUpper :
      computedPower ≤ (BONE : ℝ) + (firstRounded : ℝ) - 1 := by
    rw [hcomputedPower]
    exact le_trans hcomposedFloor.le (le_of_eq hcomputedFractional)
  have hfirstUpper :
      (firstRounded : ℝ) ≤ exactInputBinomialTerm weight computedBase 1 :=
    hfirstFloor.le
  rw [hpartial] at htail
  linarith

/--
At the second stop, the doubled negative term leaves only a sub-`1/BONE`
coefficient-floor effect, far below the selected weighted minimum-fee share.
-/
theorem baseline_single_sided_token_withdrawal_cpow_second_term_adverse_error_lt_precise_fee_share
    {weight computedBase computedFractional computedPower : ℝ}
    {firstRounded coefficientProduct multiplied secondRounded computedPowerRaw : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hbaseHalf : 1 / 2 ≤ computedBase) (hbaseStrict : computedBase < 1)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm weight computedBase 1))
    (hcoefficientFloor :
      IsFloor coefficientProduct
        ((BONE : ℝ) * (weight - 1) * (computedBase - 1)))
    (hmultiplyFloor :
      IsFloor multiplied
        ((firstRounded : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ)))
    (hdivideFloor : IsFloor secondRounded ((multiplied : ℝ) / 2))
    (hcomputedFractional :
      computedFractional =
        (BONE : ℝ) + (firstRounded : ℝ) + 2 * (secondRounded : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional) :
    computedPower - (BONE : ℝ) * computedBase ^ weight <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalComputedMinimumFeePowerValue
          weight computedBase := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  let T : ℕ → ℝ := exactInputBinomialTerm weight computedBase
  have hfirstFacts := exactInputBinomialTerm_one hweights.1.le hbaseStrict.le
  have hq0 : 0 < 1 - computedBase := by linarith
  have hfirstExact : T 1 = -(BONE : ℝ) * weight * (1 - computedBase) := by
    dsimp [T]
    rw [hfirstFacts.1]
    ring
  have hfirstNonpos : T 1 < 0 := by
    have hproduct : 0 < (BONE : ℝ) * weight * (1 - computedBase) :=
      mul_pos (mul_pos hB hweights.1) hq0
    rw [hfirstExact]
    nlinarith
  have hfirstRoundedUpper : (firstRounded : ℝ) ≤ T 1 := by
    simpa [T] using hfirstFloor.le
  let exactCoefficient : ℝ :=
    (BONE : ℝ) * (weight - 1) * (computedBase - 1)
  have hcoefficientPositive : 0 < exactCoefficient := by
    dsimp [exactCoefficient]
    have hw : weight - 1 < 0 := by linarith
    have hb : computedBase - 1 < 0 := by linarith
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hB hw) hb
  have hcoefficientRaw0 : 0 ≤ coefficientProduct := by
    by_cases hraw0 : (0 : ℤ) ≤ coefficientProduct
    · exact hraw0
    · have hraw : coefficientProduct + 1 ≤ 0 := by omega
      have hrawReal : (coefficientProduct : ℝ) + 1 ≤ 0 := by exact_mod_cast hraw
      have hlt := hcoefficientFloor.lt_add_one
      dsimp [exactCoefficient] at hcoefficientPositive
      linarith
  have hsecondTwiceUpper :
      2 * (secondRounded : ℝ) ≤
        (firstRounded : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ) := by
    have hdivide := hdivideFloor.le
    have htwice : 2 * (secondRounded : ℝ) ≤ (multiplied : ℝ) := by
      linarith
    exact le_trans htwice hmultiplyFloor.le
  have hfirstCoefficient :
      (firstRounded : ℝ) * (coefficientProduct : ℝ) ≤
        T 1 * (coefficientProduct : ℝ) :=
    mul_le_mul_of_nonneg_right hfirstRoundedUpper (by exact_mod_cast hcoefficientRaw0)
  have hcoefficientStrict : exactCoefficient - 1 < (coefficientProduct : ℝ) := by
    dsimp [exactCoefficient]
    linarith [hcoefficientFloor.lt_add_one]
  have hcoefficientFlip :
      T 1 * (coefficientProduct : ℝ) < T 1 * (exactCoefficient - 1) :=
    mul_lt_mul_of_neg_left hcoefficientStrict hfirstNonpos
  have hsecondError :
      2 * (secondRounded : ℝ) <
        2 * T 2 - T 1 / (BONE : ℝ) := by
    have hraw :
        2 * (secondRounded : ℝ) <
          T 1 * (exactCoefficient - 1) / (BONE : ℝ) := by
      calc
        2 * (secondRounded : ℝ) ≤
            (firstRounded : ℝ) * (coefficientProduct : ℝ) /
              (BONE : ℝ) := hsecondTwiceUpper
        _ ≤ T 1 * (coefficientProduct : ℝ) / (BONE : ℝ) :=
          div_le_div_of_nonneg_right hfirstCoefficient hB.le
        _ < T 1 * (exactCoefficient - 1) / (BONE : ℝ) :=
          (div_lt_div_iff_of_pos_right hB).2 hcoefficientFlip
    have hrec : T 2 = T 1 * (weight - 1) * (computedBase - 1) / 2 := by
      have := exactInputBinomialTerm_succ weight computedBase 1
      norm_num at this ⊢
      exact this
    have hid :
        T 1 * (exactCoefficient - 1) / (BONE : ℝ) =
          2 * T 2 - T 1 / (BONE : ℝ) := by
      rw [hrec]
      dsimp [exactCoefficient]
      field_simp [ne_of_gt hB]
      ring
    rw [hid] at hraw
    exact hraw
  let exactDirectional : ℝ :=
    (∑ k ∈ Finset.range 3, T k) + T 2
  have hdirectional : exactDirectional ≤ (BONE : ℝ) * computedBase ^ weight := by
    dsimp [exactDirectional, T]
    exact exact_input_binomial_doubled_last_partial_lower
      hweights.1.le hweights.2.le (lt_of_lt_of_le (by norm_num) hbaseHalf)
        hbaseStrict (by linarith) (n := 2) (by norm_num)
  have hdirectionalForm : exactDirectional = (BONE : ℝ) + T 1 + 2 * T 2 := by
    dsimp [exactDirectional, T]
    norm_num [Finset.sum_range_succ]
    ring
  have hpowerFloor : computedPower ≤ computedFractional := by
    rw [hcomputedPower]
    exact hcomposedFloor.le
  have hadverseSmall :
      computedPower - (BONE : ℝ) * computedBase ^ weight < |T 1| / (BONE : ℝ) := by
    have hcomputedDirectional :
        computedPower ≤
          (BONE : ℝ) + (firstRounded : ℝ) + 2 * (secondRounded : ℝ) := by
      rw [← hcomputedFractional]
      exact hpowerFloor
    have hcomputedVsDirectional :
        computedPower < exactDirectional - T 1 / (BONE : ℝ) := by
      rw [hdirectionalForm]
      linarith
    rw [abs_of_neg hfirstNonpos]
    calc
      computedPower - (BONE : ℝ) * computedBase ^ weight ≤
          computedPower - exactDirectional := sub_le_sub_left hdirectional _
      _ < (exactDirectional - T 1 / (BONE : ℝ)) - exactDirectional :=
        sub_lt_sub_right hcomputedVsDirectional exactDirectional
      _ = -T 1 / (BONE : ℝ) := by ring
  have hfeeScale :
      |T 1| / (BONE : ℝ) <
        (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          ((1 - weight) * |T 1|) := by
    have hfirstPositive : 0 < |T 1| := abs_pos.mpr hfirstNonpos.ne
    have hconstant :
        1 / (BONE : ℝ) <
          (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
            (1 - weight) := by
      rw [single_sided_token_withdrawal_adverse_fee_share_value,
        minimum_fee_rate_value]
      norm_num [BONE, MAX_WEIGHT, STROOP] at hweightUpper ⊢
      linarith
    have := mul_lt_mul_of_pos_right hconstant hfirstPositive
    convert this using 1 <;> ring
  have hfirstMagnitude : |T 1| = (BONE : ℝ) * weight * (1 - computedBase) := by
    simpa [T] using hfirstFacts.2
  have hfeeEq :
      (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          ((1 - weight) * |T 1|) =
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalComputedMinimumFeePowerValue
            weight computedBase := by
    rw [singleSidedTokenWithdrawalComputedMinimumFeePowerValue,
      hfirstMagnitude]
    ring
  rw [hfeeEq] at hfeeScale
  exact lt_trans hadverseSmall hfeeScale

/-- Full later-term baseline `c_pow` bound for the direct-weight withdrawal. -/
theorem baseline_single_sided_token_withdrawal_cpow_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n : ℕ}
    {weight computedBase computedFractional computedPower : ℝ}
    {computedPowerRaw : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hbaseHalf : 1 / 2 ≤ computedBase) (hbaseStrict : computedBase < 1)
    (hn3 : 3 ≤ n)
    (hn50 : n ≤ 50)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1)
        (exactInputBinomialTerm weight computedBase 1))
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (weight - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) +
        ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ) +
          (computedTerm n : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional) :
    computedPower - (BONE : ℝ) * computedBase ^ weight <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalComputedMinimumFeePowerValue
          weight computedBase := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  let T : ℕ → ℝ := exactInputBinomialTerm weight computedBase
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  have hrec : ∀ k,
      T (k + 1) =
        T k * (weight - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactInputBinomialTerm_succ weight computedBase k
  have hq0 : 0 < 1 - computedBase := by linarith
  have hx : |computedBase - 1| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hbaseStrict.le)]
    linarith
  have hfirstFacts := exactInputBinomialTerm_one hweights.1.le hbaseStrict.le
  have hfirstMagnitude : |T 1| =
      (BONE : ℝ) * weight * (1 - computedBase) := by
    simpa [T] using hfirstFacts.2
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [T, U]
    exact hfirstFloor.abs_error_lt_one
  have hfirstBelowScale : |T 1| < BONE := by
    rw [hfirstMagnitude]
    have hproduct : weight * (1 - computedBase) < 1 := by
      have hmul : weight * (1 - computedBase) ≤ 1 * (1 - computedBase) :=
        mul_le_mul_of_nonneg_right hweights.2.le hq0.le
      linarith
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    simpa only [mul_assoc, mul_one] using mul_lt_mul_of_pos_left hproduct hB
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T hweights.1.le hweights.2.le hx hrec (k - 1)
    have hindex : k - 1 + 1 = k := by omega
    rw [hindex] at hterms
    have hpower1 : (1 / 2 : ℝ) ^ (k - 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hscale : |T 1| * (1 / 2 : ℝ) ^ (k - 1) ≤ |T 1| := by
      nlinarith [abs_nonneg (T 1)]
    exact lt_of_le_of_lt (le_trans hterms hscale) hfirstBelowScale
  have herrorRec : ∀ k, 1 ≤ k → k < n →
      |T (k + 1) - U (k + 1)| <
        (1 + 1 / (((k + 1 : ℕ) : ℝ) * (BONE : ℝ))) * |T k - U k| +
          1 / ((k + 1 : ℕ) : ℝ) + 1 / ((k + 1 : ℕ) : ℝ) + 1 := by
    intro k hk hkn
    have hcoefficientNonpos : weight - (k : ℝ) ≤ 0 := by
      have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hcoefficientBound : |weight - (k : ℝ)| ≤ (k : ℝ) + 1 := by
      rw [abs_of_nonpos hcoefficientNonpos]
      linarith [hweights.1]
    have hstep := three_floor_recurrence_step_error
      (S := (BONE : ℝ)) (K := (k : ℝ) + 1)
      (exactPrevious := T k) (computedPrevious := U k)
      (coefficient := weight - (k : ℝ)) (displacement := computedBase - 1)
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
  have hn46 : n ≤ 46 := by
    by_contra hnot
    have hnlt : 46 < n := Nat.lt_of_not_ge hnot
    have herror46 : |T 46 - U 46| < 3 * (46 : ℝ) - 2 :=
      htermBounds 46 (by norm_num) (by omega)
    have hstopsBy46 : |U 46| < (CPOW_PRECISION : ℝ) :=
      pool_operating_base_converges_by_iteration_46
        T hweights.1.le hweights.2.le hbaseHalf
          (show computedBase ≤ 8 / 5 by linarith) htermZero hrec herror46
    have hstillRunning := hcontinued 46 (by norm_num) hnlt
    dsimp [U] at hstopsBy46
    linarith
  have hprevious : (CPOW_PRECISION : ℝ) < |U (n - 1)| := by
    simpa [U] using hcontinued (n - 1) (by omega) (by omega)
  have hpreviousError :
      |T (n - 1) - U (n - 1)| < 3 * ((n - 1 : ℕ) : ℝ) - 2 :=
    htermBounds (n - 1) (by omega) (by omega)
  have hcontinue := continued_loop_forces_weighted_first_term_scale
    T hweights.1.le hweights.2.le hx (by norm_num) hrec hn3 hprevious hpreviousError
  have hbudget := augmented_error_lt_half_later_fee_rate
    hn3 hn46 (by simpa [SINGLE_SIDED_TOKEN_WITHDRAWAL_LATER_FEE_RATE]
      using hcontinue)
  let exactPartial : ℝ :=
    ∑ k ∈ Finset.range (n + 1), T k
  let computedPartial : ℝ :=
    (BONE : ℝ) + ∑ k ∈ Finset.range n, U (k + 1)
  let exactDirectional : ℝ := exactPartial + T n
  have hdirectional : exactDirectional ≤ (BONE : ℝ) * computedBase ^ weight := by
    dsimp [exactDirectional, exactPartial, T]
    exact exact_input_binomial_doubled_last_partial_lower
      hweights.1.le hweights.2.le (lt_of_lt_of_le (by norm_num) hbaseHalf)
        hbaseStrict (by linarith) (n := n) (by omega)
  have hexactPartial :
      exactPartial = (BONE : ℝ) + ∑ k ∈ Finset.range n, T (k + 1) := by
    dsimp [exactPartial, T]
    rw [Finset.sum_range_succ']
    simp
    ring
  have hsumRaw := recurrence_implies_partial_sum_error_budget_until
    (BONE : ℝ) T U (show 1 ≤ n by omega) hn50 (by norm_num [BONE])
      hfirstError herrorRec
  have hsum : |exactPartial - computedPartial| < accumulatedError n := by
    rw [hexactPartial]
    dsimp [computedPartial]
    convert hsumRaw using 1
    simp [Nat.add_comm]
  have hlastError : |T n - U n| < 3 * (n : ℝ) - 2 :=
    htermBounds n (by omega) (by omega)
  have hdirectionalError :
      |exactDirectional - computedFractional| <
        accumulatedError n + (3 * (n : ℝ) - 2) := by
    have htriangle :
        |exactDirectional - computedFractional| ≤
          |exactPartial - computedPartial| + |T n - U n| := by
      rw [hcomputedFractional]
      dsimp [exactDirectional, computedPartial, U]
      have habs := abs_add (exactPartial -
        ((BONE : ℝ) + ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ)))
          (T n - (computedTerm n : ℝ))
      ring_nf at habs ⊢
      exact habs
    linarith
  have hadverse :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        accumulatedError n + (3 * (n : ℝ) - 2) := by
    have hpowerFloor : computedPower ≤ computedFractional := by
      rw [hcomputedPower]
      exact hcomposedFloor.le
    have hrounded : computedFractional - exactDirectional <
        accumulatedError n + (3 * (n : ℝ) - 2) :=
      lt_of_le_of_lt (le_abs_self _) (by simpa [abs_sub_comm] using hdirectionalError)
    linarith
  rw [singleSidedTokenWithdrawalComputedMinimumFeePowerValue]
  have hweightedFirst :
      (1 - weight) * |T 1| =
        (BONE : ℝ) * weight * (1 - weight) * (1 - computedBase) := by
    rw [hfirstMagnitude]
    ring
  rw [hweightedFirst] at hbudget
  have hscale0 :
      0 ≤ (BONE : ℝ) * weight * (1 - weight) * (1 - computedBase) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num [BONE]) hweights.1.le)
        (by linarith [hweights.2])) hq0.le
  have hrate :
      SINGLE_SIDED_TOKEN_WITHDRAWAL_LATER_FEE_RATE ≤
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
    simpa [SINGLE_SIDED_TOKEN_WITHDRAWAL_LATER_FEE_RATE,
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE] using
        half_augmented_later_fee_rate_le_selected_share
  have hscaledRate := mul_le_mul_of_nonneg_right hrate hscale0
  calc
    computedPower - (BONE : ℝ) * computedBase ^ weight <
        accumulatedError n + (3 * (n : ℝ) - 2) := hadverse
    _ < SINGLE_SIDED_TOKEN_WITHDRAWAL_LATER_FEE_RATE *
        ((BONE : ℝ) * weight * (1 - weight) * (1 - computedBase)) := hbudget
    _ ≤ (SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
        ((BONE : ℝ) * weight * (1 - weight) * (1 - computedBase)) :=
      hscaledRate
    _ = SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        (MIN_FEE_RATE *
          ((BONE : ℝ) * weight * (1 - weight) * (1 - computedBase))) := by
      ring

/-- Production output, weight, and fee bounds keep the exact adjusted ratio below `3/8`. -/
theorem single_sided_token_withdrawal_adjusted_ratio_le_three_eighths
    {nominalRatio weight feeRate : ℝ}
    (hnominalUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate)
    (hfeeUpper : feeRate ≤ (MAX_FEE : ℝ) / STROOP) :
    0 < 1 - singleSidedWithdrawalFeeRate weight feeRate ∧
      nominalRatio /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) ≤ 3 / 8 := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hfeeMax : (MAX_FEE : ℝ) / STROOP = 1 / 10 := by
    norm_num [MAX_FEE, STROOP]
  have hfee1 : feeRate ≤ 1 / 10 := by simpa [hfeeMax] using hfeeUpper
  have hweightComplement : 0 ≤ 1 - weight := by linarith
  have hweightComplementUpper : 1 - weight ≤ 9 / 10 := by
    norm_num [MIN_WEIGHT, STROOP] at hweightLower
    linarith
  have hweightedFeeUpper : (1 - weight) * feeRate ≤ 9 / 100 := by
    calc
      (1 - weight) * feeRate ≤ (9 / 10 : ℝ) * (1 / 10 : ℝ) :=
        mul_le_mul hweightComplementUpper hfee1 hfee0 (by norm_num)
      _ = 9 / 100 := by norm_num
  have hdenom : 0 < 1 - singleSidedWithdrawalFeeRate weight feeRate := by
    rw [singleSidedWithdrawalFeeRate]
    linarith
  constructor
  · exact hdenom
  · apply (div_le_iff₀ hdenom).2
    have hnominalNumeric : nominalRatio ≤ 1666667 / 5000000 := by
      norm_num [MAX_OUT_RATIO, STROOP] at hnominalUpper ⊢
      exact hnominalUpper
    rw [singleSidedWithdrawalFeeRate]
    nlinarith

/--
In the low-base region, the favorable rounded-base displacement is larger
than the entire below-one tail after the first exact term. Thus the first
partial at the rounded base is already no greater than the exact adjusted
power.
-/
theorem single_sided_token_withdrawal_low_base_first_partial_le_ideal
    {weight adjustedRatio computedBase : ℝ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hadjusted0 : 0 < adjustedRatio) (hadjustedUpper : adjustedRatio ≤ 3 / 8)
    (hbasePositive : 0 < computedBase) (hbaseHalf : computedBase ≤ 1 / 2) :
    (BONE : ℝ) + exactInputBinomialTerm weight computedBase 1 ≤
      (BONE : ℝ) * (1 - adjustedRatio) ^ weight := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  let q : ℝ := 1 - computedBase
  let idealBase : ℝ := 1 - adjustedRatio
  let T : ℕ → ℝ := exactInputBinomialTerm weight idealBase
  have hqHalf : 1 / 2 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hr0 : 0 ≤ adjustedRatio := hadjusted0.le
  have hr1 : adjustedRatio < 1 := lt_of_le_of_lt hadjustedUpper (by norm_num)
  have hideal0 : 0 < idealBase := by dsimp [idealBase]; linarith
  have hideal1 : idealBase < 1 := by dsimp [idealBase]; linarith
  have htail := exact_input_binomial_partial_tail_le
    hweights.1.le hweights.2.le hideal0 hideal1 (n := 2) (by norm_num)
  have hfirstIdeal := exactInputBinomialTerm_one hweights.1.le hideal1.le
  have hsecondRec := exactInputBinomialTerm_succ weight idealBase 1
  have hfirstIdealEq :
      T 1 = -(BONE : ℝ) * weight * adjustedRatio := by
    dsimp [T]
    rw [hfirstIdeal.1]
    dsimp [idealBase]
    ring
  have hsecondIdealEq :
      T 2 = -(BONE : ℝ) * weight * (1 - weight) * adjustedRatio ^ 2 / 2 := by
    have hsecondRecT :
        T 2 = T 1 * (weight - 1) * (idealBase - 1) / 2 := by
      norm_num at hsecondRec
      simpa [T] using hsecondRec
    rw [hsecondRecT, hfirstIdealEq]
    dsimp [idealBase]
    ring
  have hsecondNonpos : T 2 ≤ 0 := by
    rw [hsecondIdealEq]
    have hnonneg :
        0 ≤ (BONE : ℝ) * weight * (1 - weight) * adjustedRatio ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num [BONE]) hweights.1.le)
          (by linarith [hweights.2])) (sq_nonneg adjustedRatio)
    linarith
  have hpartial :
      ∑ k ∈ Finset.range 3, T k = (BONE : ℝ) + T 1 + T 2 := by
    dsimp [T]
    norm_num [Finset.sum_range_succ]
  have htailOne :
      ((BONE : ℝ) + T 1) -
          (BONE : ℝ) * idealBase ^ weight ≤
        |T 2| / (1 - adjustedRatio) := by
    change (∑ k ∈ Finset.range 3, T k) -
        (BONE : ℝ) * idealBase ^ weight ≤
          |T 2| * (1 - idealBase) / idealBase at htail
    rw [hpartial] at htail
    have htail' :
        (BONE : ℝ) + T 1 + T 2 -
            (BONE : ℝ) * idealBase ^ weight ≤
          |T 2| * adjustedRatio / (1 - adjustedRatio) := by
      change (BONE : ℝ) + T 1 + T 2 -
          (BONE : ℝ) * (1 - adjustedRatio) ^ weight ≤
        |T 2| * (1 - (1 - adjustedRatio)) / (1 - adjustedRatio) at htail
      rw [show 1 - (1 - adjustedRatio) = adjustedRatio by ring] at htail
      exact htail
    have hdenom : 0 < 1 - adjustedRatio := by linarith
    have hid :
        -T 2 * adjustedRatio / (1 - adjustedRatio) - T 2 =
          -T 2 / (1 - adjustedRatio) := by
      field_simp [ne_of_gt hdenom]
      ring
    rw [abs_of_nonpos hsecondNonpos] at htail' ⊢
    linarith
  have hcomplementUpper : 1 - weight ≤ 9 / 10 := by
    norm_num [MIN_WEIGHT, STROOP] at hweightLower
    linarith
  have hrSquare : adjustedRatio ^ 2 ≤ (3 / 8 : ℝ) ^ 2 := by
    nlinarith
  have hleft :
      (1 - weight) * adjustedRatio ^ 2 ≤ 81 / 640 := by
    calc
      (1 - weight) * adjustedRatio ^ 2 ≤
          (9 / 10 : ℝ) * (3 / 8 : ℝ) ^ 2 :=
        mul_le_mul hcomplementUpper hrSquare (sq_nonneg adjustedRatio)
          (by linarith [hweights.2])
      _ = 81 / 640 := by norm_num
  have hright :
      5 / 32 ≤ 2 * (1 - adjustedRatio) * (q - adjustedRatio) := by
    have hqGap : 0 ≤ q - 1 / 2 := by linarith
    have honeMinus : 0 ≤ 1 - adjustedRatio := by linarith
    have hqMonotone :
        2 * (1 - adjustedRatio) * (1 / 2 - adjustedRatio) ≤
          2 * (1 - adjustedRatio) * (q - adjustedRatio) := by
      nlinarith [mul_nonneg honeMinus hqGap]
    have hfactor1 : 0 ≤ 3 / 8 - adjustedRatio := by linarith
    have hfactor2 : 0 ≤ 9 / 8 - adjustedRatio := by linarith
    have hlower :
        5 / 32 ≤
          2 * (1 - adjustedRatio) * (1 / 2 - adjustedRatio) := by
      nlinarith [mul_nonneg hfactor1 hfactor2]
    exact le_trans hlower hqMonotone
  have htailFactor :
      (1 - weight) * adjustedRatio ^ 2 ≤
        2 * (1 - adjustedRatio) * (q - adjustedRatio) := by
    exact le_trans hleft (le_trans
      (show (81 / 640 : ℝ) ≤ 5 / 32 by norm_num) hright)
  have htailMargin :
      (BONE : ℝ) * weight * (1 - weight) * adjustedRatio ^ 2 / 2 /
          (1 - adjustedRatio) ≤
        (BONE : ℝ) * weight * (q - adjustedRatio) := by
    have hdenom : 0 < 2 * (1 - adjustedRatio) := by positivity
    have hnormalized :
        (1 - weight) * adjustedRatio ^ 2 / (2 * (1 - adjustedRatio)) ≤
          q - adjustedRatio := by
      apply (div_le_iff₀ hdenom).2
      simpa only [mul_assoc, mul_left_comm, mul_comm] using htailFactor
    have hscale : 0 ≤ (BONE : ℝ) * weight :=
      mul_nonneg (by norm_num [BONE]) hweights.1.le
    have := mul_le_mul_of_nonneg_left hnormalized hscale
    calc
      (BONE : ℝ) * weight * (1 - weight) * adjustedRatio ^ 2 / 2 /
          (1 - adjustedRatio) =
        ((BONE : ℝ) * weight) *
          ((1 - weight) * adjustedRatio ^ 2 /
            (2 * (1 - adjustedRatio))) := by
          field_simp [ne_of_gt (show 0 < 1 - adjustedRatio by linarith)]
          ring
      _ ≤ ((BONE : ℝ) * weight) * (q - adjustedRatio) := this
      _ = (BONE : ℝ) * weight * (q - adjustedRatio) := by ring
  have hfirstComputed := exactInputBinomialTerm_one
    hweights.1.le (show computedBase ≤ 1 by linarith)
  have hfirstComputedEq :
      exactInputBinomialTerm weight computedBase 1 =
        -(BONE : ℝ) * weight * q := by
    rw [hfirstComputed.1]
    dsimp [q]
    ring
  rw [abs_of_nonpos hsecondNonpos, hsecondIdealEq] at htailOne
  rw [hfirstIdealEq] at htailOne
  rw [hfirstComputedEq]
  dsimp [idealBase] at htailOne ⊢
  have htailOne' :
      (BONE : ℝ) - (BONE : ℝ) * weight * adjustedRatio -
          (BONE : ℝ) * (1 - adjustedRatio) ^ weight ≤
        (BONE : ℝ) * weight * (1 - weight) * adjustedRatio ^ 2 / 2 /
          (1 - adjustedRatio) := by
    convert htailOne using 1 <;> ring
  linarith

/-- One concrete below-one recurrence update preserves non-positivity. -/
theorem baseline_below_one_floor_recurrence_step_nonpos
    {k : ℕ} {weight computedBase : ℝ}
    {previous coefficientProduct multiplied next : ℤ}
    (hk : 1 ≤ k) (hweight1 : weight ≤ 1) (hbase1 : computedBase ≤ 1)
    (hprevious : (previous : ℝ) ≤ 0)
    (hcoefficientFloor :
      IsFloor coefficientProduct
        ((BONE : ℝ) * (weight - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyFloor :
      IsFloor multiplied
        ((previous : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ)))
    (hdivideFloor :
      IsFloor next ((multiplied : ℝ) / ((k : ℝ) + 1))) :
    (next : ℝ) ≤ 0 := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoefficientExact0 :
      0 ≤ (BONE : ℝ) * (weight - (k : ℝ)) * (computedBase - 1) := by
    have hw : weight - (k : ℝ) ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hB.le hw) (by linarith)
  have hcoefficientRaw0 : 0 ≤ coefficientProduct := by
    by_contra hnot
    have hraw : coefficientProduct + 1 ≤ 0 := by omega
    have hrawReal : (coefficientProduct : ℝ) + 1 ≤ 0 := by
      exact_mod_cast hraw
    linarith [hcoefficientFloor.lt_add_one]
  have hproduct0 :
      (previous : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hprevious (by exact_mod_cast hcoefficientRaw0))
      hB.le
  have hmultiplied0 : (multiplied : ℝ) ≤ 0 :=
    le_trans hmultiplyFloor.le hproduct0
  have hdivisor0 : 0 ≤ (k : ℝ) + 1 := by positivity
  exact le_trans hdivideFloor.le
    (div_nonpos_of_nonpos_of_nonneg hmultiplied0 hdivisor0)

/-- Every computed term in a concrete below-one direct-weight trace is non-positive. -/
theorem baseline_below_one_floor_recurrence_terms_nonpos
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n : ℕ} {weight computedBase : ℝ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hbase1 : computedBase ≤ 1)
    (hfirstFloor :
      IsFloor (computedTerm 1)
        (exactInputBinomialTerm weight computedBase 1))
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (weight - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1))) :
    ∀ k, 1 ≤ k → k ≤ n → (computedTerm k : ℝ) ≤ 0 := by
  intro k
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro hk hkn
      by_cases hk0 : k = 0
      · subst k
        exact le_trans hfirstFloor.le
          (exactInputBinomialTerm_nonpos hweight0 hweight1 hbase1 (by norm_num))
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hkltn : k < n := by omega
        exact baseline_below_one_floor_recurrence_step_nonpos
          hk1 hweight1 hbase1 (ih hk1 (by omega))
            (hcoefficientFloor k hk1 hkltn)
            (hmultiplyTermFloor k hk1 hkltn)
            (hdivideTermFloor k hk1 hkltn)

/-- A power rounded below the exact adjusted power cannot undercharge LP tokens. -/
theorem single_sided_token_withdrawal_pool_favoring_power_has_no_adverse_error
    {poolSupply weight feeRate nominalRatio computedPower computedInput scale : ℝ}
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hnominal : 0 < nominalRatio)
    (hfeeDenom : 0 < 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hpower : computedPower ≤ (BONE : ℝ) *
      singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight)
    (hcomputedInput :
      poolSupply / scale * (1 - computedPower / (BONE : ℝ)) ≤
        computedInput) :
    singleSidedTokenWithdrawalIdealInput
        (poolSupply / scale) weight feeRate nominalRatio - computedInput <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hsupply : 0 < poolSupply / scale := div_pos hpoolSupply hscale
  have hidealLe :
      singleSidedTokenWithdrawalIdealInput
          (poolSupply / scale) weight feeRate nominalRatio ≤
        computedInput := by
    rw [singleSidedTokenWithdrawalIdealInput]
    calc
      poolSupply / scale *
          (1 - singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ^ weight) ≤
        poolSupply / scale * (1 - computedPower / (BONE : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hsupply.le
          have hnormalizedPower :
              computedPower / (BONE : ℝ) ≤
                singleSidedTokenWithdrawalIdealBase
                  weight feeRate nominalRatio ^ weight := by
            apply (div_le_iff₀ hB).2
            simpa [mul_comm] using hpower
          linarith
      _ ≤ computedInput := hcomputedInput
  have hfeePositive :
      0 < SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
    rw [singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue,
      minimum_fee_rate_value]
    rw [single_sided_token_withdrawal_adverse_fee_share_value]
    have hraw :
        0 < (1 / 1000000 : ℝ) *
          ((poolSupply / scale) * weight * (1 - weight) * nominalRatio) := by
      exact mul_pos (by norm_num)
        (mul_pos (mul_pos (mul_pos hsupply hweight0) (by linarith)) hnominal)
    have hpositive := mul_pos (by norm_num : (0 : ℝ) < 4751 / 100000)
      (div_pos hraw hfeeDenom)
    exact hpositive
  linarith

/--
Configured weights, a positive exact output, and the caller's fixed-point
ceil/floor refinements establish the fee denominator, base direction, and
strict below-one base used by the operation proof.
-/
theorem single_sided_token_withdrawal_configured_caller_bounds
    {inputBalance inputAmount nominalRatio feeMultiplier beforeFeeRatio
      computedBase weight feeRate : ℝ}
    {beforeFee computedBaseRaw : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hbeforeFeeRatio : beforeFeeRatio = (beforeFee : ℝ) / inputBalance)
    (hbeforeFeeCeil : IsCeil beforeFee (inputAmount / feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 - beforeFeeRatio))) :
    0 < nominalRatio ∧ 0 < feeMultiplier ∧
      nominalRatio / feeMultiplier ≤ beforeFeeRatio ∧
      computedBase ≤
        singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio ∧
      computedBase < 1 := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hfeeFactor0 : 0 ≤ 1 - weight := by linarith
  have hweightedFeeUpper : (1 - weight) * feeRate ≤ 1 - weight := by
    simpa using mul_le_mul_of_nonneg_left hfee1 hfeeFactor0
  have hfeeMultiplierPositive : 0 < feeMultiplier := by
    rw [hfeeMultiplier, singleSidedWithdrawalFeeRate]
    linarith
  have hadjusted := single_sided_token_withdrawal_before_fee_ceil_refines
    hinputBalance hnominal hbeforeFeeRatio hbeforeFeeCeil
  have hbase := single_sided_token_withdrawal_base_floor_refines
    hcomputedBase hbaseFloor
  have hbaseIdeal := single_sided_token_withdrawal_computed_base_le_ideal
    hfeeMultiplier hadjusted hbase
  have hadjustedPositive : 0 < nominalRatio / feeMultiplier :=
    div_pos hnominalPositive hfeeMultiplierPositive
  have hidealStrict :
      singleSidedTokenWithdrawalIdealBase weight feeRate nominalRatio < 1 := by
    rw [singleSidedTokenWithdrawalIdealBase, ← hfeeMultiplier]
    linarith
  exact ⟨hnominalPositive, hfeeMultiplierPositive, hadjusted, hbaseIdeal,
    lt_of_le_of_lt hbaseIdeal hidealStrict⟩

/-- Instantiate the exact-token-output operation theorem from caller refinements. -/
theorem single_sided_token_withdrawal_from_fixed_point_refinements_precise_fee_share
    {inputBalance inputAmount nominalRatio feeMultiplier beforeFeeRatio
      computedBase computedPower poolSupply weight feeRate scale : ℝ}
    {beforeFee computedBaseRaw newPoolSupply result output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hbeforeFeeRatio : beforeFeeRatio = (beforeFee : ℝ) / inputBalance)
    (hbeforeFeeCeil : IsCeil beforeFee (inputAmount / feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 - beforeFeeRatio)))
    (hbasePositive : 0 < computedBase)
    (hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalComputedMinimumFeePowerValue
            weight computedBase)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hresult : (result : ℝ) = poolSupply - (newPoolSupply : ℝ))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedTokenWithdrawalIdealInput
        (poolSupply / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
  have hcaller := single_sided_token_withdrawal_configured_caller_bounds
    hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
      hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hadjusted0 :
      0 ≤ nominalRatio /
        (1 - singleSidedWithdrawalFeeRate weight feeRate) := by
    rw [← hfeeMultiplier]
    exact (div_pos hcaller.1 hcaller.2.1).le
  have hinput := single_sided_token_withdrawal_input_ceil_chain
    hscale hnewSupplyFloor hresult hdownscaleCeil
  exact single_sided_token_withdrawal_adverse_error_lt_precise_fee_share
    hpoolSupply hscale hweights.1.le hweights.2.le
      (by rw [← hfeeMultiplier]; exact hcaller.2.1) hadjusted0
      hbasePositive hcaller.2.2.2.1 hcpow hinput

/-- Complete corrected-first-term comparison for `wdr_tokn_amt_out_get_lp_tokns_in`. -/
theorem baseline_single_sided_token_withdrawal_first_term_adverse_error_lt_precise_fee_share
    {inputBalance inputAmount nominalRatio feeMultiplier beforeFeeRatio
      computedBase computedFractional computedPower poolSupply weight feeRate
      scale : ℝ}
    {beforeFee computedBaseRaw firstRounded computedPowerRaw newPoolSupply
      result output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hbeforeFeeRatio : beforeFeeRatio = (beforeFee : ℝ) / inputBalance)
    (hbeforeFeeCeil : IsCeil beforeFee (inputAmount / feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 - beforeFeeRatio)))
    (hbasePositive : 0 < computedBase)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm weight computedBase 1))
    (hstop : |(firstRounded : ℝ)| ≤ CPOW_PRECISION)
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) + (firstRounded : ℝ) - 1)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hresult : (result : ℝ) = poolSupply - (newPoolSupply : ℝ))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedTokenWithdrawalIdealInput
        (poolSupply / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
  have hcaller := single_sided_token_withdrawal_configured_caller_bounds
    hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
      hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
  have hconservative :=
    baseline_single_sided_token_withdrawal_cpow_first_term_has_no_adverse_error
      hweightLower hweightUpper hbasePositive hcaller.2.2.2.2 hfirstFloor hstop
        hcomputedFractional hcomputedPower hcomposedFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hfeePositive :
      0 < singleSidedTokenWithdrawalComputedMinimumFeePowerValue
        weight computedBase := by
    rw [singleSidedTokenWithdrawalComputedMinimumFeePowerValue,
      minimum_fee_rate_value]
    exact mul_pos (by norm_num)
      (mul_pos (mul_pos (mul_pos (by norm_num [BONE]) hweights.1)
        (by linarith [hweights.2])) (by linarith [hcaller.2.2.2.2]))
  have hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalComputedMinimumFeePowerValue
            weight computedBase := by
    have hshare :
        0 < SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedTokenWithdrawalComputedMinimumFeePowerValue
            weight computedBase :=
      mul_pos (by
        rw [single_sided_token_withdrawal_adverse_fee_share_value]
        norm_num) hfeePositive
    linarith
  exact single_sided_token_withdrawal_from_fixed_point_refinements_precise_fee_share
    hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
      hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
      hbasePositive hcpow hpoolSupply hscale
      hnewSupplyFloor hresult hdownscaleCeil

/-- Complete second-term comparison for `wdr_tokn_amt_out_get_lp_tokns_in`. -/
theorem baseline_single_sided_token_withdrawal_second_term_adverse_error_lt_precise_fee_share
    {inputBalance inputAmount nominalRatio feeMultiplier beforeFeeRatio
      computedBase computedFractional computedPower poolSupply weight feeRate
      scale : ℝ}
    {beforeFee computedBaseRaw firstRounded coefficientProduct multiplied
      secondRounded computedPowerRaw newPoolSupply result output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate)
    (hfeeUpper : feeRate ≤ (MAX_FEE : ℝ) / STROOP)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hbeforeFeeRatio : beforeFeeRatio = (beforeFee : ℝ) / inputBalance)
    (hbeforeFeeCeil : IsCeil beforeFee (inputAmount / feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 - beforeFeeRatio)))
    (hbasePositive : 0 < computedBase)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm weight computedBase 1))
    (hcoefficientFloor :
      IsFloor coefficientProduct
        ((BONE : ℝ) * (weight - 1) * (computedBase - 1)))
    (hmultiplyFloor :
      IsFloor multiplied
        ((firstRounded : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ)))
    (hdivideFloor : IsFloor secondRounded ((multiplied : ℝ) / 2))
    (hcomputedFractional :
      computedFractional =
        (BONE : ℝ) + (firstRounded : ℝ) + 2 * (secondRounded : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hresult : (result : ℝ) = poolSupply - (newPoolSupply : ℝ))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedTokenWithdrawalIdealInput
        (poolSupply / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
  have hfee1 : feeRate ≤ 1 := by
    exact le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hcaller := single_sided_token_withdrawal_configured_caller_bounds
    hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
      hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
  by_cases hbaseHalf : 1 / 2 ≤ computedBase
  · have hcpow :=
      baseline_single_sided_token_withdrawal_cpow_second_term_adverse_error_lt_precise_fee_share
        hweightLower hweightUpper hbaseHalf hcaller.2.2.2.2 hfirstFloor
          hcoefficientFloor hmultiplyFloor hdivideFloor hcomputedFractional
          hcomputedPower hcomposedFloor
    exact single_sided_token_withdrawal_from_fixed_point_refinements_precise_fee_share
      hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
        hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
        hbasePositive hcpow hpoolSupply hscale hnewSupplyFloor hresult
        hdownscaleCeil
  · have hweights := single_sided_token_deposit_configured_weight_bounds
      hweightLower hweightUpper
    have hadjustedBounds :=
      single_sided_token_withdrawal_adjusted_ratio_le_three_eighths
        hnominalUpper hweightLower hweightUpper hfee0 hfeeUpper
    have hadjustedPositive :
        0 < nominalRatio /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) :=
      div_pos hcaller.1 hadjustedBounds.1
    have hbaseLe : computedBase ≤ 1 / 2 := le_of_not_ge hbaseHalf
    have hfirstIdeal :=
      single_sided_token_withdrawal_low_base_first_partial_le_ideal
        hweightLower hweightUpper hadjustedPositive hadjustedBounds.2
          hbasePositive hbaseLe
    have hfirstExactNonpos :
        exactInputBinomialTerm weight computedBase 1 ≤ 0 :=
      exactInputBinomialTerm_nonpos hweights.1.le hweights.2.le
        hcaller.2.2.2.2.le (by norm_num)
    have hfirstRoundedNonpos : (firstRounded : ℝ) ≤ 0 :=
      le_trans hfirstFloor.le hfirstExactNonpos
    have hcoefficientFloor' :
        IsFloor coefficientProduct
          ((BONE : ℝ) * (weight - (1 : ℕ)) * (computedBase - 1)) := by
      norm_num
      exact hcoefficientFloor
    have hdivideFloor' :
        IsFloor secondRounded ((multiplied : ℝ) / ((1 : ℕ) + 1)) := by
      norm_num
      exact hdivideFloor
    have hsecondNonpos : (secondRounded : ℝ) ≤ 0 :=
      baseline_below_one_floor_recurrence_step_nonpos
        (k := 1) (by norm_num) hweights.2.le hcaller.2.2.2.2.le
          hfirstRoundedNonpos hcoefficientFloor' hmultiplyFloor hdivideFloor'
    have hcomputedFirst :
        computedPower ≤
          (BONE : ℝ) + exactInputBinomialTerm weight computedBase 1 := by
      have hpowerFloor : computedPower ≤ computedFractional := by
        rw [hcomputedPower]
        exact hcomposedFloor.le
      linarith [hfirstFloor.le]
    have hpowerIdeal :
        computedPower ≤ (BONE : ℝ) *
          singleSidedTokenWithdrawalIdealBase
            weight feeRate nominalRatio ^ weight := by
      calc
        computedPower ≤
            (BONE : ℝ) +
              exactInputBinomialTerm weight computedBase 1 := hcomputedFirst
        _ ≤ (BONE : ℝ) *
            (1 - nominalRatio /
              (1 - singleSidedWithdrawalFeeRate weight feeRate)) ^ weight :=
          hfirstIdeal
        _ = (BONE : ℝ) *
            singleSidedTokenWithdrawalIdealBase
              weight feeRate nominalRatio ^ weight := by
          rw [singleSidedTokenWithdrawalIdealBase]
    have hinput := single_sided_token_withdrawal_input_ceil_chain
      hscale hnewSupplyFloor hresult hdownscaleCeil
    exact single_sided_token_withdrawal_pool_favoring_power_has_no_adverse_error
      hpoolSupply hscale hweights.1 hweights.2 hcaller.1 hadjustedBounds.1
        hpowerIdeal hinput

/--
Complete later-term comparison for `wdr_tokn_amt_out_get_lp_tokns_in`
across both base regions. Inside the standard operating band, the concrete
trace itself proves that the loop must stop no later than iteration 46.
-/
theorem baseline_single_sided_token_withdrawal_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n : ℕ}
    {inputBalance inputAmount nominalRatio feeMultiplier beforeFeeRatio
      computedBase computedFractional computedPower poolSupply weight feeRate
      scale : ℝ}
    {beforeFee computedBaseRaw computedPowerRaw newPoolSupply result output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate)
    (hfeeUpper : feeRate ≤ (MAX_FEE : ℝ) / STROOP)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hbeforeFeeRatio : beforeFeeRatio = (beforeFee : ℝ) / inputBalance)
    (hbeforeFeeCeil : IsCeil beforeFee (inputAmount / feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 - beforeFeeRatio)))
    (hbasePositive : 0 < computedBase)
    (hn3 : 3 ≤ n)
    (hn50 : n ≤ 50)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1)
        (exactInputBinomialTerm weight computedBase 1))
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (weight - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < n →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) +
        ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ) +
          (computedTerm n : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hresult : (result : ℝ) = poolSupply - (newPoolSupply : ℝ))
    (hdownscaleCeil : IsCeil output ((result : ℝ) / scale)) :
    singleSidedTokenWithdrawalIdealInput
        (poolSupply / scale) weight feeRate nominalRatio - (output : ℝ) <
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          (poolSupply / scale) weight feeRate nominalRatio := by
  have hfee1 : feeRate ≤ 1 := by
    exact le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hcaller := single_sided_token_withdrawal_configured_caller_bounds
    hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
      hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
  by_cases hbaseHalf : 1 / 2 ≤ computedBase
  · have hcpow :=
      baseline_single_sided_token_withdrawal_cpow_later_adverse_error_lt_precise_fee_share
        coefficientProduct multiplied computedTerm hweightLower hweightUpper
          hbaseHalf hcaller.2.2.2.2 hn3 hn50 hcontinued hfirstFloor
          hcoefficientFloor hmultiplyTermFloor hdivideTermFloor
          hcomputedFractional hcomputedPower hcomposedFloor
    exact single_sided_token_withdrawal_from_fixed_point_refinements_precise_fee_share
      hinputBalance hinputAmount hnominal hweightLower hweightUpper hfee1
        hfeeMultiplier hbeforeFeeRatio hbeforeFeeCeil hcomputedBase hbaseFloor
        hbasePositive hcpow hpoolSupply hscale hnewSupplyFloor hresult
        hdownscaleCeil
  · have hweights := single_sided_token_deposit_configured_weight_bounds
      hweightLower hweightUpper
    have hadjustedBounds :=
      single_sided_token_withdrawal_adjusted_ratio_le_three_eighths
        hnominalUpper hweightLower hweightUpper hfee0 hfeeUpper
    have hadjustedPositive :
        0 < nominalRatio /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) :=
      div_pos hcaller.1 hadjustedBounds.1
    have hbaseLe : computedBase ≤ 1 / 2 := le_of_not_ge hbaseHalf
    have hfirstIdeal :=
      single_sided_token_withdrawal_low_base_first_partial_le_ideal
        hweightLower hweightUpper hadjustedPositive hadjustedBounds.2
          hbasePositive hbaseLe
    have htermsNonpos := baseline_below_one_floor_recurrence_terms_nonpos
      coefficientProduct multiplied computedTerm (n := n)
        hweights.1.le hweights.2.le
        hcaller.2.2.2.2.le hfirstFloor hcoefficientFloor hmultiplyTermFloor
        hdivideTermFloor
    have hsumTailNonpos :
        ∑ k ∈ Finset.range (n - 1), (computedTerm (k + 2) : ℝ) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      have hkUpper : k + 2 ≤ n := by
        have hkBound : k < n - 1 := Finset.mem_range.mp hk
        omega
      exact htermsNonpos (k + 2) (by omega) hkUpper
    have hsumFirst :
        ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ) ≤
          (computedTerm 1 : ℝ) := by
      rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ']
      simpa [add_assoc] using add_le_add_left hsumTailNonpos (computedTerm 1 : ℝ)
    have hlastNonpos : (computedTerm n : ℝ) ≤ 0 :=
      htermsNonpos n (by omega) le_rfl
    have hcomputedFirst :
        computedPower ≤
          (BONE : ℝ) + exactInputBinomialTerm weight computedBase 1 := by
      have hpowerFloor : computedPower ≤ computedFractional := by
        rw [hcomputedPower]
        exact hcomposedFloor.le
      linarith [hfirstFloor.le]
    have hpowerIdeal :
        computedPower ≤ (BONE : ℝ) *
          singleSidedTokenWithdrawalIdealBase
            weight feeRate nominalRatio ^ weight := by
      calc
        computedPower ≤
            (BONE : ℝ) +
              exactInputBinomialTerm weight computedBase 1 := hcomputedFirst
        _ ≤ (BONE : ℝ) *
            (1 - nominalRatio /
              (1 - singleSidedWithdrawalFeeRate weight feeRate)) ^ weight :=
          hfirstIdeal
        _ = (BONE : ℝ) *
            singleSidedTokenWithdrawalIdealBase
              weight feeRate nominalRatio ^ weight := by
          rw [singleSidedTokenWithdrawalIdealBase]
    have hinput := single_sided_token_withdrawal_input_ceil_chain
      hscale hnewSupplyFloor hresult hdownscaleCeil
    exact single_sided_token_withdrawal_pool_favoring_power_has_no_adverse_error
      hpoolSupply hscale hweights.1 hweights.2 hcaller.1 hadjustedBounds.1
        hpowerIdeal hinput

end CometPool
