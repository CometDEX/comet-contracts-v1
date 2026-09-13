import CometPool.Operations.SingleSidedDeposit

namespace CometPool

/-!
Operation-level model for `dep_tokn_amt_in_get_lp_tokns_out`, the
single-sided deposit that accepts an exact underlying-token amount and mints
LP tokens. Its `c_pow` path has an above-one base, the direct normalized
weight as an exponent, and `round_up = false`.
-/

/-- The exact fee-adjusted balance ratio for an exact-token-input deposit. -/
noncomputable def singleSidedTokenDepositIdealBase
    (weight feeRate nominalRatio : ℝ) : ℝ :=
  1 + (1 - singleSidedWithdrawalFeeRate weight feeRate) * nominalRatio

/-- Exact LP-token output in the pool supply's unit. -/
noncomputable def singleSidedTokenDepositIdealOutput
    (poolSupply weight feeRate nominalRatio : ℝ) : ℝ :=
  poolSupply *
    (singleSidedTokenDepositIdealBase weight feeRate nominalRatio ^ weight - 1)

/-- Minimum weighted-fee spot value in raw `c_pow` units. -/
noncomputable def singleSidedTokenDepositMinimumFeePowerValue
    (weight nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
    ((BONE : ℝ) * weight * (1 - weight) * nominalRatio)

/-- Minimum weighted-fee spot value in the LP token's unit. -/
noncomputable def singleSidedTokenDepositMinimumFeeOutputValue
    (poolSupply weight nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE * (poolSupply * weight * (1 - weight) * nominalRatio)

/--
The certified adverse-error share of the weighted minimum fee. The tightest
finite later-stop case is iteration 4 with retained degree 4, which requires
approximately `1.2222228%`; `1.223%` is a simple strict rational ceiling.
-/
noncomputable def SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE : ℝ :=
  1223 / 100000

/-- The certified share expressed as a rate applied to the weighted first term. -/
noncomputable def SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE : ℝ :=
  SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE

theorem single_sided_token_deposit_adverse_fee_share_value :
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE = (1223 : ℝ) / 100000 := by
  rfl

theorem single_sided_token_deposit_adverse_fee_rate_value :
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE =
      (1223 : ℝ) / 100000000000 := by
  norm_num [SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE,
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE, MIN_FEE_RATE, MIN_FEE, STROOP]

/-- Flooring the fee-adjusted token amount gives the caller's ratio bound. -/
theorem single_sided_token_deposit_adjusted_floor_refines_ratio
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier : ℝ}
    {adjustedInput : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier)) :
    adjustedRatio ≤ feeMultiplier * nominalRatio := by
  rw [hadjustedRatio, hnominal]
  calc
    (adjustedInput : ℝ) / inputBalance ≤
        (inputAmount * feeMultiplier) / inputBalance :=
      div_le_div_of_nonneg_right hadjustedFloor.le hinputBalance.le
    _ = feeMultiplier * (inputAmount / inputBalance) := by ring

/-- The normalized balance-ratio floor lies between one and its exact ratio. -/
theorem single_sided_token_deposit_base_floor_refines
    {adjustedRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio))) :
    1 ≤ computedBase ∧ computedBase ≤ 1 + adjustedRatio := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hexactLower :
      (BONE : ℝ) ≤ (BONE : ℝ) * (1 + adjustedRatio) := by
    nlinarith only [hB, hadjusted0]
  have hrawLower : (BONE : ℤ) ≤ computedBaseRaw := by
    by_contra hnot
    have hraw : computedBaseRaw + 1 ≤ (BONE : ℤ) := by omega
    have hrawReal : (computedBaseRaw : ℝ) + 1 ≤ (BONE : ℝ) := by
      exact_mod_cast hraw
    linarith [hbaseFloor.lt_add_one]
  constructor
  · rw [hcomputedBase]
    exact (le_div_iff₀ hB).2 (by exact_mod_cast hrawLower)
  · rw [hcomputedBase]
    exact hbaseFloor.normalized_le hB

/-- The caller's floors can only reduce the base relative to the ideal formula. -/
theorem single_sided_token_deposit_computed_base_le_ideal
    {weight feeRate nominalRatio adjustedRatio computedBase : ℝ}
    (hadjusted :
      adjustedRatio ≤
        (1 - singleSidedWithdrawalFeeRate weight feeRate) * nominalRatio)
    (hbase : computedBase ≤ 1 + adjustedRatio) :
    computedBase ≤
      singleSidedTokenDepositIdealBase weight feeRate nominalRatio := by
  rw [singleSidedTokenDepositIdealBase]
  linarith

/-- A smaller above-one base gives no larger power for a non-negative weight. -/
theorem single_sided_token_deposit_rounded_power_below_ideal
    {weight feeRate nominalRatio computedBase : ℝ}
    (hweight0 : 0 ≤ weight) (hcomputedBase0 : 0 ≤ computedBase)
    (hbase : computedBase ≤
      singleSidedTokenDepositIdealBase weight feeRate nominalRatio) :
    computedBase ^ weight ≤
      singleSidedTokenDepositIdealBase weight feeRate nominalRatio ^ weight := by
  exact Real.rpow_le_rpow hcomputedBase0 hbase hweight0

/-- The new-supply and token downscale floors cannot increase LP output. -/
theorem single_sided_token_deposit_output_floor_chain
    {newPoolSupply poolAmountOut output : ℤ}
    {poolSupply computedPower scale : ℝ}
    (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) ≤
      poolSupply / scale * (computedPower / (BONE : ℝ) - 1) := by
  have hamount :
      (poolAmountOut : ℝ) ≤
        poolSupply * (computedPower / (BONE : ℝ) - 1) := by
    rw [hpoolAmount]
    linarith [hnewSupplyFloor.le]
  have hscaled := (div_le_div_iff_of_pos_right hscale).2 hamount
  calc
    (output : ℝ) ≤ (poolAmountOut : ℝ) / scale := hdownscaleFloor.le
    _ ≤ poolSupply * (computedPower / (BONE : ℝ) - 1) / scale := hscaled
    _ = poolSupply / scale * (computedPower / (BONE : ℝ) - 1) := by ring

/-- Compose a raw `c_pow` bound with the ideal deposit and caller floors. -/
theorem single_sided_token_deposit_adverse_error_lt_fee_share
    {feeShare poolSupply weight feeRate nominalRatio computedBase computedPower
      computedOutput : ℝ}
    (hpoolSupply : 0 < poolSupply)
    (hweight0 : 0 ≤ weight)
    (hcomputedBase0 : 0 ≤ computedBase)
    (hbase : computedBase ≤
      singleSidedTokenDepositIdealBase weight feeRate nominalRatio)
    (hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        feeShare * singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio)
    (hcomputedOutput :
      computedOutput ≤
        poolSupply * (computedPower / (BONE : ℝ) - 1)) :
    computedOutput -
      singleSidedTokenDepositIdealOutput
          poolSupply weight feeRate nominalRatio <
      feeShare * singleSidedTokenDepositMinimumFeeOutputValue
        poolSupply weight nominalRatio := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hpowerDirection := single_sided_token_deposit_rounded_power_below_ideal
    hweight0 hcomputedBase0 hbase
  have hrawDirection :
      (BONE : ℝ) * computedBase ^ weight ≤
        (BONE : ℝ) *
          singleSidedTokenDepositIdealBase weight feeRate nominalRatio ^ weight :=
    mul_le_mul_of_nonneg_left hpowerDirection hB.le
  have hadversePower :
      computedPower - (BONE : ℝ) *
          singleSidedTokenDepositIdealBase weight feeRate nominalRatio ^ weight <
        feeShare * singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
    linarith
  have hcallerScale : 0 < poolSupply / (BONE : ℝ) := div_pos hpoolSupply hB
  have hscaled := mul_lt_mul_of_pos_left hadversePower hcallerScale
  calc
    computedOutput -
          singleSidedTokenDepositIdealOutput
            poolSupply weight feeRate nominalRatio ≤
        poolSupply * (computedPower / (BONE : ℝ) - 1) -
          singleSidedTokenDepositIdealOutput
            poolSupply weight feeRate nominalRatio :=
      sub_le_sub_right hcomputedOutput _
    _ = (poolSupply / (BONE : ℝ)) *
        (computedPower - (BONE : ℝ) *
          singleSidedTokenDepositIdealBase weight feeRate nominalRatio ^ weight) := by
      rw [singleSidedTokenDepositIdealOutput]
      field_simp [ne_of_gt hB]
      ring
    _ < (poolSupply / (BONE : ℝ)) *
        (feeShare *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio) :=
      hscaled
    _ = feeShare * singleSidedTokenDepositMinimumFeeOutputValue
          poolSupply weight nominalRatio := by
      rw [singleSidedTokenDepositMinimumFeePowerValue,
        singleSidedTokenDepositMinimumFeeOutputValue]
      field_simp [ne_of_gt hB]
      ring

/-- Instantiate the operation theorem from the fixed-point caller refinements. -/
theorem single_sided_token_deposit_from_fixed_point_refinements_fee_share
    {feeShare inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase computedPower poolSupply weight feeRate scale : ℝ}
    {adjustedInput computedBaseRaw newPoolSupply poolAmountOut output : ℤ}
    (hinputBalance : 0 < inputBalance)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio)))
    (hweight0 : 0 ≤ weight)
    (hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        feeShare * singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) -
      singleSidedTokenDepositIdealOutput
          (poolSupply / scale) weight feeRate nominalRatio <
      feeShare * singleSidedTokenDepositMinimumFeeOutputValue
        (poolSupply / scale) weight nominalRatio := by
  have hadjusted0 : 0 ≤ adjustedRatio := by
    rw [hadjustedRatio]
    positivity
  have hadjusted := single_sided_token_deposit_adjusted_floor_refines_ratio
    hinputBalance hnominal hadjustedRatio hadjustedFloor
  rw [hfeeMultiplier] at hadjusted
  have hbaseBounds := single_sided_token_deposit_base_floor_refines
    hadjusted0 hcomputedBase hbaseFloor
  have hbaseIdeal := single_sided_token_deposit_computed_base_le_ideal
    hadjusted hbaseBounds.2
  have houtput := single_sided_token_deposit_output_floor_chain
    hscale hnewSupplyFloor hpoolAmount hdownscaleFloor
  exact single_sided_token_deposit_adverse_error_lt_fee_share
    (div_pos hpoolSupply hscale) hweight0 (le_trans (by norm_num) hbaseBounds.1)
      hbaseIdeal hcpow houtput

/-- Production weights give the strict direct-exponent interval `(0,1)`. -/
theorem single_sided_token_deposit_configured_weight_bounds
    {weight : ℝ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP) :
    0 < weight ∧ weight < 1 := by
  constructor
  · have hmin : (0 : ℝ) < (MIN_WEIGHT : ℝ) / STROOP := by
      norm_num [MIN_WEIGHT, STROOP]
    exact lt_of_lt_of_le hmin hweightLower
  · have hmax : (MAX_WEIGHT : ℝ) / STROOP < 1 := by
      norm_num [MAX_WEIGHT, STROOP]
    exact lt_of_le_of_lt hweightUpper hmax

/-- The pre-call input guard places the direct deposit base in `[1,1.6]`. -/
theorem single_sided_token_deposit_configured_base_bounds
    {nominalRatio adjustedRatio feeMultiplier computedBase : ℝ}
    (hnominal0 : 0 ≤ nominalRatio)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hfeeMultiplier1 : feeMultiplier ≤ 1)
    (hadjusted : adjustedRatio ≤ feeMultiplier * nominalRatio)
    (hbaseOne : 1 ≤ computedBase)
    (hbaseUpper : computedBase ≤ 1 + adjustedRatio) :
    computedBase ≤ 8 / 5 ∧
      computedBase - 1 ≤ nominalRatio ∧
      |computedBase - 1| ≤ 3 / 5 := by
  have hadjustedNominal : adjustedRatio ≤ nominalRatio := by
    calc
      adjustedRatio ≤ feeMultiplier * nominalRatio := hadjusted
      _ ≤ 1 * nominalRatio :=
        mul_le_mul_of_nonneg_right hfeeMultiplier1 hnominal0
      _ = nominalRatio := one_mul _
  have hmax : (MAX_IN_RATIO : ℝ) / STROOP < 3 / 5 := by
    norm_num [MAX_IN_RATIO, STROOP]
  have hdisplacement : computedBase - 1 ≤ nominalRatio := by linarith
  constructor
  · linarith
  · constructor
    · exact hdisplacement
    · rw [abs_of_nonneg (sub_nonneg.mpr hbaseOne)]
      exact le_trans hdisplacement (le_trans hnominalUpper (le_of_lt hmax))

/-- The weighted minimum-fee value dominates the precise weighted first-term rate. -/
theorem single_sided_token_deposit_precise_fee_value_dominates_weighted_first_term
    {S weight q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hqNominal : q ≤ nominalRatio)
    (hfirst : firstTerm = S * weight * q)
    (hfee :
      feeValue = MIN_FEE_RATE * (S * weight * (1 - weight) * nominalRatio)) :
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE *
        ((1 - weight) * firstTerm) ≤
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * feeValue := by
  have hfactor0 : 0 ≤ S * weight * (1 - weight) :=
    mul_nonneg (mul_nonneg hS0 hweight0) (sub_nonneg.mpr hweight1)
  have hratio :
      S * weight * (1 - weight) * q ≤
        S * weight * (1 - weight) * nominalRatio :=
    mul_le_mul_of_nonneg_left hqNominal hfactor0
  have hrate0 :
      0 ≤ SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
    rw [single_sided_token_deposit_adverse_fee_share_value,
      minimum_fee_rate_value]
    norm_num
  calc
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE *
          ((1 - weight) * firstTerm) =
        (SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (S * weight * (1 - weight) * q) := by
      rw [SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE, hfirst]
      ring
    _ ≤ (SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (S * weight * (1 - weight) * nominalRatio) :=
      mul_le_mul_of_nonneg_left hratio hrate0
    _ = SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * feeValue := by
      rw [hfee]
      ring

set_option maxHeartbeats 1000000 in
/--
The public maximum-input ratio and retained-even-degree control flow bound the
later accumulated error by `1.223%` of the weighted first-term fee scale.
-/
theorem single_sided_token_deposit_later_accumulated_error_lt_precise_fee_rate
    {n degree evenIndex : ℕ} {weightedFirstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hdegreeEven : degree = 2 * evenIndex + 2)
    (hdegreeStop : degree = n ∨ degree + 1 = n)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        weightedFirstTerm *
            (((MAX_IN_RATIO : ℝ) / STROOP) / 2) *
            ((MAX_IN_RATIO : ℝ) / STROOP) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError degree <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE * weightedFirstTerm := by
  rcases hdegreeStop with hdegree | hdegree
  · rw [hdegree] at hdegreeEven ⊢
    interval_cases n <;>
      norm_num [accumulatedError,
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE,
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE, MIN_FEE_RATE,
        MIN_FEE, MAX_IN_RATIO, STROOP, CPOW_PRECISION]
        at hdegreeEven hcontinue ⊢ <;>
      (try omega) <;>
      nlinarith
  · have hdegreeValue : degree = n - 1 := by omega
    rw [hdegreeValue] at hdegreeEven ⊢
    interval_cases n <;>
      norm_num [accumulatedError,
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE,
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE, MIN_FEE_RATE,
        MIN_FEE, MAX_IN_RATIO, STROOP, CPOW_PRECISION]
        at hdegreeEven hcontinue ⊢ <;>
      (try omega) <;>
      nlinarith

/-- The exact positive second term magnitude for a direct-weight deposit. -/
theorem single_sided_token_deposit_second_term
    (weight computedBase : ℝ) :
    exactOutputBinomialTerm weight computedBase 2 =
      -(BONE : ℝ) * weight * (1 - weight) * (computedBase - 1) ^ 2 / 2 := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    exactOutputBinomialTerm_succ, exactOutputBinomialTerm_one]
  norm_num
  ring

/-- A first stop's omitted second-order scale is below `1.223%` of the minimum fee. -/
theorem single_sided_token_deposit_first_stop_second_term_lt_precise_fee_share
    {weight q nominalRatio firstExact : ℝ} {firstRounded : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hq0 : 0 < q) (hqNominal : q ≤ nominalRatio)
    (hfirst : firstExact = (BONE : ℝ) * weight * q)
    (hfirstFloor : IsFloor firstRounded firstExact)
    (hstop : |(firstRounded : ℝ)| ≤ CPOW_PRECISION) :
    (BONE : ℝ) * weight * (1 - weight) * q ^ 2 / 2 <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hfirstUpper : firstExact < (CPOW_PRECISION : ℝ) + 1 := by
    have hroundedUpper : (firstRounded : ℝ) ≤ CPOW_PRECISION :=
      le_trans (le_abs_self _) hstop
    linarith [hfirstFloor.lt_add_one]
  have hqHalfRate : q / 2 < SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE := by
    rw [hfirst] at hfirstUpper
    rw [single_sided_token_deposit_adverse_fee_rate_value]
    norm_num [BONE, CPOW_PRECISION, MIN_WEIGHT, STROOP] at hweightLower hfirstUpper ⊢
    nlinarith [mul_pos hweights.1 hq0]
  have hrate0 : 0 ≤ SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE := by
    rw [single_sided_token_deposit_adverse_fee_rate_value]
    norm_num
  have hqSquared :
      q ^ 2 / 2 <
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE * nominalRatio := by
    have hleft := mul_lt_mul_of_pos_left hqHalfRate hq0
    have hright := mul_le_mul_of_nonneg_right hqNominal hrate0
    calc
      q ^ 2 / 2 = q * (q / 2) := by ring
      _ < q * SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE := hleft
      _ ≤ nominalRatio * SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE := hright
      _ = SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE * nominalRatio := by ring
  have hfactor : 0 < (BONE : ℝ) * weight * (1 - weight) :=
    mul_pos (mul_pos (by norm_num [BONE]) hweights.1) (by linarith)
  have hscaled := mul_lt_mul_of_pos_left hqSquared hfactor
  rw [SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE] at hscaled
  rw [singleSidedTokenDepositMinimumFeePowerValue]
  nlinarith only [hscaled]

/-- The corrected first-term round-down result stays within the weighted fee budget. -/
theorem baseline_single_sided_token_deposit_cpow_first_term_adverse_error_lt_precise_fee_share
    {weight nominalRatio computedBase computedFractional computedPower : ℝ}
    {firstRounded computedPowerRaw : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hbaseStrict : 1 < computedBase)
    (hqNominal : computedBase - 1 ≤ nominalRatio)
    (hfirstFloor :
      IsFloor firstRounded (exactOutputBinomialTerm weight computedBase 1))
    (hstop : |(firstRounded : ℝ)| ≤ CPOW_PRECISION)
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) + (firstRounded : ℝ) - 1)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional) :
    computedPower - (BONE : ℝ) * computedBase ^ weight <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  let T : ℕ → ℝ := exactOutputBinomialTerm weight computedBase
  let exactPartial : ℝ := ∑ k ∈ Finset.range 3, T k
  have hpartialLower : exactPartial ≤ (BONE : ℝ) * computedBase ^ weight := by
    dsimp [exactPartial, T]
    simpa using exact_output_binomial_even_partial_lower
      hweights.1.le hweights.2.le hbaseStrict 0
  have hpartial : exactPartial =
      (BONE : ℝ) + T 1 + T 2 := by
    norm_num [exactPartial, T, Finset.sum_range_succ]
  have hfirst : T 1 = (BONE : ℝ) * weight * (computedBase - 1) := by
    exact exactOutputBinomialTerm_one weight computedBase
  have hsecond : T 2 =
      -(BONE : ℝ) * weight * (1 - weight) * (computedBase - 1) ^ 2 / 2 := by
    exact single_sided_token_deposit_second_term weight computedBase
  have hsecondBudget :=
    single_sided_token_deposit_first_stop_second_term_lt_precise_fee_share
    hweightLower hweightUpper (by linarith) hqNominal hfirst hfirstFloor hstop
  have hpowerFloor : computedPower ≤ computedFractional := by
    rw [hcomputedPower]
    exact hcomposedFloor.le
  have hadverse :
      computedPower - (BONE : ℝ) * computedBase ^ weight ≤ -T 2 := by
    have hcomputedPartial :
        computedFractional ≤ (BONE : ℝ) + T 1 - 1 := by
      rw [hcomputedFractional]
      linarith [hfirstFloor.le]
    rw [hpartial] at hpartialLower
    linarith
  rw [hsecond] at hadverse
  exact lt_of_le_of_lt hadverse (by nlinarith [hsecondBudget])

/-- At the second stop, the three term floors retain an even lower partial. -/
theorem baseline_single_sided_token_deposit_cpow_second_term_has_no_adverse_error
    {weight computedBase computedFractional computedPower : ℝ}
    {firstRounded coefficientProduct multiplied secondRounded computedPowerRaw : ℤ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hbaseStrict : 1 < computedBase)
    (hdisplacement : computedBase - 1 ≤ 3 / 5)
    (hfirstRounded0 : 0 ≤ firstRounded)
    (hfirstFloor :
      IsFloor firstRounded (exactOutputBinomialTerm weight computedBase 1))
    (hcoefficientFloor :
      IsFloor coefficientProduct
        ((BONE : ℝ) * (weight - 1) * (computedBase - 1)))
    (hmultiplyFloor :
      IsFloor multiplied
        ((firstRounded : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ)))
    (hdivideFloor : IsFloor secondRounded ((multiplied : ℝ) / 2))
    (hcomputedFractional :
      computedFractional =
        (BONE : ℝ) + (firstRounded : ℝ) + (secondRounded : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional) :
    computedPower ≤ (BONE : ℝ) * computedBase ^ weight := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hq0 : 0 ≤ computedBase - 1 := sub_nonneg.mpr hbaseStrict.le
  let T : ℕ → ℝ := exactOutputBinomialTerm weight computedBase
  let exactPartial : ℝ := ∑ k ∈ Finset.range 3, T k
  have hpartialLower : exactPartial ≤ (BONE : ℝ) * computedBase ^ weight := by
    dsimp [exactPartial, T]
    simpa using exact_output_binomial_even_partial_lower
      hweight0 hweight1 hbaseStrict 0
  have hpartial : exactPartial = (BONE : ℝ) + T 1 + T 2 := by
    norm_num [exactPartial, T, Finset.sum_range_succ]
  have hsecond : T 2 =
      T 1 * (weight - 1) * (computedBase - 1) / 2 := by
    change exactOutputBinomialTerm weight computedBase 2 =
      exactOutputBinomialTerm weight computedBase 1 * (weight - 1) *
        (computedBase - 1) / 2
    have h := exactOutputBinomialTerm_succ weight computedBase 1
    norm_num at h
    exact h
  have hmultiplyUpper :
      (multiplied : ℝ) ≤
        (firstRounded : ℝ) * (weight - 1) * (computedBase - 1) := by
    calc
      (multiplied : ℝ) ≤
          (firstRounded : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ) :=
        hmultiplyFloor.le
      _ ≤ (firstRounded : ℝ) *
          ((BONE : ℝ) * (weight - 1) * (computedBase - 1)) /
            (BONE : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoefficientFloor.le
            (by exact_mod_cast hfirstRounded0)) hB.le
      _ = (firstRounded : ℝ) * (weight - 1) * (computedBase - 1) := by
        field_simp [ne_of_gt hB]
        ring
  have hsecondRoundedUpper :
      (secondRounded : ℝ) ≤
        (firstRounded : ℝ) * (weight - 1) * (computedBase - 1) / 2 := by
    exact le_trans hdivideFloor.le
      (div_le_div_of_nonneg_right hmultiplyUpper (by norm_num))
  have hfactor :
      0 ≤ 1 + (weight - 1) * (computedBase - 1) / 2 := by
    have hcoefficientLower : -(computedBase - 1) ≤
        (weight - 1) * (computedBase - 1) := by
      have := mul_le_mul_of_nonneg_right
        (show (-1 : ℝ) ≤ weight - 1 by linarith) hq0
      simpa using this
    nlinarith
  have hfirstDifference : 0 ≤ T 1 - (firstRounded : ℝ) := by
    exact sub_nonneg.mpr hfirstFloor.le
  have hcomputedPartial : computedFractional ≤ exactPartial := by
    rw [hcomputedFractional, hpartial, hsecond]
    have hproduct := mul_nonneg hfirstDifference hfactor
    have hpartialDifference :
        0 ≤
          (T 1 + T 1 * (weight - 1) * (computedBase - 1) / 2) -
            ((firstRounded : ℝ) +
              (firstRounded : ℝ) * (weight - 1) * (computedBase - 1) / 2) := by
      calc
        _ = (T 1 - (firstRounded : ℝ)) *
            (1 + (weight - 1) * (computedBase - 1) / 2) := by ring
        _ ≥ 0 := hproduct
    linarith
  have hpowerFloor : computedPower ≤ computedFractional := by
    rw [hcomputedPower]
    exact hcomposedFloor.le
  exact le_trans hpowerFloor (le_trans hcomputedPartial hpartialLower)

/-- A unit direct-deposit base is exact and has no adverse `c_pow` error. -/
theorem baseline_single_sided_token_deposit_cpow_unit_base_has_no_adverse_error
    {weight computedBase computedPower : ℝ}
    (hbase : computedBase = 1) (hpower : computedPower ≤ BONE) :
    computedPower ≤ (BONE : ℝ) * computedBase ^ weight := by
  simpa [hbase] using hpower

/-- Any no-correction result at most `BONE` is conservative for an above-one base. -/
theorem baseline_single_sided_token_deposit_cpow_no_correction_has_no_adverse_error
    {weight computedBase computedPower : ℝ}
    (hweight0 : 0 ≤ weight) (hbaseOne : 1 ≤ computedBase)
    (hpower : computedPower ≤ BONE) :
    computedPower ≤ (BONE : ℝ) * computedBase ^ weight := by
  have hpowerOne : 1 ≤ computedBase ^ weight :=
    Real.one_le_rpow hbaseOne hweight0
  have hscaled := mul_le_mul_of_nonneg_left hpowerOne
    (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  exact le_trans hpower (by simpa using hscaled)

/-
For an above-one round-down trace, an even final term is retained. If the
final term is odd and positive, the baseline removes it, leaving the
preceding even partial. Thus `degree` is even in both later-stop branches.
-/

/-- Full later-term baseline `c_pow` bound for the direct-weight deposit. -/
theorem baseline_single_sided_token_deposit_cpow_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n degree evenIndex : ℕ}
    {weight nominalRatio computedBase computedFractional computedPower : ℝ}
    {computedPowerRaw : ℤ}
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hbaseOne : 1 ≤ computedBase)
    (hbaseUpper : computedBase ≤ 8 / 5)
    (hqNominal : computedBase - 1 ≤ nominalRatio)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hn3 : 3 ≤ n)
    (hn50 : n ≤ 50)
    (hdegreeEven : degree = 2 * evenIndex + 2)
    (hdegreeStop : degree = n ∨ degree + 1 = n)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1)
        (exactOutputBinomialTerm weight computedBase 1))
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
        ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional) :
    computedPower - (BONE : ℝ) * computedBase ^ weight <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  let T : ℕ → ℝ := exactOutputBinomialTerm weight computedBase
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  have hrec : ∀ k,
      T (k + 1) =
        T k * (weight - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactOutputBinomialTerm_succ weight computedBase k
  have hfirstExact : T 1 =
      (BONE : ℝ) * weight * (computedBase - 1) := by
    exact exactOutputBinomialTerm_one weight computedBase
  have hdisplacement0 : 0 ≤ computedBase - 1 := sub_nonneg.mpr hbaseOne
  have hfirstNonnegative : 0 ≤ T 1 := by
    rw [hfirstExact]
    exact mul_nonneg (mul_nonneg (by norm_num [BONE]) hweights.1.le)
      hdisplacement0
  have hfirstMagnitude : |T 1| =
      (BONE : ℝ) * weight * (computedBase - 1) := by
    rw [abs_of_nonneg hfirstNonnegative, hfirstExact]
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [T, U]
    exact hfirstFloor.abs_error_lt_one
  have hfirstBelowScale : |T 1| < BONE := by
    rw [hfirstMagnitude]
    have hproduct : weight * (computedBase - 1) < 1 := by
      have hweightOne : weight ≤ 1 := hweights.2.le
      have hmul : weight * (computedBase - 1) ≤ 1 * (computedBase - 1) :=
        mul_le_mul_of_nonneg_right hweightOne hdisplacement0
      have hq : computedBase - 1 ≤ 3 / 5 := by linarith
      linarith
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    simpa only [mul_assoc, mul_one] using mul_lt_mul_of_pos_left hproduct hB
  have hx : |computedBase - 1| ≤ (3 / 5 : ℝ) := by
    rw [abs_of_nonneg hdisplacement0]
    linarith
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T hweights.1.le hweights.2.le hx hrec (k - 1)
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
    by_contra hn
    have herror46 : |T 46 - U 46| < 3 * (46 : ℝ) - 2 :=
      htermBounds 46 (by norm_num) (by omega)
    have hstopsBy46 : |U 46| < (CPOW_PRECISION : ℝ) :=
      pool_operating_base_converges_by_iteration_46
        T hweights.1.le hweights.2.le
          (by linarith : (1 / 2 : ℝ) ≤ computedBase)
          hbaseUpper htermZero hrec herror46
    have hstillRunning := hcontinued 46 (by norm_num) (by omega)
    dsimp [U] at hstopsBy46
    linarith
  have hprevious : (CPOW_PRECISION : ℝ) < |U (n - 1)| := by
    simpa [U] using hcontinued (n - 1) (by omega) (by omega)
  have htermError :
      |T (n - 1) - U (n - 1)| < 3 * ((n - 1 : ℕ) : ℝ) - 2 :=
    htermBounds (n - 1) (by omega) (by omega)
  have hfirstRounded0 : 0 ≤ computedTerm 1 := by
    have hexact0 : 0 ≤ exactOutputBinomialTerm weight computedBase 1 := by
      simpa [T] using hfirstNonnegative
    by_contra hnot
    have hraw : computedTerm 1 + 1 ≤ 0 := by omega
    have hrawReal : (computedTerm 1 : ℝ) + 1 ≤ 0 := by exact_mod_cast hraw
    linarith [hfirstFloor.lt_add_one]
  have hbaseStrict : 1 < computedBase := by
    by_contra hnot
    have hbaseEq : computedBase = 1 := le_antisymm (le_of_not_gt hnot) hbaseOne
    have hroundedUpper : (computedTerm 1 : ℝ) ≤ 0 := by
      rw [hbaseEq, exactOutputBinomialTerm_one] at hfirstFloor
      norm_num at hfirstFloor
      exact hfirstFloor.le
    have hroundedZero : (computedTerm 1 : ℝ) = 0 := by
      exact le_antisymm hroundedUpper (by exact_mod_cast hfirstRounded0)
    have hcontinueOne := hcontinued 1 (by norm_num) (by omega)
    rw [hroundedZero, abs_zero] at hcontinueOne
    have : (0 : ℝ) ≤ CPOW_PRECISION := by positivity
    linarith
  let exactPartial : ℝ :=
    ∑ k ∈ Finset.range (degree + 1), exactOutputBinomialTerm weight computedBase k
  have hpartialLower : exactPartial ≤ (BONE : ℝ) * computedBase ^ weight := by
    dsimp [exactPartial]
    rw [hdegreeEven]
    exact exact_output_binomial_even_partial_lower
      hweights.1.le hweights.2.le hbaseStrict evenIndex
  have hexactPartial :
      exactPartial = (BONE : ℝ) + ∑ k ∈ Finset.range degree, T (k + 1) := by
    dsimp [exactPartial, T]
    rw [Finset.sum_range_succ']
    simp
    ring
  have hdegree1 : 1 ≤ degree := by rw [hdegreeEven]; omega
  have hdegreeN : degree ≤ n := by rcases hdegreeStop with h | h <;> omega
  have hdegree50 : degree ≤ 50 := le_trans hdegreeN hn50
  have hsumRaw := recurrence_implies_partial_sum_error_budget_until
    (BONE : ℝ) T U hdegree1 hdegree50 (by norm_num [BONE]) hfirstError
      (fun k hk hdegree ↦ herrorRec k hk (lt_of_lt_of_le hdegree hdegreeN))
  have hsumDegree : |exactPartial - computedFractional| < accumulatedError degree := by
    rw [hexactPartial, hcomputedFractional, accumulatedError]
    convert hsumRaw using 1
    simp [U, Nat.add_comm]
  have hrounded : computedFractional - exactPartial < accumulatedError degree := by
    exact lt_of_le_of_lt (le_abs_self _)
      (by simpa [abs_sub_comm] using hsumDegree)
  have hxConfigured :
      |computedBase - 1| ≤ (MAX_IN_RATIO : ℝ) / STROOP := by
    rw [abs_of_nonneg hdisplacement0]
    exact le_trans hqNominal hnominalUpper
  have hcontinue := continued_loop_forces_weighted_first_term_scale
    T hweights.1.le hweights.2.le hxConfigured
      (by norm_num [MAX_IN_RATIO, STROOP]) hrec hn3 hprevious htermError
  have hbudget :=
    single_sided_token_deposit_later_accumulated_error_lt_precise_fee_rate
      (weightedFirstTerm := (1 - weight) * |T 1|)
      hn3 hn46 hdegreeEven hdegreeStop (by simpa using hcontinue)
  have hfeeDominates :=
    single_sided_token_deposit_precise_fee_value_dominates_weighted_first_term
      (S := (BONE : ℝ)) (weight := weight) (q := computedBase - 1)
      (nominalRatio := nominalRatio) (firstTerm := |T 1|)
      (feeValue := singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio)
      (by norm_num [BONE]) hweights.1.le hweights.2.le hqNominal
      hfirstMagnitude (by rfl)
  have hfractional :
      computedFractional - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
    calc
      computedFractional - (BONE : ℝ) * computedBase ^ weight ≤
          computedFractional - exactPartial :=
        sub_le_sub_left hpartialLower computedFractional
      _ < accumulatedError degree := hrounded
      _ < SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_RATE *
          ((1 - weight) * |T 1|) := hbudget
      _ ≤ SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio :=
        hfeeDominates
  have hpowerFloor : computedPower ≤ computedFractional := by
    rw [hcomputedPower]
    exact hcomposedFloor.le
  linarith

/-- Common production caller premises establish all direct-deposit base bounds. -/
theorem single_sided_token_deposit_configured_caller_bounds
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase weight feeRate : ℝ}
    {adjustedInput computedBaseRaw : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio))) :
    0 ≤ nominalRatio ∧ 0 ≤ adjustedRatio ∧
      adjustedRatio ≤ feeMultiplier * nominalRatio ∧
      1 ≤ computedBase ∧ computedBase ≤ 8 / 5 ∧
      computedBase - 1 ≤ nominalRatio ∧
      |computedBase - 1| ≤ 3 / 5 := by
  have hnominal0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hadjusted0 : 0 ≤ adjustedRatio := by rw [hadjustedRatio]; positivity
  have hadjusted := single_sided_token_deposit_adjusted_floor_refines_ratio
    hinputBalance hnominal hadjustedRatio hadjustedFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hfeeBounds := single_sided_withdrawal_fee_multiplier_bounds
    hweights.1.le hweights.2.le hfee0 hfee1
  have hfeeMultiplier1 : feeMultiplier ≤ 1 := by
    rw [hfeeMultiplier]
    exact hfeeBounds.2
  have hbase := single_sided_token_deposit_base_floor_refines
    hadjusted0 hcomputedBase hbaseFloor
  have hconfigured := single_sided_token_deposit_configured_base_bounds
    hnominal0 hnominalUpper hfeeMultiplier1 hadjusted hbase.1 hbase.2
  exact ⟨hnominal0, hadjusted0, hadjusted, hbase.1,
    hconfigured.1, hconfigured.2.1, hconfigured.2.2⟩

/-- Positive input and configured weight make the minimum-fee power value positive. -/
theorem single_sided_token_deposit_minimum_fee_power_value_positive
    {weight nominalRatio : ℝ}
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hnominal : 0 < nominalRatio) :
    0 < singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
  rw [singleSidedTokenDepositMinimumFeePowerValue, minimum_fee_rate_value]
  exact mul_pos (by norm_num)
    (mul_pos (mul_pos (mul_pos (by norm_num [BONE]) hweight0) (by linarith))
      hnominal)

/-- Complete unit-base comparison for `dep_tokn_amt_in_get_lp_tokns_out`. -/
theorem baseline_single_sided_token_deposit_unit_base_adverse_error_lt_precise_fee_share
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase computedPower poolSupply weight feeRate scale : ℝ}
    {adjustedInput computedBaseRaw newPoolSupply poolAmountOut output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio)))
    (hunitBase : computedBase = 1)
    (hcomputedPower : computedPower = (BONE : ℝ))
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedTokenDepositIdealOutput
          (poolSupply / scale) weight feeRate nominalRatio <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue
          (poolSupply / scale) weight nominalRatio := by
  have hcaller := single_sided_token_deposit_configured_caller_bounds
    hinputBalance hinputAmount hnominal hnominalUpper hweightLower hweightUpper
      hfee0 hfee1 hfeeMultiplier hadjustedInput0 hadjustedRatio hadjustedFloor
      hcomputedBase hbaseFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hfeePositive := single_sided_token_deposit_minimum_fee_power_value_positive
    hweights.1 hweights.2 hnominalPositive
  have hconservative := baseline_single_sided_token_deposit_cpow_unit_base_has_no_adverse_error
    (weight := weight) hunitBase (le_of_eq hcomputedPower)
  have hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
    have hshare :
        0 < SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio :=
      mul_pos (by
        rw [single_sided_token_deposit_adverse_fee_share_value]
        norm_num) hfeePositive
    linarith
  exact single_sided_token_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE)
      hinputBalance hnominal hadjustedInput0 hadjustedRatio hadjustedFloor
      hfeeMultiplier hcomputedBase hbaseFloor hweights.1.le hcpow hpoolSupply
      hscale hnewSupplyFloor hpoolAmount hdownscaleFloor

/-- Complete corrected-first-term comparison for the exact-token-input deposit. -/
theorem baseline_single_sided_token_deposit_first_term_adverse_error_lt_precise_fee_share
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase computedFractional computedPower poolSupply weight feeRate scale : ℝ}
    {adjustedInput computedBaseRaw firstRounded computedPowerRaw newPoolSupply
      poolAmountOut output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio)))
    (hfirstRoundedPositive : 0 < firstRounded)
    (hfirstFloor :
      IsFloor firstRounded (exactOutputBinomialTerm weight computedBase 1))
    (hstop : |(firstRounded : ℝ)| ≤ CPOW_PRECISION)
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) + (firstRounded : ℝ) - 1)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedTokenDepositIdealOutput
          (poolSupply / scale) weight feeRate nominalRatio <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue
          (poolSupply / scale) weight nominalRatio := by
  have hcaller := single_sided_token_deposit_configured_caller_bounds
    hinputBalance hinputAmount hnominal hnominalUpper hweightLower hweightUpper
      hfee0 hfee1 hfeeMultiplier hadjustedInput0 hadjustedRatio hadjustedFloor
      hcomputedBase hbaseFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hbaseStrict : 1 < computedBase := by
    by_contra hnot
    have hbaseEq : computedBase = 1 :=
      le_antisymm (le_of_not_gt hnot) hcaller.2.2.2.1
    have hroundedUpper : (firstRounded : ℝ) ≤ 0 := by
      exact le_trans hfirstFloor.le (by
        rw [exactOutputBinomialTerm_one, hbaseEq]
        norm_num)
    have hroundedPositive : (0 : ℝ) < firstRounded := by
      exact_mod_cast hfirstRoundedPositive
    linarith
  have hcpow :=
    baseline_single_sided_token_deposit_cpow_first_term_adverse_error_lt_precise_fee_share
      hweightLower hweightUpper hbaseStrict hcaller.2.2.2.2.2.1 hfirstFloor
        hstop hcomputedFractional hcomputedPower hcomposedFloor
  exact single_sided_token_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE)
      hinputBalance hnominal hadjustedInput0 hadjustedRatio hadjustedFloor
      hfeeMultiplier hcomputedBase hbaseFloor hweights.1.le hcpow hpoolSupply
      hscale hnewSupplyFloor hpoolAmount hdownscaleFloor

/-- Complete zero-first-term, no-correction comparison for the exact-token-input deposit. -/
theorem baseline_single_sided_token_deposit_zero_first_term_adverse_error_lt_precise_fee_share
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase computedFractional computedPower poolSupply weight feeRate scale : ℝ}
    {adjustedInput computedBaseRaw firstRounded computedPowerRaw newPoolSupply
      poolAmountOut output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio)))
    (hfirstRounded : firstRounded = 0)
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) + (firstRounded : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedTokenDepositIdealOutput
          (poolSupply / scale) weight feeRate nominalRatio <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue
          (poolSupply / scale) weight nominalRatio := by
  have hcaller := single_sided_token_deposit_configured_caller_bounds
    hinputBalance hinputAmount hnominal hnominalUpper hweightLower hweightUpper
      hfee0 hfee1 hfeeMultiplier hadjustedInput0 hadjustedRatio hadjustedFloor
      hcomputedBase hbaseFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hpowerAtMostBone : computedPower ≤ BONE := by
    rw [hcomputedPower]
    exact le_trans hcomposedFloor.le (by rw [hcomputedFractional, hfirstRounded]; norm_num)
  have hconservative :=
    baseline_single_sided_token_deposit_cpow_no_correction_has_no_adverse_error
      hweights.1.le hcaller.2.2.2.1 hpowerAtMostBone
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hfeePositive := single_sided_token_deposit_minimum_fee_power_value_positive
    hweights.1 hweights.2 hnominalPositive
  have hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
    have hshare :
        0 < SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio :=
      mul_pos (by
        rw [single_sided_token_deposit_adverse_fee_share_value]
        norm_num) hfeePositive
    linarith
  exact single_sided_token_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE)
      hinputBalance hnominal hadjustedInput0 hadjustedRatio hadjustedFloor
      hfeeMultiplier hcomputedBase hbaseFloor hweights.1.le hcpow hpoolSupply
      hscale hnewSupplyFloor hpoolAmount hdownscaleFloor

/-- Complete second-term comparison for the exact-token-input deposit. -/
theorem baseline_single_sided_token_deposit_second_term_adverse_error_lt_precise_fee_share
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase computedFractional computedPower poolSupply weight feeRate scale : ℝ}
    {adjustedInput computedBaseRaw firstRounded coefficientProduct multiplied
      secondRounded computedPowerRaw newPoolSupply poolAmountOut output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio)))
    (hbaseStrict : 1 < computedBase)
    (hfirstRounded0 : 0 ≤ firstRounded)
    (hfirstFloor :
      IsFloor firstRounded (exactOutputBinomialTerm weight computedBase 1))
    (hcoefficientFloor :
      IsFloor coefficientProduct
        ((BONE : ℝ) * (weight - 1) * (computedBase - 1)))
    (hmultiplyFloor :
      IsFloor multiplied
        ((firstRounded : ℝ) * (coefficientProduct : ℝ) / (BONE : ℝ)))
    (hdivideFloor : IsFloor secondRounded ((multiplied : ℝ) / 2))
    (hcomputedFractional :
      computedFractional =
        (BONE : ℝ) + (firstRounded : ℝ) + (secondRounded : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedTokenDepositIdealOutput
          (poolSupply / scale) weight feeRate nominalRatio <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue
          (poolSupply / scale) weight nominalRatio := by
  have hcaller := single_sided_token_deposit_configured_caller_bounds
    hinputBalance hinputAmount hnominal hnominalUpper hweightLower hweightUpper
      hfee0 hfee1 hfeeMultiplier hadjustedInput0 hadjustedRatio hadjustedFloor
      hcomputedBase hbaseFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hconservative :=
    baseline_single_sided_token_deposit_cpow_second_term_has_no_adverse_error
      hweights.1.le hweights.2.le hbaseStrict
        (le_trans (le_abs_self _) hcaller.2.2.2.2.2.2)
        hfirstRounded0 hfirstFloor hcoefficientFloor hmultiplyFloor hdivideFloor
        hcomputedFractional hcomputedPower hcomposedFloor
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hfeePositive := single_sided_token_deposit_minimum_fee_power_value_positive
    hweights.1 hweights.2 hnominalPositive
  have hcpow :
      computedPower - (BONE : ℝ) * computedBase ^ weight <
        SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio := by
    have hshare :
        0 < SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedTokenDepositMinimumFeePowerValue weight nominalRatio :=
      mul_pos (by
        rw [single_sided_token_deposit_adverse_fee_share_value]
        norm_num) hfeePositive
    linarith
  exact single_sided_token_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE)
      hinputBalance hnominal hadjustedInput0 hadjustedRatio hadjustedFloor
      hfeeMultiplier hcomputedBase hbaseFloor hweights.1.le hcpow hpoolSupply
      hscale hnewSupplyFloor hpoolAmount hdownscaleFloor

/-- Complete later-term comparison for the exact-token-input deposit. -/
theorem baseline_single_sided_token_deposit_later_adverse_error_lt_precise_fee_share
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n degree evenIndex : ℕ}
    {inputBalance inputAmount nominalRatio adjustedRatio feeMultiplier
      computedBase computedFractional computedPower poolSupply weight feeRate scale : ℝ}
    {adjustedInput computedBaseRaw computedPowerRaw newPoolSupply poolAmountOut
      output : ℤ}
    (hinputBalance : 0 < inputBalance) (hinputAmount : 0 < inputAmount)
    (hnominal : nominalRatio = inputAmount / inputBalance)
    (hnominalUpper : nominalRatio ≤ (MAX_IN_RATIO : ℝ) / STROOP)
    (hweightLower : (MIN_WEIGHT : ℝ) / STROOP ≤ weight)
    (hweightUpper : weight ≤ (MAX_WEIGHT : ℝ) / STROOP)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hadjustedInput0 : 0 ≤ adjustedInput)
    (hadjustedRatio : adjustedRatio = (adjustedInput : ℝ) / inputBalance)
    (hadjustedFloor : IsFloor adjustedInput (inputAmount * feeMultiplier))
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseFloor :
      IsFloor computedBaseRaw ((BONE : ℝ) * (1 + adjustedRatio)))
    (hn3 : 3 ≤ n)
    (hn50 : n ≤ 50)
    (hdegreeEven : degree = 2 * evenIndex + 2)
    (hdegreeStop : degree = n ∨ degree + 1 = n)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor (computedTerm 1)
        (exactOutputBinomialTerm weight computedBase 1))
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
        ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ))
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedFloor : IsFloor computedPowerRaw computedFractional)
    (hpoolSupply : 0 < poolSupply) (hscale : 0 < scale)
    (hnewSupplyFloor :
      IsFloor newPoolSupply (poolSupply * (computedPower / (BONE : ℝ))))
    (hpoolAmount :
      (poolAmountOut : ℝ) = (newPoolSupply : ℝ) - poolSupply)
    (hdownscaleFloor : IsFloor output ((poolAmountOut : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedTokenDepositIdealOutput
          (poolSupply / scale) weight feeRate nominalRatio <
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue
          (poolSupply / scale) weight nominalRatio := by
  have hcaller := single_sided_token_deposit_configured_caller_bounds
    hinputBalance hinputAmount hnominal hnominalUpper hweightLower hweightUpper
      hfee0 hfee1 hfeeMultiplier hadjustedInput0 hadjustedRatio hadjustedFloor
      hcomputedBase hbaseFloor
  have hweights := single_sided_token_deposit_configured_weight_bounds
    hweightLower hweightUpper
  have hcpow :=
    baseline_single_sided_token_deposit_cpow_later_adverse_error_lt_precise_fee_share
      coefficientProduct multiplied computedTerm hweightLower hweightUpper
        hcaller.2.2.2.1 hcaller.2.2.2.2.1 hcaller.2.2.2.2.2.1
        hnominalUpper hn3 hn50 hdegreeEven hdegreeStop hcontinued hfirstFloor
        hcoefficientFloor hmultiplyTermFloor hdivideTermFloor hcomputedFractional
        hcomputedPower hcomposedFloor
  exact single_sided_token_deposit_from_fixed_point_refinements_fee_share
    (feeShare := SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE)
      hinputBalance hnominal hadjustedInput0 hadjustedRatio hadjustedFloor
      hfeeMultiplier hcomputedBase hbaseFloor hweights.1.le hcpow hpoolSupply
      hscale hnewSupplyFloor hpoolAmount hdownscaleFloor

end CometPool
