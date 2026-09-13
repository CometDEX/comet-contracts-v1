import CometPool.Operations.FeeDominance
import CometPool.Source.ExactInputSwapSource
import CometPool.Source.ExactOutputSwapSource
import CometPool.Source.SingleSidedDepositSource
import CometPool.Source.SingleSidedTokenDepositSource
import CometPool.Source.SingleSidedWithdrawalSource
import CometPool.Source.SingleSidedTokenWithdrawalSource

namespace CometPool

/-!
Source-shaped corollaries composing each certified adverse approximation-error
bound with the corresponding exact fee-advantage lower bound. The resulting
theorems compare successful computed amounts directly with the continuous
fee-free ideal.
-/

private theorem source_fee_rate_lower {fee : ℕ} (hfee : MIN_FEE ≤ fee) :
    MIN_FEE_RATE ≤ (fee : ℝ) / STROOP := by
  rw [MIN_FEE_RATE]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hfee)
    (by norm_num [STROOP])

private theorem source_fee_rate_lt_one {fee : ℕ} (hfee : fee ≤ MAX_FEE) :
    (fee : ℝ) / STROOP < 1 := by
  have hfeeReal : (fee : ℝ) ≤ MAX_FEE := by exact_mod_cast hfee
  calc
    (fee : ℝ) / STROOP ≤ (MAX_FEE : ℝ) / STROOP :=
      div_le_div_of_nonneg_right hfeeReal (by norm_num [STROOP])
    _ < 1 := by norm_num [MAX_FEE, STROOP]

private theorem source_normalized_ratio_le
    {amount balance limit : ℕ}
    (hbalance : 0 < balance)
    (hratio : amount * STROOP ≤ balance * limit) :
    (amount : ℝ) / balance ≤ (limit : ℝ) / STROOP := by
  have hbalanceReal : (0 : ℝ) < balance := by exact_mod_cast hbalance
  have hstroopReal : (0 : ℝ) < STROOP := by norm_num [STROOP]
  apply (div_le_div_iff₀ hbalanceReal hstroopReal).2
  exact_mod_cast (by simpa [mul_comm] using hratio)

private theorem source_weight_lower
    {weight : ℕ} (hweight : MIN_WEIGHT ≤ weight) :
    (MIN_WEIGHT : ℝ) / STROOP ≤ (weight : ℝ) / STROOP :=
  div_le_div_of_nonneg_right (by exact_mod_cast hweight)
    (by norm_num [STROOP])

private theorem source_weight_upper
    {weight : ℕ} (hweight : weight ≤ MAX_WEIGHT) :
    (weight : ℝ) / STROOP ≤ (MAX_WEIGHT : ℝ) / STROOP :=
  div_le_div_of_nonneg_right (by exact_mod_cast hweight)
    (by norm_num [STROOP])

private theorem source_weight_positive
    {weight : ℕ} (hweight : MIN_WEIGHT ≤ weight) :
    0 < (weight : ℝ) / STROOP := by
  have hlower := source_weight_lower hweight
  exact lt_of_lt_of_le (by norm_num [MIN_WEIGHT, STROOP]) hlower

private theorem source_weight_lt_one
    {weight : ℕ} (hweight : weight ≤ MAX_WEIGHT) :
    (weight : ℝ) / STROOP < 1 := by
  have hupper := source_weight_upper hweight
  exact lt_of_le_of_lt hupper (by norm_num [MAX_WEIGHT, STROOP])

private theorem source_weight_ratio_le_nine
    {numerator denominator : ℕ}
    (hnumerator : numerator ≤ MAX_WEIGHT)
    (hdenominator : MIN_WEIGHT ≤ denominator) :
    (numerator : ℝ) / denominator ≤ 9 := by
  have hdenominator0 : 0 < denominator :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hdenominator
  apply (div_le_iff₀ (by exact_mod_cast hdenominator0)).2
  have hbound : numerator ≤ 9 * denominator := by
    calc
      numerator ≤ MAX_WEIGHT := hnumerator
      _ = 9 * MIN_WEIGHT := by norm_num [MAX_WEIGHT, MIN_WEIGHT]
      _ ≤ 9 * denominator := Nat.mul_le_mul_left 9 hdenominator
  exact_mod_cast hbound

/-- A successful exact-input swap returns strictly less than the continuous
fee-free ideal output. -/
theorem calc_token_out_given_token_in_execution_is_pool_favoring
    {inBalance inScalar outBalance outScalar amountIn
      inWeight outWeight fee : ℕ} {output : ℤ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountIn : 0 < amountIn)
    (hinWeightLower : MIN_WEIGHT ≤ inWeight)
    (hinWeightUpper : inWeight ≤ MAX_WEIGHT)
    (houtWeightLower : MIN_WEIGHT ≤ outWeight)
    (houtWeightUpper : outWeight ≤ MAX_WEIGHT)
    (hinputRatio : amountIn * STROOP ≤ inBalance * MAX_IN_RATIO)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenOutGivenTokenInExecution inBalance inScalar
      outBalance outScalar amountIn inWeight outWeight fee = some output) :
    (output : ℝ) <
      exactInputIdealOutput (outBalance : ℝ) 0
        ((amountIn : ℝ) / inBalance) ((inWeight : ℝ) / outWeight) := by
  have herror :=
    calc_token_out_given_token_in_execution_adverse_error_lt_precise_fee_share
      hinBalance hinScalar houtBalance houtScalar hamountIn hinWeightLower
      hinWeightUpper houtWeightLower houtWeightUpper hinputRatio hfeeLower
      hfeeUpper hexec
  have hnominalUpper := source_normalized_ratio_le hinBalance hinputRatio
  have hnominalTwoFifths :
      (amountIn : ℝ) / inBalance ≤ 2 / 5 :=
    hnominalUpper.trans (by norm_num [MAX_IN_RATIO, STROOP])
  have houtWeight0 : 0 < outWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) houtWeightLower
  have hexponent0 : 0 < (inWeight : ℝ) / outWeight := by
    have hinWeight0 : 0 < inWeight :=
      lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hinWeightLower
    positivity
  have hdominance := exact_input_fee_advantage_dominates_adverse_budget
    (show (0 : ℝ) ≤ outBalance by positivity)
    (source_fee_rate_lower hfeeLower) (source_fee_rate_lt_one hfeeUpper).le
    (by positivity) hnominalTwoFifths hexponent0
    (source_weight_ratio_le_nine hinWeightUpper houtWeightLower)
  exact fixed_input_fee_dominance herror hdominance

/-- A successful exact-output swap charges strictly more than the continuous
fee-free ideal input. -/
theorem calc_token_in_given_token_out_execution_is_pool_favoring
    {inBalance inScalar outBalance outScalar amountOut
      inWeight outWeight fee : ℕ} {output : ℤ}
    (hinBalance : 0 < inBalance) (hinScalar : 0 < inScalar)
    (houtBalance : 0 < outBalance) (houtScalar : 0 < outScalar)
    (hamountOut : 0 < amountOut)
    (hinWeightLower : MIN_WEIGHT ≤ inWeight)
    (hinWeightUpper : inWeight ≤ MAX_WEIGHT)
    (houtWeightLower : MIN_WEIGHT ≤ outWeight)
    (houtWeightUpper : outWeight ≤ MAX_WEIGHT)
    (houtputRatio : amountOut * STROOP ≤ outBalance * MAX_OUT_RATIO)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenInGivenTokenOutExecution inBalance inScalar outBalance
      outScalar amountOut inWeight outWeight fee = some output) :
    exactOutputIdealInput (inBalance : ℝ) 0
        ((amountOut : ℝ) / outBalance) ((outWeight : ℝ) / inWeight) <
      (output : ℝ) := by
  have herror :=
    calc_token_in_given_token_out_execution_adverse_error_lt_precise_fee_share
      hinBalance hinScalar houtBalance houtScalar hamountOut hinWeightLower
      hinWeightUpper houtWeightLower houtWeightUpper houtputRatio hfeeUpper hexec
  have hnominalUpper := source_normalized_ratio_le houtBalance houtputRatio
  have hnominalOne : (amountOut : ℝ) / outBalance < 1 :=
    lt_of_le_of_lt hnominalUpper (by norm_num [MAX_OUT_RATIO, STROOP])
  have hinWeight0 : 0 < inWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hinWeightLower
  have hexponent0 : 0 ≤ (outWeight : ℝ) / inWeight := by positivity
  have hdominance := exact_output_fee_advantage_dominates_adverse_budget
    (show (0 : ℝ) ≤ inBalance by positivity)
    (source_fee_rate_lower hfeeLower) (source_fee_rate_lt_one hfeeUpper)
    (by positivity) hnominalOne hexponent0
  exact fixed_output_fee_dominance herror hdominance

/-- A successful exact-LP-output single-sided deposit charges strictly more
than the continuous fee-free ideal token input. -/
theorem calc_token_deposits_in_given_lp_token_amount_execution_is_pool_favoring
    {inputBalance inputScalar poolSupply poolAmountOut inputWeight fee : ℕ}
    {result : SingleSidedDepositExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenDepositsInGivenLpTokenAmountExecution inputBalance
      inputScalar poolSupply poolAmountOut inputWeight fee = some result) :
    singleSidedDepositIdealInput (inputBalance : ℝ)
        ((inputWeight : ℝ) / STROOP) 0
        ((poolAmountOut : ℝ) / poolSupply) <
      (result.output : ℝ) := by
  have herror :=
    calc_token_deposits_in_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share
      hinputBalance hinputScalar hpoolSupply hpoolAmountOut hweightLower
      hweightUpper hfeeUpper hexec
  have hweight0 := source_weight_positive hweightLower
  have hdominance :=
    single_sided_deposit_fee_advantage_dominates_adverse_budget
      (nominalRatio := (poolAmountOut : ℝ) / poolSupply)
      (show (0 : ℝ) ≤ inputBalance by positivity) hweight0
      (source_weight_lt_one hweightUpper).le
      (source_fee_rate_lower hfeeLower) (source_fee_rate_lt_one hfeeUpper)
      (div_nonneg (by positivity) (by positivity))
  exact fixed_output_fee_dominance herror hdominance

/-- A successful exact-token-input single-sided deposit returns strictly less
than the continuous fee-free ideal LP-token output. -/
theorem calc_lp_token_amount_given_token_deposits_in_execution_is_pool_favoring
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenDepositExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hinputAmount : 0 < inputAmount) (hpoolSupply : 0 < poolSupply)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hinputRatio : inputAmount * STROOP ≤ inputBalance * MAX_IN_RATIO)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcLpTokenAmountGivenTokenDepositsInExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    (result.output : ℝ) <
      singleSidedTokenDepositIdealOutput (poolSupply : ℝ)
        ((inputWeight : ℝ) / STROOP) 0
        ((inputAmount : ℝ) / inputBalance) := by
  have herror :=
    calc_lp_token_amount_given_token_deposits_in_execution_adverse_error_lt_precise_fee_share
      hinputBalance hinputScalar hinputAmount hpoolSupply hweightLower
      hweightUpper hinputRatio hfeeUpper hexec
  have hnominalUpper := source_normalized_ratio_le hinputBalance hinputRatio
  have hnominalOne : (inputAmount : ℝ) / inputBalance ≤ 1 :=
    hnominalUpper.trans (by norm_num [MAX_IN_RATIO, STROOP])
  have hweight0 := (source_weight_positive hweightLower).le
  have hdominance :=
    single_sided_token_deposit_fee_advantage_dominates_adverse_budget
      (show (0 : ℝ) ≤ poolSupply by positivity) hweight0
      (source_weight_lt_one hweightUpper).le
      (source_fee_rate_lower hfeeLower) (source_fee_rate_lt_one hfeeUpper)
      (by positivity) hnominalOne
  exact fixed_input_fee_dominance herror hdominance

/-- A successful exact-LP-input single-sided withdrawal returns strictly less
than the continuous fee-free ideal token output. -/
theorem calc_token_withdrawal_amount_given_lp_token_amount_execution_is_pool_favoring
    {outputBalance outputScalar poolSupply poolAmountIn outputWeight fee : ℕ}
    {result : SingleSidedWithdrawalExecutionResult}
    (houtputBalance : 0 < outputBalance) (houtputScalar : 0 < outputScalar)
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hweightLower : MIN_WEIGHT ≤ outputWeight)
    (hweightUpper : outputWeight ≤ MAX_WEIGHT)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenWithdrawalAmountGivenLpTokenAmountExecution outputBalance
      outputScalar poolSupply poolAmountIn outputWeight fee = some result) :
    (result.output : ℝ) <
      singleSidedWithdrawalIdealOutput outputBalance
        ((outputWeight : ℝ) / STROOP) 0
        ((poolAmountIn : ℝ) / poolSupply) := by
  have herror :=
    calc_token_withdrawal_amount_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share
      houtputBalance houtputScalar hpoolSupply hpoolAmountIn hweightLower
      hweightUpper hfeeUpper hexec
  have href := calcTokenWithdrawalAmountGivenLpTokenAmountExecution_refines
    houtputBalance houtputScalar hpoolSupply hpoolAmountIn hweightLower
      hweightUpper hfeeUpper hexec
  let rawRatio : ℝ :=
    (result.pre.poolAmountRaw : ℝ) / result.pre.poolSupplyRaw
  have hrawSupply0 : (0 : ℝ) < result.pre.poolSupplyRaw := by
    exact_mod_cast href.poolSupplyPositive
  have hbaseBounds := singleSidedDepositCPowExecution_base_bounds href.cpowExec
  have hrawRatio1 : rawRatio < 1 := by
    have hexactPositive : 0 < (BONE : ℝ) * (1 - rawRatio) := by
      have hrawLower : (1 : ℝ) ≤ result.pre.baseRaw := by
        exact_mod_cast hbaseBounds.1
      have hbaseCeil :
          IsCeil result.pre.baseRaw ((BONE : ℝ) * (1 - rawRatio)) := by
        simpa [rawRatio] using href.baseCeil
      linarith [hbaseCeil.add_one_lt]
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    nlinarith
  have hrawRatioOriginal :
      rawRatio = (poolAmountIn : ℝ) / poolSupply := by
    dsimp [rawRatio]
    rw [href.poolAmountEq, href.poolSupplyEq]
    push_cast
    norm_num [BONE, STROOP]
    field_simp [show (poolSupply : ℝ) ≠ 0 by positivity]
    ring
  have hnominal1 : (poolAmountIn : ℝ) / poolSupply < 1 := by
    rw [← hrawRatioOriginal]
    exact hrawRatio1
  have hweight0 := source_weight_positive hweightLower
  have hweightLowerReal := source_weight_lower hweightLower
  have hweightUpperReal := source_weight_upper hweightUpper
  have hreciprocal := single_sided_deposit_reciprocal_weight_bounds
    hweight0 hweightLowerReal hweightUpperReal
  have hdominance :=
    single_sided_withdrawal_fee_advantage_dominates_adverse_budget
      (show (0 : ℝ) ≤ outputBalance by positivity) hweight0
      (source_weight_lt_one hweightUpper).le hreciprocal.1
      (source_fee_rate_lower hfeeLower) (by positivity) hnominal1
  exact fixed_input_fee_dominance herror hdominance

/-- A successful exact-token-output single-sided withdrawal charges strictly
more than the continuous fee-free ideal LP-token input. -/
theorem calc_lp_token_amount_given_token_withdrawal_amount_execution_is_pool_favoring
    {inputBalance inputScalar inputAmount poolSupply inputWeight fee : ℕ}
    {result : SingleSidedTokenWithdrawalExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hinputAmount : 0 < inputAmount) (hpoolSupply : 0 < poolSupply)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hinputRatio : inputAmount * STROOP ≤ inputBalance * MAX_OUT_RATIO)
    (hfeeLower : MIN_FEE ≤ fee) (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcLpTokenAmountGivenTokenWithdrawalAmountExecution inputBalance
      inputScalar inputAmount poolSupply inputWeight fee = some result) :
    singleSidedTokenWithdrawalIdealInput (poolSupply : ℝ)
        ((inputWeight : ℝ) / STROOP) 0
        ((inputAmount : ℝ) / inputBalance) <
      (result.output : ℝ) := by
  have herror :=
    calc_lp_token_amount_given_token_withdrawal_amount_execution_adverse_error_lt_precise_fee_share
      hinputBalance hinputScalar hinputAmount hpoolSupply hweightLower
      hweightUpper hinputRatio hfeeUpper hexec
  have hnominalUpper := source_normalized_ratio_le hinputBalance hinputRatio
  have hweightLowerReal := source_weight_lower hweightLower
  have hweightUpperReal := source_weight_upper hweightUpper
  have hfeeUpperReal :
      (fee : ℝ) / STROOP ≤ (MAX_FEE : ℝ) / STROOP :=
    div_le_div_of_nonneg_right (by exact_mod_cast hfeeUpper)
      (by norm_num [STROOP])
  have hadjusted := single_sided_token_withdrawal_adjusted_ratio_le_three_eighths
    hnominalUpper hweightLowerReal hweightUpperReal (by positivity) hfeeUpperReal
  have hadjusted1 :
      (inputAmount : ℝ) / inputBalance /
          (1 - singleSidedWithdrawalFeeRate
            ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)) < 1 :=
    lt_of_le_of_lt hadjusted.2 (by norm_num)
  have hdominance :=
    single_sided_token_withdrawal_fee_advantage_dominates_adverse_budget
      (show (0 : ℝ) ≤ poolSupply by positivity)
      (source_weight_positive hweightLower).le
      (source_weight_lt_one hweightUpper).le
      (source_fee_rate_lower hfeeLower) (source_fee_rate_lt_one hfeeUpper)
      (by positivity) hadjusted1
  exact fixed_output_fee_dominance herror hdominance

end CometPool
