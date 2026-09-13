import CometPool.Source.SingleSidedDepositSource
import CometPool.Operations.SingleSidedWithdrawal

set_option maxRecDepth 65536
set_option maxHeartbeats 800000

namespace CometPool

/-!
Executable, source-shaped model for
`calc_token_withdrawal_amount_given_lp_token_amount` and the successful
`wdr_tokn_amt_in_get_lp_tokns_out` balance-cap guards. The arbitrary BONE-scaled
upper-directed `c_pow` execution is shared with the exact-LP-output deposit
bridge; the same source control flow applies on this below-one base.
-/

private theorem exact_lp_withdrawal_i128_mul_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem exact_lp_withdrawal_i256_sub_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x - y) = some result from hexec)
  exact h.2.symm

private theorem exact_lp_withdrawal_isFloor_integer_eq
    {rounded exact : ℤ} (hfloor : IsFloor rounded (exact : ℝ)) :
    rounded = exact := by
  have hlower : rounded ≤ exact := by exact_mod_cast hfloor.le
  have hupperReal : (exact : ℝ) < rounded + 1 := hfloor.lt_add_one
  have hupper : exact < rounded + 1 := by exact_mod_cast hupperReal
  omega

/-- Checked intermediates before the reciprocal-exponent `c_pow` call. -/
structure SingleSidedWithdrawalPrefix where
  tokenBalanceRaw : ℤ
  poolAmountRaw : ℤ
  poolSupplyRaw : ℤ
  feeRaw : ℤ
  weightRaw : ℤ
  newPoolSupplyRaw : ℤ
  baseRaw : ℤ
  exponentRaw : ℤ

/-- Complete successful arithmetic result, including both public balance-cap guards. -/
structure SingleSidedWithdrawalExecutionResult where
  pre : SingleSidedWithdrawalPrefix
  cpow : SingleSidedDepositCPowExecutionResult
  newTokenBalanceRaw : ℤ
  tokenAmountBeforeFeeRaw : ℤ
  weightComplementRaw : ℤ
  weightedFeeRaw : ℤ
  feeMultiplierRaw : ℤ
  resultRaw : ℤ
  downscaledRaw : ℤ
  output : ℤ
  maxOutputRaw : ℤ

/-- Source arithmetic through the reciprocal-weight calculation. -/
def singleSidedWithdrawalPrefixExecution
    (outputBalance outputScalar poolSupply poolAmountIn
      outputWeight fee : ℕ) : Option SingleSidedWithdrawalPrefix := do
  let tokenBalanceRaw ←
    SorobanFixedPointMath.I128.mul outputBalance outputScalar
  let poolAmountRaw ←
    SorobanFixedPointMath.I128.mul poolAmountIn (BONE / STROOP)
  let poolSupplyRaw ←
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP)
  let feeRaw ← SorobanFixedPointMath.I128.mul fee (BONE / STROOP)
  let weightRaw ←
    SorobanFixedPointMath.I128.mul outputWeight (BONE / STROOP)
  let newPoolSupplyRaw ←
    SorobanFixedPointMath.I256.sub poolSupplyRaw poolAmountRaw
  let baseRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      newPoolSupplyRaw poolSupplyRaw.toNat BONE
  let exponentRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      BONE weightRaw.toNat BONE
  some {
    tokenBalanceRaw
    poolAmountRaw
    poolSupplyRaw
    feeRaw
    weightRaw
    newPoolSupplyRaw
    baseRaw
    exponentRaw
  }

/-- Source arithmetic from `c_pow` through downscaling and the public guards. -/
def singleSidedWithdrawalFinishExecution
    (outputBalance outputScalar : ℕ) (pre : SingleSidedWithdrawalPrefix) :
    Option SingleSidedWithdrawalExecutionResult := do
  let cpow ← singleSidedDepositCPowExecution pre.baseRaw pre.exponentRaw
  let newTokenBalanceRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
      pre.tokenBalanceRaw cpow.powerRaw BONE
  if pre.tokenBalanceRaw < newTokenBalanceRaw then
    none
  else
    let tokenAmountBeforeFeeRaw ←
      SorobanFixedPointMath.I256.sub pre.tokenBalanceRaw newTokenBalanceRaw
    let weightComplementRaw ←
      SorobanFixedPointMath.I256.sub BONE pre.weightRaw
    let weightedFeeRaw ←
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        weightComplementRaw pre.feeRaw BONE
    let feeMultiplierRaw ←
      SorobanFixedPointMath.I256.sub BONE weightedFeeRaw
    let resultRaw ←
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        tokenAmountBeforeFeeRaw feeMultiplierRaw BONE
    let downscaledRaw ←
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        resultRaw outputScalar 1
    let output ← SorobanFixedPointMath.I128.checked downscaledRaw
    let maxOutputRaw ←
      SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
        outputBalance MAX_OUT_RATIO STROOP
    if output ≤ maxOutputRaw then
      if output ≤ outputBalance then
        some {
          pre
          cpow
          newTokenBalanceRaw
          tokenAmountBeforeFeeRaw
          weightComplementRaw
          weightedFeeRaw
          feeMultiplierRaw
          resultRaw
          downscaledRaw
          output
          maxOutputRaw
        }
      else
        none
    else
      none

/-- Executable model of the exact-LP-input single-sided withdrawal arithmetic. -/
def calcTokenWithdrawalAmountGivenLpTokenAmountExecution
    (outputBalance outputScalar poolSupply poolAmountIn
      outputWeight fee : ℕ) : Option SingleSidedWithdrawalExecutionResult := do
  let pre ← singleSidedWithdrawalPrefixExecution outputBalance outputScalar
    poolSupply poolAmountIn outputWeight fee
  singleSidedWithdrawalFinishExecution outputBalance outputScalar pre

/-- Successful prefix execution exposes every checked source operation. -/
theorem singleSidedWithdrawalPrefixExecution_success
    {outputBalance outputScalar poolSupply poolAmountIn outputWeight fee : ℕ}
    {result : SingleSidedWithdrawalPrefix}
    (hexec : singleSidedWithdrawalPrefixExecution outputBalance outputScalar
      poolSupply poolAmountIn outputWeight fee = some result) :
    SorobanFixedPointMath.I128.mul outputBalance outputScalar =
        some result.tokenBalanceRaw ∧
      SorobanFixedPointMath.I128.mul poolAmountIn (BONE / STROOP) =
        some result.poolAmountRaw ∧
      SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP) =
        some result.poolSupplyRaw ∧
      SorobanFixedPointMath.I128.mul fee (BONE / STROOP) =
        some result.feeRaw ∧
      SorobanFixedPointMath.I128.mul outputWeight (BONE / STROOP) =
        some result.weightRaw ∧
      SorobanFixedPointMath.I256.sub result.poolSupplyRaw result.poolAmountRaw =
        some result.newPoolSupplyRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.newPoolSupplyRaw result.poolSupplyRaw.toNat BONE =
          some result.baseRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        BONE result.weightRaw.toNat BONE = some result.exponentRaw := by
  rw [singleSidedWithdrawalPrefixExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceRaw, htokenBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨poolAmountRaw, hpoolAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨poolSupplyRaw, hpoolSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨feeRaw, hfee, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨weightRaw, hweight, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨newPoolSupplyRaw, hnewPoolSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨baseRaw, hbase, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨exponentRaw, hexponent, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨htokenBalance, hpoolAmount, hpoolSupply, hfee, hweight,
    hnewPoolSupply, hbase, hexponent⟩

/-- Successful finish execution exposes all post-`c_pow` operations and guards. -/
theorem singleSidedWithdrawalFinishExecution_success
    {outputBalance outputScalar : ℕ} {pre : SingleSidedWithdrawalPrefix}
    {result : SingleSidedWithdrawalExecutionResult}
    (hexec : singleSidedWithdrawalFinishExecution outputBalance outputScalar pre =
      some result) :
    result.pre = pre ∧
      singleSidedDepositCPowExecution pre.baseRaw pre.exponentRaw =
        some result.cpow ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        pre.tokenBalanceRaw result.cpow.powerRaw BONE =
          some result.newTokenBalanceRaw ∧
      result.newTokenBalanceRaw ≤ pre.tokenBalanceRaw ∧
      SorobanFixedPointMath.I256.sub pre.tokenBalanceRaw
        result.newTokenBalanceRaw = some result.tokenAmountBeforeFeeRaw ∧
      SorobanFixedPointMath.I256.sub BONE pre.weightRaw =
        some result.weightComplementRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.weightComplementRaw pre.feeRaw BONE =
          some result.weightedFeeRaw ∧
      SorobanFixedPointMath.I256.sub BONE result.weightedFeeRaw =
        some result.feeMultiplierRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.tokenAmountBeforeFeeRaw result.feeMultiplierRaw BONE =
          some result.resultRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        result.resultRaw outputScalar 1 = some result.downscaledRaw ∧
      SorobanFixedPointMath.I128.checked result.downscaledRaw =
        some result.output ∧
      SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
        outputBalance MAX_OUT_RATIO STROOP = some result.maxOutputRaw ∧
      result.output ≤ result.maxOutputRaw ∧
      result.output ≤ outputBalance := by
  rw [singleSidedWithdrawalFinishExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨cpow, hcpow, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨newTokenBalanceRaw, hnewTokenBalance, hexec⟩
  by_cases hbalance : pre.tokenBalanceRaw < newTokenBalanceRaw
  · simp [hbalance] at hexec
  · rw [if_neg hbalance] at hexec
    rcases Option.bind_eq_some.mp hexec with
      ⟨tokenAmountBeforeFeeRaw, htokenAmount, hexec⟩
    rcases Option.bind_eq_some.mp hexec with
      ⟨weightComplementRaw, hweightComplement, hexec⟩
    rcases Option.bind_eq_some.mp hexec with
      ⟨weightedFeeRaw, hweightedFee, hexec⟩
    rcases Option.bind_eq_some.mp hexec with
      ⟨feeMultiplierRaw, hfeeMultiplier, hexec⟩
    rcases Option.bind_eq_some.mp hexec with ⟨resultRaw, hresultRaw, hexec⟩
    rcases Option.bind_eq_some.mp hexec with
      ⟨downscaledRaw, hdownscaled, hexec⟩
    rcases Option.bind_eq_some.mp hexec with ⟨output, houtput, hexec⟩
    rcases Option.bind_eq_some.mp hexec with
      ⟨maxOutputRaw, hmaxOutput, hexec⟩
    by_cases hmaxGuard : output ≤ maxOutputRaw
    · rw [if_pos hmaxGuard] at hexec
      by_cases hbalanceGuard : output ≤ outputBalance
      · rw [if_pos hbalanceGuard] at hexec
        have hfields := Option.some.inj hexec
        cases hfields
        exact ⟨rfl, hcpow, hnewTokenBalance, le_of_not_gt hbalance,
          htokenAmount, hweightComplement, hweightedFee, hfeeMultiplier,
          hresultRaw, hdownscaled, houtput, hmaxOutput, hmaxGuard,
          hbalanceGuard⟩
      · simp [hbalanceGuard] at hexec
    · simp [hmaxGuard] at hexec

/-- A complete successful result supplies both execution phases. -/
theorem calcTokenWithdrawalAmountGivenLpTokenAmountExecution_success
    {outputBalance outputScalar poolSupply poolAmountIn outputWeight fee : ℕ}
    {result : SingleSidedWithdrawalExecutionResult}
    (hexec : calcTokenWithdrawalAmountGivenLpTokenAmountExecution outputBalance
      outputScalar poolSupply poolAmountIn outputWeight fee = some result) :
    ∃ pre,
      singleSidedWithdrawalPrefixExecution outputBalance outputScalar poolSupply
          poolAmountIn outputWeight fee = some pre ∧
        singleSidedWithdrawalFinishExecution outputBalance outputScalar pre =
          some result := by
  rw [calcTokenWithdrawalAmountGivenLpTokenAmountExecution] at hexec
  exact Option.bind_eq_some.mp hexec

/-- Fixed-point facts recovered from one successful source-shaped execution. -/
structure SingleSidedWithdrawalRunRefinements
    {outputBalance outputScalar poolSupply poolAmountIn outputWeight fee : ℕ}
    (result : SingleSidedWithdrawalExecutionResult) : Prop where
  tokenBalanceEq :
    result.pre.tokenBalanceRaw = (outputBalance : ℤ) * outputScalar
  poolAmountEq :
    result.pre.poolAmountRaw = (poolAmountIn : ℤ) * (BONE / STROOP)
  poolSupplyEq :
    result.pre.poolSupplyRaw = (poolSupply : ℤ) * (BONE / STROOP)
  tokenBalancePositive : 0 < result.pre.tokenBalanceRaw
  poolAmountPositive : 0 < result.pre.poolAmountRaw
  poolSupplyPositive : 0 < result.pre.poolSupplyRaw
  weightRawEq :
    result.pre.weightRaw = (outputWeight : ℤ) * (BONE / STROOP)
  newPoolSupplyEq :
    result.pre.newPoolSupplyRaw =
      result.pre.poolSupplyRaw - result.pre.poolAmountRaw
  baseCeil :
    IsCeil result.pre.baseRaw
      ((BONE : ℝ) *
        (1 - (result.pre.poolAmountRaw : ℝ) / result.pre.poolSupplyRaw))
  exponentFloor :
    IsFloor result.pre.exponentRaw
      ((BONE : ℝ) * (1 / ((outputWeight : ℝ) / STROOP)))
  exponentNonnegative : 0 ≤ result.pre.exponentRaw
  cpowExec :
    singleSidedDepositCPowExecution result.pre.baseRaw result.pre.exponentRaw =
      some result.cpow
  newTokenBalanceCeil :
    IsCeil result.newTokenBalanceRaw
      ((result.pre.tokenBalanceRaw : ℝ) *
        ((result.cpow.powerRaw : ℝ) / BONE))
  tokenAmountEq :
    result.tokenAmountBeforeFeeRaw =
      result.pre.tokenBalanceRaw - result.newTokenBalanceRaw
  feeMultiplierPositive : 0 < result.feeMultiplierRaw
  feeMultiplierEq :
    (result.feeMultiplierRaw : ℝ) / BONE =
      1 - singleSidedWithdrawalFeeRate
        ((outputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
  feeFloor :
    IsFloor result.resultRaw
      ((result.tokenAmountBeforeFeeRaw : ℝ) *
        ((result.feeMultiplierRaw : ℝ) / BONE))
  outputFloor :
    IsFloor result.output ((result.resultRaw : ℝ) / outputScalar)
  maxOutputFloor :
    IsFloor result.maxOutputRaw
      ((outputBalance : ℝ) * ((MAX_OUT_RATIO : ℝ) / STROOP))
  maxOutputGuard : result.output ≤ result.maxOutputRaw
  balanceGuard : result.output ≤ outputBalance

/-- One successful execution derives every fixed-point premise used downstream. -/
theorem calcTokenWithdrawalAmountGivenLpTokenAmountExecution_refines
    {outputBalance outputScalar poolSupply poolAmountIn outputWeight fee : ℕ}
    {result : SingleSidedWithdrawalExecutionResult}
    (houtputBalance : 0 < outputBalance) (houtputScalar : 0 < outputScalar)
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hweightLower : MIN_WEIGHT ≤ outputWeight)
    (hweightUpper : outputWeight ≤ MAX_WEIGHT)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenWithdrawalAmountGivenLpTokenAmountExecution outputBalance
      outputScalar poolSupply poolAmountIn outputWeight fee = some result) :
    SingleSidedWithdrawalRunRefinements
      (outputBalance := outputBalance) (outputScalar := outputScalar)
      (poolSupply := poolSupply) (poolAmountIn := poolAmountIn)
      (outputWeight := outputWeight) (fee := fee) result := by
  obtain ⟨pre, hpreExec, hfinishExec⟩ :=
    calcTokenWithdrawalAmountGivenLpTokenAmountExecution_success hexec
  rcases singleSidedWithdrawalFinishExecution_success hfinishExec with
    ⟨hpre, hcpow, hnewTokenBalance, hnewBalanceGuard, htokenAmount,
      hweightComplement, hweightedFee, hfeeMultiplier, hresultRaw,
      hdownscaled, houtput, hmaxOutput, hmaxOutputGuard, hbalanceGuard⟩
  subst pre
  rcases singleSidedWithdrawalPrefixExecution_success hpreExec with
    ⟨htokenBalance, hpoolAmount, hpoolSupplyExec, hfee, hweight,
      hnewPoolSupply, hbase, hexponent⟩
  have htokenBalanceEq :=
    exact_lp_withdrawal_i128_mul_success_eq htokenBalance
  have hpoolAmountEq := exact_lp_withdrawal_i128_mul_success_eq hpoolAmount
  have hpoolSupplyEq :=
    exact_lp_withdrawal_i128_mul_success_eq hpoolSupplyExec
  have hfeeEq := exact_lp_withdrawal_i128_mul_success_eq hfee
  have hweightEq := exact_lp_withdrawal_i128_mul_success_eq hweight
  have htokenBalance0 : 0 < result.pre.tokenBalanceRaw := by
    rw [htokenBalanceEq]
    positivity
  have hpoolAmount0 : 0 < result.pre.poolAmountRaw := by
    rw [hpoolAmountEq]
    exact_mod_cast Nat.mul_pos hpoolAmountIn
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hpoolSupply0 : 0 < result.pre.poolSupplyRaw := by
    rw [hpoolSupplyEq]
    exact_mod_cast Nat.mul_pos hpoolSupply
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hweight0 : 0 < outputWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hweightLower
  have hweightLt : outputWeight < STROOP :=
    lt_of_le_of_lt hweightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have hfeeLt : fee < STROOP :=
    lt_of_le_of_lt hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hnewPoolSupplyEq :=
    exact_lp_withdrawal_i256_sub_success_eq hnewPoolSupply
  have hpoolSupplyRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      ((poolSupply : ℤ) * (BONE / STROOP)) = some result.pre.poolSupplyRaw
      from hpoolSupplyExec)
  have hpoolSupplyNatMax :
      (result.pre.poolSupplyRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hpoolSupply0.le]
    calc
      result.pre.poolSupplyRaw ≤ SorobanFixedPointMath.I128.maxValue := by
        rw [← hpoolSupplyRange.2]
        exact hpoolSupplyRange.1.2
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hbaseCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hpoolSupply0) hpoolSupplyNatMax hbase).1
  have hpoolSupplyCast :
      (result.pre.poolSupplyRaw.toNat : ℝ) = result.pre.poolSupplyRaw := by
    exact_mod_cast Int.toNat_of_nonneg hpoolSupply0.le
  have hbaseCeil :
      IsCeil result.pre.baseRaw
        ((BONE : ℝ) *
          (1 - (result.pre.poolAmountRaw : ℝ) /
            result.pre.poolSupplyRaw)) := by
    rw [hpoolSupplyCast, hnewPoolSupplyEq] at hbaseCeilRaw
    convert hbaseCeilRaw using 1
    push_cast
    field_simp [show (result.pre.poolSupplyRaw : ℝ) ≠ 0 by
      exact_mod_cast ne_of_gt hpoolSupply0]
    ring
  have hweightRaw0 : 0 < result.pre.weightRaw := by
    rw [hweightEq]
    exact_mod_cast Nat.mul_pos hweight0
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hweightRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      ((outputWeight : ℤ) * (BONE / STROOP)) = some result.pre.weightRaw
      from hweight)
  have hweightNatMax :
      (result.pre.weightRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hweightRaw0.le]
    calc
      result.pre.weightRaw ≤ SorobanFixedPointMath.I128.maxValue := by
        rw [← hweightRange.2]
        exact hweightRange.1.2
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hexponentFloorRaw := (i256_fixed_div_floor_success_refines
    (Int.pos_iff_toNat_pos.mp hweightRaw0) hweightNatMax hexponent).1
  have hweightCast :
      (result.pre.weightRaw.toNat : ℝ) = result.pre.weightRaw := by
    exact_mod_cast Int.toNat_of_nonneg hweightRaw0.le
  have hexponentFloor :
      IsFloor result.pre.exponentRaw
        ((BONE : ℝ) * (1 / ((outputWeight : ℝ) / STROOP))) := by
    rw [hweightCast, hweightEq] at hexponentFloorRaw
    convert hexponentFloorRaw using 1
    push_cast
    norm_num [BONE, STROOP]
    field_simp [show (outputWeight : ℝ) ≠ 0 by positivity]
    ring
  have hexponent0 : 0 ≤ result.pre.exponentRaw := by
    apply hexponentFloor.nonnegative_of_nonnegative_exact
    positivity
  have hnewTokenBalanceCeilRaw := (i256_fixed_mul_ceil_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue])
      hnewTokenBalance).1
  have hnewTokenBalanceCeil :
      IsCeil result.newTokenBalanceRaw
        ((result.pre.tokenBalanceRaw : ℝ) *
          ((result.cpow.powerRaw : ℝ) / BONE)) := by
    convert hnewTokenBalanceCeilRaw using 1
    push_cast
    ring
  have htokenAmountEq :=
    exact_lp_withdrawal_i256_sub_success_eq htokenAmount
  have hweightComplementEq :=
    exact_lp_withdrawal_i256_sub_success_eq hweightComplement
  let weightedFeeExpected : ℤ :=
    (STROOP - outputWeight) * fee * (BONE / (STROOP * STROOP) : ℕ)
  have hweightedFloor := (i256_fixed_mul_floor_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hweightedFee).1
  have hweightedExact :
      ((((result.weightComplementRaw * result.pre.feeRaw : ℤ) : ℝ) /
          BONE)) = (weightedFeeExpected : ℝ) := by
    rw [hweightComplementEq, hweightEq, hfeeEq]
    dsimp [weightedFeeExpected]
    push_cast
    norm_num [BONE, STROOP]
    ring
  have hweightedFeeEq : result.weightedFeeRaw = weightedFeeExpected := by
    apply exact_lp_withdrawal_isFloor_integer_eq
    rw [← hweightedExact]
    exact hweightedFloor
  have hfeeMultiplierRawEq :=
    exact_lp_withdrawal_i256_sub_success_eq hfeeMultiplier
  have hfeeMultiplierEq :
      (result.feeMultiplierRaw : ℝ) / BONE =
        1 - singleSidedWithdrawalFeeRate
          ((outputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP) := by
    rw [hfeeMultiplierRawEq, hweightedFeeEq,
      singleSidedWithdrawalFeeRate]
    dsimp [weightedFeeExpected]
    push_cast
    norm_num [BONE, STROOP]
    ring
  have hfeeMultiplier0 : 0 < result.feeMultiplierRaw := by
    have hnormalizedPositive :
        0 < (result.feeMultiplierRaw : ℝ) / BONE := by
      rw [hfeeMultiplierEq, singleSidedWithdrawalFeeRate]
      have hweightReal0 : 0 ≤ (outputWeight : ℝ) / STROOP := by positivity
      have hweightReal1 : (outputWeight : ℝ) / STROOP ≤ 1 := by
        apply (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
        exact_mod_cast hweightLt.le
      have hfeeReal0 : 0 ≤ (fee : ℝ) / STROOP := by positivity
      have hfeeReal1 : (fee : ℝ) / STROOP < 1 := by
        apply (div_lt_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
        exact_mod_cast hfeeLt
      have hweightedLt :
          (1 - (outputWeight : ℝ) / STROOP) * ((fee : ℝ) / STROOP) < 1 := by
        have hle := mul_le_mul_of_nonneg_right
          (show 1 - (outputWeight : ℝ) / STROOP ≤ 1 by linarith)
          hfeeReal0
        linarith
      linarith
    have hrawPositive : (0 : ℝ) < result.feeMultiplierRaw := by
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      rcases div_pos_iff.mp hnormalizedPositive with hpos | hneg
      · exact hpos.1
      · linarith [hneg.2]
    exact_mod_cast hrawPositive
  have hfeeFloorRaw := (i256_fixed_mul_floor_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hresultRaw).1
  have hfeeFloor :
      IsFloor result.resultRaw
        ((result.tokenAmountBeforeFeeRaw : ℝ) *
          ((result.feeMultiplierRaw : ℝ) / BONE)) := by
    convert hfeeFloorRaw using 1
    push_cast
    ring
  have hdownscaleFloorRaw := (i256_fixed_div_floor_success_refines
    houtputScalar (by
      calc
        (outputScalar : ℤ) ≤ SorobanFixedPointMath.I128.maxValue := by
          have hrange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
            (show SorobanFixedPointMath.I128.checked
              ((outputBalance : ℤ) * outputScalar) =
                some result.pre.tokenBalanceRaw from htokenBalance)
          have houtputBalanceOne : (1 : ℤ) ≤ outputBalance := by
            exact_mod_cast houtputBalance
          nlinarith [hrange.1.2]
        _ ≤ SorobanFixedPointMath.I256.maxValue := by
          norm_num [SorobanFixedPointMath.I128.maxValue,
            SorobanFixedPointMath.I256.maxValue]) hdownscaled).1
  have houtputEq : result.output = result.downscaledRaw :=
    (SorobanFixedPointMath.I128.checked_eq_some_iff.mp houtput).2.symm
  have houtputFloor :
      IsFloor result.output ((result.resultRaw : ℝ) / outputScalar) := by
    rw [houtputEq]
    convert hdownscaleFloorRaw using 1
    push_cast
    ring
  have hmaxOutputFloor := (i128_fixed_mul_floor_success_refines
    (by norm_num [STROOP]) (by
      norm_num [STROOP, SorobanFixedPointMath.I128.maxValue]) hmaxOutput).1
  have hmaxOutputFloor' :
      IsFloor result.maxOutputRaw
        ((outputBalance : ℝ) * ((MAX_OUT_RATIO : ℝ) / STROOP)) := by
    convert hmaxOutputFloor using 1
    push_cast
    ring
  exact {
    tokenBalanceEq := htokenBalanceEq
    poolAmountEq := hpoolAmountEq
    poolSupplyEq := hpoolSupplyEq
    tokenBalancePositive := htokenBalance0
    poolAmountPositive := hpoolAmount0
    poolSupplyPositive := hpoolSupply0
    weightRawEq := hweightEq
    newPoolSupplyEq := hnewPoolSupplyEq
    baseCeil := hbaseCeil
    exponentFloor := hexponentFloor
    exponentNonnegative := hexponent0
    cpowExec := hcpow
    newTokenBalanceCeil := hnewTokenBalanceCeil
    tokenAmountEq := htokenAmountEq
    feeMultiplierPositive := hfeeMultiplier0
    feeMultiplierEq := hfeeMultiplierEq
    feeFloor := hfeeFloor
    outputFloor := houtputFloor
    maxOutputFloor := hmaxOutputFloor'
    maxOutputGuard := hmaxOutputGuard
    balanceGuard := hbalanceGuard
  }

/-
Every successful source-shaped exact-LP-input withdrawal has pool-adverse
error strictly below `3001 / 100000 = 3.001%` of the weighted minimum-fee
value.
-/
theorem calc_token_withdrawal_amount_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share
    {outputBalance outputScalar poolSupply poolAmountIn outputWeight fee : ℕ}
    {result : SingleSidedWithdrawalExecutionResult}
    (houtputBalance : 0 < outputBalance) (houtputScalar : 0 < outputScalar)
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hweightLower : MIN_WEIGHT ≤ outputWeight)
    (hweightUpper : outputWeight ≤ MAX_WEIGHT)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenWithdrawalAmountGivenLpTokenAmountExecution outputBalance
      outputScalar poolSupply poolAmountIn outputWeight fee = some result) :
    (result.output : ℝ) -
        singleSidedWithdrawalIdealOutput outputBalance
          ((outputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
          ((poolAmountIn : ℝ) / poolSupply) <
      SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedWithdrawalMinimumFeeOutputValue outputBalance
          ((outputWeight : ℝ) / STROOP)
          ((poolAmountIn : ℝ) / poolSupply) := by
  have href := calcTokenWithdrawalAmountGivenLpTokenAmountExecution_refines
    houtputBalance houtputScalar hpoolSupply hpoolAmountIn hweightLower
      hweightUpper hfeeUpper hexec
  let outputBalanceRaw : ℝ := result.pre.tokenBalanceRaw
  let poolSupplyRaw : ℝ := result.pre.poolSupplyRaw
  let poolAmountRaw : ℝ := result.pre.poolAmountRaw
  let weight : ℝ := (outputWeight : ℝ) / STROOP
  let feeRate : ℝ := (fee : ℝ) / STROOP
  let nominalRatio : ℝ := poolAmountRaw / poolSupplyRaw
  let computedBase : ℝ := (result.pre.baseRaw : ℝ) / BONE
  let computedExponent : ℝ := (result.pre.exponentRaw : ℝ) / BONE
  let feeMultiplier : ℝ := (result.feeMultiplierRaw : ℝ) / BONE
  let scale : ℝ := outputScalar
  have houtputBalanceRaw : 0 < outputBalanceRaw := by
    dsimp [outputBalanceRaw]
    exact_mod_cast href.tokenBalancePositive
  have hpoolSupplyRaw : 0 < poolSupplyRaw := by
    dsimp [poolSupplyRaw]
    exact_mod_cast href.poolSupplyPositive
  have hpoolAmountRaw : 0 < poolAmountRaw := by
    dsimp [poolAmountRaw]
    exact_mod_cast href.poolAmountPositive
  have hscale : 0 < scale := by
    dsimp [scale]
    exact_mod_cast houtputScalar
  have hweightLowerReal : (MIN_WEIGHT : ℝ) / STROOP ≤ weight := by
    dsimp [weight]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hweightLower)
      (by norm_num [STROOP])
  have hweightUpperReal : weight ≤ (MAX_WEIGHT : ℝ) / STROOP := by
    dsimp [weight]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hweightUpper)
      (by norm_num [STROOP])
  have hweightBounds : 0 < weight ∧ weight < 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num [MIN_WEIGHT, STROOP]) hweightLowerReal
    · exact lt_of_le_of_lt hweightUpperReal
        (by norm_num [MAX_WEIGHT, STROOP])
  have hfee0 : 0 ≤ feeRate := by positivity
  have hfeeUpperReal : feeRate ≤ (MAX_FEE : ℝ) / STROOP := by
    dsimp [feeRate]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfeeUpper)
      (by norm_num [STROOP])
  have hfee1 : feeRate ≤ 1 :=
    le_trans hfeeUpperReal (by norm_num [MAX_FEE, STROOP])
  have hnominal : nominalRatio = poolAmountRaw / poolSupplyRaw := rfl
  have hnominalPositive : 0 < nominalRatio := by
    rw [hnominal]
    positivity
  have hnominalOriginal :
      nominalRatio = (poolAmountIn : ℝ) / poolSupply := by
    dsimp [nominalRatio, poolAmountRaw, poolSupplyRaw]
    rw [href.poolAmountEq, href.poolSupplyEq]
    push_cast
    norm_num [BONE, STROOP]
    field_simp [show (poolSupply : ℝ) ≠ 0 by positivity]
    ring
  have houtputBalanceOriginal : outputBalanceRaw / scale = outputBalance := by
    dsimp [outputBalanceRaw, scale]
    rw [href.tokenBalanceEq]
    push_cast
    field_simp [show (outputScalar : ℝ) ≠ 0 by positivity]
  have hcomputedBase :
      computedBase = (result.pre.baseRaw : ℝ) / BONE := rfl
  have hbaseCeil :
      IsCeil result.pre.baseRaw
        ((BONE : ℝ) * (1 - nominalRatio)) := by
    simpa [nominalRatio, poolAmountRaw, poolSupplyRaw] using href.baseCeil
  have hcomputedExponent :
      computedExponent = (result.pre.exponentRaw : ℝ) / BONE := rfl
  have hexponentFloor :
      IsFloor result.pre.exponentRaw ((BONE : ℝ) * (1 / weight)) := by
    simpa [weight] using href.exponentFloor
  have hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate := by
    simpa [feeMultiplier, weight, feeRate] using href.feeMultiplierEq
  have hnewTokenBalanceCeil :
      IsCeil result.newTokenBalanceRaw
        (outputBalanceRaw *
          ((result.cpow.powerRaw : ℝ) / (BONE : ℝ))) := by
    simpa [outputBalanceRaw] using href.newTokenBalanceCeil
  have htokenAmount :
      (result.tokenAmountBeforeFeeRaw : ℝ) =
        outputBalanceRaw - result.newTokenBalanceRaw := by
    rw [href.tokenAmountEq]
    simp [outputBalanceRaw]
  have hfeeFloor :
      IsFloor result.resultRaw
        ((result.tokenAmountBeforeFeeRaw : ℝ) * feeMultiplier) := by
    simpa [feeMultiplier] using href.feeFloor
  have houtputFloor :
      IsFloor result.output ((result.resultRaw : ℝ) / scale) := by
    simpa [scale] using href.outputFloor
  have hmaxOutputFloor :
      IsFloor result.maxOutputRaw
        (outputBalanceRaw / scale * ((MAX_OUT_RATIO : ℝ) / STROOP)) := by
    rw [houtputBalanceOriginal]
    exact href.maxOutputFloor
  have hreciprocalBounds := single_sided_deposit_reciprocal_weight_bounds
    hweightBounds.1 hweightLowerReal hweightUpperReal
  have hexactExponentUpper :
      (BONE : ℝ) * (1 / weight) ≤ (10 * BONE : ℤ) := by
    exact_mod_cast mul_le_mul_of_nonneg_left hreciprocalBounds.1
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  have hexponentRawUpper : result.pre.exponentRaw ≤ 10 * BONE := by
    exact_mod_cast le_trans hexponentFloor.le hexactExponentUpper
  have hexponentSplit := bounded_bone_exponent_source_split
    href.exponentNonnegative hexponentRawUpper
  have hbaseExecutionBounds :=
    singleSidedDepositCPowExecution_base_bounds href.cpowExec
  have hratio1 : nominalRatio < 1 := by
    have hexactPositive : 0 < (BONE : ℝ) * (1 - nominalRatio) := by
      have hrawLower : (1 : ℝ) ≤ result.pre.baseRaw := by
        exact_mod_cast hbaseExecutionBounds.1
      linarith [hbaseCeil.add_one_lt]
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    nlinarith
  have hbaseRawUpper : result.pre.baseRaw ≤ BONE := by
    apply hbaseCeil.le_integer_upper
    have hnominal0 : 0 ≤ nominalRatio := hnominalPositive.le
    norm_num [BONE] at ⊢
    nlinarith
  have hbaseFacts := single_sided_withdrawal_base_ceil_refines
    hnominalPositive.le hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := by
    dsimp [computedBase]
    exact div_pos (by exact_mod_cast hbaseExecutionBounds.1)
      (by norm_num [BONE])
  have hbaseUpper : computedBase ≤ 1 := by
    dsimp [computedBase]
    exact (div_le_one (by norm_num [BONE] : (0 : ℝ) < BONE)).2
      (by exact_mod_cast hbaseRawUpper)
  have hrawResult :
      (result.output : ℝ) -
          singleSidedWithdrawalIdealOutput
            (outputBalanceRaw / scale) weight feeRate nominalRatio <
        SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
          singleSidedWithdrawalMinimumFeeOutputValue
            (outputBalanceRaw / scale) weight nominalRatio := by
    cases hcpowCase : result.cpow with
    | integer integerPart wholeRaw =>
        have hcpowExec :
            singleSidedDepositCPowExecution result.pre.baseRaw
                result.pre.exponentRaw = some (.integer integerPart wholeRaw) := by
          simpa [hcpowCase] using href.cpowExec
        have hcomponents := singleSidedDepositCPowExecution_integer_components
          hexponentSplit.1 hcpowExec
        have hwholeTrace := upperPowiExecution_refines
          (le_trans (by norm_num) hbaseExecutionBounds.1) hcomponents.2.2
        have hcomputedExponentInteger :
            (integerPart : ℝ) =
              (result.pre.exponentRaw : ℝ) / BONE := by
          rw [hcomponents.1]
          have hsplit := hexponentSplit.2.2.2
          rw [hcomponents.2.1] at hsplit
          simpa using hsplit.symm
        exact baseline_single_sided_withdrawal_integer_adverse_error_lt_precise_fee_share
          (integerPart := integerPart) (poolSupply := poolSupplyRaw)
          (poolAmountIn := poolAmountRaw) (nominalRatio := nominalRatio)
          (outputBalance := outputBalanceRaw) (weight := weight)
          (feeRate := feeRate) (computedBase := computedBase)
          (computedPower := (wholeRaw : ℝ)) (feeMultiplier := feeMultiplier)
          (scale := scale) (computedBaseRaw := result.pre.baseRaw)
          (computedExponentRaw := result.pre.exponentRaw)
          (newBalance := result.newTokenBalanceRaw)
          (tokenAmountBeforeFee := result.tokenAmountBeforeFeeRaw)
          (result := result.resultRaw) (output := result.output)
          hpoolSupplyRaw hpoolAmountRaw hnominal hratio1 houtputBalanceRaw
          hweightBounds.1 hweightBounds.2 hfee0 hfee1 hcomputedBase hbaseCeil
          href.exponentNonnegative hcomputedExponentInteger hexponentFloor
          (by simpa [computedBase] using hwholeTrace) hfeeMultiplier hscale
          (by simpa [hcpowCase] using hnewTokenBalanceCeil) htokenAmount
          hfeeFloor houtputFloor
    | fractional integerPart remainRaw wholeRaw approx powerRaw =>
        have hcpowExec :
            singleSidedDepositCPowExecution result.pre.baseRaw
                result.pre.exponentRaw =
              some (.fractional integerPart remainRaw wholeRaw approx powerRaw) := by
          simpa [hcpowCase] using href.cpowExec
        have hcomponents := singleSidedDepositCPowExecution_fractional_components
          hexponentSplit.1 hcpowExec
        let a : ℝ := (remainRaw : ℝ) / BONE
        let wholeComputed : ℝ := (wholeRaw : ℝ) / BONE
        let computedPower : ℝ := powerRaw
        have hremain0 : 0 < remainRaw := by
          have hnonnegative : 0 ≤ remainRaw := by
            rw [hcomponents.2.1]
            exact hexponentSplit.2.1
          exact lt_of_le_of_ne hnonnegative (Ne.symm hcomponents.2.2.1)
        have hremainUpper : remainRaw < BONE := by
          rw [hcomponents.2.1]
          exact hexponentSplit.2.2.1
        have ha0 : 0 ≤ a := by dsimp [a]; positivity
        have ha1 : a ≤ 1 := by
          dsimp [a]
          exact (div_le_one (by norm_num [BONE] : (0 : ℝ) < BONE)).2
            (by exact_mod_cast hremainUpper.le)
        have haLt : a < 1 := by
          dsimp [a]
          exact (div_lt_one (by norm_num [BONE] : (0 : ℝ) < BONE)).2
            (by exact_mod_cast hremainUpper)
        have hcomputedExponentSplit :
            computedExponent = (integerPart : ℝ) + a := by
          dsimp [computedExponent, a]
          rw [hcomponents.1, hcomponents.2.1]
          exact hexponentSplit.2.2.2
        have hreciprocalLower : (10 / 9 : ℝ) ≤ 1 / weight := by
          apply (le_div_iff₀ hweightBounds.1).2
          have hmax : (MAX_WEIGHT : ℝ) / STROOP = 9 / 10 := by
            norm_num [MAX_WEIGHT, STROOP]
          rw [hmax] at hweightUpperReal
          nlinarith
        have hexponentRawStrict : (BONE : ℝ) < result.pre.exponentRaw := by
          have hlower := mul_le_mul_of_nonneg_left hreciprocalLower
            (show (0 : ℝ) ≤ BONE by norm_num [BONE])
          have hgap : (BONE : ℝ) + 1 < (BONE : ℝ) * (10 / 9) := by
            norm_num [BONE]
          linarith [hexponentFloor.lt_add_one]
        have hcomputedExponentOne : 1 < computedExponent := by
          dsimp [computedExponent]
          exact (one_lt_div (by norm_num [BONE] : (0 : ℝ) < BONE)).2
            hexponentRawStrict
        have hintegerPart : 1 ≤ integerPart := by
          have hpositive : 0 < integerPart := by
            by_contra hnot
            have hzero : integerPart = 0 := Nat.eq_zero_of_not_pos hnot
            subst integerPart
            norm_num at hcomputedExponentSplit
            linarith
          exact hpositive
        have happExec :
            exactOutputApproxExecution result.pre.baseRaw remainRaw =
              some approx := hcomponents.2.2.2.2.1
        have hwholeTrace :
            UpperCPowiTrace computedBase integerPart wholeComputed := by
          simpa [computedBase, wholeComputed] using
            upperPowiExecution_refines
              (le_trans (by norm_num) hbaseExecutionBounds.1)
                hcomponents.2.2.2.1
        have hfirstFloorRaw :=
          exactOutputApproxExecution_first_term_refines happExec
        have hfirstFloor :
            IsFloor (exactInputApproxStateAt approx.xRaw remainRaw 1).term
              ((BONE : ℝ) * a * (computedBase - 1)) := by
          convert hfirstFloorRaw using 1
          have hx := (exactOutputApproxExecution_success happExec).choose_spec.1
          rw [hx]
          dsimp [a, computedBase]
          push_cast
          norm_num [BONE]
          ring
        have hcomposedCeilRaw := (i256_fixed_mul_ceil_success_refines
          (by norm_num [BONE]) (by
            norm_num [BONE, SorobanFixedPointMath.I256.maxValue])
          hcomponents.2.2.2.2.2).1
        have happFacts := exactOutputApproxExecution_success happExec
        obtain ⟨finalState, hxRaw, hsteps, hunadjusted, hfinalTerm,
          hn1, hn50, hcontinued, hcorrected, hadjusted, hplain⟩ := happFacts
        by_cases hunit : result.pre.baseRaw = BONE
        · have hunitBase : computedBase = 1 := by
            dsimp [computedBase]
            rw [hunit]
            norm_num [BONE]
          have hx0 : approx.xRaw = 0 := by rw [hxRaw, hunit]; omega
          have hstateSum : finalState.sum = BONE := by
            rw [hx0] at hsteps
            exact exactInputApproxSteps_unit_sum hn50 hsteps
          have hpartialUnit : approx.partialRaw = BONE := by
            rw [hplain (by constructor <;> simp [hx0]), hunadjusted,
              hstateSum]
          have hwholeUpper := hwholeTrace.upper_bound hbase0.le
          have hcomposedUpper :
              wholeComputed * (approx.partialRaw : ℝ) ≤ computedPower := by
            dsimp [computedPower, wholeComputed]
            convert hcomposedCeilRaw.le using 1
            all_goals push_cast
            all_goals ring
          have hpowerUnit : (BONE : ℝ) ≤ computedPower := by
            rw [hpartialUnit] at hcomposedUpper
            rw [hunitBase] at hwholeUpper
            norm_num at hwholeUpper
            calc
              (BONE : ℝ) = 1 * BONE := by ring
              _ ≤ wholeComputed * BONE :=
                mul_le_mul_of_nonneg_right hwholeUpper (by norm_num [BONE])
              _ ≤ computedPower := hcomposedUpper
          exact baseline_single_sided_withdrawal_unit_base_adverse_error_lt_precise_fee_share
            (poolSupply := poolSupplyRaw) (poolAmountIn := poolAmountRaw)
            (nominalRatio := nominalRatio) (outputBalance := outputBalanceRaw)
            (weight := weight) (feeRate := feeRate) (computedBase := computedBase)
            (computedExponent := computedExponent) (computedPower := computedPower)
            (feeMultiplier := feeMultiplier) (scale := scale)
            (computedBaseRaw := result.pre.baseRaw)
            (computedExponentRaw := result.pre.exponentRaw)
            (newBalance := result.newTokenBalanceRaw)
            (tokenAmountBeforeFee := result.tokenAmountBeforeFeeRaw)
            (result := result.resultRaw) (output := result.output)
            hpoolSupplyRaw hpoolAmountRaw hnominal hratio1 houtputBalanceRaw
            hweightBounds.1 hweightBounds.2 hfee0 hfee1 hcomputedBase hbaseCeil
            href.exponentNonnegative hcomputedExponent hexponentFloor hunitBase
            hpowerUnit hfeeMultiplier hscale
            (by simpa [hcpowCase, computedPower] using hnewTokenBalanceCeil)
            htokenAmount hfeeFloor houtputFloor
        · have hbaseNonunit : computedBase < 1 := by
            have hrawStrict : result.pre.baseRaw < BONE :=
              lt_of_le_of_ne hbaseRawUpper hunit
            dsimp [computedBase]
            exact (div_lt_one (by norm_num [BONE] : (0 : ℝ) < BONE)).2
              (by exact_mod_cast hrawStrict)
          have hxNegative : approx.xRaw < 0 := by rw [hxRaw]; omega
          by_cases hfirst : approx.iterations = 1
          · have hpartialFirst :
                approx.partialRaw = BONE +
                  (exactInputApproxStateAt approx.xRaw remainRaw 1).term + 1 := by
              rw [hcorrected ⟨hfirst, ne_of_lt hxNegative⟩, hunadjusted]
              have hsum := exactInputApproxSteps_sum hn50 hsteps
              rw [hfirst] at hsum
              rw [hsum]
              simp
            have hcomposedCeil :
                IsCeil powerRaw
                  (wholeComputed *
                    ((BONE : ℝ) +
                      (exactInputApproxStateAt approx.xRaw remainRaw 1).term + 1)) := by
              have hpartialReal :
                  (approx.partialRaw : ℝ) =
                    (BONE : ℝ) +
                      (exactInputApproxStateAt approx.xRaw remainRaw 1).term + 1 := by
                exact_mod_cast hpartialFirst
              rw [← hpartialReal]
              dsimp [wholeComputed]
              convert hcomposedCeilRaw using 1
              all_goals push_cast
              all_goals ring
            exact baseline_single_sided_withdrawal_first_term_adverse_error_lt_precise_fee_share
              (integerPart := integerPart) (poolSupply := poolSupplyRaw)
              (poolAmountIn := poolAmountRaw) (nominalRatio := nominalRatio)
              (outputBalance := outputBalanceRaw) (weight := weight)
              (feeRate := feeRate) (computedBase := computedBase)
              (computedExponent := computedExponent) (a := a)
              (wholeComputed := wholeComputed) (computedPower := computedPower)
              (feeMultiplier := feeMultiplier) (scale := scale)
              (computedBaseRaw := result.pre.baseRaw)
              (computedExponentRaw := result.pre.exponentRaw)
              (firstRounded :=
                (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
              (computedPowerRaw := powerRaw)
              (newBalance := result.newTokenBalanceRaw)
              (tokenAmountBeforeFee := result.tokenAmountBeforeFeeRaw)
              (result := result.resultRaw) (output := result.output)
              hpoolSupplyRaw hpoolAmountRaw hnominal hratio1 houtputBalanceRaw
              hweightBounds.1 hweightBounds.2 hfee0 hfee1 hcomputedBase hbaseCeil
              href.exponentNonnegative hcomputedExponent hexponentFloor ha0 ha1
              hcomputedExponentSplit hfirstFloor hwholeTrace (by rfl)
              hcomposedCeil hfeeMultiplier hscale
              (by simpa [hcpowCase, computedPower] using hnewTokenBalanceCeil)
              htokenAmount hfeeFloor houtputFloor
          · have hn2 : 2 ≤ approx.iterations := by omega
            let coefficientProduct : ℕ → ℤ := fun k ↦
              (exactInputApproxStateAt approx.xRaw remainRaw k).coefficientProduct
            let multiplied : ℕ → ℤ := fun k ↦
              (exactInputApproxStateAt approx.xRaw remainRaw k).multiplied
            let computedTerm : ℕ → ℤ := fun k ↦
              (exactInputApproxStateAt approx.xRaw remainRaw k).term
            have hcoefficientFloor : ∀ k, 1 ≤ k → k < approx.iterations →
                IsFloor (coefficientProduct (k + 1))
                  ((BONE : ℝ) * (a - (k : ℝ)) * (computedBase - 1)) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ :=
                exactOutputApproxExecution_prefix happExec (k + 1)
                  (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by
                simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [coefficientProduct]
              rw [hstepAt]
              convert hstepFacts.1 using 1
              rw [hxRaw]
              dsimp [a, computedBase]
              push_cast
              norm_num [BONE]
              ring
            have hmultiplyFloor : ∀ k, 1 ≤ k → k < approx.iterations →
                IsFloor (multiplied (k + 1))
                  (((computedTerm k : ℤ) : ℝ) *
                    (coefficientProduct (k + 1) : ℝ) / BONE) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ :=
                exactOutputApproxExecution_prefix happExec (k + 1)
                  (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by
                simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [multiplied, computedTerm, coefficientProduct]
              rw [hstepAt]
              simpa using hstepFacts.2.1
            have hdivideFloor : ∀ k, 1 ≤ k → k < approx.iterations →
                IsFloor (computedTerm (k + 1))
                  ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ :=
                exactOutputApproxExecution_prefix happExec (k + 1)
                  (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by
                simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [computedTerm, multiplied]
              rw [hstepAt]
              simpa [Nat.cast_add, Nat.cast_one] using hstepFacts.2.2.1
            have hpartialUncorrected :
                approx.partialRaw = approx.unadjustedSumRaw := by
              apply hplain
              constructor
              · intro hbad
                exact hfirst hbad.1
              · omega
            have hsumState := exactInputApproxSteps_sum hn50 hsteps
            have hcomputedFractional :
                (approx.partialRaw : ℝ) = (BONE : ℝ) +
                  ∑ k ∈ Finset.range approx.iterations,
                    (computedTerm (k + 1) : ℝ) := by
              rw [hpartialUncorrected, hunadjusted, hsumState]
              push_cast
              rfl
            have hcomposedCeil :
                IsCeil powerRaw
                  (wholeComputed * (approx.partialRaw : ℝ)) := by
              dsimp [wholeComputed]
              convert hcomposedCeilRaw using 1
              all_goals push_cast
              all_goals ring
            exact baseline_single_sided_withdrawal_multiterm_adverse_error_lt_precise_fee_share
              coefficientProduct multiplied computedTerm
              (n := approx.iterations) (integerPart := integerPart)
              (poolSupply := poolSupplyRaw) (poolAmountIn := poolAmountRaw)
              (nominalRatio := nominalRatio) (outputBalance := outputBalanceRaw)
              (weight := weight) (feeRate := feeRate)
              (computedBase := computedBase)
              (computedExponent := computedExponent) (a := a)
              (computedFractional := (approx.partialRaw : ℝ))
              (wholeComputed := wholeComputed) (computedPower := computedPower)
              (feeMultiplier := feeMultiplier) (scale := scale)
              (computedBaseRaw := result.pre.baseRaw)
              (computedExponentRaw := result.pre.exponentRaw)
              (firstRounded :=
                (exactInputApproxStateAt approx.xRaw remainRaw 1).term)
              (computedPowerRaw := powerRaw)
              (newBalance := result.newTokenBalanceRaw)
              (tokenAmountBeforeFee := result.tokenAmountBeforeFeeRaw)
              (result := result.resultRaw) (output := result.output)
              (maxOutput := result.maxOutputRaw)
              hpoolSupplyRaw hpoolAmountRaw hnominal hratio1 houtputBalanceRaw
              hweightBounds.1 hweightBounds.2 hfee0 hfeeUpperReal
              hcomputedBase hbaseCeil hbaseNonunit href.exponentNonnegative
              hcomputedExponent hexponentFloor ha0 ha1 hintegerPart
              hcomputedExponentSplit hn2 hn50
              (by
                intro k hk hkn
                exact_mod_cast hcontinued k hk hkn)
              (by
                rw [(exactInputBinomialTerm_one ha0 hbaseUpper).1]
                simpa [computedTerm] using hfirstFloor)
              rfl hcoefficientFloor hmultiplyFloor hdivideFloor
              hcomputedFractional hwholeTrace (by rfl) hcomposedCeil
              hfeeMultiplier hscale
              (by simpa [hcpowCase, computedPower] using hnewTokenBalanceCeil)
              htokenAmount hfeeFloor houtputFloor hmaxOutputFloor
              href.maxOutputGuard
  rw [houtputBalanceOriginal, hnominalOriginal] at hrawResult
  simpa [weight, feeRate] using hrawResult

end CometPool
