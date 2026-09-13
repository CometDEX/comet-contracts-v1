import CometPool.Source.ExactOutputSwapSource
import CometPool.Operations.SingleSidedDeposit

set_option maxRecDepth 65536
set_option maxHeartbeats 800000

namespace CometPool

/-!
Executable, source-shaped model for
`calc_token_deposits_in_given_lp_token_amount` and the successful
`dep_lp_tokn_amt_out_get_tokn_in` ratio guard. Unlike swap exponents, the
ceiled reciprocal weight is produced directly at BONE precision, so this file
models the source `c_pow` split without assuming STROOP alignment.
-/

/-- Source control-flow result for an arbitrary BONE-scaled upper-directed exponent. -/
inductive SingleSidedDepositCPowExecutionResult where
  | integer (integerPart : ℕ) (wholeRaw : ℤ)
  | fractional
      (integerPart : ℕ) (remainRaw wholeRaw : ℤ)
      (approx : ExactOutputApproxExecutionResult) (powerRaw : ℤ)
deriving DecidableEq

def SingleSidedDepositCPowExecutionResult.powerRaw :
    SingleSidedDepositCPowExecutionResult → ℤ
  | .integer _ wholeRaw => wholeRaw
  | .fractional _ _ _ _ powerRaw => powerRaw

private theorem rustU32Cast_eq_self_of_le_ten
    {value : ℕ} (hvalue : value ≤ 10) : rustU32Cast value = value := by
  unfold rustU32Cast
  apply Nat.mod_eq_of_lt
  norm_num at ⊢
  omega

/-- Source-shaped `c_pow(..., round_up = true)` with an arbitrary raw exponent. -/
def singleSidedDepositCPowExecution
    (baseRaw exponentRaw : ℤ) : Option SingleSidedDepositCPowExecutionResult := do
  if baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw then
    none
  else
    let integerPart := rustU32Cast (exponentRaw / BONE).toNat
    let remainRaw := exponentRaw - (exponentRaw / BONE) * BONE
    let wholeRaw ← upperPowiExecution baseRaw integerPart
    if remainRaw = 0 then
      some (.integer integerPart wholeRaw)
    else
      let approx ← exactOutputApproxExecution baseRaw remainRaw
      let powerRaw ←
        SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
          wholeRaw approx.partialRaw BONE
      some (.fractional integerPart remainRaw wholeRaw approx powerRaw)

/-- Successful integer control flow exposes the exact source split. -/
theorem singleSidedDepositCPowExecution_integer_components
    {baseRaw exponentRaw : ℤ} {integerPart : ℕ} {wholeRaw : ℤ}
    (hintegerPart : (exponentRaw / BONE).toNat ≤ 10)
    (hexec : singleSidedDepositCPowExecution baseRaw exponentRaw =
      some (.integer integerPart wholeRaw)) :
    integerPart = (exponentRaw / BONE).toNat ∧
      exponentRaw - (exponentRaw / BONE) * BONE = 0 ∧
      upperPowiExecution baseRaw integerPart = some wholeRaw := by
  rw [singleSidedDepositCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · rw [if_neg hguard] at hexec
    rcases Option.bind_eq_some.mp hexec with ⟨whole, hwhole, hafterWhole⟩
    by_cases hremain : exponentRaw - (exponentRaw / BONE) * BONE = 0
    · rw [if_pos hremain] at hafterWhole
      have hfields := Option.some.inj hafterWhole
      cases hfields
      exact ⟨rustU32Cast_eq_self_of_le_ten hintegerPart, hremain, hwhole⟩
    · rw [if_neg hremain] at hafterWhole
      rcases Option.bind_eq_some.mp hafterWhole with ⟨approx, happ, hafterApprox⟩
      rcases Option.bind_eq_some.mp hafterApprox with ⟨power, hpower, hresult⟩
      cases hresult

/-- Successful fractional control flow exposes the exact source split. -/
theorem singleSidedDepositCPowExecution_fractional_components
    {baseRaw exponentRaw : ℤ} {integerPart : ℕ}
    {remainRaw wholeRaw powerRaw : ℤ}
    {approx : ExactOutputApproxExecutionResult}
    (hintegerPart : (exponentRaw / BONE).toNat ≤ 10)
    (hexec : singleSidedDepositCPowExecution baseRaw exponentRaw =
      some (.fractional integerPart remainRaw wholeRaw approx powerRaw)) :
    integerPart = (exponentRaw / BONE).toNat ∧
      remainRaw = exponentRaw - (exponentRaw / BONE) * BONE ∧
      remainRaw ≠ 0 ∧
      upperPowiExecution baseRaw integerPart = some wholeRaw ∧
      exactOutputApproxExecution baseRaw remainRaw = some approx ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        wholeRaw approx.partialRaw BONE = some powerRaw := by
  rw [singleSidedDepositCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · rw [if_neg hguard] at hexec
    rcases Option.bind_eq_some.mp hexec with ⟨whole, hwhole, hafterWhole⟩
    by_cases hremain : exponentRaw - (exponentRaw / BONE) * BONE = 0
    · rw [if_pos hremain] at hafterWhole
      cases Option.some.inj hafterWhole
    · rw [if_neg hremain] at hafterWhole
      rcases Option.bind_eq_some.mp hafterWhole with
        ⟨approxResult, happ, hafterApprox⟩
      rcases Option.bind_eq_some.mp hafterApprox with
        ⟨power, hpower, hresult⟩
      have hfields := Option.some.inj hresult
      cases hfields
      exact ⟨rustU32Cast_eq_self_of_le_ten hintegerPart,
        rfl, hremain, hwhole, happ, hpower⟩

/-- Successful source execution satisfies the production base guards. -/
theorem singleSidedDepositCPowExecution_base_bounds
    {baseRaw exponentRaw : ℤ} {result : SingleSidedDepositCPowExecutionResult}
    (hexec : singleSidedDepositCPowExecution baseRaw exponentRaw = some result) :
    1 ≤ baseRaw ∧ baseRaw ≤ 2 * BONE - 1 := by
  rw [singleSidedDepositCPowExecution] at hexec
  by_cases hguard : baseRaw < 1 ∨ (2 * (BONE : ℤ) - 1) < baseRaw
  · simp [hguard] at hexec
  · omega

private theorem exact_lp_deposit_i128_mul_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem exact_lp_deposit_i256_add_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x + y) = some result from hexec)
  exact h.2.symm

private theorem exact_lp_deposit_i256_sub_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I256.sub x y = some result) :
    result = x - y := by
  have h := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked (x - y) = some result from hexec)
  exact h.2.symm

private theorem exact_lp_deposit_isFloor_integer_eq
    {rounded exact : ℤ} (hfloor : IsFloor rounded (exact : ℝ)) :
    rounded = exact := by
  have hlower : rounded ≤ exact := by exact_mod_cast hfloor.le
  have hupperReal : (exact : ℝ) < rounded + 1 := hfloor.lt_add_one
  have hupper : exact < rounded + 1 := by exact_mod_cast hupperReal
  omega

/-- Successful checked i128 floor multiplication has exact floor semantics. -/
theorem i128_fixed_mul_floor_success_refines
    {x y result : ℤ} {denominator : ℕ}
    (hdenominator : 0 < denominator)
    (hdenominatorMax :
      (denominator : ℤ) ≤ SorobanFixedPointMath.I128.maxValue)
    (hexec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
        x y denominator = some result) :
    IsFloor result ((((x * y : ℤ) : ℝ) / (denominator : ℝ))) ∧
      SorobanFixedPointMath.I128.InRange result := by
  have hprod : SorobanFixedPointMath.I128.InRange (x * y) := by
    by_contra hprod
    have hnone :
        SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
          x y denominator = none := by
      simpa [SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor] using
        (SorobanFixedPointMath.I128FixedPointImpl.mulDivFloor_eq_none_of_product_out_of_range
          (x := x) (y := y) (d := denominator) hprod)
    rw [hexec] at hnone
    cases hnone
  have hvalueExec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
          x y denominator =
        some (SorobanFixedPointMath.I128FixedPointImpl.mulDivFloorValue
          x y denominator) := by
    simpa [SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor] using
      (SorobanFixedPointMath.I128FixedPointImpl.mulDivFloor_eq_some
        (x := x) (y := y) (d := denominator) hprod hdenominator hdenominatorMax)
  have hresult :
      result = SorobanFixedPointMath.I128FixedPointImpl.mulDivFloorValue
        x y denominator := Option.some.inj (hexec.symm.trans hvalueExec)
  rw [hresult]
  exact ⟨
    SorobanFixedPointMath.FixedPointImpl.mulDivFloorValue_isFloor
      x y hdenominator,
    SorobanFixedPointMath.I128FixedPointImpl.mulDivFloorValue_inRange
      hprod hdenominator⟩

/-- Checked intermediates before the reciprocal-exponent `c_pow` call. -/
structure SingleSidedDepositPrefix where
  tokenBalanceRaw : ℤ
  poolAmountRaw : ℤ
  poolSupplyRaw : ℤ
  feeRaw : ℤ
  weightRaw : ℤ
  newPoolSupplyRaw : ℤ
  baseRaw : ℤ
  exponentRaw : ℤ

/-- Complete successful arithmetic result, including the public ratio guard. -/
structure SingleSidedDepositExecutionResult where
  pre : SingleSidedDepositPrefix
  cpow : SingleSidedDepositCPowExecutionResult
  newTokenBalanceRaw : ℤ
  tokenAmountAfterFeeRaw : ℤ
  weightComplementRaw : ℤ
  weightedFeeRaw : ℤ
  feeMultiplierRaw : ℤ
  resultRaw : ℤ
  downscaledRaw : ℤ
  output : ℤ
  maxInputRaw : ℤ

/-- Source arithmetic through the reciprocal-weight calculation. -/
def singleSidedDepositPrefixExecution
    (inputBalance inputScalar poolSupply poolAmountOut
      inputWeight fee : ℕ) : Option SingleSidedDepositPrefix := do
  let tokenBalanceRaw ←
    SorobanFixedPointMath.I128.mul inputBalance inputScalar
  let poolAmountRaw ←
    SorobanFixedPointMath.I128.mul poolAmountOut (BONE / STROOP)
  let poolSupplyRaw ←
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP)
  let feeRaw ← SorobanFixedPointMath.I128.mul fee (BONE / STROOP)
  let weightRaw ←
    SorobanFixedPointMath.I128.mul inputWeight (BONE / STROOP)
  let newPoolSupplyRaw ←
    SorobanFixedPointMath.I256.add poolSupplyRaw poolAmountRaw
  let baseRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      newPoolSupplyRaw poolSupplyRaw.toNat BONE
  let exponentRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
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

/-- Source arithmetic from `c_pow` through token downscaling and MAX_IN_RATIO. -/
def singleSidedDepositFinishExecution
    (inputBalance inputScalar : ℕ) (pre : SingleSidedDepositPrefix) :
    Option SingleSidedDepositExecutionResult := do
  let cpow ← singleSidedDepositCPowExecution pre.baseRaw pre.exponentRaw
  let newTokenBalanceRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
      pre.tokenBalanceRaw cpow.powerRaw BONE
  let tokenAmountAfterFeeRaw ←
    SorobanFixedPointMath.I256.sub newTokenBalanceRaw pre.tokenBalanceRaw
  let weightComplementRaw ← SorobanFixedPointMath.I256.sub BONE pre.weightRaw
  let weightedFeeRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      weightComplementRaw pre.feeRaw BONE
  let feeMultiplierRaw ← SorobanFixedPointMath.I256.sub BONE weightedFeeRaw
  let resultRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      tokenAmountAfterFeeRaw feeMultiplierRaw.toNat BONE
  let downscaledRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      resultRaw inputScalar 1
  let output ← SorobanFixedPointMath.I128.checked downscaledRaw
  let maxInputRaw ←
    SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
      inputBalance MAX_IN_RATIO STROOP
  if output ≤ maxInputRaw then
    some {
      pre
      cpow
      newTokenBalanceRaw
      tokenAmountAfterFeeRaw
      weightComplementRaw
      weightedFeeRaw
      feeMultiplierRaw
      resultRaw
      downscaledRaw
      output
      maxInputRaw
    }
  else
    none

/-- Executable model of the exact-LP-output single-sided deposit arithmetic. -/
def calcTokenDepositsInGivenLpTokenAmountExecution
    (inputBalance inputScalar poolSupply poolAmountOut
      inputWeight fee : ℕ) : Option SingleSidedDepositExecutionResult := do
  let pre ← singleSidedDepositPrefixExecution inputBalance inputScalar
    poolSupply poolAmountOut inputWeight fee
  singleSidedDepositFinishExecution inputBalance inputScalar pre

/-- Successful prefix execution exposes every checked source operation. -/
theorem singleSidedDepositPrefixExecution_success
    {inputBalance inputScalar poolSupply poolAmountOut inputWeight fee : ℕ}
    {result : SingleSidedDepositPrefix}
    (hexec : singleSidedDepositPrefixExecution inputBalance inputScalar
      poolSupply poolAmountOut inputWeight fee = some result) :
    SorobanFixedPointMath.I128.mul inputBalance inputScalar =
        some result.tokenBalanceRaw ∧
      SorobanFixedPointMath.I128.mul poolAmountOut (BONE / STROOP) =
        some result.poolAmountRaw ∧
      SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP) =
        some result.poolSupplyRaw ∧
      SorobanFixedPointMath.I128.mul fee (BONE / STROOP) =
        some result.feeRaw ∧
      SorobanFixedPointMath.I128.mul inputWeight (BONE / STROOP) =
        some result.weightRaw ∧
      SorobanFixedPointMath.I256.add result.poolSupplyRaw result.poolAmountRaw =
        some result.newPoolSupplyRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.newPoolSupplyRaw result.poolSupplyRaw.toNat BONE =
          some result.baseRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        BONE result.weightRaw.toNat BONE = some result.exponentRaw := by
  rw [singleSidedDepositPrefixExecution] at hexec
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

/-- Successful finish execution exposes all post-`c_pow` operations and guard. -/
theorem singleSidedDepositFinishExecution_success
    {inputBalance inputScalar : ℕ} {pre : SingleSidedDepositPrefix}
    {result : SingleSidedDepositExecutionResult}
    (hexec : singleSidedDepositFinishExecution inputBalance inputScalar pre =
      some result) :
    result.pre = pre ∧
      singleSidedDepositCPowExecution pre.baseRaw pre.exponentRaw =
        some result.cpow ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        pre.tokenBalanceRaw result.cpow.powerRaw BONE =
          some result.newTokenBalanceRaw ∧
      SorobanFixedPointMath.I256.sub result.newTokenBalanceRaw
        pre.tokenBalanceRaw = some result.tokenAmountAfterFeeRaw ∧
      SorobanFixedPointMath.I256.sub BONE pre.weightRaw =
        some result.weightComplementRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.weightComplementRaw pre.feeRaw BONE =
          some result.weightedFeeRaw ∧
      SorobanFixedPointMath.I256.sub BONE result.weightedFeeRaw =
        some result.feeMultiplierRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.tokenAmountAfterFeeRaw result.feeMultiplierRaw.toNat BONE =
          some result.resultRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.resultRaw inputScalar 1 = some result.downscaledRaw ∧
      SorobanFixedPointMath.I128.checked result.downscaledRaw =
        some result.output ∧
      SorobanFixedPointMath.I128FixedPointImpl.fixedMulFloor
        inputBalance MAX_IN_RATIO STROOP = some result.maxInputRaw ∧
      result.output ≤ result.maxInputRaw := by
  rw [singleSidedDepositFinishExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨cpow, hcpow, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨newTokenBalanceRaw, hnewTokenBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenAmountAfterFeeRaw, htokenAmount, hexec⟩
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
  rcases Option.bind_eq_some.mp hexec with ⟨maxInputRaw, hmaxInput, hexec⟩
  by_cases hguard : output ≤ maxInputRaw
  · rw [if_pos hguard] at hexec
    have hfields := Option.some.inj hexec
    cases hfields
    exact ⟨rfl, hcpow, hnewTokenBalance, htokenAmount,
      hweightComplement, hweightedFee, hfeeMultiplier, hresultRaw,
      hdownscaled, houtput, hmaxInput, hguard⟩
  · simp [hguard] at hexec

/-- A complete successful result supplies both execution phases. -/
theorem calcTokenDepositsInGivenLpTokenAmountExecution_success
    {inputBalance inputScalar poolSupply poolAmountOut inputWeight fee : ℕ}
    {result : SingleSidedDepositExecutionResult}
    (hexec : calcTokenDepositsInGivenLpTokenAmountExecution inputBalance
      inputScalar poolSupply poolAmountOut inputWeight fee = some result) :
    ∃ pre,
      singleSidedDepositPrefixExecution inputBalance inputScalar poolSupply
          poolAmountOut inputWeight fee = some pre ∧
        singleSidedDepositFinishExecution inputBalance inputScalar pre =
          some result := by
  rw [calcTokenDepositsInGivenLpTokenAmountExecution] at hexec
  exact Option.bind_eq_some.mp hexec

/-- Fixed-point facts recovered from one successful source-shaped execution. -/
structure SingleSidedDepositRunRefinements
    {inputBalance inputScalar poolSupply poolAmountOut inputWeight fee : ℕ}
    (result : SingleSidedDepositExecutionResult) : Prop where
  tokenBalanceEq :
    result.pre.tokenBalanceRaw = (inputBalance : ℤ) * inputScalar
  poolAmountEq :
    result.pre.poolAmountRaw = (poolAmountOut : ℤ) * (BONE / STROOP)
  poolSupplyEq :
    result.pre.poolSupplyRaw = (poolSupply : ℤ) * (BONE / STROOP)
  tokenBalancePositive : 0 < result.pre.tokenBalanceRaw
  poolAmountPositive : 0 < result.pre.poolAmountRaw
  poolSupplyPositive : 0 < result.pre.poolSupplyRaw
  weightRawEq :
    result.pre.weightRaw = (inputWeight : ℤ) * (BONE / STROOP)
  newPoolSupplyEq :
    result.pre.newPoolSupplyRaw =
      result.pre.poolSupplyRaw + result.pre.poolAmountRaw
  baseCeil :
    IsCeil result.pre.baseRaw
      ((BONE : ℝ) *
        (1 + (result.pre.poolAmountRaw : ℝ) / result.pre.poolSupplyRaw))
  exponentCeil :
    IsCeil result.pre.exponentRaw
      ((BONE : ℝ) * (1 / ((inputWeight : ℝ) / STROOP)))
  cpowExec :
    singleSidedDepositCPowExecution result.pre.baseRaw result.pre.exponentRaw =
      some result.cpow
  newTokenBalanceCeil :
    IsCeil result.newTokenBalanceRaw
      ((result.pre.tokenBalanceRaw : ℝ) *
        ((result.cpow.powerRaw : ℝ) / BONE))
  tokenAmountEq :
    result.tokenAmountAfterFeeRaw =
      result.newTokenBalanceRaw - result.pre.tokenBalanceRaw
  feeMultiplierPositive : 0 < result.feeMultiplierRaw
  feeMultiplierEq :
    (result.feeMultiplierRaw : ℝ) / BONE =
      1 - singleSidedWithdrawalFeeRate
        ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
  feeCeil :
    IsCeil result.resultRaw
      ((result.tokenAmountAfterFeeRaw : ℝ) /
        ((result.feeMultiplierRaw : ℝ) / BONE))
  outputCeil :
    IsCeil result.output ((result.resultRaw : ℝ) / inputScalar)
  maxInputFloor :
    IsFloor result.maxInputRaw
      ((inputBalance : ℝ) * ((MAX_IN_RATIO : ℝ) / STROOP))
  maxInputGuard : result.output ≤ result.maxInputRaw

/-- One successful execution derives every fixed-point premise used downstream. -/
theorem calcTokenDepositsInGivenLpTokenAmountExecution_refines
    {inputBalance inputScalar poolSupply poolAmountOut inputWeight fee : ℕ}
    {result : SingleSidedDepositExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenDepositsInGivenLpTokenAmountExecution inputBalance
      inputScalar poolSupply poolAmountOut inputWeight fee = some result) :
    SingleSidedDepositRunRefinements
      (inputBalance := inputBalance) (inputScalar := inputScalar)
      (poolSupply := poolSupply) (poolAmountOut := poolAmountOut)
      (inputWeight := inputWeight) (fee := fee) result := by
  obtain ⟨pre, hpreExec, hfinishExec⟩ :=
    calcTokenDepositsInGivenLpTokenAmountExecution_success hexec
  rcases singleSidedDepositFinishExecution_success hfinishExec with
    ⟨hpre, hcpow, hnewTokenBalance, htokenAmount, hweightComplement,
      hweightedFee, hfeeMultiplier, hresultRaw, hdownscaled, houtput,
      hmaxInput, hmaxInputGuard⟩
  subst pre
  rcases singleSidedDepositPrefixExecution_success hpreExec with
    ⟨htokenBalance, hpoolAmount, hpoolSupplyExec, hfee, hweight,
      hnewPoolSupply, hbase, hexponent⟩
  have htokenBalanceEq := exact_lp_deposit_i128_mul_success_eq htokenBalance
  have hpoolAmountEq := exact_lp_deposit_i128_mul_success_eq hpoolAmount
  have hpoolSupplyEq := exact_lp_deposit_i128_mul_success_eq hpoolSupplyExec
  have hfeeEq := exact_lp_deposit_i128_mul_success_eq hfee
  have hweightEq := exact_lp_deposit_i128_mul_success_eq hweight
  have htokenBalance0 : 0 < result.pre.tokenBalanceRaw := by
    rw [htokenBalanceEq]
    positivity
  have hpoolAmount0 : 0 < result.pre.poolAmountRaw := by
    rw [hpoolAmountEq]
    exact_mod_cast Nat.mul_pos hpoolAmountOut
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hpoolSupply0 : 0 < result.pre.poolSupplyRaw := by
    rw [hpoolSupplyEq]
    exact_mod_cast Nat.mul_pos hpoolSupply
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hweight0 : 0 < inputWeight :=
    lt_of_lt_of_le (by norm_num [MIN_WEIGHT]) hweightLower
  have hweightLt : inputWeight < STROOP :=
    lt_of_le_of_lt hweightUpper (by norm_num [MAX_WEIGHT, STROOP])
  have hfeeLt : fee < STROOP :=
    lt_of_le_of_lt hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hnewPoolSupplyEq := exact_lp_deposit_i256_add_success_eq hnewPoolSupply
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
      (result.pre.poolSupplyRaw.toNat : ℝ) =
        result.pre.poolSupplyRaw := by
    exact_mod_cast Int.toNat_of_nonneg hpoolSupply0.le
  have hbaseCeil :
      IsCeil result.pre.baseRaw
        ((BONE : ℝ) *
          (1 + (result.pre.poolAmountRaw : ℝ) /
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
      ((inputWeight : ℤ) * (BONE / STROOP)) = some result.pre.weightRaw
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
  have hexponentCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hweightRaw0) hweightNatMax hexponent).1
  have hweightCast :
      (result.pre.weightRaw.toNat : ℝ) = result.pre.weightRaw := by
    exact_mod_cast Int.toNat_of_nonneg hweightRaw0.le
  have hexponentCeil :
      IsCeil result.pre.exponentRaw
        ((BONE : ℝ) * (1 / ((inputWeight : ℝ) / STROOP))) := by
    rw [hweightCast, hweightEq] at hexponentCeilRaw
    convert hexponentCeilRaw using 1
    push_cast
    norm_num [BONE, STROOP]
    field_simp [show (inputWeight : ℝ) ≠ 0 by positivity]
    ring
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
  have htokenAmountEq := exact_lp_deposit_i256_sub_success_eq htokenAmount
  have hweightComplementEq :=
    exact_lp_deposit_i256_sub_success_eq hweightComplement
  let weightedFeeExpected : ℤ :=
    (STROOP - inputWeight) * fee * (BONE / (STROOP * STROOP) : ℕ)
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
    apply exact_lp_deposit_isFloor_integer_eq
    rw [← hweightedExact]
    exact hweightedFloor
  have hfeeMultiplierRawEq :=
    exact_lp_deposit_i256_sub_success_eq hfeeMultiplier
  have hfeeMultiplierEq :
      (result.feeMultiplierRaw : ℝ) / BONE =
        1 - singleSidedWithdrawalFeeRate
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP) := by
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
      have hweightReal0 : 0 ≤ (inputWeight : ℝ) / STROOP := by positivity
      have hweightReal1 : (inputWeight : ℝ) / STROOP ≤ 1 := by
        apply (div_le_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
        exact_mod_cast hweightLt.le
      have hfeeReal0 : 0 ≤ (fee : ℝ) / STROOP := by positivity
      have hfeeReal1 : (fee : ℝ) / STROOP < 1 := by
        apply (div_lt_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
        exact_mod_cast hfeeLt
      have hweightedLt :
          (1 - (inputWeight : ℝ) / STROOP) * ((fee : ℝ) / STROOP) < 1 := by
        have hle := mul_le_mul_of_nonneg_right
          (show 1 - (inputWeight : ℝ) / STROOP ≤ 1 by linarith)
          hfeeReal0
        linarith
      linarith
    have hrawPositive : (0 : ℝ) < result.feeMultiplierRaw := by
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      rcases div_pos_iff.mp hnormalizedPositive with hpos | hneg
      · exact hpos.1
      · linarith [hneg.2]
    exact_mod_cast hrawPositive
  have hfeeMultiplierRange := SorobanFixedPointMath.I256.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I256.checked
      (BONE - result.weightedFeeRaw) = some result.feeMultiplierRaw
      from hfeeMultiplier)
  have hfeeMultiplierNatMax :
      (result.feeMultiplierRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hfeeMultiplier0.le]
    rw [← hfeeMultiplierRange.2]
    exact hfeeMultiplierRange.1.2
  have hfeeCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hfeeMultiplier0) hfeeMultiplierNatMax
      hresultRaw).1
  have hfeeMultiplierCast :
      (result.feeMultiplierRaw.toNat : ℝ) = result.feeMultiplierRaw := by
    exact_mod_cast Int.toNat_of_nonneg hfeeMultiplier0.le
  have hfeeCeil :
      IsCeil result.resultRaw
        ((result.tokenAmountAfterFeeRaw : ℝ) /
          ((result.feeMultiplierRaw : ℝ) / BONE)) := by
    rw [hfeeMultiplierCast] at hfeeCeilRaw
    convert hfeeCeilRaw using 1
    push_cast
    field_simp [show (result.feeMultiplierRaw : ℝ) ≠ 0 by
      exact_mod_cast ne_of_gt hfeeMultiplier0]
  have hdownscaleCeil := (i256_fixed_div_ceil_success_refines
    hinputScalar (by
      calc
        (inputScalar : ℤ) ≤ SorobanFixedPointMath.I128.maxValue := by
          have hrange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
            (show SorobanFixedPointMath.I128.checked
              ((inputBalance : ℤ) * inputScalar) =
                some result.pre.tokenBalanceRaw from htokenBalance)
          have hinputBalanceOne : (1 : ℤ) ≤ inputBalance := by
            exact_mod_cast hinputBalance
          nlinarith [hrange.1.2]
        _ ≤ SorobanFixedPointMath.I256.maxValue := by
          norm_num [SorobanFixedPointMath.I128.maxValue,
            SorobanFixedPointMath.I256.maxValue]) hdownscaled).1
  have houtputEq : result.output = result.downscaledRaw :=
    (SorobanFixedPointMath.I128.checked_eq_some_iff.mp houtput).2.symm
  have houtputCeil :
      IsCeil result.output ((result.resultRaw : ℝ) / inputScalar) := by
    rw [houtputEq]
    convert hdownscaleCeil using 1
    push_cast
    ring
  have hmaxInputFloor := (i128_fixed_mul_floor_success_refines
    (by norm_num [STROOP]) (by
      norm_num [STROOP, SorobanFixedPointMath.I128.maxValue]) hmaxInput).1
  have hmaxInputFloor' :
      IsFloor result.maxInputRaw
        ((inputBalance : ℝ) * ((MAX_IN_RATIO : ℝ) / STROOP)) := by
    convert hmaxInputFloor using 1
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
    exponentCeil := hexponentCeil
    cpowExec := hcpow
    newTokenBalanceCeil := hnewTokenBalanceCeil
    tokenAmountEq := htokenAmountEq
    feeMultiplierPositive := hfeeMultiplier0
    feeMultiplierEq := hfeeMultiplierEq
    feeCeil := hfeeCeil
    outputCeil := houtputCeil
    maxInputFloor := hmaxInputFloor'
    maxInputGuard := hmaxInputGuard
  }

/-- Euclidean source split for a nonnegative exponent bounded by ten. -/
theorem bounded_bone_exponent_source_split
    {exponentRaw : ℤ}
    (hexponent0 : 0 ≤ exponentRaw)
    (hexponentUpper : exponentRaw ≤ 10 * BONE) :
    (exponentRaw / BONE).toNat ≤ 10 ∧
      0 ≤ exponentRaw - (exponentRaw / BONE) * BONE ∧
      exponentRaw - (exponentRaw / BONE) * BONE < BONE ∧
      (exponentRaw : ℝ) / BONE =
        ((exponentRaw / BONE).toNat : ℝ) +
          ((exponentRaw - (exponentRaw / BONE) * BONE : ℤ) : ℝ) / BONE := by
  have hB : (0 : ℤ) < BONE := by norm_num [BONE]
  have hdecomp := Int.ediv_add_emod exponentRaw BONE
  have hremainEq :
      exponentRaw - (exponentRaw / BONE) * BONE = exponentRaw % BONE := by
    nlinarith
  have hremain0 : 0 ≤ exponentRaw - (exponentRaw / BONE) * BONE := by
    rw [hremainEq]
    exact Int.emod_nonneg _ (ne_of_gt hB)
  have hremainUpper :
      exponentRaw - (exponentRaw / BONE) * BONE < BONE := by
    rw [hremainEq]
    exact Int.emod_lt_of_pos _ hB
  have hquotient0 : 0 ≤ exponentRaw / BONE :=
    Int.ediv_nonneg hexponent0 hB.le
  have hquotientUpper : exponentRaw / BONE ≤ 10 := by
    norm_num [BONE] at hexponentUpper hremain0 ⊢
    nlinarith
  have htoNat : ((exponentRaw / BONE).toNat : ℤ) = exponentRaw / BONE :=
    Int.toNat_of_nonneg hquotient0
  constructor
  · have hcast : (((exponentRaw / BONE).toNat : ℕ) : ℤ) ≤ 10 := by
      rw [htoNat]
      exact hquotientUpper
    exact_mod_cast hcast
  constructor
  · exact hremain0
  constructor
  · exact hremainUpper
  · have htoNatReal :
        (((exponentRaw / BONE).toNat : ℕ) : ℝ) =
          (exponentRaw / BONE : ℤ) := by
      exact_mod_cast htoNat
    rw [htoNatReal]
    have hBReal : (0 : ℝ) < BONE := by norm_num [BONE]
    field_simp [ne_of_gt hBReal]

/-
Every successful source-shaped exact-LP-output deposit has pool-adverse error
strictly below `1.107%` of the adjusted weighted minimum-fee value.
-/
theorem calc_token_deposits_in_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share
    {inputBalance inputScalar poolSupply poolAmountOut inputWeight fee : ℕ}
    {result : SingleSidedDepositExecutionResult}
    (hinputBalance : 0 < inputBalance) (hinputScalar : 0 < inputScalar)
    (hpoolSupply : 0 < poolSupply) (hpoolAmountOut : 0 < poolAmountOut)
    (hweightLower : MIN_WEIGHT ≤ inputWeight)
    (hweightUpper : inputWeight ≤ MAX_WEIGHT)
    (hfeeUpper : fee ≤ MAX_FEE)
    (hexec : calcTokenDepositsInGivenLpTokenAmountExecution inputBalance
      inputScalar poolSupply poolAmountOut inputWeight fee = some result) :
    singleSidedDepositIdealInput (inputBalance : ℝ)
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
          ((poolAmountOut : ℝ) / poolSupply) - (result.output : ℝ) <
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositAdjustedMinimumFeeInputValue (inputBalance : ℝ)
          ((inputWeight : ℝ) / STROOP) ((fee : ℝ) / STROOP)
          ((poolAmountOut : ℝ) / poolSupply) := by
  have href := calcTokenDepositsInGivenLpTokenAmountExecution_refines
    hinputBalance hinputScalar hpoolSupply hpoolAmountOut hweightLower
      hweightUpper hfeeUpper hexec
  let inputBalanceRaw : ℝ := result.pre.tokenBalanceRaw
  let poolSupplyRaw : ℝ := result.pre.poolSupplyRaw
  let poolAmountRaw : ℝ := result.pre.poolAmountRaw
  let weight : ℝ := (inputWeight : ℝ) / STROOP
  let feeRate : ℝ := (fee : ℝ) / STROOP
  let nominalRatio : ℝ := poolAmountRaw / poolSupplyRaw
  let computedBase : ℝ := (result.pre.baseRaw : ℝ) / BONE
  let computedExponent : ℝ := (result.pre.exponentRaw : ℝ) / BONE
  let feeMultiplier : ℝ := (result.feeMultiplierRaw : ℝ) / BONE
  let scale : ℝ := inputScalar
  have hinputBalanceRaw : 0 < inputBalanceRaw := by
    dsimp [inputBalanceRaw]
    exact_mod_cast href.tokenBalancePositive
  have hpoolSupplyRaw : 0 < poolSupplyRaw := by
    dsimp [poolSupplyRaw]
    exact_mod_cast href.poolSupplyPositive
  have hpoolAmountRaw : 0 < poolAmountRaw := by
    dsimp [poolAmountRaw]
    exact_mod_cast href.poolAmountPositive
  have hscale : 0 < scale := by
    dsimp [scale]
    exact_mod_cast hinputScalar
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
  have hfee1 : feeRate < 1 := by
    dsimp [feeRate]
    apply (div_lt_one (by norm_num [STROOP] : (0 : ℝ) < STROOP)).2
    exact_mod_cast lt_of_le_of_lt hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hnominal : nominalRatio = poolAmountRaw / poolSupplyRaw := rfl
  have hnominalPositive : 0 < nominalRatio := by
    rw [hnominal]
    positivity
  have hnominalOriginal :
      nominalRatio = (poolAmountOut : ℝ) / poolSupply := by
    dsimp [nominalRatio, poolAmountRaw, poolSupplyRaw]
    rw [href.poolAmountEq, href.poolSupplyEq]
    push_cast
    norm_num [BONE, STROOP]
    field_simp [show (poolSupply : ℝ) ≠ 0 by positivity]
    ring
  have hinputBalanceOriginal : inputBalanceRaw / scale = inputBalance := by
    dsimp [inputBalanceRaw, scale]
    rw [href.tokenBalanceEq]
    push_cast
    field_simp [show (inputScalar : ℝ) ≠ 0 by positivity]
  have hcomputedBase :
      computedBase = (result.pre.baseRaw : ℝ) / BONE := rfl
  have hbaseCeil :
      IsCeil result.pre.baseRaw
        ((BONE : ℝ) * (1 + nominalRatio)) := by
    simpa [nominalRatio, poolAmountRaw, poolSupplyRaw] using href.baseCeil
  have hcomputedExponent :
      computedExponent = (result.pre.exponentRaw : ℝ) / BONE := rfl
  have hexponentCeil :
      IsCeil result.pre.exponentRaw ((BONE : ℝ) * (1 / weight)) := by
    simpa [weight] using href.exponentCeil
  have hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate := by
    simpa [feeMultiplier, weight, feeRate] using href.feeMultiplierEq
  have hnewTokenBalanceCeil :
      IsCeil result.newTokenBalanceRaw
        (inputBalanceRaw *
          ((result.cpow.powerRaw : ℝ) / (BONE : ℝ))) := by
    simpa [inputBalanceRaw] using href.newTokenBalanceCeil
  have htokenAmount :
      (result.tokenAmountAfterFeeRaw : ℝ) =
        result.newTokenBalanceRaw - inputBalanceRaw := by
    rw [href.tokenAmountEq]
    simp [inputBalanceRaw]
  have hfeeCeil :
      IsCeil result.resultRaw
        ((result.tokenAmountAfterFeeRaw : ℝ) / feeMultiplier) := by
    simpa [feeMultiplier] using href.feeCeil
  have houtputCeil :
      IsCeil result.output ((result.resultRaw : ℝ) / scale) := by
    simpa [scale] using href.outputCeil
  have hmaxInputFloor :
      IsFloor result.maxInputRaw
        (inputBalanceRaw / scale * ((MAX_IN_RATIO : ℝ) / STROOP)) := by
    rw [hinputBalanceOriginal]
    exact href.maxInputFloor
  have hreciprocalBounds := single_sided_deposit_reciprocal_weight_bounds
    hweightBounds.1 hweightLowerReal hweightUpperReal
  have hexactExponentUpper :
      (BONE : ℝ) * (1 / weight) ≤ (10 * BONE : ℤ) := by
    exact_mod_cast mul_le_mul_of_nonneg_left hreciprocalBounds.1
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  have hexponentRawUpper : result.pre.exponentRaw ≤ 10 * BONE :=
    hexponentCeil.le_integer_upper hexactExponentUpper
  have hexponentRaw0 : 0 ≤ result.pre.exponentRaw := by
    have hreal : (0 : ℝ) ≤ result.pre.exponentRaw := by
      have hexact0 : 0 ≤ (BONE : ℝ) * (1 / weight) := by positivity
      exact le_trans hexact0 hexponentCeil.le
    exact_mod_cast hreal
  have hexponentSplit := bounded_bone_exponent_source_split
    hexponentRaw0 hexponentRawUpper
  have hbaseBounds := singleSidedDepositCPowExecution_base_bounds href.cpowExec
  have hbaseFacts := single_sided_deposit_base_ceil_refines
    (by positivity : 0 ≤ nominalRatio) hcomputedBase hbaseCeil
  have hbaseStrict : 1 < computedBase := by
    have hidealStrict : 1 < singleSidedDepositIdealBase nominalRatio := by
      rw [singleSidedDepositIdealBase]
      linarith
    exact lt_of_lt_of_le hidealStrict hbaseFacts.1
  have hbaseRawStrict : BONE < result.pre.baseRaw := by
    have hreal : (BONE : ℝ) < result.pre.baseRaw := by
      have hB : (0 : ℝ) < BONE := by norm_num [BONE]
      have := (one_lt_div hB).mp (by simpa [computedBase] using hbaseStrict)
      simpa using this
    exact_mod_cast hreal
  have hbaseTwo : computedBase < 2 := by
    dsimp [computedBase]
    have hraw : (result.pre.baseRaw : ℝ) < 2 * BONE := by
      exact_mod_cast (lt_of_le_of_lt hbaseBounds.2 (by omega))
    exact (div_lt_iff₀ (by norm_num [BONE] : (0 : ℝ) < BONE)).2 (by
      simpa [mul_comm] using hraw)
  have hrawResult :
      singleSidedDepositIdealInput (inputBalanceRaw / scale) weight feeRate
            nominalRatio - (result.output : ℝ) <
        SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
          singleSidedDepositAdjustedMinimumFeeInputValue
            (inputBalanceRaw / scale) weight feeRate nominalRatio := by
    cases hcpowCase : result.cpow with
    | integer integerPart wholeRaw =>
        have hcpowExec :
            singleSidedDepositCPowExecution result.pre.baseRaw
                result.pre.exponentRaw = some (.integer integerPart wholeRaw) := by
          simpa [hcpowCase] using href.cpowExec
        have hcomponents := singleSidedDepositCPowExecution_integer_components
          hexponentSplit.1 hcpowExec
        have hwholeTrace := upperPowiExecution_refines
          (le_trans (by norm_num) hbaseBounds.1)
          hcomponents.2.2
        have hcomputedExponentInteger :
            (integerPart : ℝ) =
              (result.pre.exponentRaw : ℝ) / BONE := by
          rw [hcomponents.1]
          have hsplit := hexponentSplit.2.2.2
          rw [hcomponents.2.1] at hsplit
          simpa using hsplit.symm
        exact baseline_single_sided_deposit_integer_adverse_error_lt_precise_fee_share
          (integerPart := integerPart) (poolSupply := poolSupplyRaw)
          (poolAmountOut := poolAmountRaw) (nominalRatio := nominalRatio)
          (inputBalance := inputBalanceRaw) (weight := weight)
          (feeRate := feeRate) (computedBase := computedBase)
          (computedPower := (wholeRaw : ℝ)) (feeMultiplier := feeMultiplier)
          (scale := scale) (computedBaseRaw := result.pre.baseRaw)
          (computedExponentRaw := result.pre.exponentRaw)
          (newBalance := result.newTokenBalanceRaw)
          (tokenAmountAfterFee := result.tokenAmountAfterFeeRaw)
          (result := result.resultRaw) (output := result.output)
          hpoolSupplyRaw hpoolAmountRaw hnominal hinputBalanceRaw
          hweightBounds.1 hweightBounds.2 hfee0 hfee1 hcomputedBase hbaseCeil
          hcomputedExponentInteger hexponentCeil
          (by simpa [computedBase] using hwholeTrace) hfeeMultiplier hscale
          (by simpa [hcpowCase] using hnewTokenBalanceCeil) htokenAmount
          hfeeCeil houtputCeil
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
        have ha0 : 0 ≤ a := by
          dsimp [a]
          positivity
        have ha1 : a ≤ 1 := by
          dsimp [a]
          exact (div_le_one (by norm_num [BONE] : (0 : ℝ) < BONE)).2
            (by exact_mod_cast hremainUpper.le)
        have hcomputedExponentSplit :
            computedExponent = (integerPart : ℝ) + a := by
          dsimp [computedExponent, a]
          rw [hcomponents.1, hcomponents.2.1]
          exact hexponentSplit.2.2.2
        have happExec :
            exactOutputApproxExecution result.pre.baseRaw remainRaw =
              some approx := hcomponents.2.2.2.2.1
        have hwholeTrace :
            UpperCPowiTrace computedBase integerPart wholeComputed := by
          simpa [computedBase, wholeComputed] using
            upperPowiExecution_refines
              (le_trans (by norm_num) hbaseBounds.1) hcomponents.2.2.2.1
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
          hn1, hn50, hcontinued, hfirstCorrection, hlaterCorrection, hplain⟩ :=
            happFacts
        by_cases hfirst : approx.iterations = 1
        · have hpartial := exactOutputApproxExecution_first_sum
            hbaseRawStrict happExec hfirst
          have hcomposedCeil :
              IsCeil powerRaw
                (wholeComputed *
                  ((BONE : ℝ) +
                    (exactInputApproxStateAt approx.xRaw remainRaw 1).term + 1)) := by
            have hpartialReal :
                (approx.partialRaw : ℝ) =
                  (BONE : ℝ) +
                    (exactInputApproxStateAt approx.xRaw remainRaw 1).term + 1 := by
              exact_mod_cast hpartial
            rw [← hpartialReal]
            dsimp [wholeComputed]
            convert hcomposedCeilRaw using 1
            all_goals push_cast
            all_goals ring
          exact baseline_single_sided_deposit_first_term_adverse_error_lt_precise_fee_share
            (integerPart := integerPart) (poolSupply := poolSupplyRaw)
            (poolAmountOut := poolAmountRaw) (nominalRatio := nominalRatio)
            (inputBalance := inputBalanceRaw) (weight := weight)
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
            (tokenAmountAfterFee := result.tokenAmountAfterFeeRaw)
            (result := result.resultRaw) (output := result.output)
            hpoolSupplyRaw hpoolAmountRaw hnominal hinputBalanceRaw
            hweightBounds.1 hweightBounds.2 hfee0 hfee1 hcomputedBase hbaseCeil
            hcomputedExponent hexponentCeil ha0 ha1 hcomputedExponentSplit
            hfirstFloor hwholeTrace (by rfl) hcomposedCeil hfeeMultiplier
            hscale (by simpa [hcpowCase, computedPower] using
              hnewTokenBalanceCeil) htokenAmount hfeeCeil houtputCeil
        · have hn2 : 2 ≤ approx.iterations := by omega
          by_cases hsecond : approx.iterations = 2
          · have hpartial := exactOutputApproxExecution_second_sum
              hbaseRawStrict hremain0 hremainUpper happExec hsecond
            have hfirstNonnegative :=
              (exactOutputApproxExecution_term_sign hbaseRawStrict hremain0
                hremainUpper happExec 1 (by omega) (by omega)).1 (by norm_num)
            have hfirstContinued :
                (CPOW_PRECISION : ℝ) <
                  (exactInputApproxStateAt approx.xRaw remainRaw 1).term := by
              have hsource := hcontinued 1 (by omega) (by omega)
              rw [abs_of_nonneg hfirstNonnegative] at hsource
              exact_mod_cast hsource
            have hcomposedCeil :
                IsCeil powerRaw
                  (wholeComputed *
                    ((BONE : ℝ) +
                      (exactInputApproxStateAt approx.xRaw remainRaw 1).term)) := by
              have hpartialReal :
                  (approx.partialRaw : ℝ) =
                    (BONE : ℝ) +
                      (exactInputApproxStateAt approx.xRaw remainRaw 1).term := by
                exact_mod_cast hpartial
              rw [← hpartialReal]
              dsimp [wholeComputed]
              convert hcomposedCeilRaw using 1
              all_goals push_cast
              all_goals ring
            exact baseline_single_sided_deposit_second_term_adverse_error_lt_precise_fee_share
              (integerPart := integerPart) (poolSupply := poolSupplyRaw)
              (poolAmountOut := poolAmountRaw) (nominalRatio := nominalRatio)
              (inputBalance := inputBalanceRaw) (weight := weight)
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
              (tokenAmountAfterFee := result.tokenAmountAfterFeeRaw)
              (result := result.resultRaw) (output := result.output)
              (maxInput := result.maxInputRaw) hpoolSupplyRaw hpoolAmountRaw
              hnominal hinputBalanceRaw hweightBounds.1 hweightLowerReal
              hweightUpperReal hweightBounds.2 hfee0 hfee1 hcomputedBase
              hbaseCeil hcomputedExponent hexponentCeil ha0 ha1
              hcomputedExponentSplit hfirstFloor hfirstContinued hwholeTrace
              (by rfl) hcomposedCeil hfeeMultiplier hscale
              (by simpa [hcpowCase, computedPower] using hnewTokenBalanceCeil)
              htokenAmount hfeeCeil houtputCeil hmaxInputFloor href.maxInputGuard
          · have hn3 : 3 ≤ approx.iterations := by omega
            obtain ⟨degree, oddIndex, hdegreeOdd, hdegreeStop, hpartial⟩ :=
              exactOutputApproxExecution_later_sum hbaseRawStrict hremain0
                hremainUpper happExec hn3
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
                    stepState := by simp [exactInputApproxStateAt, hstep]
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
                  ((computedTerm k : ℝ) *
                    (coefficientProduct (k + 1) : ℝ) / BONE) := by
              intro k hk hkn
              obtain ⟨stepState, hstep⟩ :=
                exactOutputApproxExecution_prefix happExec (k + 1)
                  (by omega) (by omega)
              have hstepAt :
                  exactInputApproxStateAt approx.xRaw remainRaw (k + 1) =
                    stepState := by simp [exactInputApproxStateAt, hstep]
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
                    stepState := by simp [exactInputApproxStateAt, hstep]
              have hstepFacts := exactInputApproxSteps_refinements
                (iteration := k + 1) (by omega) (by omega) hstep
              dsimp [computedTerm, multiplied]
              rw [hstepAt]
              simpa [Nat.cast_add, Nat.cast_one] using hstepFacts.2.2.1
            have hcomputedFractional :
                (approx.partialRaw : ℝ) = (BONE : ℝ) +
                  ∑ k ∈ Finset.range degree, (computedTerm (k + 1) : ℝ) := by
              exact_mod_cast hpartial
            have hcomposedCeil :
                IsCeil powerRaw
                  (wholeComputed * (approx.partialRaw : ℝ)) := by
              dsimp [wholeComputed]
              convert hcomposedCeilRaw using 1
              all_goals push_cast
              all_goals ring
            exact baseline_single_sided_deposit_later_adverse_error_lt_precise_fee_share
              coefficientProduct multiplied computedTerm
              (n := approx.iterations) (degree := degree)
              (oddIndex := oddIndex) (integerPart := integerPart)
              (poolSupply := poolSupplyRaw) (poolAmountOut := poolAmountRaw)
              (nominalRatio := nominalRatio) (inputBalance := inputBalanceRaw)
              (weight := weight) (feeRate := feeRate)
              (computedBase := computedBase) (computedExponent := computedExponent)
              (a := a) (computedFractional := (approx.partialRaw : ℝ))
              (wholeComputed := wholeComputed) (computedPower := computedPower)
              (feeMultiplier := feeMultiplier) (scale := scale)
              (computedBaseRaw := result.pre.baseRaw)
              (computedExponentRaw := result.pre.exponentRaw)
              (computedPowerRaw := powerRaw)
              (newBalance := result.newTokenBalanceRaw)
              (tokenAmountAfterFee := result.tokenAmountAfterFeeRaw)
              (result := result.resultRaw) (output := result.output)
              (maxInput := result.maxInputRaw) hpoolSupplyRaw hpoolAmountRaw
              hnominal hinputBalanceRaw hweightBounds.1 hweightLowerReal
              hweightUpperReal hweightBounds.2 hfee0 hfee1 hcomputedBase
              hbaseCeil hbaseTwo hcomputedExponent hexponentCeil ha0 ha1
              hcomputedExponentSplit hn3 hn50 hdegreeOdd hdegreeStop
              (by
                intro k hk hkn
                exact_mod_cast hcontinued k hk hkn)
              (by
                rw [exactOutputBinomialTerm_one]
                simpa [computedTerm] using hfirstFloor)
              hcoefficientFloor hmultiplyFloor hdivideFloor hcomputedFractional
              hwholeTrace (by rfl) hcomposedCeil hfeeMultiplier hscale
              (by simpa [hcpowCase, computedPower] using hnewTokenBalanceCeil)
              htokenAmount hfeeCeil houtputCeil hmaxInputFloor href.maxInputGuard
  rw [hinputBalanceOriginal, hnominalOriginal] at hrawResult
  simpa [weight, feeRate] using hrawResult

end CometPool
