import CometPool.Source.SingleSidedDepositSource
import CometPool.Operations.ProportionalLiquidity

set_option maxRecDepth 65536

namespace CometPool

/-!
Executable, source-shaped models for the proportional `join_pool` and
`exit_pool` arithmetic. Each shared ratio is evaluated once, then applied to
every modeled token record. Successful list execution proves the existing
per-token pool-favoring theorem for every returned token amount.
-/

private theorem proportional_i128_mul_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.mul x y = some result) :
    result = x * y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x * y) = some result from hexec)
  exact h.2.symm

private theorem proportional_i128_add_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x + y) = some result from hexec)
  exact h.2.symm

/-- Successful source execution of `calc_join_ratio`. -/
structure JoinPoolRatioExecutionResult where
  poolSupplyRaw : ℤ
  poolAmountRaw : ℤ
  ratioRaw : ℤ

/-- Source-shaped `calc_join_ratio` plus its public positive-ratio guard. -/
def joinPoolRatioExecution
    (poolSupply poolAmountOut : ℕ) : Option JoinPoolRatioExecutionResult := do
  let poolSupplyRaw ←
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP)
  let poolAmountRaw ←
    SorobanFixedPointMath.I128.mul poolAmountOut (BONE / STROOP)
  let ratioRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      poolAmountRaw poolSupplyRaw.toNat BONE
  if 0 < ratioRaw then
    some { poolSupplyRaw, poolAmountRaw, ratioRaw }
  else
    none

/-- One token record and its user-selected maximum input. -/
structure JoinPoolTokenInput where
  balance : ℕ
  scalar : ℕ
  maxAmountIn : ℕ
deriving DecidableEq

/-- Successful source execution for one token in the public join loop. -/
structure JoinPoolTokenExecutionResult where
  input : JoinPoolTokenInput
  tokenBalanceRaw : ℤ
  productRaw : ℤ
  downscaledRaw : ℤ
  output : ℤ
  balanceAfter : ℤ
deriving DecidableEq

/--
Source-shaped `calc_join_deposit_amount` plus the public positive-output,
positive-maximum, maximum-input guards and checked balance update.
-/
def joinPoolTokenExecution
    (ratioRaw : ℤ) (input : JoinPoolTokenInput) :
    Option JoinPoolTokenExecutionResult := do
  let tokenBalanceRaw ←
    SorobanFixedPointMath.I128.mul input.balance input.scalar
  let productRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
      tokenBalanceRaw ratioRaw BONE
  let downscaledRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
      productRaw input.scalar 1
  let output ← SorobanFixedPointMath.I128.checked downscaledRaw
  if output ≤ 0 then
    none
  else if input.maxAmountIn = 0 then
    none
  else if (input.maxAmountIn : ℤ) < output then
    none
  else
    let balanceAfter ←
      SorobanFixedPointMath.I128.add input.balance output
    some {
      input
      tokenBalanceRaw
      productRaw
      downscaledRaw
      output
      balanceAfter
    }

/-- Apply the shared join ratio to every token record in source loop order. -/
def joinPoolTokensExecution
    (ratioRaw : ℤ) : List JoinPoolTokenInput →
      Option (List JoinPoolTokenExecutionResult)
  | [] => some []
  | input :: inputs => do
      let result ← joinPoolTokenExecution ratioRaw input
      let results ← joinPoolTokensExecution ratioRaw inputs
      some (result :: results)

/-- Complete successful proportional join result. -/
structure JoinPoolExecutionResult where
  ratio : JoinPoolRatioExecutionResult
  tokens : List JoinPoolTokenExecutionResult

/-- Executable model of the public proportional join arithmetic and guards. -/
def joinPoolExecution
    (poolSupply poolAmountOut : ℕ) (inputs : List JoinPoolTokenInput) :
    Option JoinPoolExecutionResult := do
  let ratio ← joinPoolRatioExecution poolSupply poolAmountOut
  let tokens ← joinPoolTokensExecution ratio.ratioRaw inputs
  some { ratio, tokens }

/-- Successful ratio execution exposes all checked operations and its guard. -/
theorem joinPoolRatioExecution_success
    {poolSupply poolAmountOut : ℕ} {result : JoinPoolRatioExecutionResult}
    (hexec : joinPoolRatioExecution poolSupply poolAmountOut = some result) :
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP) =
        some result.poolSupplyRaw ∧
      SorobanFixedPointMath.I128.mul poolAmountOut (BONE / STROOP) =
        some result.poolAmountRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.poolAmountRaw result.poolSupplyRaw.toNat BONE =
          some result.ratioRaw ∧
      0 < result.ratioRaw := by
  rw [joinPoolRatioExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨poolSupplyRaw, hpoolSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨poolAmountRaw, hpoolAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨ratioRaw, hratio, hexec⟩
  by_cases hpositive : 0 < ratioRaw
  · rw [if_pos hpositive] at hexec
    have hfields := Option.some.inj hexec
    cases hfields
    exact ⟨hpoolSupply, hpoolAmount, hratio, hpositive⟩
  · simp [hpositive] at hexec

/-- Successful per-token execution exposes every operation and caller guard. -/
theorem joinPoolTokenExecution_success
    {ratioRaw : ℤ} {input : JoinPoolTokenInput}
    {result : JoinPoolTokenExecutionResult}
    (hexec : joinPoolTokenExecution ratioRaw input = some result) :
    result.input = input ∧
      SorobanFixedPointMath.I128.mul input.balance input.scalar =
        some result.tokenBalanceRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulCeil
        result.tokenBalanceRaw ratioRaw BONE = some result.productRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivCeil
        result.productRaw input.scalar 1 = some result.downscaledRaw ∧
      SorobanFixedPointMath.I128.checked result.downscaledRaw =
        some result.output ∧
      0 < result.output ∧
      0 < input.maxAmountIn ∧
      result.output ≤ input.maxAmountIn ∧
      SorobanFixedPointMath.I128.add input.balance result.output =
        some result.balanceAfter := by
  rw [joinPoolTokenExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceRaw, htokenBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨productRaw, hproduct, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨downscaledRaw, hdownscaled, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨output, houtput, hexec⟩
  by_cases hpositive : output ≤ 0
  · simp [hpositive] at hexec
  · rw [if_neg hpositive] at hexec
    by_cases hmaximumPositive : input.maxAmountIn = 0
    · simp [hmaximumPositive] at hexec
    · rw [if_neg hmaximumPositive] at hexec
      by_cases hmaximum : (input.maxAmountIn : ℤ) < output
      · simp [hmaximum] at hexec
      · rw [if_neg hmaximum] at hexec
        rcases Option.bind_eq_some.mp hexec with
          ⟨balanceAfter, hbalanceAfter, hresult⟩
        have hfields := Option.some.inj hresult
        cases hfields
        exact ⟨rfl, htokenBalance, hproduct, hdownscaled, houtput,
          lt_of_not_ge hpositive, Nat.pos_of_ne_zero hmaximumPositive,
          le_of_not_gt hmaximum, hbalanceAfter⟩

/-- A successful complete execution exposes its ratio and list phases. -/
theorem joinPoolExecution_success
    {poolSupply poolAmountOut : ℕ} {inputs : List JoinPoolTokenInput}
    {result : JoinPoolExecutionResult}
    (hexec : joinPoolExecution poolSupply poolAmountOut inputs = some result) :
    joinPoolRatioExecution poolSupply poolAmountOut = some result.ratio ∧
      joinPoolTokensExecution result.ratio.ratioRaw inputs =
        some result.tokens := by
  rw [joinPoolExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨ratio, hratio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨tokens, htokens, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨hratio, htokens⟩

/-- Every returned token result comes from its recorded source input. -/
theorem joinPoolTokensExecution_each_success
    {ratioRaw : ℤ} {inputs : List JoinPoolTokenInput}
    {results : List JoinPoolTokenExecutionResult}
    (hexec : joinPoolTokensExecution ratioRaw inputs = some results) :
    ∀ result ∈ results,
      result.input ∈ inputs ∧
        joinPoolTokenExecution ratioRaw result.input = some result := by
  induction inputs generalizing results with
  | nil =>
      simp [joinPoolTokensExecution] at hexec
      subst results
      simp
  | cons input inputs ih =>
      rw [joinPoolTokensExecution] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨head, hhead, hexec⟩
      rcases Option.bind_eq_some.mp hexec with ⟨tail, htail, hresult⟩
      have hlist := Option.some.inj hresult
      subst results
      intro result hmember
      rcases List.mem_cons.mp hmember with hresult | hresult
      · subst result
        have hinput := (joinPoolTokenExecution_success hhead).1
        constructor
        · simp [hinput]
        · simpa [hinput] using hhead
      · have htailResult := ih htail result hresult
        exact ⟨List.mem_cons_of_mem input htailResult.1, htailResult.2⟩

/-- Mathematical ceiling refinement of one successful shared join ratio. -/
theorem joinPoolRatioExecution_refines
    {poolSupply poolAmountOut : ℕ} {result : JoinPoolRatioExecutionResult}
    (hpoolSupply : 0 < poolSupply)
    (hexec : joinPoolRatioExecution poolSupply poolAmountOut = some result) :
    result.poolSupplyRaw = (poolSupply : ℤ) * (BONE / STROOP) ∧
      result.poolAmountRaw = (poolAmountOut : ℤ) * (BONE / STROOP) ∧
      IsCeil result.ratioRaw
        ((((poolAmountOut : ℝ) * (BONE / STROOP : ℕ)) * (BONE : ℝ)) /
          ((poolSupply : ℝ) * (BONE / STROOP : ℕ))) := by
  rcases joinPoolRatioExecution_success hexec with
    ⟨hpoolSupplyExec, hpoolAmountExec, hratioExec, hratioPositive⟩
  have hpoolSupplyEq := proportional_i128_mul_success_eq hpoolSupplyExec
  have hpoolAmountEq := proportional_i128_mul_success_eq hpoolAmountExec
  have hpoolSupply0 : 0 < result.poolSupplyRaw := by
    rw [hpoolSupplyEq]
    exact_mod_cast Nat.mul_pos hpoolSupply
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hpoolSupplyRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      ((poolSupply : ℤ) * (BONE / STROOP)) = some result.poolSupplyRaw
      from hpoolSupplyExec)
  have hpoolSupplyNatMax :
      (result.poolSupplyRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hpoolSupply0.le]
    calc
      result.poolSupplyRaw ≤ SorobanFixedPointMath.I128.maxValue := by
        rw [← hpoolSupplyRange.2]
        exact hpoolSupplyRange.1.2
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hratioCeilRaw := (i256_fixed_div_ceil_success_refines
    (Int.pos_iff_toNat_pos.mp hpoolSupply0) hpoolSupplyNatMax hratioExec).1
  have hpoolSupplyCast :
      (result.poolSupplyRaw.toNat : ℝ) = result.poolSupplyRaw := by
    exact_mod_cast Int.toNat_of_nonneg hpoolSupply0.le
  have hratioCeil :
      IsCeil result.ratioRaw
        ((((poolAmountOut : ℝ) * (BONE / STROOP : ℕ)) * (BONE : ℝ)) /
          ((poolSupply : ℝ) * (BONE / STROOP : ℕ))) := by
    rw [hpoolSupplyCast, hpoolSupplyEq, hpoolAmountEq] at hratioCeilRaw
    convert hratioCeilRaw using 1
    push_cast
    norm_num [BONE, STROOP]
  exact ⟨hpoolSupplyEq, hpoolAmountEq, hratioCeil⟩

/-- Mathematical refinements of one successful token deposit. -/
theorem joinPoolTokenExecution_refines
    {ratioRaw : ℤ} {input : JoinPoolTokenInput}
    {result : JoinPoolTokenExecutionResult}
    (hscalar : 0 < input.scalar) (hscalarUpper : input.scalar ≤ BONE)
    (hexec : joinPoolTokenExecution ratioRaw input = some result) :
    result.input = input ∧
      IsCeil result.productRaw
        ((((input.balance : ℝ) * input.scalar) * (ratioRaw : ℝ)) /
          (BONE : ℝ)) ∧
      IsCeil result.output ((result.productRaw : ℝ) / input.scalar) ∧
      0 < result.output ∧ 0 < input.maxAmountIn ∧
      result.output ≤ input.maxAmountIn ∧
      result.balanceAfter = input.balance + result.output := by
  rcases joinPoolTokenExecution_success hexec with
    ⟨hinput, htokenBalanceExec, hproductExec, hdownscaledExec, houtputExec,
      houtputPositive, hmaximumPositive, hmaximumGuard, hbalanceAfterExec⟩
  have htokenBalanceEq :=
    proportional_i128_mul_success_eq htokenBalanceExec
  have hproductCeilRaw := (i256_fixed_mul_ceil_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hproductExec).1
  have hproductCeil :
      IsCeil result.productRaw
        ((((input.balance : ℝ) * input.scalar) * (ratioRaw : ℝ)) /
          (BONE : ℝ)) := by
    rw [htokenBalanceEq] at hproductCeilRaw
    convert hproductCeilRaw using 1
    push_cast
    ring
  have hscalarMax :
      (input.scalar : ℤ) ≤ SorobanFixedPointMath.I256.maxValue := by
    calc
      (input.scalar : ℤ) ≤ BONE := by exact_mod_cast hscalarUpper
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [BONE, SorobanFixedPointMath.I256.maxValue]
  have hdownscaledCeilRaw := (i256_fixed_div_ceil_success_refines
    hscalar hscalarMax hdownscaledExec).1
  have houtputEq : result.output = result.downscaledRaw :=
    (SorobanFixedPointMath.I128.checked_eq_some_iff.mp houtputExec).2.symm
  have houtputCeil :
      IsCeil result.output ((result.productRaw : ℝ) / input.scalar) := by
    rw [houtputEq]
    convert hdownscaledCeilRaw using 1
    push_cast
    ring
  have hbalanceAfterEq :=
    proportional_i128_add_success_eq hbalanceAfterExec
  exact ⟨hinput, hproductCeil, houtputCeil, houtputPositive,
    hmaximumPositive, hmaximumGuard, hbalanceAfterEq⟩

/-- A successful source-shaped token join cannot charge below its ideal share. -/
theorem joinPoolTokenExecution_cannot_undercharge
    {poolSupply poolAmountOut : ℕ} {ratio : JoinPoolRatioExecutionResult}
    {input : JoinPoolTokenInput} {result : JoinPoolTokenExecutionResult}
    (hpoolSupply : 0 < poolSupply)
    (hscalar : 0 < input.scalar) (hscalarUpper : input.scalar ≤ BONE)
    (hratioExec : joinPoolRatioExecution poolSupply poolAmountOut = some ratio)
    (htokenExec : joinPoolTokenExecution ratio.ratioRaw input = some result) :
    proportionalAmount input.balance poolAmountOut poolSupply ≤
      (result.output : ℝ) := by
  have hratio := joinPoolRatioExecution_refines
    hpoolSupply hratioExec
  have htoken := joinPoolTokenExecution_refines
    hscalar hscalarUpper htokenExec
  exact join_pool_per_token_cannot_undercharge
    (poolSupply := poolSupply) (poolAmountOut := poolAmountOut)
    (tokenBalance := input.balance) (poolScale := (BONE / STROOP : ℕ))
    (tokenScale := input.scalar) (ratioRaw := ratio.ratioRaw)
    (productRaw := result.productRaw) (tokenAmountIn := result.output)
    (by exact_mod_cast hpoolSupply)
    (by norm_num [BONE, STROOP]) (by positivity) (by exact_mod_cast hscalar)
    hratio.2.2 htoken.2.1 htoken.2.2.1

/--
Every token amount in a successful modeled public join is pool-favoring.
The premise on scalars is exactly the range established by initialization for
token decimal scalars `10^(18 - decimals)` with `decimals ≤ 18`.
-/
theorem joinPoolExecution_every_token_cannot_undercharge
    {poolSupply poolAmountOut : ℕ} {inputs : List JoinPoolTokenInput}
    {result : JoinPoolExecutionResult}
    (hpoolSupply : 0 < poolSupply)
    (hscalars : ∀ input ∈ inputs, 0 < input.scalar ∧ input.scalar ≤ BONE)
    (hexec : joinPoolExecution poolSupply poolAmountOut inputs = some result) :
    ∀ tokenResult ∈ result.tokens,
      proportionalAmount tokenResult.input.balance poolAmountOut poolSupply ≤
        (tokenResult.output : ℝ) := by
  have hphases := joinPoolExecution_success hexec
  have heach := joinPoolTokensExecution_each_success hphases.2
  intro tokenResult hmember
  have hsource := heach tokenResult hmember
  have hscalar := hscalars tokenResult.input hsource.1
  exact joinPoolTokenExecution_cannot_undercharge
    hpoolSupply hscalar.1 hscalar.2 hphases.1 hsource.2

/-- Successful source execution of `calc_exit_ratio`. -/
structure ExitPoolRatioExecutionResult where
  poolSupplyRaw : ℤ
  poolAmountRaw : ℤ
  ratioRaw : ℤ

/-- Source-shaped `calc_exit_ratio` plus its public positive-ratio guard. -/
def exitPoolRatioExecution
    (poolSupply poolAmountIn : ℕ) : Option ExitPoolRatioExecutionResult := do
  let poolSupplyRaw ←
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP)
  let poolAmountRaw ←
    SorobanFixedPointMath.I128.mul poolAmountIn (BONE / STROOP)
  let ratioRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      poolAmountRaw poolSupplyRaw.toNat BONE
  if 0 < ratioRaw then
    some { poolSupplyRaw, poolAmountRaw, ratioRaw }
  else
    none

/-- One token record and its user-selected minimum output. -/
structure ExitPoolTokenInput where
  balance : ℕ
  scalar : ℕ
  minAmountOut : ℕ
deriving DecidableEq

/-- Successful source execution for one token in the public exit loop. -/
structure ExitPoolTokenExecutionResult where
  input : ExitPoolTokenInput
  tokenBalanceRaw : ℤ
  productRaw : ℤ
  downscaledRaw : ℤ
  output : ℤ
  balanceAfter : ℤ
deriving DecidableEq

/--
Source-shaped `calc_exit_withdrawal_amount` plus the public positive-output,
minimum-output, and available-balance guards and the resulting balance update.
-/
def exitPoolTokenExecution
    (ratioRaw : ℤ) (input : ExitPoolTokenInput) :
    Option ExitPoolTokenExecutionResult := do
  let tokenBalanceRaw ←
    SorobanFixedPointMath.I128.mul input.balance input.scalar
  let productRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
      tokenBalanceRaw ratioRaw BONE
  let downscaledRaw ←
    SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
      productRaw input.scalar 1
  let output ← SorobanFixedPointMath.I128.checked downscaledRaw
  if output ≤ 0 then
    none
  else if output < input.minAmountOut then
    none
  else if input.balance < output then
    none
  else
    some {
      input
      tokenBalanceRaw
      productRaw
      downscaledRaw
      output
      balanceAfter := input.balance - output
    }

/-- Apply the shared exit ratio to every token record in source loop order. -/
def exitPoolTokensExecution
    (ratioRaw : ℤ) : List ExitPoolTokenInput →
      Option (List ExitPoolTokenExecutionResult)
  | [] => some []
  | input :: inputs => do
      let result ← exitPoolTokenExecution ratioRaw input
      let results ← exitPoolTokensExecution ratioRaw inputs
      some (result :: results)

/-- Complete successful proportional exit result. -/
structure ExitPoolExecutionResult where
  ratio : ExitPoolRatioExecutionResult
  tokens : List ExitPoolTokenExecutionResult

/-- Executable model of the public proportional exit arithmetic and guards. -/
def exitPoolExecution
    (poolSupply poolAmountIn : ℕ) (inputs : List ExitPoolTokenInput) :
    Option ExitPoolExecutionResult := do
  let ratio ← exitPoolRatioExecution poolSupply poolAmountIn
  let tokens ← exitPoolTokensExecution ratio.ratioRaw inputs
  some { ratio, tokens }

/-- Successful ratio execution exposes all checked operations and its guard. -/
theorem exitPoolRatioExecution_success
    {poolSupply poolAmountIn : ℕ} {result : ExitPoolRatioExecutionResult}
    (hexec : exitPoolRatioExecution poolSupply poolAmountIn = some result) :
    SorobanFixedPointMath.I128.mul poolSupply (BONE / STROOP) =
        some result.poolSupplyRaw ∧
      SorobanFixedPointMath.I128.mul poolAmountIn (BONE / STROOP) =
        some result.poolAmountRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        result.poolAmountRaw result.poolSupplyRaw.toNat BONE =
          some result.ratioRaw ∧
      0 < result.ratioRaw := by
  rw [exitPoolRatioExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨poolSupplyRaw, hpoolSupply, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨poolAmountRaw, hpoolAmount, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨ratioRaw, hratio, hexec⟩
  by_cases hpositive : 0 < ratioRaw
  · rw [if_pos hpositive] at hexec
    have hfields := Option.some.inj hexec
    cases hfields
    exact ⟨hpoolSupply, hpoolAmount, hratio, hpositive⟩
  · simp [hpositive] at hexec

/-- Successful per-token execution exposes every operation and caller guard. -/
theorem exitPoolTokenExecution_success
    {ratioRaw : ℤ} {input : ExitPoolTokenInput}
    {result : ExitPoolTokenExecutionResult}
    (hexec : exitPoolTokenExecution ratioRaw input = some result) :
    result.input = input ∧
      SorobanFixedPointMath.I128.mul input.balance input.scalar =
        some result.tokenBalanceRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedMulFloor
        result.tokenBalanceRaw ratioRaw BONE = some result.productRaw ∧
      SorobanFixedPointMath.FixedPointImpl.fixedDivFloor
        result.productRaw input.scalar 1 = some result.downscaledRaw ∧
      SorobanFixedPointMath.I128.checked result.downscaledRaw =
        some result.output ∧
      0 < result.output ∧
      input.minAmountOut ≤ result.output ∧
      result.output ≤ input.balance ∧
      result.balanceAfter = input.balance - result.output := by
  rw [exitPoolTokenExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with
    ⟨tokenBalanceRaw, htokenBalance, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨productRaw, hproduct, hexec⟩
  rcases Option.bind_eq_some.mp hexec with
    ⟨downscaledRaw, hdownscaled, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨output, houtput, hexec⟩
  by_cases hpositive : output ≤ 0
  · simp [hpositive] at hexec
  · rw [if_neg hpositive] at hexec
    by_cases hminimum : output < input.minAmountOut
    · simp [hminimum] at hexec
    · rw [if_neg hminimum] at hexec
      by_cases hbalance : input.balance < output
      · simp [hbalance] at hexec
      · rw [if_neg hbalance] at hexec
        have hfields := Option.some.inj hexec
        cases hfields
        exact ⟨rfl, htokenBalance, hproduct, hdownscaled, houtput,
          lt_of_not_ge hpositive, le_of_not_gt hminimum,
          le_of_not_gt hbalance, rfl⟩

/-- A successful complete execution exposes its ratio and list phases. -/
theorem exitPoolExecution_success
    {poolSupply poolAmountIn : ℕ} {inputs : List ExitPoolTokenInput}
    {result : ExitPoolExecutionResult}
    (hexec : exitPoolExecution poolSupply poolAmountIn inputs = some result) :
    exitPoolRatioExecution poolSupply poolAmountIn = some result.ratio ∧
      exitPoolTokensExecution result.ratio.ratioRaw inputs =
        some result.tokens := by
  rw [exitPoolExecution] at hexec
  rcases Option.bind_eq_some.mp hexec with ⟨ratio, hratio, hexec⟩
  rcases Option.bind_eq_some.mp hexec with ⟨tokens, htokens, hresult⟩
  have hfields := Option.some.inj hresult
  cases hfields
  exact ⟨hratio, htokens⟩

/-- Every returned token result comes from its recorded source input. -/
theorem exitPoolTokensExecution_each_success
    {ratioRaw : ℤ} {inputs : List ExitPoolTokenInput}
    {results : List ExitPoolTokenExecutionResult}
    (hexec : exitPoolTokensExecution ratioRaw inputs = some results) :
    ∀ result ∈ results,
      result.input ∈ inputs ∧
        exitPoolTokenExecution ratioRaw result.input = some result := by
  induction inputs generalizing results with
  | nil =>
      simp [exitPoolTokensExecution] at hexec
      subst results
      simp
  | cons input inputs ih =>
      rw [exitPoolTokensExecution] at hexec
      rcases Option.bind_eq_some.mp hexec with ⟨head, hhead, hexec⟩
      rcases Option.bind_eq_some.mp hexec with ⟨tail, htail, hresult⟩
      have hlist := Option.some.inj hresult
      subst results
      intro result hmember
      rcases List.mem_cons.mp hmember with hresult | hresult
      · subst result
        have hinput := (exitPoolTokenExecution_success hhead).1
        constructor
        · simp [hinput]
        · simpa [hinput] using hhead
      · have htailResult := ih htail result hresult
        exact ⟨List.mem_cons_of_mem input htailResult.1, htailResult.2⟩

/-- Mathematical floor refinement of one successful shared exit ratio. -/
theorem exitPoolRatioExecution_refines
    {poolSupply poolAmountIn : ℕ} {result : ExitPoolRatioExecutionResult}
    (hpoolSupply : 0 < poolSupply)
    (hexec : exitPoolRatioExecution poolSupply poolAmountIn = some result) :
    result.poolSupplyRaw = (poolSupply : ℤ) * (BONE / STROOP) ∧
      result.poolAmountRaw = (poolAmountIn : ℤ) * (BONE / STROOP) ∧
      IsFloor result.ratioRaw
        ((((poolAmountIn : ℝ) * (BONE / STROOP : ℕ)) * (BONE : ℝ)) /
          ((poolSupply : ℝ) * (BONE / STROOP : ℕ))) := by
  rcases exitPoolRatioExecution_success hexec with
    ⟨hpoolSupplyExec, hpoolAmountExec, hratioExec, hratioPositive⟩
  have hpoolSupplyEq := proportional_i128_mul_success_eq hpoolSupplyExec
  have hpoolAmountEq := proportional_i128_mul_success_eq hpoolAmountExec
  have hpoolSupply0 : 0 < result.poolSupplyRaw := by
    rw [hpoolSupplyEq]
    exact_mod_cast Nat.mul_pos hpoolSupply
      (by norm_num [BONE, STROOP] : 0 < BONE / STROOP)
  have hpoolSupplyRange := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked
      ((poolSupply : ℤ) * (BONE / STROOP)) = some result.poolSupplyRaw
      from hpoolSupplyExec)
  have hpoolSupplyNatMax :
      (result.poolSupplyRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I256.maxValue := by
    rw [Int.toNat_of_nonneg hpoolSupply0.le]
    calc
      result.poolSupplyRaw ≤ SorobanFixedPointMath.I128.maxValue := by
        rw [← hpoolSupplyRange.2]
        exact hpoolSupplyRange.1.2
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [SorobanFixedPointMath.I128.maxValue,
          SorobanFixedPointMath.I256.maxValue]
  have hratioFloorRaw := (i256_fixed_div_floor_success_refines
    (Int.pos_iff_toNat_pos.mp hpoolSupply0) hpoolSupplyNatMax hratioExec).1
  have hpoolSupplyCast :
      (result.poolSupplyRaw.toNat : ℝ) = result.poolSupplyRaw := by
    exact_mod_cast Int.toNat_of_nonneg hpoolSupply0.le
  have hratioFloor :
      IsFloor result.ratioRaw
        ((((poolAmountIn : ℝ) * (BONE / STROOP : ℕ)) * (BONE : ℝ)) /
          ((poolSupply : ℝ) * (BONE / STROOP : ℕ))) := by
    rw [hpoolSupplyCast, hpoolSupplyEq, hpoolAmountEq] at hratioFloorRaw
    convert hratioFloorRaw using 1
    push_cast
    norm_num [BONE, STROOP]
  exact ⟨hpoolSupplyEq, hpoolAmountEq, hratioFloor⟩

/-- Mathematical refinements of one successful token withdrawal. -/
theorem exitPoolTokenExecution_refines
    {ratioRaw : ℤ} {input : ExitPoolTokenInput}
    {result : ExitPoolTokenExecutionResult}
    (hscalar : 0 < input.scalar) (hscalarUpper : input.scalar ≤ BONE)
    (hexec : exitPoolTokenExecution ratioRaw input = some result) :
    result.input = input ∧
      IsFloor result.productRaw
        ((((input.balance : ℝ) * input.scalar) * (ratioRaw : ℝ)) /
          (BONE : ℝ)) ∧
      IsFloor result.output ((result.productRaw : ℝ) / input.scalar) ∧
      0 < result.output ∧ result.output ≤ input.balance ∧
      result.balanceAfter = input.balance - result.output := by
  rcases exitPoolTokenExecution_success hexec with
    ⟨hinput, htokenBalanceExec, hproductExec, hdownscaledExec, houtputExec,
      houtputPositive, hminimumGuard, hbalanceGuard, hbalanceAfter⟩
  have htokenBalanceEq :=
    proportional_i128_mul_success_eq htokenBalanceExec
  have hproductFloorRaw := (i256_fixed_mul_floor_success_refines
    (by norm_num [BONE]) (by
      norm_num [BONE, SorobanFixedPointMath.I256.maxValue]) hproductExec).1
  have hproductFloor :
      IsFloor result.productRaw
        ((((input.balance : ℝ) * input.scalar) * (ratioRaw : ℝ)) /
          (BONE : ℝ)) := by
    rw [htokenBalanceEq] at hproductFloorRaw
    convert hproductFloorRaw using 1
    push_cast
    ring
  have hscalarMax :
      (input.scalar : ℤ) ≤ SorobanFixedPointMath.I256.maxValue := by
    calc
      (input.scalar : ℤ) ≤ BONE := by exact_mod_cast hscalarUpper
      _ ≤ SorobanFixedPointMath.I256.maxValue := by
        norm_num [BONE, SorobanFixedPointMath.I256.maxValue]
  have hdownscaledFloorRaw := (i256_fixed_div_floor_success_refines
    hscalar hscalarMax hdownscaledExec).1
  have houtputEq : result.output = result.downscaledRaw :=
    (SorobanFixedPointMath.I128.checked_eq_some_iff.mp houtputExec).2.symm
  have houtputFloor :
      IsFloor result.output ((result.productRaw : ℝ) / input.scalar) := by
    rw [houtputEq]
    convert hdownscaledFloorRaw using 1
    push_cast
    ring
  exact ⟨hinput, hproductFloor, houtputFloor, houtputPositive,
    hbalanceGuard, hbalanceAfter⟩

/-- A successful source-shaped token exit cannot pay above its ideal share. -/
theorem exitPoolTokenExecution_cannot_overpay
    {poolSupply poolAmountIn : ℕ} {ratio : ExitPoolRatioExecutionResult}
    {input : ExitPoolTokenInput} {result : ExitPoolTokenExecutionResult}
    (hpoolSupply : 0 < poolSupply)
    (hscalar : 0 < input.scalar) (hscalarUpper : input.scalar ≤ BONE)
    (hratioExec : exitPoolRatioExecution poolSupply poolAmountIn = some ratio)
    (htokenExec : exitPoolTokenExecution ratio.ratioRaw input = some result) :
    (result.output : ℝ) ≤
      proportionalAmount input.balance poolAmountIn poolSupply := by
  have hratio := exitPoolRatioExecution_refines
    hpoolSupply hratioExec
  have htoken := exitPoolTokenExecution_refines
    hscalar hscalarUpper htokenExec
  exact exit_pool_per_token_cannot_overpay
    (poolSupply := poolSupply) (poolAmountIn := poolAmountIn)
    (tokenBalance := input.balance) (poolScale := (BONE / STROOP : ℕ))
    (tokenScale := input.scalar) (ratioRaw := ratio.ratioRaw)
    (productRaw := result.productRaw) (tokenAmountOut := result.output)
    (by exact_mod_cast hpoolSupply)
    (by norm_num [BONE, STROOP]) (by positivity) (by exact_mod_cast hscalar)
    hratio.2.2 htoken.2.1 htoken.2.2.1

/--
Every token amount in a successful modeled public exit is pool-favoring.
The premise on scalars is exactly the range established by initialization for
token decimal scalars `10^(18 - decimals)` with `decimals ≤ 18`.
-/
theorem exitPoolExecution_every_token_cannot_overpay
    {poolSupply poolAmountIn : ℕ} {inputs : List ExitPoolTokenInput}
    {result : ExitPoolExecutionResult}
    (hpoolSupply : 0 < poolSupply)
    (hscalars : ∀ input ∈ inputs, 0 < input.scalar ∧ input.scalar ≤ BONE)
    (hexec : exitPoolExecution poolSupply poolAmountIn inputs = some result) :
    ∀ tokenResult ∈ result.tokens,
      (tokenResult.output : ℝ) ≤
        proportionalAmount tokenResult.input.balance poolAmountIn poolSupply := by
  have hphases := exitPoolExecution_success hexec
  have heach := exitPoolTokensExecution_each_success hphases.2
  intro tokenResult hmember
  have hsource := heach tokenResult hmember
  have hscalar := hscalars tokenResult.input hsource.1
  exact exitPoolTokenExecution_cannot_overpay
    hpoolSupply hscalar.1 hscalar.2 hphases.1 hsource.2

end CometPool
