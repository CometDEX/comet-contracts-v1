import CometPool.Operations.SpotPrice
import SorobanFixedPointMath.I128FixedPointImpl

namespace CometPool

/-!
This module connects the operation-level spot-price theorems to an executable
model and successful trace of the positive-denominator `FixedPoint for i128`
calls in `calc_spot_price`. The use of `Int.toNat` models the
already-proved-positive intermediate output denominator in the companion
implementation model.
-/

/--
A successful source-shaped execution of `calc_spot_price`. Each equality
records one production `fixed_div_floor(...).unwrap_optimized()` call in source
order. The trace covers both public getters: `fee = 0` is
`get_spot_price_sans_fee`.
-/
structure SuccessfulSpotPriceRun
    (inBalance : ℤ) (inWeight : ℕ)
    (outBalance : ℤ) (outWeight fee : ℕ) where
  numerRaw : ℤ
  denomRaw : ℤ
  ratioRaw : ℤ
  priceRaw : ℤ
  numerExec :
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      inBalance inWeight (STROOP : ℤ) = some numerRaw
  denomExec :
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      outBalance outWeight (STROOP : ℤ) = some denomRaw
  ratioExec :
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      numerRaw denomRaw.toNat (STROOP : ℤ) = some ratioRaw
  priceExec :
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      ratioRaw (STROOP - fee) (STROOP : ℤ) = some priceRaw

/--
Executable Lean model of the four checked `i128` divisions in the production
`calc_spot_price` function. Returning `none` models a source `unwrap_optimized`
failure; every `some` result therefore represents a successful arithmetic run.
-/
def calcSpotPriceExecution
    (inBalance : ℤ) (inWeight : ℕ)
    (outBalance : ℤ) (outWeight fee : ℕ) : Option ℤ := do
  let numerRaw ←
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      inBalance inWeight (STROOP : ℤ)
  let denomRaw ←
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      outBalance outWeight (STROOP : ℤ)
  let ratioRaw ←
    SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
      numerRaw denomRaw.toNat (STROOP : ℤ)
  SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
    ratioRaw (STROOP - fee) (STROOP : ℤ)

/--
A successful result from the executable model determines all intermediate
values and constructs the source-shaped trace; callers do not supply any
rounding premises or trace fields.
-/
theorem successfulSpotPriceRun_of_execution
    {inBalance outBalance priceRaw : ℤ}
    {inWeight outWeight fee : ℕ}
    (hexec :
      calcSpotPriceExecution
        inBalance inWeight outBalance outWeight fee = some priceRaw) :
    ∃ run : SuccessfulSpotPriceRun
        inBalance inWeight outBalance outWeight fee,
      run.priceRaw = priceRaw := by
  simp [calcSpotPriceExecution, Option.bind_eq_some_iff] at hexec
  rcases hexec with
    ⟨numerRaw, hnumerExec, denomRaw, hdenomExec,
      ratioRaw, hratioExec, hpriceExec⟩
  exact ⟨{
    numerRaw := numerRaw
    denomRaw := denomRaw
    ratioRaw := ratioRaw
    priceRaw := priceRaw
    numerExec := hnumerExec
    denomExec := hdenomExec
    ratioExec := hratioExec
    priceExec := hpriceExec
  }, rfl⟩

/--
Success of the companion execution model recovers both exact floor semantics
and the fact that the returned value is representable as `i128`.
-/
theorem i128_fixed_div_floor_success_refines
    {x denominator result : ℤ} {y : ℕ}
    (hy : 0 < y)
    (hymax : (y : ℤ) ≤ SorobanFixedPointMath.I128.maxValue)
    (hexec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
        x y denominator = some result) :
    IsFloor result ((((x * denominator : ℤ) : ℝ) / (y : ℝ))) ∧
      SorobanFixedPointMath.I128.InRange result := by
  have hprod : SorobanFixedPointMath.I128.InRange (x * denominator) := by
    by_contra hprod
    have hnone :
        SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
          x y denominator = none := by
      simpa [SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor] using
        (SorobanFixedPointMath.I128FixedPointImpl.mulDivFloor_eq_none_of_product_out_of_range
            (x := x) (y := denominator) (d := y) hprod)
    rw [hexec] at hnone
    cases hnone
  have hvalueExec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
          x y denominator =
        some (SorobanFixedPointMath.I128FixedPointImpl.mulDivFloorValue
          x denominator y) := by
    simpa [SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor] using
      (SorobanFixedPointMath.I128FixedPointImpl.mulDivFloor_eq_some
        (x := x) (y := denominator) (d := y) hprod hy hymax)
  have hresult :
      result = SorobanFixedPointMath.I128FixedPointImpl.mulDivFloorValue
        x denominator y :=
    Option.some.inj (hexec.symm.trans hvalueExec)
  rw [hresult]
  exact ⟨
    SorobanFixedPointMath.FixedPointImpl.mulDivFloorValue_isFloor
      x denominator hy,
    SorobanFixedPointMath.I128FixedPointImpl.mulDivFloorValue_inRange
      hprod hy⟩

private theorem nat_cast_le_i128_max_of_le_stroop
    {value : ℕ} (hvalue : value ≤ STROOP) :
    (value : ℤ) ≤ SorobanFixedPointMath.I128.maxValue := by
  calc
    (value : ℤ) ≤ (STROOP : ℤ) := by exact_mod_cast hvalue
    _ ≤ SorobanFixedPointMath.I128.maxValue := by
      norm_num [STROOP, SorobanFixedPointMath.I128.maxValue]

/--
Every successful source-shaped spot-price run supplies the four exact floor
refinements consumed by the operation-level proof.
-/
theorem SuccessfulSpotPriceRun.refinements
    {inBalance outBalance : ℤ} {inWeight outWeight fee : ℕ}
    (run : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight fee)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfeeUpper : fee < STROOP) :
    IsFloor run.numerRaw
        (weightedBalance (inBalance : ℝ) (inWeight : ℝ)) ∧
      IsFloor run.denomRaw
        (weightedBalance (outBalance : ℝ) (outWeight : ℝ)) ∧
      IsFloor run.ratioRaw
        (((run.numerRaw : ℝ) * (STROOP : ℝ)) /
          (run.denomRaw : ℝ)) ∧
      IsFloor run.priceRaw
        (((run.ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - (fee : ℝ))) := by
  have hnumer := i128_fixed_div_floor_success_refines
    hinWeight0 (nat_cast_le_i128_max_of_le_stroop hinWeightUpper)
      run.numerExec
  have hdenom := i128_fixed_div_floor_success_refines
    houtWeight0 (nat_cast_le_i128_max_of_le_stroop houtWeightUpper)
      run.denomExec
  have hinBalanceReal : (1 : ℝ) ≤ (inBalance : ℝ) := by exact_mod_cast hinBalance
  have houtBalanceReal : (1 : ℝ) ≤ (outBalance : ℝ) := by exact_mod_cast houtBalance
  have hinWeightReal0 : (0 : ℝ) < (inWeight : ℝ) := by exact_mod_cast hinWeight0
  have houtWeightReal0 : (0 : ℝ) < (outWeight : ℝ) := by exact_mod_cast houtWeight0
  have hinWeightRealUpper : (inWeight : ℝ) ≤ (STROOP : ℝ) := by
    exact_mod_cast hinWeightUpper
  have houtWeightRealUpper : (outWeight : ℝ) ≤ (STROOP : ℝ) := by
    exact_mod_cast houtWeightUpper
  have hnumerFloor :
      IsFloor run.numerRaw
        (weightedBalance (inBalance : ℝ) (inWeight : ℝ)) := by
    simpa [weightedBalance] using hnumer.1
  have hdenomFloor :
      IsFloor run.denomRaw
        (weightedBalance (outBalance : ℝ) (outWeight : ℝ)) := by
    simpa [weightedBalance] using hdenom.1
  have hdenomExact := weighted_balance_one_le
    houtBalanceReal houtWeightReal0 houtWeightRealUpper
  have hdenom0 : 0 < run.denomRaw :=
    hdenomFloor.positive_of_one_le_exact hdenomExact
  have hdenomCast : (run.denomRaw.toNat : ℤ) = run.denomRaw :=
    Int.toNat_of_nonneg hdenom0.le
  have hdenomCastReal : (run.denomRaw.toNat : ℝ) = (run.denomRaw : ℝ) := by
    exact_mod_cast hdenomCast
  have hdenomNat0Int : (0 : ℤ) < (run.denomRaw.toNat : ℤ) := by
    rw [hdenomCast]
    exact hdenom0
  have hdenomNat0 : 0 < run.denomRaw.toNat := by
    exact_mod_cast hdenomNat0Int
  have hdenomNatMax :
      (run.denomRaw.toNat : ℤ) ≤
        SorobanFixedPointMath.I128.maxValue := by
    rw [hdenomCast]
    exact hdenom.2.2
  have hratio := i128_fixed_div_floor_success_refines
    hdenomNat0 hdenomNatMax run.ratioExec
  have hratioFloor :
      IsFloor run.ratioRaw
        (((run.numerRaw : ℝ) * (STROOP : ℝ)) /
          (run.denomRaw : ℝ)) := by
    simpa only [Int.cast_mul, Int.cast_natCast, hdenomCastReal] using hratio.1
  have hfeeDiv0 : 0 < STROOP - fee := Nat.sub_pos_of_lt hfeeUpper
  have hfeeDivUpper : STROOP - fee ≤ STROOP := Nat.sub_le _ _
  have hprice := i128_fixed_div_floor_success_refines
    hfeeDiv0 (nat_cast_le_i128_max_of_le_stroop hfeeDivUpper)
      run.priceExec
  have hfeeLe : fee ≤ STROOP := Nat.le_of_lt hfeeUpper
  have hpriceFloor :
      IsFloor run.priceRaw
        (((run.ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - (fee : ℝ))) := by
    simpa [Nat.cast_sub hfeeLe] using hprice.1
  exact ⟨hnumerFloor, hdenomFloor, hratioFloor, hpriceFloor⟩

/--
A successful execution of either public getter satisfies the complete
operation-level spot-price error envelope without taking rounding refinements
as assumptions.
-/
theorem SuccessfulSpotPriceRun.error_bounds
    {inBalance outBalance : ℤ} {inWeight outWeight fee : ℕ}
    (run : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight fee)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfeeUpper : fee < STROOP) :
    idealSpotPrice (inBalance : ℝ) (inWeight : ℝ)
          (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) -
        spotPriceLowerError (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) <
      (run.priceRaw : ℝ) / (STROOP : ℝ) ∧
    (run.priceRaw : ℝ) / (STROOP : ℝ) <
      idealSpotPrice (inBalance : ℝ) (inWeight : ℝ)
          (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) +
        idealSpotPrice (inBalance : ℝ) (inWeight : ℝ)
          (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) /
          (run.denomRaw : ℝ) := by
  have hrefinements := run.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hfeeUpper
  exact get_spot_price_from_fixed_point_refinements
    (by exact_mod_cast hinBalance) (by exact_mod_cast houtBalance)
    (by exact_mod_cast hinWeight0) (by exact_mod_cast houtWeight0)
    (by exact_mod_cast hinWeightUpper) (by exact_mod_cast houtWeightUpper)
    (by exact_mod_cast hfeeUpper) hrefinements.1 hrefinements.2.1
      hrefinements.2.2.1 hrefinements.2.2.2

/--
The end-to-end arithmetic result for a successful modeled `calc_spot_price`
call. The existential `denomRaw` is the concrete second division result that
appears in the sharp upper envelope.
-/
theorem calc_spot_price_execution_error_bounds
    {inBalance outBalance priceRaw : ℤ}
    {inWeight outWeight fee : ℕ}
    (hexec :
      calcSpotPriceExecution
        inBalance inWeight outBalance outWeight fee = some priceRaw)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfeeUpper : fee < STROOP) :
    SorobanFixedPointMath.I128.InRange priceRaw ∧
      ∃ denomRaw : ℤ,
        IsFloor denomRaw
            (weightedBalance (outBalance : ℝ) (outWeight : ℝ)) ∧
          0 < denomRaw ∧
          idealSpotPrice (inBalance : ℝ) (inWeight : ℝ)
                (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) -
              spotPriceLowerError
                (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) <
            (priceRaw : ℝ) / (STROOP : ℝ) ∧
          (priceRaw : ℝ) / (STROOP : ℝ) <
            idealSpotPrice (inBalance : ℝ) (inWeight : ℝ)
                (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) +
              idealSpotPrice (inBalance : ℝ) (inWeight : ℝ)
                (outBalance : ℝ) (outWeight : ℝ) (fee : ℝ) /
                (denomRaw : ℝ) := by
  obtain ⟨run, rfl⟩ := successfulSpotPriceRun_of_execution hexec
  have hrefinements := run.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hfeeUpper
  have hdenomExact := weighted_balance_one_le
    (by exact_mod_cast houtBalance : (1 : ℝ) ≤ (outBalance : ℝ))
    (by exact_mod_cast houtWeight0 : (0 : ℝ) < (outWeight : ℝ))
    (by exact_mod_cast houtWeightUpper :
      (outWeight : ℝ) ≤ (STROOP : ℝ))
  have hdenom0 : 0 < run.denomRaw :=
    hrefinements.2.1.positive_of_one_le_exact hdenomExact
  have hfeeDiv0 : 0 < STROOP - fee := Nat.sub_pos_of_lt hfeeUpper
  have hfeeDivUpper : STROOP - fee ≤ STROOP := Nat.sub_le _ _
  have hpriceRange := (i128_fixed_div_floor_success_refines
    hfeeDiv0 (nat_cast_le_i128_max_of_le_stroop hfeeDivUpper)
      run.priceExec).2
  have hbounds := run.error_bounds hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hfeeUpper
  exact ⟨hpriceRange, run.denomRaw, hrefinements.2.1,
    hdenom0, hbounds.1, hbounds.2⟩

/-- The successful zero-fee getter execution returns the computed raw ratio. -/
theorem SuccessfulSpotPriceRun.sans_fee_returns_ratio
    {inBalance outBalance : ℤ} {inWeight outWeight : ℕ}
    (run : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight 0)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP) :
    run.priceRaw = run.ratioRaw := by
  have hfeeUpper : 0 < STROOP := by norm_num [STROOP]
  have hrefinements := run.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hfeeUpper
  apply get_spot_price_sans_fee_returns_ratio
  simpa using hrefinements.2.2.2

/-- Runs with the same records have identical pre-fee intermediate values. -/
theorem SuccessfulSpotPriceRun.prefix_eq
    {inBalance outBalance : ℤ} {inWeight outWeight lowerFee upperFee : ℕ}
    (lowerRun : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight lowerFee)
    (upperRun : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight upperFee) :
    lowerRun.numerRaw = upperRun.numerRaw ∧
      lowerRun.denomRaw = upperRun.denomRaw ∧
      lowerRun.ratioRaw = upperRun.ratioRaw := by
  have hnumer : lowerRun.numerRaw = upperRun.numerRaw :=
    Option.some.inj (lowerRun.numerExec.symm.trans upperRun.numerExec)
  have hdenom : lowerRun.denomRaw = upperRun.denomRaw :=
    Option.some.inj (lowerRun.denomExec.symm.trans upperRun.denomExec)
  have hupperRatioExec :
      SorobanFixedPointMath.I128FixedPointImpl.fixedDivFloor
          lowerRun.numerRaw lowerRun.denomRaw.toNat (STROOP : ℤ) =
        some upperRun.ratioRaw := by
    simpa [hnumer, hdenom] using upperRun.ratioExec
  have hratio : lowerRun.ratioRaw = upperRun.ratioRaw :=
    Option.some.inj (lowerRun.ratioExec.symm.trans hupperRatioExec)
  exact ⟨hnumer, hdenom, hratio⟩

/-- The shared raw ratio in any active successful run is non-negative. -/
theorem SuccessfulSpotPriceRun.ratio_nonnegative
    {inBalance outBalance : ℤ} {inWeight outWeight fee : ℕ}
    (run : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight fee)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfeeUpper : fee < STROOP) :
    0 ≤ run.ratioRaw := by
  have hrefinements := run.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hfeeUpper
  have hnumerExact := weighted_balance_one_le
    (by exact_mod_cast hinBalance : (1 : ℝ) ≤ (inBalance : ℝ))
    (by exact_mod_cast hinWeight0 : (0 : ℝ) < (inWeight : ℝ))
    (by exact_mod_cast hinWeightUpper : (inWeight : ℝ) ≤ (STROOP : ℝ))
  have hdenomExact := weighted_balance_one_le
    (by exact_mod_cast houtBalance : (1 : ℝ) ≤ (outBalance : ℝ))
    (by exact_mod_cast houtWeight0 : (0 : ℝ) < (outWeight : ℝ))
    (by exact_mod_cast houtWeightUpper : (outWeight : ℝ) ≤ (STROOP : ℝ))
  have hnumer0 : 0 < run.numerRaw :=
    hrefinements.1.positive_of_one_le_exact hnumerExact
  have hdenom0 : 0 < run.denomRaw :=
    hrefinements.2.1.positive_of_one_le_exact hdenomExact
  apply hrefinements.2.2.1.nonnegative_of_nonnegative_exact
  have hnumer0Real : (0 : ℝ) < (run.numerRaw : ℝ) := by exact_mod_cast hnumer0
  have hdenom0Real : (0 : ℝ) < (run.denomRaw : ℝ) := by exact_mod_cast hdenom0
  positivity

/--
The successful fee-adjusted getter cannot return less than a successful
zero-fee getter over the same records.
-/
theorem successful_get_spot_price_not_below_sans_fee
    {inBalance outBalance : ℤ} {inWeight outWeight fee : ℕ}
    (feeRun : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight fee)
    (sansFeeRun : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight 0)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfeeUpper : fee < STROOP) :
    sansFeeRun.priceRaw ≤ feeRun.priceRaw := by
  have hfeeRefinements := feeRun.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hfeeUpper
  have hzeroFeeUpper : 0 < STROOP := by norm_num [STROOP]
  have hsansFeeRefinements := sansFeeRun.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hzeroFeeUpper
  have hprefix := feeRun.prefix_eq sansFeeRun
  have hsansFeePriceFloor :
      IsFloor sansFeeRun.priceRaw
        (((feeRun.ratioRaw : ℝ) * (STROOP : ℝ)) / (STROOP : ℝ)) := by
    rw [hprefix.2.2]
    simpa using hsansFeeRefinements.2.2.2
  exact get_spot_price_not_below_sans_fee
    (by exact_mod_cast hinBalance) (by exact_mod_cast houtBalance)
    (by exact_mod_cast hinWeight0) (by exact_mod_cast houtWeight0)
    (by exact_mod_cast hinWeightUpper) (by exact_mod_cast houtWeightUpper)
    (by positivity) (by exact_mod_cast hfeeUpper)
    hfeeRefinements.1 hfeeRefinements.2.1 hfeeRefinements.2.2.1
      hfeeRefinements.2.2.2 hsansFeePriceFloor

/-- Successful spot-price executions are monotone in their configured fee. -/
theorem successful_spot_price_is_monotone_in_fee
    {inBalance outBalance : ℤ}
    {inWeight outWeight lowerFee upperFee : ℕ}
    (lowerRun : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight lowerFee)
    (upperRun : SuccessfulSpotPriceRun
      inBalance inWeight outBalance outWeight upperFee)
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfees : lowerFee ≤ upperFee)
    (hupperFee : upperFee < STROOP) :
    lowerRun.priceRaw ≤ upperRun.priceRaw := by
  have hlowerFee : lowerFee < STROOP := lt_of_le_of_lt hfees hupperFee
  have hlowerRefinements := lowerRun.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hlowerFee
  have hupperRefinements := upperRun.refinements hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hupperFee
  have hratio0 := lowerRun.ratio_nonnegative hinBalance houtBalance
    hinWeight0 houtWeight0 hinWeightUpper houtWeightUpper hlowerFee
  have hratio := (lowerRun.prefix_eq upperRun).2.2
  have hupperPriceFloor :
      IsFloor upperRun.priceRaw
        (((lowerRun.ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - (upperFee : ℝ))) := by
    rw [hratio]
    exact hupperRefinements.2.2.2
  exact spot_price_is_monotone_in_fee hratio0
    (by exact_mod_cast hfees) (by exact_mod_cast hupperFee)
      hlowerRefinements.2.2.2 hupperPriceFloor

/--
Successful source-shaped executions before and after a swap inherit the
operation-level post-swap spot-price monotonicity theorem.
-/
theorem successful_spot_price_does_not_decrease_after_swap_balance_update
    {beforeInBalance afterInBalance beforeOutBalance afterOutBalance : ℤ}
    {inWeight outWeight fee : ℕ}
    (beforeRun : SuccessfulSpotPriceRun
      beforeInBalance inWeight beforeOutBalance outWeight fee)
    (afterRun : SuccessfulSpotPriceRun
      afterInBalance inWeight afterOutBalance outWeight fee)
    (hbeforeInBalance : 1 ≤ beforeInBalance)
    (hafterOutBalance : 1 ≤ afterOutBalance)
    (hinBalances : beforeInBalance ≤ afterInBalance)
    (houtBalances : afterOutBalance ≤ beforeOutBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ STROOP)
    (houtWeightUpper : outWeight ≤ STROOP)
    (hfeeUpper : fee < STROOP) :
    beforeRun.priceRaw ≤ afterRun.priceRaw := by
  have hafterInBalance : 1 ≤ afterInBalance :=
    hbeforeInBalance.trans hinBalances
  have hbeforeOutBalance : 1 ≤ beforeOutBalance :=
    hafterOutBalance.trans houtBalances
  have hbeforeRefinements := beforeRun.refinements
    hbeforeInBalance hbeforeOutBalance hinWeight0 houtWeight0
      hinWeightUpper houtWeightUpper hfeeUpper
  have hafterRefinements := afterRun.refinements
    hafterInBalance hafterOutBalance hinWeight0 houtWeight0
      hinWeightUpper houtWeightUpper hfeeUpper
  exact spot_price_does_not_decrease_after_swap_balance_update
    (by exact_mod_cast hbeforeInBalance) (by exact_mod_cast hafterOutBalance)
    (by exact_mod_cast hinBalances) (by exact_mod_cast houtBalances)
    (by exact_mod_cast hinWeight0) (by exact_mod_cast houtWeight0)
    (by exact_mod_cast hinWeightUpper) (by exact_mod_cast houtWeightUpper)
    (by exact_mod_cast hfeeUpper)
    hbeforeRefinements.1 hafterRefinements.1
    hbeforeRefinements.2.1 hafterRefinements.2.1
    hbeforeRefinements.2.2.1 hafterRefinements.2.2.1
    hbeforeRefinements.2.2.2 hafterRefinements.2.2.2

end CometPool
