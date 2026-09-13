import CometPool.Operations.ExactInputSwap
import CometPool.Operations.ExactOutputSwap
import CometPool.Operations.SingleSidedDeposit
import CometPool.Operations.SingleSidedTokenDeposit
import CometPool.Operations.SingleSidedWithdrawal
import CometPool.Operations.SingleSidedTokenWithdrawal
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace CometPool

/-!
Fee-dominance composition for the six public operations whose arithmetic uses
`c_pow`. The existing operation theorems bound adverse approximation error
relative to the exact fee-adjusted formula. This module proves that the exact
fee advantage dominates those budgets, and therefore compares the computed
result directly with the corresponding fee-free ideal.
-/

/-- An adverse fixed-input error dominated by the exact fee advantage cannot
exceed the fee-free ideal output. -/
theorem fixed_input_fee_dominance
    {computed idealWithFee idealWithoutFee budget : ℝ}
    (herror : computed - idealWithFee < budget)
    (hfee : budget ≤ idealWithoutFee - idealWithFee) :
    computed < idealWithoutFee := by
  linarith

/-- An adverse fixed-output error dominated by the exact fee advantage cannot
reduce the required input below its fee-free ideal. -/
theorem fixed_output_fee_dominance
    {computed idealWithFee idealWithoutFee budget : ℝ}
    (herror : idealWithFee - computed < budget)
    (hfee : budget ≤ idealWithFee - idealWithoutFee) :
    idealWithoutFee < computed := by
  linarith

/-- The inverse-power increase over a withdrawal ratio dominates its linear
first-order term. -/
theorem inverse_one_sub_rpow_sub_one_ge_linear
    {exponent ratio : ℝ}
    (hexponent0 : 0 ≤ exponent) (hratio1 : ratio < 1) :
    exponent * ratio ≤ (1 / (1 - ratio)) ^ exponent - 1 := by
  have hbase : 0 < 1 - ratio := by linarith
  have hlog : Real.log (1 - ratio) ≤ -ratio := by
    have := Real.log_le_sub_one_of_pos hbase
    linarith
  have hscaled : exponent * ratio ≤ Real.log (1 - ratio) * (-exponent) := by
    have hmul := mul_le_mul_of_nonpos_right hlog (neg_nonpos.mpr hexponent0)
    nlinarith
  have hexp : Real.exp (exponent * ratio) ≤
      Real.exp (Real.log (1 - ratio) * (-exponent)) :=
    Real.exp_le_exp.mpr hscaled
  have hlinear : 1 + exponent * ratio ≤ Real.exp (exponent * ratio) :=
    by simpa [add_comm] using Real.add_one_le_exp (exponent * ratio)
  have hrpow :
      Real.exp (Real.log (1 - ratio) * (-exponent)) =
        (1 - ratio) ^ (-exponent) := by
    rw [Real.rpow_def_of_pos hbase]
  have hinverse :
      (1 / (1 - ratio)) ^ exponent = (1 - ratio) ^ (-exponent) := by
    rw [one_div, Real.inv_rpow hbase.le, ← Real.rpow_neg hbase.le]
  rw [hinverse]
  linarith [hlinear.trans (hexp.trans_eq hrpow)]

/-- On the exact-input base interval, every positive exponent at most nine has
a secant slope at least `exponent / 18`. -/
theorem bounded_unit_rpow_secant_lower
    {lower upper exponent : ℝ}
    (hlower : 7 / 10 ≤ lower) (horder : lower ≤ upper)
    (hupper : upper ≤ 1)
    (hexponent0 : 0 < exponent) (hexponentUpper : exponent ≤ 9) :
    exponent / 18 * (upper - lower) ≤
      upper ^ exponent - lower ^ exponent := by
  by_cases heq : lower = upper
  · subst upper
    simp
  have hlt : lower < upper := lt_of_le_of_ne horder heq
  have hlower0 : 0 < lower := lt_of_lt_of_le (by norm_num) hlower
  have hupper0 : 0 < upper := lt_of_lt_of_le hlower0 hlt.le
  let f : ℝ → ℝ := fun x ↦ x ^ exponent
  have hdenom : 0 < upper - lower := sub_pos.mpr hlt
  rcases le_total exponent 1 with hexponentOne | hexponentOne
  · have hconcave : ConcaveOn ℝ (Set.Ici 0) f :=
      Real.concaveOn_rpow hexponent0.le hexponentOne
    have hderiv :
        HasDerivAt f (exponent * upper ^ (exponent - 1)) upper := by
      exact Real.hasDerivAt_rpow_const (Or.inl hupper0.ne')
    have hslope := hconcave.le_slope_of_hasDerivAt
      hlower0.le hupper0.le hlt hderiv
    have hfactor : 1 ≤ upper ^ (exponent - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hupper0 hupper (by linarith)
    have hderivLower : exponent / 18 ≤
        exponent * upper ^ (exponent - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hfactor hexponent0.le]
    have hslopeLower : exponent / 18 ≤
        (upper ^ exponent - lower ^ exponent) / (upper - lower) :=
      le_trans hderivLower (by
        simpa [f, slope, div_eq_mul_inv, mul_comm] using hslope)
    exact (le_div_iff₀ hdenom).mp hslopeLower
  · have hconvex : ConvexOn ℝ (Set.Ici 0) f := convexOn_rpow hexponentOne
    have hderiv :
        HasDerivAt f (exponent * lower ^ (exponent - 1)) lower := by
      exact Real.hasDerivAt_rpow_const (Or.inl hlower0.ne')
    have hslope := hconvex.le_slope_of_hasDerivAt
      hlower0.le hupper0.le hlt hderiv
    have hbasePower : (7 / 10 : ℝ) ^ (8 : ℝ) ≤
        lower ^ (exponent - 1) := by
      calc
        (7 / 10 : ℝ) ^ (8 : ℝ) ≤
            (7 / 10 : ℝ) ^ (exponent - 1) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
            (by linarith)
        _ ≤ lower ^ (exponent - 1) :=
          Real.rpow_le_rpow (by norm_num) hlower (by linarith)
    have hnumeric : (1 / 18 : ℝ) ≤ (7 / 10 : ℝ) ^ (8 : ℝ) := by
      norm_num [Real.rpow_natCast]
    have hfactor : (1 / 18 : ℝ) ≤ lower ^ (exponent - 1) :=
      hnumeric.trans hbasePower
    have hderivLower : exponent / 18 ≤
        exponent * lower ^ (exponent - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hfactor hexponent0.le]
    have hslopeLower : exponent / 18 ≤
        (upper ^ exponent - lower ^ exponent) / (upper - lower) :=
      le_trans hderivLower (by
        simpa [f, slope, div_eq_mul_inv, mul_comm] using hslope)
    exact (le_div_iff₀ hdenom).mp hslopeLower

/-- On `[1,2]`, a fractional power has secant slope at least half its
exponent. -/
theorem fractional_rpow_secant_lower_half
    {lower upper exponent : ℝ}
    (hlower : 1 ≤ lower) (horder : lower ≤ upper) (hupper : upper ≤ 2)
    (hexponent0 : 0 ≤ exponent) (hexponent1 : exponent ≤ 1) :
    exponent / 2 * (upper - lower) ≤
      upper ^ exponent - lower ^ exponent := by
  by_cases heq : lower = upper
  · subst upper
    simp
  have hlt : lower < upper := lt_of_le_of_ne horder heq
  have hlower0 : 0 < lower := lt_of_lt_of_le (by norm_num) hlower
  have hupper0 : 0 < upper := lt_of_lt_of_le hlower0 hlt.le
  let f : ℝ → ℝ := fun x ↦ x ^ exponent
  have hconcave : ConcaveOn ℝ (Set.Ici 0) f :=
    Real.concaveOn_rpow hexponent0 hexponent1
  have hderiv :
      HasDerivAt f (exponent * upper ^ (exponent - 1)) upper := by
    exact Real.hasDerivAt_rpow_const (Or.inl hupper0.ne')
  have hslope := hconcave.le_slope_of_hasDerivAt
    hlower0.le hupper0.le hlt hderiv
  have hinverse : (1 / 2 : ℝ) ≤ upper ^ (-1 : ℝ) := by
    calc
      (1 / 2 : ℝ) ≤ 1 / upper := one_div_le_one_div_of_le hupper0 hupper
      _ = upper ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; simp [one_div]
  have hfactorOrder : upper ^ (-1 : ℝ) ≤
      upper ^ (exponent - 1) :=
    Real.rpow_le_rpow_of_exponent_le
      (le_trans (by norm_num) (le_trans hlower horder)) (by linarith)
  have hfactor : (1 / 2 : ℝ) ≤ upper ^ (exponent - 1) :=
    hinverse.trans hfactorOrder
  have hderivLower : exponent / 2 ≤
      exponent * upper ^ (exponent - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hfactor hexponent0]
  have hdenom : 0 < upper - lower := sub_pos.mpr hlt
  have hslopeLower : exponent / 2 ≤
      (upper ^ exponent - lower ^ exponent) / (upper - lower) :=
    le_trans hderivLower (by
      simpa [f, slope, div_eq_mul_inv, mul_comm] using hslope)
  exact (le_div_iff₀ hdenom).mp hslopeLower

/-- For an exact-input swap, the configured fee advantage dominates the
entire certified adverse-error budget. -/
theorem exact_input_fee_advantage_dominates_adverse_budget
    {outputBalance feeRate nominalRatio exponent : ℝ}
    (houtputBalance0 : 0 ≤ outputBalance)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate) (hfeeUpper : feeRate ≤ 1)
    (hnominal0 : 0 ≤ nominalRatio) (hnominalUpper : nominalRatio ≤ 2 / 5)
    (hexponent0 : 0 < exponent) (hexponentUpper : exponent ≤ 9) :
    EXACT_INPUT_ADVERSE_FEE_SHARE *
        exactInputMinimumFeeOutputValue outputBalance exponent nominalRatio ≤
      exactInputIdealOutput outputBalance 0 nominalRatio exponent -
        exactInputIdealOutput
          outputBalance feeRate nominalRatio exponent := by
  have hminimum0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  have hfee0 : 0 ≤ feeRate := le_trans hminimum0 hfeeLower
  have hadjusted0 : 0 ≤ (1 - feeRate) * nominalRatio :=
    mul_nonneg (sub_nonneg.mpr hfeeUpper) hnominal0
  let withoutFeeBase : ℝ := exactInputIdealBase 0 nominalRatio
  let withFeeBase : ℝ := exactInputIdealBase feeRate nominalRatio
  have hwithoutDenom : 0 < 1 + nominalRatio := by linarith
  have hwithDenom : 0 < 1 + (1 - feeRate) * nominalRatio := by linarith
  have hdenomOrder :
      1 + (1 - feeRate) * nominalRatio ≤ 1 + nominalRatio := by
    nlinarith
  have hbaseOrder : withoutFeeBase ≤ withFeeBase := by
    simpa [withoutFeeBase, withFeeBase, exactInputIdealBase] using
      (one_div_le_one_div_of_le hwithDenom hdenomOrder)
  have hwithBaseOne : withFeeBase ≤ 1 := by
    dsimp [withFeeBase, exactInputIdealBase]
    exact (div_le_one hwithDenom).2 (by linarith)
  have hwithoutBaseLower : 7 / 10 ≤ withoutFeeBase := by
    dsimp [withoutFeeBase, exactInputIdealBase]
    simp only [sub_zero, one_mul]
    apply (le_div_iff₀ hwithoutDenom).2
    nlinarith
  have hsecant := bounded_unit_rpow_secant_lower hwithoutBaseLower
    hbaseOrder hwithBaseOne hexponent0 hexponentUpper
  have hdenomProduct0 :
      0 < (1 + (1 - feeRate) * nominalRatio) * (1 + nominalRatio) :=
    mul_pos hwithDenom hwithoutDenom
  have hdenomProductUpper :
      (1 + (1 - feeRate) * nominalRatio) * (1 + nominalRatio) ≤ 2 := by
    have hfirstUpper : 1 + (1 - feeRate) * nominalRatio ≤ 7 / 5 := by
      nlinarith
    have hsecondUpper : 1 + nominalRatio ≤ 7 / 5 := by linarith
    nlinarith [mul_le_mul hfirstUpper hsecondUpper
      hwithoutDenom.le (by norm_num : (0 : ℝ) ≤ 7 / 5)]
  have hbaseDiff : feeRate * nominalRatio / 2 ≤
      withFeeBase - withoutFeeBase := by
    have heq :
        withFeeBase - withoutFeeBase =
          feeRate * nominalRatio /
            ((1 + (1 - feeRate) * nominalRatio) * (1 + nominalRatio)) := by
      dsimp [withFeeBase, withoutFeeBase, exactInputIdealBase]
      field_simp [ne_of_gt hwithDenom, ne_of_gt hwithoutDenom]
      ring
    rw [heq]
    have hnumerator0 : 0 ≤ feeRate * nominalRatio := mul_nonneg hfee0 hnominal0
    exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      hdenomProduct0).2
        (mul_le_mul_of_nonneg_left hdenomProductUpper hnumerator0)
  have hpowerDiff : exponent / 36 * (feeRate * nominalRatio) ≤
      withFeeBase ^ exponent - withoutFeeBase ^ exponent := by
    calc
      exponent / 36 * (feeRate * nominalRatio) =
          exponent / 18 * (feeRate * nominalRatio / 2) := by ring
      _ ≤ exponent / 18 * (withFeeBase - withoutFeeBase) :=
        mul_le_mul_of_nonneg_left hbaseDiff (by positivity)
      _ ≤ withFeeBase ^ exponent - withoutFeeBase ^ exponent := hsecant
  have hshare : EXACT_INPUT_ADVERSE_FEE_SHARE ≤ 1 / 36 := by
    rw [exact_input_adverse_fee_share_value]
    norm_num
  have hrate : EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤ feeRate / 36 := by
    calc
      EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤
          (1 / 36) * MIN_FEE_RATE :=
        mul_le_mul_of_nonneg_right hshare hminimum0
      _ ≤ (1 / 36) * feeRate :=
        mul_le_mul_of_nonneg_left hfeeLower (by norm_num)
      _ = feeRate / 36 := by ring
  have hscale0 : 0 ≤ outputBalance * exponent * nominalRatio := by positivity
  have hbudgetPower :
      EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE *
          (outputBalance * exponent * nominalRatio) ≤
        outputBalance *
          (exponent / 36 * (feeRate * nominalRatio)) := by
    calc
      EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE *
          (outputBalance * exponent * nominalRatio) ≤
        (feeRate / 36) * (outputBalance * exponent * nominalRatio) :=
          mul_le_mul_of_nonneg_right hrate hscale0
      _ = outputBalance *
          (exponent / 36 * (feeRate * nominalRatio)) := by ring
  have hpowerScaled := mul_le_mul_of_nonneg_left hpowerDiff houtputBalance0
  have hdiff :
      exactInputIdealOutput outputBalance 0 nominalRatio exponent -
          exactInputIdealOutput outputBalance feeRate nominalRatio exponent =
        outputBalance *
          (withFeeBase ^ exponent - withoutFeeBase ^ exponent) := by
    dsimp [exactInputIdealOutput, withFeeBase, withoutFeeBase]
    ring
  rw [exactInputMinimumFeeOutputValue, hdiff]
  calc
    EXACT_INPUT_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE * (outputBalance * exponent * nominalRatio)) =
        EXACT_INPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE *
          (outputBalance * exponent * nominalRatio) := by ring
    _ ≤ outputBalance *
          (exponent / 36 * (feeRate * nominalRatio)) := hbudgetPower
    _ ≤ outputBalance *
          (withFeeBase ^ exponent - withoutFeeBase ^ exponent) := hpowerScaled

/-- For an exact-output swap, the configured fee advantage dominates the
entire certified adverse-error budget. -/
theorem exact_output_fee_advantage_dominates_adverse_budget
    {inputBalance feeRate nominalRatio exponent : ℝ}
    (hinputBalance0 : 0 ≤ inputBalance)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate)
    (hfeeUpper : feeRate < 1)
    (hnominal0 : 0 ≤ nominalRatio) (hnominal1 : nominalRatio < 1)
    (hexponent0 : 0 ≤ exponent) :
    EXACT_OUTPUT_ADVERSE_FEE_SHARE *
        exactOutputAdjustedMinimumFeeInputValue
          inputBalance feeRate exponent nominalRatio ≤
      exactOutputIdealInput inputBalance feeRate nominalRatio exponent -
        exactOutputIdealInput inputBalance 0 nominalRatio exponent := by
  have hdenom : 0 < 1 - feeRate := by linarith
  have hlinear := inverse_one_sub_rpow_sub_one_ge_linear
    hexponent0 hnominal1
  let powerDelta : ℝ := exactOutputIdealBase nominalRatio ^ exponent - 1
  have hpowerDelta : inputBalance * exponent * nominalRatio ≤
      inputBalance * powerDelta := by
    calc
      inputBalance * exponent * nominalRatio =
          inputBalance * (exponent * nominalRatio) := by ring
      _ ≤ inputBalance * powerDelta :=
        mul_le_mul_of_nonneg_left
          (by simpa [powerDelta, exactOutputIdealBase] using hlinear)
          hinputBalance0
  have hfee0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  have hshare : 0 ≤ EXACT_OUTPUT_ADVERSE_FEE_SHARE ∧
      EXACT_OUTPUT_ADVERSE_FEE_SHARE ≤ 1 := by
    rw [exact_output_adverse_fee_share_value]
    norm_num
  have hrate : EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤ feeRate := by
    calc
      EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤ 1 * MIN_FEE_RATE :=
        mul_le_mul_of_nonneg_right hshare.2 hfee0
      _ = MIN_FEE_RATE := one_mul _
      _ ≤ feeRate := hfeeLower
  have hlinear0 : 0 ≤ inputBalance * exponent * nominalRatio := by positivity
  have hpower0 : 0 ≤ inputBalance * powerDelta :=
    le_trans hlinear0 hpowerDelta
  have hnumerator :
      (EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * exponent * nominalRatio) ≤
        feeRate * (inputBalance * powerDelta) := by
    calc
      (EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * exponent * nominalRatio) ≤
        feeRate * (inputBalance * exponent * nominalRatio) :=
          mul_le_mul_of_nonneg_right hrate hlinear0
      _ ≤ feeRate * (inputBalance * powerDelta) :=
        mul_le_mul_of_nonneg_left hpowerDelta
          (le_trans hfee0 hfeeLower)
  have hdiff :
      exactOutputIdealInput inputBalance feeRate nominalRatio exponent -
          exactOutputIdealInput inputBalance 0 nominalRatio exponent =
        feeRate * (inputBalance * powerDelta) / (1 - feeRate) := by
    simp only [exactOutputIdealInput, sub_zero, div_one]
    dsimp [powerDelta]
    field_simp [ne_of_gt hdenom]
    ring
  rw [exactOutputAdjustedMinimumFeeInputValue, hdiff]
  calc
    EXACT_OUTPUT_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE * (inputBalance * exponent * nominalRatio) /
            (1 - feeRate)) =
        ((EXACT_OUTPUT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * exponent * nominalRatio)) / (1 - feeRate) := by
      ring
    _ ≤ feeRate * (inputBalance * powerDelta) / (1 - feeRate) :=
      (div_le_div_iff_of_pos_right hdenom).2 hnumerator

/-- For an exact-LP-output single-sided deposit, Bernoulli's inequality makes
the exact weighted fee advantage dominate the certified adverse budget. -/
theorem single_sided_deposit_fee_advantage_dominates_adverse_budget
    {inputBalance weight feeRate nominalRatio : ℝ}
    (hinputBalance0 : 0 ≤ inputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight ≤ 1)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate) (hfeeUpper : feeRate < 1)
    (hnominal0 : 0 ≤ nominalRatio) :
    SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedDepositAdjustedMinimumFeeInputValue
          inputBalance weight feeRate nominalRatio ≤
      singleSidedDepositIdealInput inputBalance weight feeRate nominalRatio -
        singleSidedDepositIdealInput inputBalance weight 0 nominalRatio := by
  have hfee0 : 0 ≤ feeRate := le_trans (by
    rw [minimum_fee_rate_value]
    norm_num) hfeeLower
  have hdenom := single_sided_deposit_fee_denominator_positive
    hweight0.le hweight1 hfee0 hfeeUpper
  have hp : 1 ≤ 1 / weight := (one_le_div hweight0).2 hweight1
  have hbernoulli := one_add_mul_self_le_rpow_one_add
    (p := 1 / weight) (s := nominalRatio) (by linarith) hp
  let powerDelta : ℝ := singleSidedDepositIdealBase nominalRatio ^ (1 / weight) - 1
  have hpowerDelta : (1 / weight) * nominalRatio ≤ powerDelta := by
    simpa [powerDelta, singleSidedDepositIdealBase] using
      (sub_le_sub_right hbernoulli 1)
  have hshare : 0 ≤ SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE ∧
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE ≤ 1 := by
    rw [single_sided_deposit_adverse_fee_share_value]
    norm_num
  have hminimum0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  have hrate :
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤ feeRate := by
    calc
      SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤
          1 * MIN_FEE_RATE := mul_le_mul_of_nonneg_right hshare.2 hminimum0
      _ = MIN_FEE_RATE := one_mul _
      _ ≤ feeRate := hfeeLower
  have hweightComplement0 : 0 ≤ 1 - weight := by linarith
  have hlinear0 : 0 ≤ inputBalance * (1 - weight) * ((1 / weight) * nominalRatio) :=
    by positivity
  have hpower0 : 0 ≤ inputBalance * (1 - weight) * powerDelta := by
    exact le_trans hlinear0
      (mul_le_mul_of_nonneg_left hpowerDelta
        (mul_nonneg hinputBalance0 hweightComplement0))
  have hnumerator :
      (SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * ((1 - weight) / weight) * nominalRatio) ≤
        feeRate * (inputBalance * (1 - weight) * powerDelta) := by
    calc
      (SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * ((1 - weight) / weight) * nominalRatio) =
        (SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * (1 - weight) * ((1 / weight) * nominalRatio)) := by
            ring
      _ ≤ feeRate *
          (inputBalance * (1 - weight) * ((1 / weight) * nominalRatio)) :=
        mul_le_mul_of_nonneg_right hrate hlinear0
      _ ≤ feeRate * (inputBalance * (1 - weight) * powerDelta) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpowerDelta
            (mul_nonneg hinputBalance0 hweightComplement0)) hfee0
  have hdiff :
      singleSidedDepositIdealInput inputBalance weight feeRate nominalRatio -
          singleSidedDepositIdealInput inputBalance weight 0 nominalRatio =
        feeRate * (inputBalance * (1 - weight) * powerDelta) /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) := by
    change
      inputBalance * powerDelta /
            (1 - (1 - weight) * feeRate) -
          inputBalance * powerDelta /
            (1 - (1 - weight) * 0) =
        feeRate * (inputBalance * (1 - weight) * powerDelta) /
          (1 - (1 - weight) * feeRate)
    simp only [mul_zero, sub_zero, div_one]
    rw [singleSidedWithdrawalFeeRate] at hdenom
    field_simp [ne_of_gt hdenom, ne_of_gt hweight0]
    ring
  rw [singleSidedDepositAdjustedMinimumFeeInputValue, hdiff]
  calc
    SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE *
              (inputBalance * ((1 - weight) / weight) * nominalRatio) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate)) =
        ((SINGLE_SIDED_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (inputBalance * ((1 - weight) / weight) * nominalRatio)) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate) := by ring
    _ ≤ feeRate * (inputBalance * (1 - weight) * powerDelta) /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) :=
      (div_le_div_iff_of_pos_right hdenom).2 hnumerator

/-- For an exact-LP-input single-sided withdrawal, the direct fee multiplier
dominates the certified adverse budget throughout the configured reciprocal
weight range. -/
theorem single_sided_withdrawal_fee_advantage_dominates_adverse_budget
    {outputBalance weight feeRate nominalRatio : ℝ}
    (houtputBalance0 : 0 ≤ outputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight ≤ 1)
    (hreciprocalUpper : 1 / weight ≤ 10)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate)
    (hnominal0 : 0 ≤ nominalRatio) (hnominal1 : nominalRatio < 1) :
    SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedWithdrawalMinimumFeeOutputValue
          outputBalance weight nominalRatio ≤
      singleSidedWithdrawalIdealOutput outputBalance weight 0 nominalRatio -
        singleSidedWithdrawalIdealOutput
          outputBalance weight feeRate nominalRatio := by
  have hfee0 : 0 ≤ feeRate := le_trans (by
    rw [minimum_fee_rate_value]
    norm_num) hfeeLower
  have hbase : 0 < 1 - nominalRatio := by linarith
  have hbaseOne : 1 - nominalRatio ≤ 1 := by linarith
  have hp : 1 ≤ 1 / weight := (one_le_div hweight0).2 hweight1
  have hpower : (1 - nominalRatio) ^ (1 / weight) ≤ 1 - nominalRatio := by
    have := Real.rpow_le_rpow_of_exponent_ge hbase hbaseOne hp
    simpa using this
  let outputFraction : ℝ := 1 - (1 - nominalRatio) ^ (1 / weight)
  have hfraction : nominalRatio ≤ outputFraction := by
    dsimp [outputFraction]
    linarith
  have hshareReciprocal :
      SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE * (1 / weight) ≤ 1 := by
    rw [single_sided_withdrawal_adverse_fee_share_value]
    nlinarith
  have hshare0 : 0 ≤ SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE := by
    rw [single_sided_withdrawal_adverse_fee_share_value]
    norm_num
  have hscaledFraction :
      SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
          ((1 - weight) / weight) * nominalRatio ≤
        (1 - weight) * outputFraction := by
    have hsmall :
        SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
            (1 / weight) * nominalRatio ≤ outputFraction := by
      calc
        SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
            (1 / weight) * nominalRatio ≤ 1 * nominalRatio :=
          mul_le_mul_of_nonneg_right hshareReciprocal hnominal0
        _ = nominalRatio := one_mul _
        _ ≤ outputFraction := hfraction
    calc
      SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
          ((1 - weight) / weight) * nominalRatio =
        (1 - weight) *
          (SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
            (1 / weight) * nominalRatio) := by ring
      _ ≤ (1 - weight) * outputFraction :=
        mul_le_mul_of_nonneg_left hsmall (by linarith)
  have hminimum0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  have hbudgetBase0 :
      0 ≤ outputBalance *
        (SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
          ((1 - weight) / weight) * nominalRatio) := by
    exact mul_nonneg houtputBalance0
      (mul_nonneg
        (mul_nonneg hshare0
          (div_nonneg (sub_nonneg.mpr hweight1) hweight0.le)) hnominal0)
  have hscaled :
      MIN_FEE_RATE *
          (outputBalance *
            (SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
              ((1 - weight) / weight) * nominalRatio)) ≤
        feeRate * (outputBalance * ((1 - weight) * outputFraction)) := by
    calc
      MIN_FEE_RATE *
          (outputBalance *
            (SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
              ((1 - weight) / weight) * nominalRatio)) ≤
        feeRate *
          (outputBalance *
            (SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
              ((1 - weight) / weight) * nominalRatio)) :=
        mul_le_mul_of_nonneg_right hfeeLower hbudgetBase0
      _ ≤ feeRate * (outputBalance * ((1 - weight) * outputFraction)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hscaledFraction houtputBalance0) hfee0
  have hdiff :
      singleSidedWithdrawalIdealOutput outputBalance weight 0 nominalRatio -
          singleSidedWithdrawalIdealOutput outputBalance weight feeRate nominalRatio =
        feeRate * (outputBalance * ((1 - weight) * outputFraction)) := by
    simp only [singleSidedWithdrawalIdealOutput,
      singleSidedWithdrawalIdealBase, singleSidedWithdrawalFeeRate,
      mul_zero, sub_zero]
    dsimp [outputFraction]
    ring
  rw [singleSidedWithdrawalMinimumFeeOutputValue, hdiff]
  calc
    SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE *
            (outputBalance * ((1 - weight) / weight) * nominalRatio)) =
        MIN_FEE_RATE *
          (outputBalance *
            (SINGLE_SIDED_WITHDRAWAL_ADVERSE_FEE_SHARE *
              ((1 - weight) / weight) * nominalRatio)) := by ring
    _ ≤ feeRate * (outputBalance * ((1 - weight) * outputFraction)) := hscaled

/-- For an exact-token-input single-sided deposit, concavity on the public
`[1,2]` base interval makes the exact weighted fee advantage dominate the
certified adverse budget. -/
theorem single_sided_token_deposit_fee_advantage_dominates_adverse_budget
    {poolSupply weight feeRate nominalRatio : ℝ}
    (hpoolSupply0 : 0 ≤ poolSupply)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate) (hfeeUpper : feeRate < 1)
    (hnominal0 : 0 ≤ nominalRatio) (hnominalUpper : nominalRatio ≤ 1) :
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
        singleSidedTokenDepositMinimumFeeOutputValue
          poolSupply weight nominalRatio ≤
      singleSidedTokenDepositIdealOutput poolSupply weight 0 nominalRatio -
        singleSidedTokenDepositIdealOutput
          poolSupply weight feeRate nominalRatio := by
  have hminimum0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  have hfee0 : 0 ≤ feeRate := le_trans hminimum0 hfeeLower
  have hmultiplier := single_sided_deposit_fee_denominator_positive
    hweight0 hweight1 hfee0 hfeeUpper
  let withoutFeeBase : ℝ := 1 + nominalRatio
  let withFeeBase : ℝ :=
    1 + (1 - singleSidedWithdrawalFeeRate weight feeRate) * nominalRatio
  have hwithBaseOne : 1 ≤ withFeeBase := by
    dsimp [withFeeBase]
    nlinarith [mul_nonneg hmultiplier.le hnominal0]
  have hbaseOrder : withFeeBase ≤ withoutFeeBase := by
    dsimp [withFeeBase, withoutFeeBase]
    have hfeeProduct0 : 0 ≤ (1 - weight) * feeRate :=
      mul_nonneg (sub_nonneg.mpr hweight1) hfee0
    rw [singleSidedWithdrawalFeeRate]
    nlinarith [mul_le_mul_of_nonneg_right
      (sub_le_self 1 hfeeProduct0) hnominal0]
  have hwithoutBaseUpper : withoutFeeBase ≤ 2 := by
    dsimp [withoutFeeBase]
    linarith
  have hsecant := fractional_rpow_secant_lower_half
    hwithBaseOne hbaseOrder hwithoutBaseUpper hweight0 hweight1
  have hbaseDiff :
      withoutFeeBase - withFeeBase =
        (1 - weight) * feeRate * nominalRatio := by
    dsimp [withoutFeeBase, withFeeBase]
    rw [singleSidedWithdrawalFeeRate]
    ring
  have hshare :
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE ≤ 1 / 2 := by
    rw [single_sided_token_deposit_adverse_fee_share_value]
    norm_num
  have hrate :
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤
        feeRate / 2 := by
    calc
      SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤
          (1 / 2) * MIN_FEE_RATE :=
        mul_le_mul_of_nonneg_right hshare hminimum0
      _ ≤ (1 / 2) * feeRate :=
        mul_le_mul_of_nonneg_left hfeeLower (by norm_num)
      _ = feeRate / 2 := by ring
  have hscale0 : 0 ≤ poolSupply * weight * (1 - weight) * nominalRatio := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hpoolSupply0 hweight0) (sub_nonneg.mpr hweight1))
      hnominal0
  have hbudgetPower :
      (SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (poolSupply * weight * (1 - weight) * nominalRatio) ≤
        poolSupply *
          (weight / 2 * ((1 - weight) * feeRate * nominalRatio)) := by
    calc
      (SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (poolSupply * weight * (1 - weight) * nominalRatio) ≤
        (feeRate / 2) *
          (poolSupply * weight * (1 - weight) * nominalRatio) :=
        mul_le_mul_of_nonneg_right hrate hscale0
      _ = poolSupply *
          (weight / 2 * ((1 - weight) * feeRate * nominalRatio)) := by ring
  have hpower :
      poolSupply *
          (weight / 2 * ((1 - weight) * feeRate * nominalRatio)) ≤
        poolSupply * (withoutFeeBase ^ weight - withFeeBase ^ weight) := by
    rw [← hbaseDiff]
    exact mul_le_mul_of_nonneg_left hsecant hpoolSupply0
  have hdiff :
      singleSidedTokenDepositIdealOutput poolSupply weight 0 nominalRatio -
          singleSidedTokenDepositIdealOutput
            poolSupply weight feeRate nominalRatio =
        poolSupply * (withoutFeeBase ^ weight - withFeeBase ^ weight) := by
    dsimp [singleSidedTokenDepositIdealOutput,
      singleSidedTokenDepositIdealBase, withoutFeeBase, withFeeBase]
    simp only [singleSidedWithdrawalFeeRate, mul_zero, sub_zero, one_mul]
    ring
  rw [singleSidedTokenDepositMinimumFeeOutputValue, hdiff]
  calc
    SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE *
            (poolSupply * weight * (1 - weight) * nominalRatio)) =
        (SINGLE_SIDED_TOKEN_DEPOSIT_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (poolSupply * weight * (1 - weight) * nominalRatio) := by ring
    _ ≤ poolSupply *
          (weight / 2 * ((1 - weight) * feeRate * nominalRatio)) := hbudgetPower
    _ ≤ poolSupply * (withoutFeeBase ^ weight - withFeeBase ^ weight) := hpower

/-- For an exact-token-output single-sided withdrawal, concavity of the direct
weight power makes the exact weighted fee advantage dominate the certified
adverse budget. -/
theorem single_sided_token_withdrawal_fee_advantage_dominates_adverse_budget
    {poolSupply weight feeRate nominalRatio : ℝ}
    (hpoolSupply0 : 0 ≤ poolSupply)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hfeeLower : MIN_FEE_RATE ≤ feeRate) (hfeeUpper : feeRate < 1)
    (hnominal0 : 0 ≤ nominalRatio)
    (hadjusted1 :
      nominalRatio /
        (1 - singleSidedWithdrawalFeeRate weight feeRate) < 1) :
    SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
        singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue
          poolSupply weight feeRate nominalRatio ≤
      singleSidedTokenWithdrawalIdealInput
          poolSupply weight feeRate nominalRatio -
        singleSidedTokenWithdrawalIdealInput
          poolSupply weight 0 nominalRatio := by
  have hminimum0 : 0 ≤ MIN_FEE_RATE := by
    rw [minimum_fee_rate_value]
    norm_num
  have hfee0 : 0 ≤ feeRate := le_trans hminimum0 hfeeLower
  have hdenom := single_sided_deposit_fee_denominator_positive
    hweight0 hweight1 hfee0 hfeeUpper
  have hdenomOne :
      1 - singleSidedWithdrawalFeeRate weight feeRate ≤ 1 := by
    rw [singleSidedWithdrawalFeeRate]
    have : 0 ≤ (1 - weight) * feeRate :=
      mul_nonneg (sub_nonneg.mpr hweight1) hfee0
    linarith
  let adjustedRatio : ℝ :=
    nominalRatio / (1 - singleSidedWithdrawalFeeRate weight feeRate)
  have hratioOrder : nominalRatio ≤ adjustedRatio := by
    dsimp [adjustedRatio]
    exact (le_div_iff₀ hdenom).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hdenomOne hnominal0])
  have hpower := fractional_power_drop_ge_linear hweight0 hweight1
    hnominal0 hratioOrder (by simpa [adjustedRatio] using hadjusted1)
  have hratioDiff :
      adjustedRatio - nominalRatio =
        nominalRatio * (1 - weight) * feeRate /
          (1 - singleSidedWithdrawalFeeRate weight feeRate) := by
    dsimp [adjustedRatio]
    field_simp [ne_of_gt hdenom]
    rw [singleSidedWithdrawalFeeRate]
    ring
  have hshare : 0 ≤ SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE ∧
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE ≤ 1 := by
    rw [single_sided_token_withdrawal_adverse_fee_share_value]
    norm_num
  have hrate :
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤
        feeRate := by
    calc
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE ≤
          1 * MIN_FEE_RATE := mul_le_mul_of_nonneg_right hshare.2 hminimum0
      _ = MIN_FEE_RATE := one_mul _
      _ ≤ feeRate := hfeeLower
  have hscale0 :
      0 ≤ poolSupply * weight * (1 - weight) * nominalRatio := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hpoolSupply0 hweight0) (sub_nonneg.mpr hweight1))
      hnominal0
  have hbudgetToLinear :
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE *
              (poolSupply * weight * (1 - weight) * nominalRatio) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate)) ≤
        poolSupply * weight * (adjustedRatio - nominalRatio) := by
    calc
      SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE *
          (MIN_FEE_RATE *
              (poolSupply * weight * (1 - weight) * nominalRatio) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate)) =
        ((SINGLE_SIDED_TOKEN_WITHDRAWAL_ADVERSE_FEE_SHARE * MIN_FEE_RATE) *
          (poolSupply * weight * (1 - weight) * nominalRatio)) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate) := by ring
      _ ≤ (feeRate *
          (poolSupply * weight * (1 - weight) * nominalRatio)) /
            (1 - singleSidedWithdrawalFeeRate weight feeRate) :=
        (div_le_div_iff_of_pos_right hdenom).2
          (mul_le_mul_of_nonneg_right hrate hscale0)
      _ = poolSupply * weight * (adjustedRatio - nominalRatio) := by
        rw [hratioDiff]
        ring
  have hpowerScaled :
      poolSupply * weight * (adjustedRatio - nominalRatio) ≤
        poolSupply *
          ((1 - nominalRatio) ^ weight - (1 - adjustedRatio) ^ weight) :=
    by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hpower hpoolSupply0)
  have hdiff :
      singleSidedTokenWithdrawalIdealInput
          poolSupply weight feeRate nominalRatio -
        singleSidedTokenWithdrawalIdealInput
          poolSupply weight 0 nominalRatio =
      poolSupply *
        ((1 - nominalRatio) ^ weight - (1 - adjustedRatio) ^ weight) := by
    simp only [singleSidedTokenWithdrawalIdealInput,
      singleSidedTokenWithdrawalIdealBase, singleSidedWithdrawalFeeRate,
      mul_zero, sub_zero, div_one]
    dsimp [adjustedRatio]
    rw [singleSidedWithdrawalFeeRate]
    ring
  rw [singleSidedTokenWithdrawalAdjustedMinimumFeeInputValue, hdiff]
  exact hbudgetToLinear.trans hpowerScaled

end CometPool
