import CometPool.Math.FixedPoint
import CometPool.Config.Constants

namespace CometPool

/-- The exact balance-per-weight value before the production floor. -/
noncomputable def weightedBalance (balance weight : ℝ) : ℝ :=
  balance * (STROOP : ℝ) / weight

/-- The continuous fee-adjusted spot price, expressed in native price units. -/
noncomputable def idealSpotPrice
    (inBalance inWeight outBalance outWeight fee : ℝ) : ℝ :=
  (weightedBalance inBalance inWeight /
      weightedBalance outBalance outWeight) *
    (STROOP : ℝ) / ((STROOP : ℝ) - fee)

/-- Additive downward-error budget for the three or four production floors. -/
noncomputable def spotPriceLowerError
    (outBalance outWeight fee : ℝ) : ℝ :=
  (STROOP : ℝ) /
      (weightedBalance outBalance outWeight * ((STROOP : ℝ) - fee)) +
    1 / ((STROOP : ℝ) - fee) + 1 / (STROOP : ℝ)

/-- The scaled definition is the usual weighted spot-price formula. -/
theorem ideal_spot_price_eq_weighted_ratio
    {inBalance inWeight outBalance outWeight fee : ℝ}
    (hinWeight0 : 0 < inWeight)
    (houtBalance0 : 0 < outBalance)
    (houtWeight0 : 0 < outWeight)
    (hfeeUpper : fee < (STROOP : ℝ)) :
    idealSpotPrice inBalance inWeight outBalance outWeight fee =
      ((inBalance / inWeight) / (outBalance / outWeight)) /
        (1 - fee / (STROOP : ℝ)) := by
  have hstroopNe : (STROOP : ℝ) ≠ 0 := by norm_num [STROOP]
  have hinWeightNe : inWeight ≠ 0 := ne_of_gt hinWeight0
  have houtBalanceNe : outBalance ≠ 0 := ne_of_gt houtBalance0
  have houtWeightNe : outWeight ≠ 0 := ne_of_gt houtWeight0
  have hfeeDenomNe : (STROOP : ℝ) - fee ≠ 0 := ne_of_gt (sub_pos.mpr hfeeUpper)
  rw [idealSpotPrice, weightedBalance, weightedBalance]
  field_simp
  ring

/-- A native-unit balance and configured weight give a weighted balance of at least one. -/
theorem weighted_balance_one_le
    {balance weight : ℝ}
    (hbalance : 1 ≤ balance)
    (hweight0 : 0 < weight)
    (hweightUpper : weight ≤ (STROOP : ℝ)) :
    1 ≤ weightedBalance balance weight := by
  rw [weightedBalance]
  apply (le_div_iff₀ hweight0).2
  have hstroop0 : 0 < (STROOP : ℝ) := by norm_num [STROOP]
  calc
    1 * weight ≤ 1 * (STROOP : ℝ) := by simpa using hweightUpper
    _ ≤ balance * (STROOP : ℝ) :=
      mul_le_mul_of_nonneg_right hbalance hstroop0.le

/-- At a fixed positive weight, the exact balance-per-weight value is monotone in balance. -/
theorem weighted_balance_mono
    {lowerBalance upperBalance weight : ℝ}
    (hweight0 : 0 < weight)
    (hbalances : lowerBalance ≤ upperBalance) :
    weightedBalance lowerBalance weight ≤
      weightedBalance upperBalance weight := by
  rw [weightedBalance, weightedBalance]
  apply (div_le_div_iff_of_pos_right hweight0).2
  exact mul_le_mul_of_nonneg_right hbalances (by norm_num [STROOP])

/-- A mathematical floor of a value at least one is a positive integer. -/
theorem IsFloor.positive_of_one_le_exact
    {rounded : ℤ} {exact : ℝ}
    (h : IsFloor rounded exact) (hexact : 1 ≤ exact) :
    0 < rounded := by
  have hreal : (0 : ℝ) < (rounded : ℝ) := by
    linarith [h.lt_add_one]
  exact_mod_cast hreal

/-- A mathematical floor of a non-negative value is a non-negative integer. -/
theorem IsFloor.nonnegative_of_nonnegative_exact
    {rounded : ℤ} {exact : ℝ}
    (h : IsFloor rounded exact) (hexact : 0 ≤ exact) :
    0 ≤ rounded := by
  have hreal : (-1 : ℝ) < (rounded : ℝ) := by
    linarith [h.lt_add_one]
  have hint : (-1 : ℤ) < rounded := by
    exact_mod_cast hreal
  omega

/-- Exact floor refinements are monotone when their exact inputs are monotone. -/
theorem floor_refinement_mono
    {lowerRounded upperRounded : ℤ} {lowerExact upperExact : ℝ}
    (hlower : IsFloor lowerRounded lowerExact)
    (hupper : IsFloor upperRounded upperExact)
    (hexact : lowerExact ≤ upperExact) :
    lowerRounded ≤ upperRounded := by
  by_contra hnot
  have hstep : upperRounded + 1 ≤ lowerRounded := by omega
  have hstepReal : (upperRounded : ℝ) + 1 ≤ (lowerRounded : ℝ) := by
    exact_mod_cast hstep
  linarith [hlower.le, hupper.lt_add_one]

/--
The active-pool balance and weight bounds make every divisor in
`calc_spot_price` positive. A fully exited pool is intentionally excluded: its
zero balances do not support a spot price.
-/
theorem get_spot_price_divisors_positive
    {inBalance inWeight outBalance outWeight fee : ℝ}
    {numerRaw denomRaw : ℤ}
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ (STROOP : ℝ))
    (houtWeightUpper : outWeight ≤ (STROOP : ℝ))
    (hfeeUpper : fee < (STROOP : ℝ))
    (hnumerFloor :
      IsFloor numerRaw (weightedBalance inBalance inWeight))
    (hdenomFloor :
      IsFloor denomRaw (weightedBalance outBalance outWeight)) :
    0 < numerRaw ∧ 0 < denomRaw ∧ 0 < (STROOP : ℝ) - fee := by
  have hnumerExact := weighted_balance_one_le
    hinBalance hinWeight0 hinWeightUpper
  have hdenomExact := weighted_balance_one_le
    houtBalance houtWeight0 houtWeightUpper
  exact ⟨hnumerFloor.positive_of_one_le_exact hnumerExact,
    hdenomFloor.positive_of_one_le_exact hdenomExact, sub_pos.mpr hfeeUpper⟩

/--
Complete real-error envelope for the nested floor chain in `calc_spot_price`.

The downward budget accounts for one raw unit from the numerator, ratio, and
final price floors. The strict upward budget is the ideal price divided by the
positive floored output weighted balance; only flooring that denominator can
raise the result above the ideal price.
-/
theorem spot_price_floor_chain_bounds
    {exactNumer exactDenom fee : ℝ}
    {numerRaw denomRaw ratioRaw priceRaw : ℤ}
    (hnumerExact : 1 ≤ exactNumer)
    (hdenomExact : 1 ≤ exactDenom)
    (hfeeUpper : fee < (STROOP : ℝ))
    (hnumerFloor : IsFloor numerRaw exactNumer)
    (hdenomFloor : IsFloor denomRaw exactDenom)
    (hratioFloor :
      IsFloor ratioRaw
        (((numerRaw : ℝ) * (STROOP : ℝ)) / (denomRaw : ℝ)))
    (hpriceFloor :
      IsFloor priceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee))) :
    exactNumer / exactDenom * (STROOP : ℝ) /
          ((STROOP : ℝ) - fee) -
        ((STROOP : ℝ) /
            (exactDenom * ((STROOP : ℝ) - fee)) +
          1 / ((STROOP : ℝ) - fee) + 1 / (STROOP : ℝ)) <
      (priceRaw : ℝ) / (STROOP : ℝ) ∧
    (priceRaw : ℝ) / (STROOP : ℝ) <
      exactNumer / exactDenom * (STROOP : ℝ) /
          ((STROOP : ℝ) - fee) +
        (exactNumer / exactDenom * (STROOP : ℝ) /
          ((STROOP : ℝ) - fee)) / (denomRaw : ℝ) := by
  have hstroop : 0 < (STROOP : ℝ) := by norm_num [STROOP]
  have hfeeDenom : 0 < (STROOP : ℝ) - fee := sub_pos.mpr hfeeUpper
  have hexactDenom0 : 0 < exactDenom := lt_of_lt_of_le zero_lt_one hdenomExact
  have hnumerRaw0 : 0 < numerRaw :=
    hnumerFloor.positive_of_one_le_exact hnumerExact
  have hdenomRaw0 : 0 < denomRaw :=
    hdenomFloor.positive_of_one_le_exact hdenomExact
  have hnumerRaw0Real : 0 < (numerRaw : ℝ) := by exact_mod_cast hnumerRaw0
  have hdenomRaw0Real : 0 < (denomRaw : ℝ) := by exact_mod_cast hdenomRaw0
  have hnumerLower : exactNumer - 1 < (numerRaw : ℝ) := by
    linarith [hnumerFloor.lt_add_one]
  have hnumerMinusOne0 : 0 ≤ exactNumer - 1 := by linarith
  have hdenomMonotone :
      (exactNumer - 1) / exactDenom ≤
        (exactNumer - 1) / (denomRaw : ℝ) :=
    div_le_div_of_nonneg_left hnumerMinusOne0 hdenomRaw0Real hdenomFloor.le
  have hnumerMonotone :
      (exactNumer - 1) / (denomRaw : ℝ) <
        (numerRaw : ℝ) / (denomRaw : ℝ) :=
    (div_lt_div_iff_of_pos_right hdenomRaw0Real).2 hnumerLower
  have hweightedLower :
      (exactNumer - 1) / exactDenom <
        (numerRaw : ℝ) / (denomRaw : ℝ) :=
    hdenomMonotone.trans_lt hnumerMonotone
  have hratioInputLower :
      (STROOP : ℝ) * ((exactNumer - 1) / exactDenom) - 1 <
        (ratioRaw : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_left hweightedLower hstroop
    have hrounded :
        ((numerRaw : ℝ) * (STROOP : ℝ)) / (denomRaw : ℝ) - 1 <
          (ratioRaw : ℝ) := by
      linarith [hratioFloor.lt_add_one]
    calc
      (STROOP : ℝ) * ((exactNumer - 1) / exactDenom) - 1 <
          (STROOP : ℝ) *
              ((numerRaw : ℝ) / (denomRaw : ℝ)) - 1 :=
        sub_lt_sub_right hscaled 1
      _ = ((numerRaw : ℝ) * (STROOP : ℝ)) /
            (denomRaw : ℝ) - 1 := by ring
      _ < (ratioRaw : ℝ) := hrounded
  have hratioAfterFeeLower :
      ((STROOP : ℝ) * ((exactNumer - 1) / exactDenom) - 1) /
          ((STROOP : ℝ) - fee) <
        (ratioRaw : ℝ) / ((STROOP : ℝ) - fee) :=
    (div_lt_div_iff_of_pos_right hfeeDenom).2 hratioInputLower
  have hpriceUnitLower :
      (ratioRaw : ℝ) / ((STROOP : ℝ) - fee) -
          1 / (STROOP : ℝ) <
        (priceRaw : ℝ) / (STROOP : ℝ) := by
    apply (lt_div_iff₀ hstroop).2
    have hrounded :
        ((ratioRaw : ℝ) * (STROOP : ℝ)) /
              ((STROOP : ℝ) - fee) - 1 <
          (priceRaw : ℝ) := by
      linarith [hpriceFloor.lt_add_one]
    calc
      ((ratioRaw : ℝ) / ((STROOP : ℝ) - fee) -
          1 / (STROOP : ℝ)) * (STROOP : ℝ) =
          ((ratioRaw : ℝ) * (STROOP : ℝ)) /
            ((STROOP : ℝ) - fee) - 1 := by
        field_simp
        ring
      _ < (priceRaw : ℝ) := hrounded
  have hlower :
      ((STROOP : ℝ) * ((exactNumer - 1) / exactDenom) - 1) /
            ((STROOP : ℝ) - fee) -
          1 / (STROOP : ℝ) <
        (priceRaw : ℝ) / (STROOP : ℝ) :=
    (sub_lt_sub_right hratioAfterFeeLower (1 / (STROOP : ℝ))).trans
      hpriceUnitLower
  have hpriceUpper :
      (priceRaw : ℝ) / (STROOP : ℝ) ≤
        (ratioRaw : ℝ) / ((STROOP : ℝ) - fee) := by
    apply (div_le_iff₀ hstroop).2
    calc
      (priceRaw : ℝ) ≤
          ((ratioRaw : ℝ) * (STROOP : ℝ)) /
            ((STROOP : ℝ) - fee) := hpriceFloor.le
      _ = ((ratioRaw : ℝ) / ((STROOP : ℝ) - fee)) *
            (STROOP : ℝ) := by ring
  have hratioUpper :
      (ratioRaw : ℝ) ≤
        (STROOP : ℝ) * exactNumer / (denomRaw : ℝ) := by
    calc
      (ratioRaw : ℝ) ≤
          ((numerRaw : ℝ) * (STROOP : ℝ)) / (denomRaw : ℝ) :=
        hratioFloor.le
      _ = (STROOP : ℝ) *
            ((numerRaw : ℝ) / (denomRaw : ℝ)) := by ring
      _ ≤ (STROOP : ℝ) *
            (exactNumer / (denomRaw : ℝ)) :=
        mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right hdenomRaw0Real).2 hnumerFloor.le)
          hstroop.le
      _ = (STROOP : ℝ) * exactNumer / (denomRaw : ℝ) := by ring
  have hcontinuousUpper :
      (priceRaw : ℝ) / (STROOP : ℝ) ≤
        ((STROOP : ℝ) * exactNumer / (denomRaw : ℝ)) /
          ((STROOP : ℝ) - fee) := by
    exact hpriceUpper.trans
      ((div_le_div_iff_of_pos_right hfeeDenom).2 hratioUpper)
  have hdenomFactor :
      exactDenom / (denomRaw : ℝ) <
        1 + 1 / (denomRaw : ℝ) := by
    calc
      exactDenom / (denomRaw : ℝ) <
          ((denomRaw : ℝ) + 1) / (denomRaw : ℝ) :=
        (div_lt_div_iff_of_pos_right hdenomRaw0Real).2
          hdenomFloor.lt_add_one
      _ = 1 + 1 / (denomRaw : ℝ) := by
        field_simp
  have hideal0 :
      0 < exactNumer / exactDenom * (STROOP : ℝ) /
        ((STROOP : ℝ) - fee) := by positivity
  have hfactorUpper := mul_lt_mul_of_pos_left hdenomFactor hideal0
  constructor
  · calc
      exactNumer / exactDenom * (STROOP : ℝ) /
            ((STROOP : ℝ) - fee) -
          ((STROOP : ℝ) /
              (exactDenom * ((STROOP : ℝ) - fee)) +
            1 / ((STROOP : ℝ) - fee) + 1 / (STROOP : ℝ)) =
          ((STROOP : ℝ) * ((exactNumer - 1) / exactDenom) - 1) /
              ((STROOP : ℝ) - fee) -
            1 / (STROOP : ℝ) := by
        field_simp
        ring
      _ < (priceRaw : ℝ) / (STROOP : ℝ) := hlower
  · calc
      (priceRaw : ℝ) / (STROOP : ℝ) ≤
          ((STROOP : ℝ) * exactNumer / (denomRaw : ℝ)) /
            ((STROOP : ℝ) - fee) := hcontinuousUpper
      _ = (exactNumer / exactDenom * (STROOP : ℝ) /
            ((STROOP : ℝ) - fee)) *
          (exactDenom / (denomRaw : ℝ)) := by
        field_simp
        ring
      _ < (exactNumer / exactDenom * (STROOP : ℝ) /
              ((STROOP : ℝ) - fee)) *
            (1 + 1 / (denomRaw : ℝ)) := hfactorUpper
      _ = exactNumer / exactDenom * (STROOP : ℝ) /
            ((STROOP : ℝ) - fee) +
          (exactNumer / exactDenom * (STROOP : ℝ) /
            ((STROOP : ℝ) - fee)) / (denomRaw : ℝ) := by ring

/-- Complete error envelope for a successful call to either public spot-price getter. -/
theorem get_spot_price_from_fixed_point_refinements
    {inBalance inWeight outBalance outWeight fee : ℝ}
    {numerRaw denomRaw ratioRaw priceRaw : ℤ}
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ (STROOP : ℝ))
    (houtWeightUpper : outWeight ≤ (STROOP : ℝ))
    (hfeeUpper : fee < (STROOP : ℝ))
    (hnumerFloor :
      IsFloor numerRaw (weightedBalance inBalance inWeight))
    (hdenomFloor :
      IsFloor denomRaw (weightedBalance outBalance outWeight))
    (hratioFloor :
      IsFloor ratioRaw
        (((numerRaw : ℝ) * (STROOP : ℝ)) / (denomRaw : ℝ)))
    (hpriceFloor :
      IsFloor priceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee))) :
    idealSpotPrice inBalance inWeight outBalance outWeight fee -
        spotPriceLowerError outBalance outWeight fee <
      (priceRaw : ℝ) / (STROOP : ℝ) ∧
    (priceRaw : ℝ) / (STROOP : ℝ) <
      idealSpotPrice inBalance inWeight outBalance outWeight fee +
        idealSpotPrice inBalance inWeight outBalance outWeight fee /
          (denomRaw : ℝ) := by
  have hnumerExact := weighted_balance_one_le
    hinBalance hinWeight0 hinWeightUpper
  have hdenomExact := weighted_balance_one_le
    houtBalance houtWeight0 houtWeightUpper
  simpa [idealSpotPrice, spotPriceLowerError] using
    spot_price_floor_chain_bounds hnumerExact hdenomExact hfeeUpper
      hnumerFloor hdenomFloor hratioFloor hpriceFloor

/-- With zero fee, the production's final floor returns its integer ratio unchanged. -/
theorem get_spot_price_sans_fee_returns_ratio
    {ratioRaw sansFeePriceRaw : ℤ}
    (hpriceFloor :
      IsFloor sansFeePriceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) / (STROOP : ℝ))) :
    sansFeePriceRaw = ratioRaw := by
  have hstroopNe : (STROOP : ℝ) ≠ 0 := by norm_num [STROOP]
  have hexact :
      ((ratioRaw : ℝ) * (STROOP : ℝ)) / (STROOP : ℝ) =
        (ratioRaw : ℝ) := by
    field_simp
  have hleReal : (sansFeePriceRaw : ℝ) ≤ (ratioRaw : ℝ) := by
    rw [← hexact]
    exact hpriceFloor.le
  have hltReal : (ratioRaw : ℝ) < (sansFeePriceRaw : ℝ) + 1 := by
    rw [← hexact]
    exact hpriceFloor.lt_add_one
  have hle : sansFeePriceRaw ≤ ratioRaw := by exact_mod_cast hleReal
  have hlt : ratioRaw < sansFeePriceRaw + 1 := by exact_mod_cast hltReal
  omega

/-- Applying a valid non-negative fee cannot reduce a non-negative raw ratio. -/
theorem fee_adjusted_spot_price_not_below_ratio
    {ratioRaw feePriceRaw : ℤ} {fee : ℝ}
    (hratio0 : 0 ≤ ratioRaw)
    (hfee0 : 0 ≤ fee)
    (hfeeUpper : fee < (STROOP : ℝ))
    (hpriceFloor :
      IsFloor feePriceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee))) :
    ratioRaw ≤ feePriceRaw := by
  have hfeeDenom : 0 < (STROOP : ℝ) - fee := sub_pos.mpr hfeeUpper
  have hratio0Real : 0 ≤ (ratioRaw : ℝ) := by exact_mod_cast hratio0
  have hstroop0 : 0 < (STROOP : ℝ) := by norm_num [STROOP]
  have hratioLeExact :
      (ratioRaw : ℝ) ≤
        ((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee) := by
    apply (le_div_iff₀ hfeeDenom).2
    nlinarith [mul_nonneg hratio0Real hfee0]
  have hltReal : (ratioRaw : ℝ) < (feePriceRaw : ℝ) + 1 :=
    hratioLeExact.trans_lt hpriceFloor.lt_add_one
  have hlt : ratioRaw < feePriceRaw + 1 := by exact_mod_cast hltReal
  omega

/-- The public fee-adjusted getter cannot return less than the fee-free getter. -/
theorem get_spot_price_not_below_sans_fee
    {inBalance inWeight outBalance outWeight fee : ℝ}
    {numerRaw denomRaw ratioRaw feePriceRaw sansFeePriceRaw : ℤ}
    (hinBalance : 1 ≤ inBalance)
    (houtBalance : 1 ≤ outBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ (STROOP : ℝ))
    (houtWeightUpper : outWeight ≤ (STROOP : ℝ))
    (hfee0 : 0 ≤ fee)
    (hfeeUpper : fee < (STROOP : ℝ))
    (hnumerFloor :
      IsFloor numerRaw (weightedBalance inBalance inWeight))
    (hdenomFloor :
      IsFloor denomRaw (weightedBalance outBalance outWeight))
    (hratioFloor :
      IsFloor ratioRaw
        (((numerRaw : ℝ) * (STROOP : ℝ)) / (denomRaw : ℝ)))
    (hfeePriceFloor :
      IsFloor feePriceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee)))
    (hsansFeePriceFloor :
      IsFloor sansFeePriceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) / (STROOP : ℝ))) :
    sansFeePriceRaw ≤ feePriceRaw := by
  have hdivisors := get_spot_price_divisors_positive
    hinBalance houtBalance hinWeight0 houtWeight0 hinWeightUpper
      houtWeightUpper hfeeUpper hnumerFloor hdenomFloor
  have hnumerRaw0Real : 0 ≤ (numerRaw : ℝ) := by
    exact_mod_cast hdivisors.1.le
  have hdenomRaw0Real : 0 < (denomRaw : ℝ) := by
    exact_mod_cast hdivisors.2.1
  have hratioExact0 :
      0 ≤ ((numerRaw : ℝ) * (STROOP : ℝ)) / (denomRaw : ℝ) := by
    positivity
  have hratio0 := hratioFloor.nonnegative_of_nonnegative_exact hratioExact0
  rw [get_spot_price_sans_fee_returns_ratio hsansFeePriceFloor]
  exact fee_adjusted_spot_price_not_below_ratio
    hratio0 hfee0 hfeeUpper hfeePriceFloor

/-- For a fixed non-negative ratio, the returned spot price is monotone in the fee. -/
theorem spot_price_is_monotone_in_fee
    {ratioRaw lowerPriceRaw upperPriceRaw : ℤ} {lowerFee upperFee : ℝ}
    (hratio0 : 0 ≤ ratioRaw)
    (hfees : lowerFee ≤ upperFee)
    (hupperFee : upperFee < (STROOP : ℝ))
    (hlowerFloor :
      IsFloor lowerPriceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - lowerFee)))
    (hupperFloor :
      IsFloor upperPriceRaw
        (((ratioRaw : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - upperFee))) :
    lowerPriceRaw ≤ upperPriceRaw := by
  have hlowerDenom : 0 < (STROOP : ℝ) - lowerFee := by linarith
  have hupperDenom : 0 < (STROOP : ℝ) - upperFee := sub_pos.mpr hupperFee
  have hratio0Real : 0 ≤ (ratioRaw : ℝ) := by exact_mod_cast hratio0
  have hstroop0 : 0 < (STROOP : ℝ) := by norm_num [STROOP]
  have hnumer0 : 0 ≤ (ratioRaw : ℝ) * (STROOP : ℝ) :=
    mul_nonneg hratio0Real hstroop0.le
  apply floor_refinement_mono hlowerFloor hupperFloor
  apply (div_le_div_iff₀ hlowerDenom hupperDenom).2
  exact mul_le_mul_of_nonneg_left (by linarith) hnumer0

/--
Increasing the input balance and decreasing the output balance cannot reduce
the computed spot price. This is the state change made before both swap callers
perform their `spot_price_after >= spot_price_before` check.
-/
theorem spot_price_does_not_decrease_after_swap_balance_update
    {beforeInBalance afterInBalance beforeOutBalance afterOutBalance : ℝ}
    {inWeight outWeight fee : ℝ}
    {beforeNumer afterNumer beforeDenom afterDenom : ℤ}
    {beforeRatio afterRatio beforePrice afterPrice : ℤ}
    (hbeforeInBalance : 1 ≤ beforeInBalance)
    (hafterOutBalance : 1 ≤ afterOutBalance)
    (hinBalances : beforeInBalance ≤ afterInBalance)
    (houtBalances : afterOutBalance ≤ beforeOutBalance)
    (hinWeight0 : 0 < inWeight)
    (houtWeight0 : 0 < outWeight)
    (hinWeightUpper : inWeight ≤ (STROOP : ℝ))
    (houtWeightUpper : outWeight ≤ (STROOP : ℝ))
    (hfeeUpper : fee < (STROOP : ℝ))
    (hbeforeNumerFloor :
      IsFloor beforeNumer (weightedBalance beforeInBalance inWeight))
    (hafterNumerFloor :
      IsFloor afterNumer (weightedBalance afterInBalance inWeight))
    (hbeforeDenomFloor :
      IsFloor beforeDenom (weightedBalance beforeOutBalance outWeight))
    (hafterDenomFloor :
      IsFloor afterDenom (weightedBalance afterOutBalance outWeight))
    (hbeforeRatioFloor :
      IsFloor beforeRatio
        (((beforeNumer : ℝ) * (STROOP : ℝ)) / (beforeDenom : ℝ)))
    (hafterRatioFloor :
      IsFloor afterRatio
        (((afterNumer : ℝ) * (STROOP : ℝ)) / (afterDenom : ℝ)))
    (hbeforePriceFloor :
      IsFloor beforePrice
        (((beforeRatio : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee)))
    (hafterPriceFloor :
      IsFloor afterPrice
        (((afterRatio : ℝ) * (STROOP : ℝ)) /
          ((STROOP : ℝ) - fee))) :
    beforePrice ≤ afterPrice := by
  have hstroop0 : 0 < (STROOP : ℝ) := by norm_num [STROOP]
  have hfeeDenom : 0 < (STROOP : ℝ) - fee := sub_pos.mpr hfeeUpper
  have hafterInBalance : 1 ≤ afterInBalance := hbeforeInBalance.trans hinBalances
  have hbeforeOutBalance : 1 ≤ beforeOutBalance :=
    hafterOutBalance.trans houtBalances
  have hnumerOrder : beforeNumer ≤ afterNumer :=
    floor_refinement_mono hbeforeNumerFloor hafterNumerFloor
      (weighted_balance_mono hinWeight0 hinBalances)
  have hdenomOrder : afterDenom ≤ beforeDenom :=
    floor_refinement_mono hafterDenomFloor hbeforeDenomFloor
      (weighted_balance_mono houtWeight0 houtBalances)
  have hafterNumer0 : 0 ≤ afterNumer :=
    (hafterNumerFloor.positive_of_one_le_exact
      (weighted_balance_one_le hafterInBalance hinWeight0 hinWeightUpper)).le
  have hbeforeDenom0 : 0 < beforeDenom :=
    hbeforeDenomFloor.positive_of_one_le_exact
      (weighted_balance_one_le hbeforeOutBalance houtWeight0 houtWeightUpper)
  have hafterDenom0 : 0 < afterDenom :=
    hafterDenomFloor.positive_of_one_le_exact
      (weighted_balance_one_le hafterOutBalance houtWeight0 houtWeightUpper)
  have hbeforeDenom0Real : 0 < (beforeDenom : ℝ) := by
    exact_mod_cast hbeforeDenom0
  have hafterDenom0Real : 0 < (afterDenom : ℝ) := by
    exact_mod_cast hafterDenom0
  have hnumerOrderReal : (beforeNumer : ℝ) ≤ (afterNumer : ℝ) := by
    exact_mod_cast hnumerOrder
  have hdenomOrderReal : (afterDenom : ℝ) ≤ (beforeDenom : ℝ) := by
    exact_mod_cast hdenomOrder
  have hafterNumer0Real : 0 ≤ (afterNumer : ℝ) := by
    exact_mod_cast hafterNumer0
  have hratioExactOrder :
      ((beforeNumer : ℝ) * (STROOP : ℝ)) / (beforeDenom : ℝ) ≤
        ((afterNumer : ℝ) * (STROOP : ℝ)) / (afterDenom : ℝ) := by
    calc
      ((beforeNumer : ℝ) * (STROOP : ℝ)) / (beforeDenom : ℝ) ≤
          ((afterNumer : ℝ) * (STROOP : ℝ)) / (beforeDenom : ℝ) :=
        (div_le_div_iff_of_pos_right hbeforeDenom0Real).2
          (mul_le_mul_of_nonneg_right hnumerOrderReal hstroop0.le)
      _ ≤ ((afterNumer : ℝ) * (STROOP : ℝ)) / (afterDenom : ℝ) :=
        div_le_div_of_nonneg_left
          (mul_nonneg hafterNumer0Real hstroop0.le)
          hafterDenom0Real hdenomOrderReal
  have hratioOrder : beforeRatio ≤ afterRatio :=
    floor_refinement_mono hbeforeRatioFloor hafterRatioFloor hratioExactOrder
  have hratioOrderReal : (beforeRatio : ℝ) ≤ (afterRatio : ℝ) := by
    exact_mod_cast hratioOrder
  apply floor_refinement_mono hbeforePriceFloor hafterPriceFloor
  apply (div_le_div_iff_of_pos_right hfeeDenom).2
  exact mul_le_mul_of_nonneg_right hratioOrderReal hstroop0.le

end CometPool
