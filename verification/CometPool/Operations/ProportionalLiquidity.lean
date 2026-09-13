import CometPool.Operations.OperationFeeBound

namespace CometPool

/-- The continuous per-token amount corresponding to a proportional LP-token change. -/
noncomputable def proportionalAmount
    (tokenBalance poolAmount poolSupply : ℝ) : ℝ :=
  tokenBalance * (poolAmount / poolSupply)

/--
The exact ceiling refinements used by `calc_join_ratio` and
`calc_join_deposit_amount` imply that one successful `join_pool` loop iteration
cannot charge less than the ideal proportional amount for that token.

`poolScale` models `STROOP_SCALAR`; `tokenScale` models the token record's
decimal scalar. The three refinements respectively model the ratio division,
token-balance multiplication, and final token downscale.
-/
theorem join_pool_per_token_cannot_undercharge
    {poolSupply poolAmountOut tokenBalance poolScale tokenScale : ℝ}
    {ratioRaw productRaw tokenAmountIn : ℤ}
    (hpoolSupply : 0 < poolSupply)
    (hpoolScale : 0 < poolScale)
    (htokenBalance : 0 ≤ tokenBalance)
    (htokenScale : 0 < tokenScale)
    (hratioCeil :
      IsCeil ratioRaw
        (((poolAmountOut * poolScale) * (BONE : ℝ)) /
          (poolSupply * poolScale)))
    (hproductCeil :
      IsCeil productRaw
        (((tokenBalance * tokenScale) * (ratioRaw : ℝ)) / (BONE : ℝ)))
    (hdownscaleCeil :
      IsCeil tokenAmountIn ((productRaw : ℝ) / tokenScale)) :
    proportionalAmount tokenBalance poolAmountOut poolSupply ≤
      (tokenAmountIn : ℝ) := by
  have hbone : 0 < (BONE : ℝ) := by norm_num [BONE]
  have hpoolSupplyNe : poolSupply ≠ 0 := ne_of_gt hpoolSupply
  have hpoolScaleNe : poolScale ≠ 0 := ne_of_gt hpoolScale
  have hscaledRatio :
      ((poolAmountOut * poolScale) * (BONE : ℝ)) /
          (poolSupply * poolScale) =
        (poolAmountOut / poolSupply) * (BONE : ℝ) := by
    field_simp
    ring
  have hratioUpper :
      poolAmountOut / poolSupply ≤ (ratioRaw : ℝ) / (BONE : ℝ) := by
    apply (le_div_iff₀ hbone).2
    rw [← hscaledRatio]
    exact hratioCeil.le
  have hproductUpper :
      tokenBalance * ((ratioRaw : ℝ) / (BONE : ℝ)) ≤
        (productRaw : ℝ) / tokenScale := by
    apply (le_div_iff₀ htokenScale).2
    calc
      tokenBalance * ((ratioRaw : ℝ) / (BONE : ℝ)) * tokenScale =
          ((tokenBalance * tokenScale) * (ratioRaw : ℝ)) / (BONE : ℝ) := by
            ring
      _ ≤ (productRaw : ℝ) := hproductCeil.le
  have hdepositUpper :
      tokenBalance * ((ratioRaw : ℝ) / (BONE : ℝ)) ≤
        (tokenAmountIn : ℝ) :=
    hproductUpper.trans hdownscaleCeil.le
  exact proportional_join_rounding_is_pool_favoring
    htokenBalance hratioUpper hdepositUpper

/--
The exact floor refinements used by `calc_exit_ratio` and
`calc_exit_withdrawal_amount` imply that one successful `exit_pool` loop
iteration cannot pay more than the ideal proportional amount for that token.

As for the join theorem, the premises explicitly include both production
upscales and all three directed rounding operations.
-/
theorem exit_pool_per_token_cannot_overpay
    {poolSupply poolAmountIn tokenBalance poolScale tokenScale : ℝ}
    {ratioRaw productRaw tokenAmountOut : ℤ}
    (hpoolSupply : 0 < poolSupply)
    (hpoolScale : 0 < poolScale)
    (htokenBalance : 0 ≤ tokenBalance)
    (htokenScale : 0 < tokenScale)
    (hratioFloor :
      IsFloor ratioRaw
        (((poolAmountIn * poolScale) * (BONE : ℝ)) /
          (poolSupply * poolScale)))
    (hproductFloor :
      IsFloor productRaw
        (((tokenBalance * tokenScale) * (ratioRaw : ℝ)) / (BONE : ℝ)))
    (hdownscaleFloor :
      IsFloor tokenAmountOut ((productRaw : ℝ) / tokenScale)) :
    (tokenAmountOut : ℝ) ≤
      proportionalAmount tokenBalance poolAmountIn poolSupply := by
  have hbone : 0 < (BONE : ℝ) := by norm_num [BONE]
  have hpoolSupplyNe : poolSupply ≠ 0 := ne_of_gt hpoolSupply
  have hpoolScaleNe : poolScale ≠ 0 := ne_of_gt hpoolScale
  have hscaledRatio :
      ((poolAmountIn * poolScale) * (BONE : ℝ)) /
          (poolSupply * poolScale) =
        (poolAmountIn / poolSupply) * (BONE : ℝ) := by
    field_simp
    ring
  have hratioLower :
      (ratioRaw : ℝ) / (BONE : ℝ) ≤ poolAmountIn / poolSupply := by
    apply (div_le_iff₀ hbone).2
    rw [← hscaledRatio]
    exact hratioFloor.le
  have hproductLower :
      (productRaw : ℝ) / tokenScale ≤
        tokenBalance * ((ratioRaw : ℝ) / (BONE : ℝ)) := by
    apply (div_le_iff₀ htokenScale).2
    calc
      (productRaw : ℝ) ≤
          ((tokenBalance * tokenScale) * (ratioRaw : ℝ)) / (BONE : ℝ) :=
        hproductFloor.le
      _ = tokenBalance * ((ratioRaw : ℝ) / (BONE : ℝ)) * tokenScale := by
        ring
  have hwithdrawalLower :
      (tokenAmountOut : ℝ) ≤
        tokenBalance * ((ratioRaw : ℝ) / (BONE : ℝ)) :=
    hdownscaleFloor.le.trans hproductLower
  exact proportional_exit_rounding_is_pool_favoring
    htokenBalance hratioLower hwithdrawalLower

end CometPool
