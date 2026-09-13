import CometPool.CPow.BaselineFeeBound

namespace CometPool

/-!
Shared second-term, continuation, half-band, and proportional-rounding bounds
consumed by the operation-specific proofs. These theorems remain at the same
abstract continuous-approximation layer as `BaselineFeeBound.lean`.
-/

/-- A practical strict ceiling for augmented half-band later error. -/
noncomputable def HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE : ℝ :=
  4751 / 100000

/-- The augmented half-band finite recurrence rate. -/
noncomputable def HALF_AUGMENTED_LATER_FEE_RATE : ℝ :=
  MIN_FEE_RATE * (47501 / 1000000)

theorem half_augmented_later_adverse_fee_share_value :
    HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE = (4751 : ℝ) / 100000 := by
  rfl

theorem half_augmented_later_fee_rate_value :
    HALF_AUGMENTED_LATER_FEE_RATE = (47501 : ℝ) / 1000000000000 := by
  norm_num [HALF_AUGMENTED_LATER_FEE_RATE, MIN_FEE_RATE, MIN_FEE, STROOP]

theorem half_augmented_later_fee_rate_le_selected_share :
    HALF_AUGMENTED_LATER_FEE_RATE ≤
      HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
  rw [half_augmented_later_fee_rate_value,
    half_augmented_later_adverse_fee_share_value, minimum_fee_rate_value]
  norm_num

/-
The generic geometric estimate discards the division by two in the second
binomial term. Retaining it is what leaves enough margin for above-one paths,
whose configured displacement is close to one half rather than one quarter.
-/

/-- The second fractional-binomial term contracts by at most `q / 2`. -/
theorem fractional_binomial_second_term_contracts
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    |T 2| ≤ |T 1| * (q / 2) := by
  rw [hrec 1]
  have ha : |a - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_div, abs_mul, abs_mul]
  norm_num
  calc
    |T 1| * |a - 1| * |x| / 2 ≤ |T 1| * 1 * q / 2 := by
      gcongr
    _ = |T 1| * (q / 2) := by ring

/-- Every term after the second inherits the sharper second-term factor. -/
theorem fractional_binomial_terms_from_second_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hq0 : 0 ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T (n + 2)| ≤ |T 1| * (q / 2) * q ^ n := by
  apply geometric_term_bound
    (M := fun n ↦ |T (n + 2)|)
    (S := |T 1| * (q / 2))
    (fractional_binomial_second_term_contracts T ha0 ha1 hx hrec)
    hq0
  intro n
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, hrec (n + 2)]
  exact fractional_binomial_step_contracts ha0 ha1 hx (n + 2)

/-- The exact second term retains the fee-relevant `(1 - a)` factor. -/
theorem fractional_binomial_second_term_weighted_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    |T 2| ≤ |T 1| * ((1 - a) * q / 2) := by
  have ht2 : T 2 = T 1 * (a - 1) * x / 2 := by
    have h := hrec 1
    norm_num at h
    exact h
  rw [ht2]
  have hsign : |a - 1| = 1 - a := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rw [abs_div, abs_mul, abs_mul, hsign, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hfactor0 : 0 ≤ |T 1| * (1 - a) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr ha1)
  calc
    |T 1| * (1 - a) * |x| / 2 ≤ |T 1| * (1 - a) * q / 2 := by
      gcongr
    _ = |T 1| * ((1 - a) * q / 2) := by ring

/-- Later terms preserve the exact second term's `(1 - a)` factor. -/
theorem fractional_binomial_terms_from_weighted_second_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hq0 : 0 ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T (n + 2)| ≤ |T 1| * ((1 - a) * q / 2) * q ^ n := by
  apply geometric_term_bound
    (M := fun n ↦ |T (n + 2)|)
    (S := |T 1| * ((1 - a) * q / 2))
    (fractional_binomial_second_term_weighted_bound T ha1 hx hrec)
    hq0
  intro n
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, hrec (n + 2)]
  exact fractional_binomial_step_contracts ha0 ha1 hx (n + 2)

/-- A continued loop exposes the weighted first-term scale paid for by single-sided fees. -/
theorem continued_loop_forces_weighted_first_term_scale
    (T : ℕ → ℝ) {a x previous q : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ q) (hq0 : 0 ≤ q)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      ((1 - a) * |T 1|) * (q / 2) * q ^ (n - 3) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_weighted_second_bound
    T ha0 ha1 hx hq0 hrec (n - 3)
  have hindex : n - 3 + 2 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  have hrearrange :
      |T 1| * ((1 - a) * q / 2) * q ^ (n - 3) =
        ((1 - a) * |T 1|) * (q / 2) * q ^ (n - 3) := by ring
  rw [hrearrange] at hterms
  linarith

/-- Reaching iteration `n ≥ 3` forces the first term above the sharper scale. -/
theorem continued_loop_forces_sharp_first_term_scale
    (T : ℕ → ℝ) {a x previous q : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ q) (hq0 : 0 ≤ q)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      |T 1| * (q / 2) * q ^ (n - 3) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_second_bound
    T ha0 ha1 hx hq0 hrec (n - 3)
  have hindex : n - 3 + 2 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  linarith

/--
At displacement at most one half, the weighted fee also covers the extra
final-term recurrence budget introduced by the below-one round-down path,
which adds its final negative term a second time.
-/
theorem augmented_error_lt_half_later_fee_rate
    {n : ℕ} {weightedFirstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        weightedFirstTerm * ((1 : ℝ) / 2 / 2) * ((1 : ℝ) / 2) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n + (3 * (n : ℝ) - 2) <
      HALF_AUGMENTED_LATER_FEE_RATE * weightedFirstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, HALF_AUGMENTED_LATER_FEE_RATE, MIN_FEE_RATE,
      MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- A positive exact first term is above every threshold exceeded by its floor. -/
theorem positive_floor_above_threshold
    {rounded : ℤ} {exact threshold : ℝ}
    (hfloor : IsFloor rounded exact)
    (hrounded : threshold < (rounded : ℝ)) :
    threshold < exact :=
  lt_of_lt_of_le hrounded hfloor.le

/-- Directed rounding in a proportional join cannot require less than the exact deposit. -/
theorem proportional_join_rounding_is_pool_favoring
    {balance exactRatio roundedRatio roundedDeposit : ℝ}
    (hbalance0 : 0 ≤ balance)
    (hratioUpper : exactRatio ≤ roundedRatio)
    (hdepositUpper : balance * roundedRatio ≤ roundedDeposit) :
    balance * exactRatio ≤ roundedDeposit := by
  calc
    balance * exactRatio ≤ balance * roundedRatio :=
      mul_le_mul_of_nonneg_left hratioUpper hbalance0
    _ ≤ roundedDeposit := hdepositUpper

/-- Directed rounding in a proportional exit cannot return more than the exact withdrawal. -/
theorem proportional_exit_rounding_is_pool_favoring
    {balance exactRatio roundedRatio roundedWithdrawal : ℝ}
    (hbalance0 : 0 ≤ balance)
    (hratioLower : roundedRatio ≤ exactRatio)
    (hwithdrawalLower : roundedWithdrawal ≤ balance * roundedRatio) :
    roundedWithdrawal ≤ balance * exactRatio := by
  calc
    roundedWithdrawal ≤ balance * roundedRatio := hwithdrawalLower
    _ ≤ balance * exactRatio := mul_le_mul_of_nonneg_left hratioLower hbalance0

end CometPool
