import CometCPow.ErrorBudget
import CometCPow.PoolConfig

namespace CometCPow

/-- A sequence whose term magnitudes contract by at most `q` is bounded by `S * q^n`. -/
theorem geometric_term_bound (M : ℕ → ℝ) {S q : ℝ}
    (hM0 : M 0 ≤ S) (hq0 : 0 ≤ q)
    (hstep : ∀ n, M (n + 1) ≤ M n * q) :
    ∀ n, M n ≤ S * q ^ n := by
  intro n
  induction n with
  | zero => simpa using hM0
  | succ n ih =>
      calc
        M (n + 1) ≤ M n * q := hstep n
        _ ≤ (S * q ^ n) * q := mul_le_mul_of_nonneg_right ih hq0
        _ = S * q ^ (n + 1) := by rw [pow_succ]; ring

/-- For a fractional exponent, the absolute binomial coefficient multiplier is at most one. -/
theorem fractional_binomial_factor_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    |a - (n : ℝ)| / ((n : ℝ) + 1) ≤ 1 := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hdenom : 0 < (n : ℝ) + 1 := by positivity
  apply (div_le_one hdenom).2
  rw [abs_le]
  constructor <;> linarith

/-- One exact fractional-binomial recurrence step contracts by at most `q ≥ abs(x)`. -/
theorem fractional_binomial_step_contracts {a x q term : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q) (n : ℕ) :
    |term * (a - (n : ℝ)) * x / ((n : ℝ) + 1)| ≤ |term| * q := by
  have hfactor1 := fractional_binomial_factor_le_one ha0 ha1 n
  have hproduct :
      (|a - (n : ℝ)| / ((n : ℝ) + 1)) * |x| ≤ q := by
    calc
      (|a - (n : ℝ)| / ((n : ℝ) + 1)) * |x| ≤ 1 * q := by
        exact mul_le_mul hfactor1 hx (abs_nonneg x) (by norm_num)
      _ = q := one_mul q
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  calc
    |term| * |a - (n : ℝ)| * |x| / ((n : ℝ) + 1) =
        |term| * ((|a - (n : ℝ)| / ((n : ℝ) + 1)) * |x|) := by ring
    _ ≤ |term| * q := mul_le_mul_of_nonneg_left hproduct (abs_nonneg term)

/-- Exact terms of the fractional binomial recurrence are bounded by `S * q^n`. -/
theorem fractional_binomial_terms_geometric_bound
    (T : ℕ → ℝ) {S a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hT0 : |T 0| ≤ S)
    (hrec : ∀ n, T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T n| ≤ S * q ^ n := by
  apply geometric_term_bound (M := fun n ↦ |T n|) hT0 (le_trans (abs_nonneg x) hx)
  intro n
  rw [hrec n]
  exact fractional_binomial_step_contracts ha0 ha1 hx n

/-- A symmetric exact-term error bound transfers to an absolute computed-term bound. -/
theorem computed_term_abs_lt {exact computed error : ℝ}
    (herror : |exact - computed| < error) :
    |computed| < |exact| + error := by
  calc
    |computed| = |exact + (computed - exact)| := by ring_nf
    _ ≤ |exact| + |computed - exact| := abs_add _ _
    _ = |exact| + |exact - computed| := by rw [abs_sub_comm]
    _ < |exact| + error := by linarith

/-- The numeric margin available at iteration 46 for `|x| ≤ 3/5`. -/
theorem pool_operating_band_numeric_margin :
    (BONE : ℝ) * (3 / 5 : ℝ) ^ 46 + (3 * 46 - 2) < (CPOW_PRECISION : ℝ) := by
  norm_num [BONE, CPOW_PRECISION]

/-- Production's iteration cap includes the operating-band stopping iteration. -/
theorem pool_operating_band_iteration_within_cap : 46 ≤ MAX_CPOW_ITERS := by
  norm_num [MAX_CPOW_ITERS]

/--
For `|x| ≤ 3/5`, the exact geometric term bound and the recurrence error budget
force the computed term below production `CPOW_PRECISION` by iteration 46.
-/
theorem pool_operating_band_converges_by_iteration_46
    (T : ℕ → ℝ) {a x computed : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ 3 / 5)
    (hT0 : |T 0| ≤ (BONE : ℝ))
    (hrec : ∀ n, T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1))
    (herror : |T 46 - computed| < 3 * 46 - 2) :
    |computed| < (CPOW_PRECISION : ℝ) := by
  have hterms := fractional_binomial_terms_geometric_bound
    T ha0 ha1 hx hT0 hrec
  have hexact := hterms 46
  have hcomputed := computed_term_abs_lt herror
  have hmargin := pool_operating_band_numeric_margin
  linarith

/-- Bases in the configured operating envelope satisfy the iteration-46 stopping theorem. -/
theorem pool_operating_base_converges_by_iteration_46
    (T : ℕ → ℝ) {a base computed : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase0 : 1 / 2 ≤ base) (hbase1 : base ≤ 8 / 5)
    (hT0 : |T 0| ≤ (BONE : ℝ))
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * (base - 1) / ((n : ℝ) + 1))
    (herror : |T 46 - computed| < 3 * 46 - 2) :
    |computed| < (CPOW_PRECISION : ℝ) := by
  exact pool_operating_band_converges_by_iteration_46
    T ha0 ha1 (operating_base_implies_abs_x_le_three_fifths hbase0 hbase1)
      hT0 hrec herror

end CometCPow
