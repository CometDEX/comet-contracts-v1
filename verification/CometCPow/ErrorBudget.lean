import Mathlib

namespace CometCPow

/-- The three new floors in recurrence step `k` add less than three raw units of error. -/
theorem recurrence_increment_lt_three {S D k : ℝ}
    (hS : 0 < S) (hD : D < S) (hk : 2 ≤ k) :
    (1 + 1 / (k * S)) * D + 1 / k + 1 / k + 1 < D + 3 := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkS0 : 0 < k * S := mul_pos hk0 hS
  have hDkS : D < k * S := by
    have hSkS : S ≤ k * S := by nlinarith
    exact lt_of_lt_of_le hD hSkS
  have hfracD : D / (k * S) < 1 := (div_lt_one hkS0).2 hDkS
  have hfracK : 1 / k + 1 / k ≤ 1 := by
    calc
      1 / k + 1 / k = 2 / k := by ring
      _ ≤ 1 := (div_le_one hk0).2 hk
  calc
    (1 + 1 / (k * S)) * D + 1 / k + 1 / k + 1 =
        D + D / (k * S) + (1 / k + 1 / k) + 1 := by ring
    _ < D + 1 + 1 + 1 := by linarith
    _ = D + 3 := by ring

/-- Induction principle used by the implementation's `3k - 2` term-error budget. -/
theorem linear_error_budget (D : ℕ → ℝ)
    (hbase : D 1 < 1)
    (hstep : ∀ n, 1 ≤ n → n < 50 → D (n + 1) < D n + 3) :
    ∀ n, 1 ≤ n → n ≤ 50 → D n < 3 * (n : ℝ) - 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn h50
      cases n with
      | zero => omega
      | succ m =>
          by_cases hm : m = 0
          · subst m
            norm_num
            exact hbase
          · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
            have hm50 : m ≤ 50 := le_trans (Nat.le_succ m) h50
            have hmlt : m < 50 := Nat.lt_of_succ_le h50
            have hi := ih m (Nat.lt_succ_self m) hm1 hm50
            have hs := hstep m hm1 hmlt
            push_cast at hi hs ⊢
            nlinarith

/-- The raw recurrence inequality implies the implementation's `3k - 2` budget. -/
theorem recurrence_error_budget (S : ℝ) (D : ℕ → ℝ)
    (hS : 148 < S)
    (hbase : D 1 < 1)
    (hrec : ∀ n, 1 ≤ n → n < 50 →
      D (n + 1) <
        (1 + 1 / (((n + 1 : ℕ) : ℝ) * S)) * D n +
          1 / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) + 1) :
    ∀ n, 1 ≤ n → n ≤ 50 → D n < 3 * (n : ℝ) - 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn h50
      cases n with
      | zero => omega
      | succ m =>
          by_cases hm : m = 0
          · subst m
            norm_num
            exact hbase
          · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
            have hm50 : m ≤ 50 := le_trans (Nat.le_succ m) h50
            have hmlt : m < 50 := Nat.lt_of_succ_le h50
            have hi := ih m (Nat.lt_succ_self m) hm1 hm50
            have hmReal : (m : ℝ) < 50 := by exact_mod_cast hmlt
            have hDmS : D m < S := by nlinarith
            have hk : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_succ hm1
            have hraw := hrec m hm1 hmlt
            have hincrement := recurrence_increment_lt_three
              (S := S) (D := D m) (k := ((m + 1 : ℕ) : ℝ)) (by nlinarith) hDmS hk
            have hstep : D (m + 1) < D m + 3 := lt_trans hraw hincrement
            push_cast at hi hstep ⊢
            nlinarith

/-- Closed form for the sum of the per-term budgets `3k - 2`, for `k = 1..N`. -/
theorem sum_error_budget (N : ℕ) :
    (∑ k ∈ Finset.range N, (3 * ((k + 1 : ℕ) : ℝ) - 2)) =
      (3 * (N : ℝ) ^ 2 - N) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      simp only [Finset.mem_range, true_and, ih]
      push_cast
      ring

/-- In the common `0 ≤ q ≤ 1/2` case, the geometric-tail factor is in `[0, 1]`. -/
theorem geometric_factor_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    0 ≤ q / (1 - q) ∧ q / (1 - q) ≤ 1 := by
  have hdenom : 0 < 1 - q := by linarith
  constructor
  · positivity
  · exact (div_le_one hdenom).2 (by linarith)

theorem geometric_tail_le_current {term q : ℝ}
    (hterm : 0 ≤ term) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    term * (q / (1 - q)) ≤ term := by
  exact mul_le_of_le_one_right hterm (geometric_factor_bounds hq0 hq).2

end CometCPow
