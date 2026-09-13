import Mathlib

namespace CometPool

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

/--
The raw recurrence inequality implies the implementation's `3k - 2` budget
through any stopping index no larger than the production cap.
-/
theorem recurrence_error_budget_until (S : ℝ) (D : ℕ → ℝ) {N : ℕ}
    (hN50 : N ≤ 50)
    (hS : 148 < S)
    (hbase : D 1 < 1)
    (hrec : ∀ n, 1 ≤ n → n < N →
      D (n + 1) <
        (1 + 1 / (((n + 1 : ℕ) : ℝ) * S)) * D n +
          1 / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) + 1) :
    ∀ n, 1 ≤ n → n ≤ N → D n < 3 * (n : ℝ) - 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hN
      cases n with
      | zero => omega
      | succ m =>
          by_cases hm : m = 0
          · subst m
            norm_num
            exact hbase
          · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
            have hmN : m ≤ N := le_trans (Nat.le_succ m) hN
            have hmltN : m < N := Nat.lt_of_succ_le hN
            have hmlt50 : m < 50 := lt_of_lt_of_le hmltN hN50
            have hi := ih m (Nat.lt_succ_self m) hm1 hmN
            have hmReal : (m : ℝ) < 50 := by exact_mod_cast hmlt50
            have hDmS : D m < S := by nlinarith
            have hk : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_succ hm1
            have hraw := hrec m hm1 hmltN
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

/--
Pointwise `3k - 2` term-error bounds imply the corresponding strict bound on
the accumulated finite sum. This is the bridge from the recurrence induction
to the partial sum consumed by the adverse-error theorem.
-/
theorem partial_sum_error_lt_sum_error_budget
    (exactTerm computedTerm : ℕ → ℝ) {N : ℕ}
    (hN : 1 ≤ N)
    (hterm : ∀ k, 1 ≤ k → k ≤ N →
      |exactTerm k - computedTerm k| < 3 * (k : ℝ) - 2) :
    |(∑ k ∈ Finset.range N, exactTerm (k + 1)) -
        (∑ k ∈ Finset.range N, computedTerm (k + 1))| <
      (3 * (N : ℝ) ^ 2 - N) / 2 := by
  have hrange : (Finset.range N).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    omega
  have hpointwise : ∀ k ∈ Finset.range N,
      |exactTerm (k + 1) - computedTerm (k + 1)| <
        3 * (((k + 1 : ℕ) : ℝ)) - 2 := by
    intro k hk
    apply hterm (k + 1)
    · omega
    · exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
  calc
    |(∑ k ∈ Finset.range N, exactTerm (k + 1)) -
          (∑ k ∈ Finset.range N, computedTerm (k + 1))| =
        |∑ k ∈ Finset.range N,
          (exactTerm (k + 1) - computedTerm (k + 1))| := by
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range N,
          |exactTerm (k + 1) - computedTerm (k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ < ∑ k ∈ Finset.range N,
          (3 * (((k + 1 : ℕ) : ℝ)) - 2) :=
      Finset.sum_lt_sum_of_nonempty hrange hpointwise
    _ = (3 * (N : ℝ) ^ 2 - N) / 2 := sum_error_budget N

/--
The partial-sum budget using only recurrence steps that production executed
before its stopping index.
-/
theorem recurrence_implies_partial_sum_error_budget_until
    (S : ℝ) (exactTerm computedTerm : ℕ → ℝ) {N : ℕ}
    (hN1 : 1 ≤ N) (hN50 : N ≤ 50)
    (hS : 148 < S)
    (hbase : |exactTerm 1 - computedTerm 1| < 1)
    (hrec : ∀ n, 1 ≤ n → n < N →
      |exactTerm (n + 1) - computedTerm (n + 1)| <
        (1 + 1 / (((n + 1 : ℕ) : ℝ) * S)) *
            |exactTerm n - computedTerm n| +
          1 / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) + 1) :
    |(∑ k ∈ Finset.range N, exactTerm (k + 1)) -
        (∑ k ∈ Finset.range N, computedTerm (k + 1))| <
      (3 * (N : ℝ) ^ 2 - N) / 2 := by
  have hterm := recurrence_error_budget_until S
    (fun k ↦ |exactTerm k - computedTerm k|) hN50 hS hbase hrec
  exact partial_sum_error_lt_sum_error_budget exactTerm computedTerm hN1
    (fun k hk1 hkN ↦ hterm k hk1 hkN)

end CometPool
