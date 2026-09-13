import CometPool.Math.FixedPoint

namespace CometPool

/-!
Refinement of one baseline `c_pow_approx` term update. The Rust update uses
three mathematical floors: coefficient times base displacement, multiplication
by the preceding term, and division by the term index. This theorem derives
the raw recurrence-error inequality consumed by `recurrence_error_budget_until`.
-/

/-- Three exact floors imply the implementation's one-step error inequality. -/
theorem three_floor_recurrence_step_error
    {S K exactPrevious computedPrevious coefficient displacement : ℝ}
    {coefficientProduct multiplied nextComputed : ℤ}
    (hS : 0 < S) (hK : 0 < K)
    (hcoefficient : |coefficient| ≤ K)
    (hdisplacement : |displacement| ≤ 1)
    (hexactPrevious : |exactPrevious| < S)
    (hcoefficientFloor :
      IsFloor coefficientProduct (S * coefficient * displacement))
    (hmultiplyFloor :
      IsFloor multiplied
        (computedPrevious * (coefficientProduct : ℝ) / S))
    (hdivideFloor :
      IsFloor nextComputed ((multiplied : ℝ) / K)) :
    |exactPrevious * coefficient * displacement / K - (nextComputed : ℝ)| <
      (1 + 1 / (K * S)) * |exactPrevious - computedPrevious| +
        1 / K + 1 / K + 1 := by
  let D : ℝ := |exactPrevious - computedPrevious|
  let coefficientError : ℝ :=
    S * coefficient * displacement - (coefficientProduct : ℝ)
  let multiplyError : ℝ :=
    computedPrevious * (coefficientProduct : ℝ) / S - (multiplied : ℝ)
  let divideError : ℝ := (multiplied : ℝ) / K - (nextComputed : ℝ)
  have hD0 : 0 ≤ D := abs_nonneg _
  have hcoefficientError0 : 0 ≤ coefficientError := by
    dsimp [coefficientError]
    exact sub_nonneg.mpr hcoefficientFloor.le
  have hcoefficientError1 : coefficientError < 1 := by
    dsimp [coefficientError]
    linarith [hcoefficientFloor.lt_add_one]
  have hmultiplyError0 : 0 ≤ multiplyError := by
    dsimp [multiplyError]
    exact sub_nonneg.mpr hmultiplyFloor.le
  have hmultiplyError1 : multiplyError < 1 := by
    dsimp [multiplyError]
    linarith [hmultiplyFloor.lt_add_one]
  have hdivideError0 : 0 ≤ divideError := by
    dsimp [divideError]
    exact sub_nonneg.mpr hdivideFloor.le
  have hdivideError1 : divideError < 1 := by
    dsimp [divideError]
    linarith [hdivideFloor.lt_add_one]
  have hcoefficientDisplacement : |coefficient * displacement| ≤ K := by
    rw [abs_mul]
    calc
      |coefficient| * |displacement| ≤ |coefficient| * 1 :=
        mul_le_mul_of_nonneg_left hdisplacement (abs_nonneg _)
      _ = |coefficient| := mul_one _
      _ ≤ K := hcoefficient
  have hfirstContribution :
      |(exactPrevious - computedPrevious) * coefficient * displacement / K| ≤ D := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hK]
    apply (div_le_iff₀ hK).2
    dsimp [D]
    calc
      |exactPrevious - computedPrevious| * |coefficient| * |displacement| =
          |exactPrevious - computedPrevious| *
            (|coefficient| * |displacement|) := by ring
      _ ≤ |exactPrevious - computedPrevious| * K :=
        mul_le_mul_of_nonneg_left
          (by simpa [abs_mul] using hcoefficientDisplacement) (abs_nonneg _)
  have hcomputedPrevious : |computedPrevious| < S + D := by
    have htriangle : |computedPrevious| ≤
        |exactPrevious| + |exactPrevious - computedPrevious| := by
      calc
        |computedPrevious| =
            |exactPrevious + (computedPrevious - exactPrevious)| := by ring_nf
        _ ≤ |exactPrevious| + |computedPrevious - exactPrevious| := abs_add _ _
        _ = |exactPrevious| + |exactPrevious - computedPrevious| := by
          rw [abs_sub_comm]
    dsimp [D]
    linarith
  have hSK : 0 < S * K := mul_pos hS hK
  have hsecondNumerator : |computedPrevious| * coefficientError < S + D := by
    calc
      |computedPrevious| * coefficientError ≤ |computedPrevious| * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hcoefficientError1) (abs_nonneg _)
      _ = |computedPrevious| := mul_one _
      _ < S + D := hcomputedPrevious
  have hsecondContribution :
      |computedPrevious * coefficientError / (S * K)| <
        1 / K + D / (K * S) := by
    rw [abs_div, abs_mul, abs_of_nonneg hcoefficientError0, abs_of_pos hSK]
    have hdiv : |computedPrevious| * coefficientError / (S * K) <
        (S + D) / (S * K) :=
      (div_lt_div_iff_of_pos_right hSK).2 hsecondNumerator
    calc
      |computedPrevious| * coefficientError / (S * K) <
          (S + D) / (S * K) := hdiv
      _ = S / (S * K) + D / (S * K) := by rw [add_div]
      _ = 1 / K + D / (K * S) := by
        have hcancel : S / (S * K) = 1 / K := by
          field_simp [ne_of_gt hS, ne_of_gt hK]
        rw [hcancel, mul_comm S K]
  have hthirdContribution : |multiplyError / K| < 1 / K := by
    rw [abs_div, abs_of_nonneg hmultiplyError0, abs_of_pos hK]
    exact (div_lt_div_iff_of_pos_right hK).2 hmultiplyError1
  have hfourthContribution : |divideError| < 1 := by
    rw [abs_of_nonneg hdivideError0]
    exact hdivideError1
  have hdecompose :
      exactPrevious * coefficient * displacement / K - (nextComputed : ℝ) =
        (exactPrevious - computedPrevious) * coefficient * displacement / K +
          computedPrevious * coefficientError / (S * K) +
          multiplyError / K + divideError := by
    dsimp [coefficientError, multiplyError, divideError]
    field_simp [ne_of_gt hS, ne_of_gt hK]
    ring
  rw [hdecompose]
  calc
    |(exactPrevious - computedPrevious) * coefficient * displacement / K +
          computedPrevious * coefficientError / (S * K) +
          multiplyError / K + divideError| ≤
        |(exactPrevious - computedPrevious) * coefficient * displacement / K| +
          |computedPrevious * coefficientError / (S * K)| +
          |multiplyError / K| + |divideError| := by
      calc
        |_ + _ + _ + _| ≤ |_ + _ + _| + |divideError| := abs_add _ _
        _ ≤ (|_ + _| + |multiplyError / K|) + |divideError| := by
          gcongr
          exact abs_add _ _
        _ ≤ ((|_| + |_|) + |multiplyError / K|) + |divideError| := by
          gcongr
          exact abs_add _ _
    _ < (1 + 1 / (K * S)) * D + 1 / K + 1 / K + 1 := by
      have htarget :
          (1 + 1 / (K * S)) * D + 1 / K + 1 / K + 1 =
            D + (1 / K + D / (K * S)) + 1 / K + 1 := by ring
      rw [htarget]
      linarith
    _ = (1 + 1 / (K * S)) *
          |exactPrevious - computedPrevious| + 1 / K + 1 / K + 1 := by
      rfl

end CometPool
