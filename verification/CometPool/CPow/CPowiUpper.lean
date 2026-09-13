import CometPool.Math.FixedPoint

namespace CometPool

/-!
A trace relation for the exponentiation-by-squaring control flow in `c_powi`
when every multiplication rounds upward. Values are normalized reals; the
companion ceiling lemma below constructs each step from a raw fixed-point
`IsCeil` refinement.
-/

/-- One loop trace for upper-rounded exponentiation by squaring. -/
inductive UpperCPowiLoop : ℝ → ℝ → ℕ → ℝ → Prop
  | done (z a : ℝ) : UpperCPowiLoop z a 0 z
  | even {z a aNext result : ℝ} {m : ℕ}
      (haNext0 : 0 ≤ aNext)
      (hsquare : a * a ≤ aNext)
      (tail : UpperCPowiLoop z aNext m result) :
      UpperCPowiLoop z a (2 * m) result
  | odd {z a aNext zNext result : ℝ} {m : ℕ}
      (haNext0 : 0 ≤ aNext)
      (hzNext0 : 0 ≤ zNext)
      (hsquare : a * a ≤ aNext)
      (hmultiply : z * aNext ≤ zNext)
      (tail : UpperCPowiLoop zNext aNext m result) :
      UpperCPowiLoop z a (2 * m + 1) result

/-- The exact state represented by an upper-rounded loop trace cannot exceed its result. -/
theorem UpperCPowiLoop.upper_bound
    {z a result : ℝ} {n : ℕ}
    (trace : UpperCPowiLoop z a n result)
    (hz0 : 0 ≤ z) (ha0 : 0 ≤ a) :
    z * (a * a) ^ n ≤ result := by
  induction trace with
  | done z a => simp
  | @even z a aNext result m haNext0 hsquare tail ih =>
      have hsquare0 : 0 ≤ a * a := mul_nonneg ha0 ha0
      have hpow : ((a * a) * (a * a)) ^ m ≤ (aNext * aNext) ^ m := by
        gcongr
      calc
        z * (a * a) ^ (2 * m) =
            z * ((a * a) * (a * a)) ^ m := by
          rw [pow_mul]
          congr 2
          simp [pow_two]
        _ ≤ z * (aNext * aNext) ^ m :=
          mul_le_mul_of_nonneg_left hpow hz0
        _ ≤ result := ih hz0 haNext0
  | @odd z a aNext zNext result m haNext0 hzNext0 hsquare hmultiply tail ih =>
      have hsquare0 : 0 ≤ a * a := mul_nonneg ha0 ha0
      have haNextSquare0 : 0 ≤ aNext * aNext := mul_nonneg haNext0 haNext0
      have hpow : ((a * a) * (a * a)) ^ m ≤ (aNext * aNext) ^ m := by
        gcongr
      have hfactor : (a * a) * ((a * a) * (a * a)) ^ m ≤
          aNext * (aNext * aNext) ^ m := by
        exact mul_le_mul hsquare hpow
          (pow_nonneg (mul_nonneg hsquare0 hsquare0) _) haNext0
      calc
        z * (a * a) ^ (2 * m + 1) =
            z * ((a * a) * ((a * a) * (a * a)) ^ m) := by
          rw [pow_add, pow_mul]
          ring_nf
        _ ≤ z * (aNext * (aNext * aNext) ^ m) :=
          mul_le_mul_of_nonneg_left hfactor hz0
        _ = (z * aNext) * (aNext * aNext) ^ m := by ring
        _ ≤ zNext * (aNext * aNext) ^ m :=
          mul_le_mul_of_nonneg_right hmultiply (pow_nonneg haNextSquare0 _)
        _ ≤ result := ih hzNext0 haNext0

/-- Initialization cases matching `c_powi`'s parity-dependent `z` value. -/
inductive UpperCPowiTrace (base : ℝ) : ℕ → ℝ → Prop
  | even {m : ℕ} {result : ℝ}
      (loop : UpperCPowiLoop 1 base m result) :
      UpperCPowiTrace base (2 * m) result
  | odd {m : ℕ} {result : ℝ}
      (loop : UpperCPowiLoop base base m result) :
      UpperCPowiTrace base (2 * m + 1) result

/-- An upper-rounded `c_powi` trace is no smaller than the exact natural power. -/
theorem UpperCPowiTrace.upper_bound
    {base result : ℝ} {n : ℕ}
    (trace : UpperCPowiTrace base n result) (hbase0 : 0 ≤ base) :
    base ^ n ≤ result := by
  cases trace with
  | @even m result loop =>
      have h := loop.upper_bound (by norm_num) hbase0
      simpa [pow_mul, pow_two] using h
  | @odd m result loop =>
      have h := loop.upper_bound hbase0 hbase0
      have heq : base ^ (2 * m + 1) = base * (base * base) ^ m := by
        rw [pow_add, pow_mul]
        simp [pow_two]
        ring
      rwa [heq]

end CometPool
