import CometPool.CPow.BinomialUpper
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace CometPool

open Set

/-!
The exact-output path has a base above one.  Writing that base as `1 + q`,
the generalized-binomial terms alternate after the positive linear term when
`0 <= a <= 1`.  Consequently every odd Taylor partial is an upper bound for
the exact fractional power.  This is the analytic direction used by the
baseline implementation: an odd stop retains the odd partial, while an even
stop removes its final negative computed term and therefore retains the
preceding odd partial.
-/

/-- Coefficient of the `n`-th derivative of `t |-> (1 + t)^a`. -/
noncomputable def oneAddRpowDerivativeCoefficient (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => oneAddRpowDerivativeCoefficient a n * (a - n)

@[simp]
theorem oneAddRpowDerivativeCoefficient_zero (a : ℝ) :
    oneAddRpowDerivativeCoefficient a 0 = 1 := rfl

@[simp]
theorem oneAddRpowDerivativeCoefficient_succ (a : ℝ) (n : ℕ) :
    oneAddRpowDerivativeCoefficient a (n + 1) =
      oneAddRpowDerivativeCoefficient a n * (a - n) := rfl

/-- The above-one and below-one derivative coefficients differ by `(-1)^n`. -/
theorem oneAddRpowDerivativeCoefficient_eq_sign_mul_oneSub
    (a : ℝ) : ∀ n,
    oneAddRpowDerivativeCoefficient a n =
      (-1 : ℝ) ^ n * oneSubRpowDerivativeCoefficient a n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [oneAddRpowDerivativeCoefficient_succ,
        oneSubRpowDerivativeCoefficient_succ, ih]
      rw [pow_succ]
      ring

/-- Every positive even derivative coefficient is non-positive on `a in [0,1]`. -/
theorem oneAddRpowDerivativeCoefficient_even_nonpos
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    oneAddRpowDerivativeCoefficient a (2 * k + 2) ≤ 0 := by
  rw [oneAddRpowDerivativeCoefficient_eq_sign_mul_oneSub]
  have heven : (-1 : ℝ) ^ (2 * k + 2) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  rw [heven, one_mul]
  exact oneSubRpowDerivativeCoefficient_nonpos ha0 ha1 (2 * k + 2) (by omega)

/-- Every odd derivative coefficient from degree three onward is non-negative. -/
theorem oneAddRpowDerivativeCoefficient_odd_nonneg
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    0 ≤ oneAddRpowDerivativeCoefficient a (2 * k + 3) := by
  rw [oneAddRpowDerivativeCoefficient_eq_sign_mul_oneSub]
  have hodd : (-1 : ℝ) ^ (2 * k + 3) = -1 := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  rw [hodd]
  simpa using neg_nonneg.mpr
    (oneSubRpowDerivativeCoefficient_nonpos ha0 ha1 (2 * k + 3) (by omega))

/-- Formula for every within-set derivative on a non-negative interval. -/
theorem iteratedDerivWithin_one_add_rpow
    {a q : ℝ} (hq0 : 0 < q) : ∀ n t, t ∈ Icc (0 : ℝ) q →
      iteratedDerivWithin n (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q) t =
        oneAddRpowDerivativeCoefficient a n * (1 + t) ^ (a - n) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simp
  | succ n ih =>
      intro t ht
      rw [iteratedDerivWithin_succ]
      have heq : Set.EqOn
          (iteratedDerivWithin n (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q))
          (fun y : ℝ ↦
            oneAddRpowDerivativeCoefficient a n * (1 + y) ^ (a - n))
          (Icc 0 q) := fun y hy ↦ ih y hy
      rw [derivWithin_congr heq (ih t ht)]
      have hpositive : 0 < 1 + t := by linarith [ht.1]
      have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 t := by
        convert (hasDerivAt_const t 1).add (hasDerivAt_id t) using 1
        ring_nf
      have hderiv :=
        (hinner.rpow_const (p := a - n) (Or.inl hpositive.ne')).const_mul
          (oneAddRpowDerivativeCoefficient a n)
      have hunique : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) q) t :=
        (uniqueDiffOn_Icc hq0) t ht
      rw [hderiv.hasDerivWithinAt.derivWithin hunique]
      rw [oneAddRpowDerivativeCoefficient_succ]
      push_cast
      ring_nf

/-- The raw-scale exact generalized-binomial term for an above-one base. -/
noncomputable def exactOutputBinomialTerm (a base : ℝ) (n : ℕ) : ℝ :=
  (BONE : ℝ) *
    (oneAddRpowDerivativeCoefficient a n / (n.factorial : ℝ)) *
      (base - 1) ^ n

@[simp]
theorem exactOutputBinomialTerm_zero (a base : ℝ) :
    exactOutputBinomialTerm a base 0 = BONE := by
  simp [exactOutputBinomialTerm]

/-- The exact terms obey the recurrence implemented by `c_pow_approx`. -/
theorem exactOutputBinomialTerm_succ (a base : ℝ) (n : ℕ) :
    exactOutputBinomialTerm a base (n + 1) =
      exactOutputBinomialTerm a base n * (a - (n : ℝ)) *
        (base - 1) / ((n : ℝ) + 1) := by
  rw [exactOutputBinomialTerm, exactOutputBinomialTerm,
    oneAddRpowDerivativeCoefficient_succ, Nat.factorial_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The positive first term is exactly `BONE * a * (base - 1)`. -/
theorem exactOutputBinomialTerm_one (a base : ℝ) :
  exactOutputBinomialTerm a base 1 =
      (BONE : ℝ) * a * (base - 1) := by
  simp [exactOutputBinomialTerm, oneAddRpowDerivativeCoefficient]

/-- The scaled Taylor polynomial is the finite sum of exact output terms. -/
theorem bone_mul_taylorWithinEval_eq_exactOutputBinomialSum
    {a q : ℝ} (hq0 : 0 < q) (n : ℕ) :
    (BONE : ℝ) *
        taylorWithinEval (fun y : ℝ ↦ (1 + y) ^ a) n (Icc 0 q) 0 q =
      ∑ k ∈ Finset.range (n + 1), exactOutputBinomialTerm a (1 + q) k := by
  rw [taylor_within_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hderiv := iteratedDerivWithin_one_add_rpow (a := a) hq0 k 0
    (show (0 : ℝ) ∈ Icc 0 q by constructor <;> linarith)
  rw [hderiv]
  norm_num
  rw [exactOutputBinomialTerm]
  ring_nf

/-- Every odd above-one generalized-binomial partial upper-bounds the exact power. -/
theorem exact_output_binomial_odd_partial_upper
    {a base : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase1 : 1 < base) (k : ℕ) :
    (BONE : ℝ) * base ^ a ≤
      ∑ j ∈ Finset.range ((2 * k + 1) + 1),
        exactOutputBinomialTerm a base j := by
  let q : ℝ := base - 1
  let n : ℕ := 2 * k + 1
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hnonzero : ∀ y ∈ Icc (0 : ℝ) q, 1 + y ≠ 0 := by
    intro y hy
    have : 0 < 1 + y := by linarith [hy.1]
    exact this.ne'
  have hcont : ContDiffOn ℝ (n + 1)
      (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q) :=
    (contDiff_const.add contDiff_id).contDiffOn.rpow_const_of_ne hnonzero
  have hcontN : ContDiffOn ℝ n
      (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q) :=
    hcont.of_le (by exact_mod_cast Nat.le_succ n)
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin n (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q))
      (Ioo 0 q) :=
    (hcont.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast n.lt_succ_self) (uniqueDiffOn_Icc hq0)).mono
        Ioo_subset_Icc_self
  rcases taylor_mean_remainder_lagrange hq0 hcontN hdiff with
    ⟨point, hpoint, hremainder⟩
  have hremainder' :
      (1 + q) ^ a -
          taylorWithinEval (fun y : ℝ ↦ (1 + y) ^ a) n (Icc 0 q) 0 q =
        iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 + y) ^ a)
            (Icc 0 q) point * q ^ (n + 1) / (n + 1).factorial := by
    simpa using hremainder
  have hderiv := iteratedDerivWithin_one_add_rpow (a := a) hq0 (n + 1) point
    ⟨hpoint.1.le, hpoint.2.le⟩
  have hindex : n + 1 = 2 * (k + 1) := by dsimp [n]; omega
  have hcoeff : oneAddRpowDerivativeCoefficient a (n + 1) ≤ 0 := by
    rw [hindex]
    simpa [Nat.mul_add] using
      oneAddRpowDerivativeCoefficient_even_nonpos ha0 ha1 k
  have hbaseAtPoint : 0 ≤ 1 + point := by linarith [hpoint.1]
  have hderivNonpos :
      iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 + y) ^ a)
          (Icc 0 q) point ≤ 0 := by
    rw [hderiv]
    exact mul_nonpos_of_nonpos_of_nonneg hcoeff (Real.rpow_nonneg hbaseAtPoint _)
  have hqpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq0.le _
  have hfactorial : (0 : ℝ) ≤ (n + 1).factorial := by positivity
  have hremaindernonpos :
      iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 + y) ^ a)
          (Icc 0 q) point * q ^ (n + 1) / (n + 1).factorial ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hderivNonpos hqpow) hfactorial
  have hpowerTaylor :
      (1 + q) ^ a ≤
        taylorWithinEval (fun y : ℝ ↦ (1 + y) ^ a) n (Icc 0 q) 0 q := by
    linarith [hremainder', hremaindernonpos]
  have hscaled := mul_le_mul_of_nonneg_left hpowerTaylor
    (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  rw [bone_mul_taylorWithinEval_eq_exactOutputBinomialSum hq0 n] at hscaled
  simpa [q, n] using hscaled

/-- Every positive even above-one generalized-binomial partial is a lower bound. -/
theorem exact_output_binomial_even_partial_lower
    {a base : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase1 : 1 < base) (k : ℕ) :
    (∑ j ∈ Finset.range ((2 * k + 2) + 1),
        exactOutputBinomialTerm a base j) ≤
      (BONE : ℝ) * base ^ a := by
  let q : ℝ := base - 1
  let n : ℕ := 2 * k + 2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hnonzero : ∀ y ∈ Icc (0 : ℝ) q, 1 + y ≠ 0 := by
    intro y hy
    have : 0 < 1 + y := by linarith [hy.1]
    exact this.ne'
  have hcont : ContDiffOn ℝ (n + 1)
      (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q) :=
    (contDiff_const.add contDiff_id).contDiffOn.rpow_const_of_ne hnonzero
  have hcontN : ContDiffOn ℝ n
      (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q) :=
    hcont.of_le (by exact_mod_cast Nat.le_succ n)
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin n (fun y : ℝ ↦ (1 + y) ^ a) (Icc 0 q))
      (Ioo 0 q) :=
    (hcont.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast n.lt_succ_self) (uniqueDiffOn_Icc hq0)).mono
        Ioo_subset_Icc_self
  rcases taylor_mean_remainder_lagrange hq0 hcontN hdiff with
    ⟨point, hpoint, hremainder⟩
  have hremainder' :
      (1 + q) ^ a -
          taylorWithinEval (fun y : ℝ ↦ (1 + y) ^ a) n (Icc 0 q) 0 q =
        iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 + y) ^ a)
            (Icc 0 q) point * q ^ (n + 1) / (n + 1).factorial := by
    simpa using hremainder
  have hderiv := iteratedDerivWithin_one_add_rpow (a := a) hq0 (n + 1) point
    ⟨hpoint.1.le, hpoint.2.le⟩
  have hindex' : n + 1 = 2 * k + 3 := by omega
  have hcoeff : 0 ≤ oneAddRpowDerivativeCoefficient a (n + 1) := by
    rw [hindex']
    exact oneAddRpowDerivativeCoefficient_odd_nonneg ha0 ha1 k
  have hbaseAtPoint : 0 ≤ 1 + point := by linarith [hpoint.1]
  have hderivNonneg :
      0 ≤ iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 + y) ^ a)
          (Icc 0 q) point := by
    rw [hderiv]
    exact mul_nonneg hcoeff (Real.rpow_nonneg hbaseAtPoint _)
  have hqpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq0.le _
  have hfactorial : (0 : ℝ) ≤ (n + 1).factorial := by positivity
  have hremaindernonneg :
      0 ≤ iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 + y) ^ a)
          (Icc 0 q) point * q ^ (n + 1) / (n + 1).factorial :=
    div_nonneg (mul_nonneg hderivNonneg hqpow) hfactorial
  have hpowerTaylor :
      taylorWithinEval (fun y : ℝ ↦ (1 + y) ^ a) n (Icc 0 q) 0 q ≤
        (1 + q) ^ a := by
    linarith [hremainder', hremaindernonneg]
  have hscaled := mul_le_mul_of_nonneg_left hpowerTaylor
    (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  rw [bone_mul_taylorWithinEval_eq_exactOutputBinomialSum hq0 n] at hscaled
  simpa [q, n] using hscaled

end CometPool
