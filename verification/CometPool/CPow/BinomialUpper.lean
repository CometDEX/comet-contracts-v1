import CometPool.Config.Constants
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace CometPool

open Set

/-!
The generalized binomial series used by `c_pow` is most conveniently related
to real exponentiation through Taylor's theorem. On the exact-input path write
the base as `1 - q`, with `0 < q < 1`, and consider `f(t) = (1 - t)^a`.
For `0 ≤ a ≤ 1`, every derivative after the constant term is non-positive.
The Lagrange remainder is therefore non-positive, so every finite Taylor
partial sum upper-bounds the exact power.
-/

/-- Coefficient of the `n`-th derivative of `t ↦ (1 - t)^a`. -/
noncomputable def oneSubRpowDerivativeCoefficient (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => -oneSubRpowDerivativeCoefficient a n * (a - n)

@[simp]
theorem oneSubRpowDerivativeCoefficient_zero (a : ℝ) :
    oneSubRpowDerivativeCoefficient a 0 = 1 := rfl

@[simp]
theorem oneSubRpowDerivativeCoefficient_succ (a : ℝ) (n : ℕ) :
    oneSubRpowDerivativeCoefficient a (n + 1) =
      -oneSubRpowDerivativeCoefficient a n * (a - n) := rfl

/-- All non-constant derivative coefficients are non-positive for `a ∈ [0,1]`. -/
theorem oneSubRpowDerivativeCoefficient_nonpos
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n, 1 ≤ n → oneSubRpowDerivativeCoefficient a n ≤ 0 := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      intro _
      cases n with
      | zero =>
          simp [oneSubRpowDerivativeCoefficient]
          exact ha0
      | succ n =>
          have hcoeff : oneSubRpowDerivativeCoefficient a (n + 1) ≤ 0 :=
            ih (by omega)
          have hfactor : a - (n + 1 : ℕ) ≤ 0 := by
            push_cast
            linarith
          rw [oneSubRpowDerivativeCoefficient_succ]
          calc
            -oneSubRpowDerivativeCoefficient a (n + 1) * (a - (n + 1 : ℕ)) =
                -(oneSubRpowDerivativeCoefficient a (n + 1) *
                  (a - (n + 1 : ℕ))) := by ring
            _ ≤ 0 := neg_nonpos.mpr
              (mul_nonneg_of_nonpos_of_nonpos hcoeff hfactor)

/-- Formula for every within-set derivative on an interval staying below one. -/
theorem iteratedDerivWithin_one_sub_rpow
    {a q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ n t, t ∈ Icc (0 : ℝ) q →
      iteratedDerivWithin n (fun y : ℝ ↦ (1 - y) ^ a) (Icc 0 q) t =
        oneSubRpowDerivativeCoefficient a n * (1 - t) ^ (a - n) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simp
  | succ n ih =>
      intro t ht
      rw [iteratedDerivWithin_succ]
      have heq : Set.EqOn
          (iteratedDerivWithin n (fun y : ℝ ↦ (1 - y) ^ a) (Icc 0 q))
          (fun y : ℝ ↦
            oneSubRpowDerivativeCoefficient a n * (1 - y) ^ (a - n))
          (Icc 0 q) := fun y hy ↦ ih y hy
      rw [derivWithin_congr heq (ih t ht)]
      have hpositive : 0 < 1 - t := by
        have htq := ht.2
        linarith
      have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) t := by
        convert (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1
        ring_nf
      have hderiv :=
        (hinner.rpow_const (p := a - n) (Or.inl hpositive.ne')).const_mul
          (oneSubRpowDerivativeCoefficient a n)
      have hunique : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) q) t :=
        (uniqueDiffOn_Icc hq0) t ht
      rw [hderiv.hasDerivWithinAt.derivWithin hunique]
      rw [oneSubRpowDerivativeCoefficient_succ]
      push_cast
      ring_nf

/-- The raw-scale exact generalized-binomial term used by the recurrence. -/
noncomputable def exactInputBinomialTerm (a base : ℝ) (n : ℕ) : ℝ :=
  (BONE : ℝ) *
    (oneSubRpowDerivativeCoefficient a n / (n.factorial : ℝ)) *
      (1 - base) ^ n

@[simp]
theorem exactInputBinomialTerm_zero (a base : ℝ) :
    exactInputBinomialTerm a base 0 = BONE := by
  simp [exactInputBinomialTerm]

/-- The Taylor coefficients obey the same exact recurrence as `c_pow`. -/
theorem exactInputBinomialTerm_succ (a base : ℝ) (n : ℕ) :
    exactInputBinomialTerm a base (n + 1) =
      exactInputBinomialTerm a base n * (a - (n : ℝ)) *
        (base - 1) / ((n : ℝ) + 1) := by
  rw [exactInputBinomialTerm, exactInputBinomialTerm,
    oneSubRpowDerivativeCoefficient_succ, Nat.factorial_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The first raw-scale exact term has the expected below-one magnitude. -/
theorem exactInputBinomialTerm_one
    {a base : ℝ} (ha0 : 0 ≤ a) (hbase1 : base ≤ 1) :
    exactInputBinomialTerm a base 1 =
        (BONE : ℝ) * a * (base - 1) ∧
      |exactInputBinomialTerm a base 1| =
        (BONE : ℝ) * a * (1 - base) := by
  have hB : (0 : ℝ) ≤ BONE := by norm_num [BONE]
  have hnonpos : (BONE : ℝ) * a * (base - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB ha0) (sub_nonpos.mpr hbase1)
  have heq : exactInputBinomialTerm a base 1 =
      (BONE : ℝ) * a * (base - 1) := by
    simp [exactInputBinomialTerm, oneSubRpowDerivativeCoefficient]
    ring
  constructor
  · exact heq
  · rw [heq, abs_of_nonpos hnonpos]
    ring

/-- The scaled Taylor polynomial is exactly the finite raw-term sum. -/
theorem bone_mul_taylorWithinEval_eq_exactInputBinomialSum
    {a q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (BONE : ℝ) *
        taylorWithinEval (fun y : ℝ ↦ (1 - y) ^ a) n (Icc 0 q) 0 q =
      ∑ k ∈ Finset.range (n + 1), exactInputBinomialTerm a (1 - q) k := by
  rw [taylor_within_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hderiv := iteratedDerivWithin_one_sub_rpow (a := a) hq0 hq1 k 0
    (show (0 : ℝ) ∈ Icc 0 q by constructor <;> linarith)
  rw [hderiv]
  norm_num
  rw [exactInputBinomialTerm]
  ring_nf

/--
Every finite generalized-binomial partial sum upper-bounds the exact
below-one fractional power. This discharges the analytic tail-direction
premise used by the exact-input error proof.
-/
theorem exact_input_binomial_partial_upper
    {a base : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase0 : 0 < base) (hbase1 : base < 1) (n : ℕ) :
    (BONE : ℝ) * base ^ a ≤
      ∑ k ∈ Finset.range (n + 1), exactInputBinomialTerm a base k := by
  let q : ℝ := 1 - base
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hnonzero : ∀ y ∈ Icc (0 : ℝ) q, 1 - y ≠ 0 := by
    intro y hy
    have : 0 < 1 - y := by linarith [hy.2]
    exact this.ne'
  have hcont : ContDiffOn ℝ (n + 1)
      (fun y : ℝ ↦ (1 - y) ^ a) (Icc 0 q) :=
    (contDiff_const.sub contDiff_id).contDiffOn.rpow_const_of_ne hnonzero
  have hcontN : ContDiffOn ℝ n
      (fun y : ℝ ↦ (1 - y) ^ a) (Icc 0 q) :=
    hcont.of_le (by exact_mod_cast Nat.le_succ n)
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin n (fun y : ℝ ↦ (1 - y) ^ a) (Icc 0 q))
      (Ioo 0 q) :=
    (hcont.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast n.lt_succ_self) (uniqueDiffOn_Icc hq0)).mono
        Ioo_subset_Icc_self
  rcases taylor_mean_remainder_lagrange hq0 hcontN hdiff with
    ⟨point, hpoint, hremainder⟩
  have hremainder' :
      (1 - q) ^ a -
          taylorWithinEval (fun y : ℝ ↦ (1 - y) ^ a) n (Icc 0 q) 0 q =
        iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 - y) ^ a)
            (Icc 0 q) point * q ^ (n + 1) / (n + 1).factorial := by
    simpa using hremainder
  have hderiv := iteratedDerivWithin_one_sub_rpow (a := a) hq0 hq1 (n + 1) point
    ⟨hpoint.1.le, hpoint.2.le⟩
  have hcoeff : oneSubRpowDerivativeCoefficient a (n + 1) ≤ 0 :=
    oneSubRpowDerivativeCoefficient_nonpos ha0 ha1 (n + 1) (by omega)
  have hbaseAtPoint : 0 ≤ 1 - point := by linarith [hpoint.2]
  have hderivNonpos :
      iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 - y) ^ a)
          (Icc 0 q) point ≤ 0 := by
    rw [hderiv]
    exact mul_nonpos_of_nonpos_of_nonneg hcoeff (Real.rpow_nonneg hbaseAtPoint _)
  have hqpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq0.le _
  have hfactorial : (0 : ℝ) ≤ (n + 1).factorial := by positivity
  have hremaindernonpos :
      iteratedDerivWithin (n + 1) (fun y : ℝ ↦ (1 - y) ^ a)
          (Icc 0 q) point * q ^ (n + 1) / (n + 1).factorial ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hderivNonpos hqpow) hfactorial
  have hpowerTaylor :
      (1 - q) ^ a ≤
        taylorWithinEval (fun y : ℝ ↦ (1 - y) ^ a) n (Icc 0 q) 0 q := by
    linarith [hremainder', hremaindernonpos]
  have hscaled := mul_le_mul_of_nonneg_left hpowerTaylor
    (show (0 : ℝ) ≤ BONE by norm_num [BONE])
  rw [bone_mul_taylorWithinEval_eq_exactInputBinomialSum hq0 hq1 n] at hscaled
  simpa [q] using hscaled

end CometPool
