import CometPool.CPow.BinomialUpper
import CometPool.CPow.BaselineFeeBound
import Mathlib.Analysis.Complex.TaylorSeries

namespace CometPool

open Set


theorem complex_one_sub_mem_slitPlane {z : ℂ} (hz : z ∈ Metric.ball 0 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hre : z.re < 1 := by
    have hzabs : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    exact lt_of_le_of_lt z.re_le_norm hzabs
  norm_num at ⊢
  linarith

theorem complex_iteratedDeriv_one_sub_cpow
    (a : ℝ) : ∀ n z, z ∈ Metric.ball (0 : ℂ) 1 →
      iteratedDeriv n (fun y : ℂ ↦ (1 - y) ^ (a : ℂ)) z =
        (oneSubRpowDerivativeCoefficient a n : ℂ) *
          (1 - z) ^ ((a - n : ℝ) : ℂ) := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simp
  | succ n ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have heq : Set.EqOn
          (iteratedDeriv n (fun y : ℂ ↦ (1 - y) ^ (a : ℂ)))
          (fun y : ℂ ↦
            (oneSubRpowDerivativeCoefficient a n : ℂ) *
              (1 - y) ^ ((a - n : ℝ) : ℂ))
          (Metric.ball 0 1) := fun y hy ↦ ih y hy
      have heventually : Filter.EventuallyEq (nhds z)
          (iteratedDeriv n (fun y : ℂ ↦ (1 - y) ^ (a : ℂ)))
            (fun y : ℂ ↦
              (oneSubRpowDerivativeCoefficient a n : ℂ) *
                (1 - y) ^ ((a - n : ℝ) : ℂ)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
        exact heq hy
      have hderivCongr := Filter.EventuallyEq.deriv_eq heventually
      rw [hderivCongr]
      have hinner : HasDerivAt (fun y : ℂ ↦ 1 - y) (-1) z := by
        convert (hasDerivAt_const z 1).sub (hasDerivAt_id z) using 1
        ring_nf
      have hpowerDeriv := hinner.cpow_const (c := ((a - n : ℝ) : ℂ))
        (complex_one_sub_mem_slitPlane hz)
      have hderiv := hpowerDeriv.const_mul
        (oneSubRpowDerivativeCoefficient a n : ℂ)
      rw [hderiv.deriv]
      rw [oneSubRpowDerivativeCoefficient_succ]
      push_cast
      ring_nf

theorem exact_input_binomial_hasSum
    {a base : ℝ} (hbase0 : 0 < base) (hbase1 : base < 1) :
    HasSum (exactInputBinomialTerm a base) ((BONE : ℝ) * base ^ a) := by
  let q : ℝ := 1 - base
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  let f : ℂ → ℂ := fun z ↦ (1 - z) ^ (a : ℂ)
  have hdiff : DifferentiableOn ℂ f (Metric.ball 0 1) := by
    intro z hz
    exact ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).differentiableWithinAt.cpow_const
      (complex_one_sub_mem_slitPlane hz)
  have hz : (q : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball]
    simp
    rw [abs_of_pos hq0]
    exact hq1
  have hsum := Complex.hasSum_taylorSeries_on_ball hdiff hz
  have hsumRe := Complex.hasSum_re hsum
  have hterms :
      (fun n : ℕ ↦
          (((n.factorial : ℂ)⁻¹ *
            (((q : ℂ) - 0) ^ n * iteratedDeriv n f 0))).re) =
        (fun n : ℕ ↦ exactInputBinomialTerm a base n / (BONE : ℝ)) := by
    funext n
    have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
    rw [complex_iteratedDeriv_one_sub_cpow a n 0 hzero]
    dsimp [f]
    simp only [sub_zero, Complex.smul_re, Complex.inv_re, Complex.natCast_re,
      Complex.natCast_im, zero_div, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.one_cpow]
    rw [exactInputBinomialTerm]
    dsimp [q]
    push_cast
    norm_num [BONE]
    norm_cast
    ring
  change HasSum
    (fun n : ℕ ↦
      (((n.factorial : ℂ)⁻¹ *
        (((q : ℂ) - 0) ^ n * iteratedDeriv n f 0))).re)
    (f (q : ℂ)).re at hsumRe
  rw [hterms] at hsumRe
  have hresult : f (q : ℂ) = ((base ^ a : ℝ) : ℂ) := by
    dsimp [f, q]
    have harg : (1 : ℂ) - ((1 - base : ℝ) : ℂ) = (base : ℂ) := by
      push_cast
      ring
    rw [harg]
    rw [← Complex.ofReal_cpow hbase0.le]
  rw [hresult] at hsumRe
  have hscaled := hsumRe.mul_left (BONE : ℝ)
  convert hscaled using 1
  · funext n
    field_simp [ne_of_gt (show (0 : ℝ) < BONE by norm_num [BONE])]

/-- All non-constant below-one generalized-binomial terms are non-positive. -/
theorem exactInputBinomialTerm_nonpos
    {a base : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase1 : base ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    exactInputBinomialTerm a base n ≤ 0 := by
  rw [exactInputBinomialTerm]
  have hcoeff := oneSubRpowDerivativeCoefficient_nonpos ha0 ha1 n hn
  have hfactorial : (0 : ℝ) ≤ (n.factorial : ℝ) := by positivity
  have hpower : 0 ≤ (1 - base) ^ n := pow_nonneg (by linarith) n
  have hquotient : oneSubRpowDerivativeCoefficient a n / (n.factorial : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hcoeff hfactorial
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num [BONE]) hquotient) hpower

/-- The exact fractional recurrence contracts geometrically from any non-constant term. -/
theorem fractional_binomial_terms_from_current_bound
    (T : ℕ → ℝ) {a x q : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1)) :
    ∀ j, |T (n + j)| ≤ |T n| * q ^ j := by
  apply geometric_term_bound
    (M := fun j ↦ |T (n + j)|) (S := |T n|) (q := q)
    (by simp) (le_trans (abs_nonneg x) hx)
  intro j
  rw [show n + (j + 1) = (n + j) + 1 by omega, hrec (n + j)]
  exact fractional_binomial_step_contracts
    (a := a) (x := x) (q := q) (term := T (n + j)) ha0 ha1 hx (n + j)

/--
The omitted below-one tail is bounded by the geometric tail generated from
the last retained term.
-/
theorem exact_input_binomial_partial_tail_le
    {a base : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase0 : 0 < base) (hbase1 : base < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), exactInputBinomialTerm a base k) -
        (BONE : ℝ) * base ^ a ≤
      |exactInputBinomialTerm a base n| * (1 - base) / base := by
  let T : ℕ → ℝ := exactInputBinomialTerm a base
  let q : ℝ := 1 - base
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hsum : HasSum T ((BONE : ℝ) * base ^ a) := by
    exact exact_input_binomial_hasSum hbase0 hbase1
  have hsign : ∀ k, 1 ≤ k → T k ≤ 0 := by
    intro k hk
    exact exactInputBinomialTerm_nonpos ha0 ha1 hbase1.le hk
  have hcontract : ∀ j, |T (n + j)| ≤ |T n| * q ^ j := by
    apply fractional_binomial_terms_from_current_bound
      (a := a) (x := base - 1) (q := q) (n := n) T ha0 ha1
      (show |base - 1| ≤ q by
        rw [abs_of_nonpos (sub_nonpos.mpr hbase1.le)]
        dsimp [q]
        linarith)
      (fun k ↦ exactInputBinomialTerm_succ a base k)
  let A : ℕ → ℝ := fun j ↦ |T (j + (n + 1))|
  let G : ℕ → ℝ := fun j ↦ |T n| * q * q ^ j
  have hAG : ∀ j, A j ≤ G j := by
    intro j
    have hbound := hcontract (j + 1)
    dsimp [A, G]
    rw [show j + (n + 1) = n + (j + 1) by omega]
    calc
      |T (n + (j + 1))| ≤ |T n| * q ^ (j + 1) := hbound
      _ = |T n| * q * q ^ j := by rw [pow_succ']; ring
  have hgeom : HasSum G (|T n| * q / (1 - q)) := by
    have h := hasSum_geometric_of_abs_lt_one
      (show |q| < 1 by rw [abs_of_nonneg hq0]; exact hq1)
    have hscaled := h.mul_left (|T n| * q)
    convert hscaled using 1
  have hAsummable : Summable A := by
    apply Summable.of_nonneg_of_le (fun j ↦ abs_nonneg _) hAG hgeom.summable
  have hAtotal : ∑' j, A j ≤ |T n| * q / (1 - q) := by
    calc
      ∑' j, A j ≤ ∑' j, G j :=
        Summable.tsum_le_tsum hAG hAsummable hgeom.summable
      _ = |T n| * q / (1 - q) := hgeom.tsum_eq
  have htailEq :
      (∑' j, T (j + (n + 1))) = -(∑' j, A j) := by
    rw [← tsum_neg]
    congr 1
    funext j
    dsimp [A]
    rw [abs_of_nonpos (hsign _ (by omega))]
    ring
  have hsplit := hsum.summable.sum_add_tsum_nat_add (n + 1)
  rw [hsum.tsum_eq] at hsplit
  dsimp [T] at hsplit ⊢
  have hdenom : 1 - q = base := by dsimp [q]; ring
  rw [hdenom] at hAtotal
  linarith

/--
For a below-one fractional power with displacement at most one half, adding
the last retained exact term a second time places the result below the exact
power. This certifies the baseline round-down adjustment for every later stop.
-/
theorem exact_input_binomial_doubled_last_partial_lower
    {a base : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hbase0 : 0 < base) (hbase1 : base < 1)
    (hq : 1 - base ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), exactInputBinomialTerm a base k) +
        exactInputBinomialTerm a base n ≤
      (BONE : ℝ) * base ^ a := by
  have htail := exact_input_binomial_partial_tail_le
    ha0 ha1 hbase0 hbase1 hn
  have htermNonpos := exactInputBinomialTerm_nonpos
    ha0 ha1 hbase1.le hn
  have hfactor : (1 - base) / base ≤ 1 := by
    have hbaseHalf : 1 / 2 ≤ base := by linarith
    exact (div_le_one hbase0).2 (by linarith)
  have htailCurrent :
      |exactInputBinomialTerm a base n| * (1 - base) / base ≤
        |exactInputBinomialTerm a base n| := by
    have habs0 := abs_nonneg (exactInputBinomialTerm a base n)
    calc
      |exactInputBinomialTerm a base n| * (1 - base) / base =
          |exactInputBinomialTerm a base n| * ((1 - base) / base) := by ring
      _ ≤ |exactInputBinomialTerm a base n| :=
        mul_le_of_le_one_right habs0 hfactor
  rw [abs_of_nonpos htermNonpos] at htail htailCurrent
  linarith

end CometPool
