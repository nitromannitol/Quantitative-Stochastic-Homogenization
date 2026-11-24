import QuantitativeStochasticHomogenization.Ch02.Sec01.CubeCorrectorDefect
import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma27
import QuantitativeStochasticHomogenization.Ch02.Sec02.Definition214
import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition111
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestRandomFamily

/-!
# Theorem 2.4: the quantitative convergence of `a(□_n)` and `a*(□_n)` to `ā`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, Theorem 2.4, (2.21): for `d ≥ 2` there is `α(d, Λ) ∈ (0, ½]` such that for every
`s ∈ (0, d)` there is `C(s, d, Λ) < ∞` with, for every law satisfying (0.10)–(0.11) and every `n`,
`|a(□_n) - ā| + |a*(□_n) - ā| ≤ C 3^{-nα(d-s)} + O₁(C 3^{-ns})` (`theorem_2_4`), for the Frobenius
norm. The statement `X ≤ A + O₁(θ)` is `OsBound P (X - A) 1 θ`, as in (0.42).

The proof is not the book's (the book proves Theorem 2.4 from Proposition 2.11 and the unit range
of dependence, in Section 2.2). It uses the first-order correctors and the skew flux correctors of
Lemma 3.17, Lemma 6.1 and Proposition 6.2 above a random scale `R ≤ O_s(C_s)`
(`exists_ae_sublinearCorrectorFamily`), whose oscillations on `B_r`, `r ≥ R`, are at most
`C r^{1 - μ}`, `μ = β(d - s)`:

* on `{R ≤ √d 3ⁿ}`, `J(□_n, p, Dp) ≤ K |p|² 3^{-2μn/3}` (`dualityDefect_triadicCube_le_of_family`)
  and hence `|a(□_n) - D| + |a*(□_n) - D| ≤ C 3^{-μn/3}` (`frobeniusNorm_sub_add_le_of_family`);
* this and Proposition 1.7 identify the matrix `D` of the correctors with `ā`
  (`eq_homogenizedMatrix_of_ae_family`);
* on `{R ≥ 3ⁿ}` the left side of (2.21) is bounded, and `1{R ≥ 3ⁿ} ≤ (R/3ⁿ)^s = O₁(C 3^{-ns})`.

The exponent is `α = min(β/3, ½)`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Measurability of `a*(U)` -/

theorem measurable_det_of_apply {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Mat d}
    (hM : ∀ i j, Measurable fun ω => M ω i j) : Measurable fun ω => (M ω).det := by
  simp only [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hM _ _)

theorem measurable_inv_apply_of_apply {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Mat d}
    (hM : ∀ i j, Measurable fun ω => M ω i j) (i j : Fin d) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have hdet := measurable_det_of_apply hM
  have hadj : Measurable fun ω => (M ω).adjugate i j := by
    simp only [Matrix.adjugate_apply]
    refine measurable_det_of_apply fun k l => ?_
    simp only [Matrix.updateRow_apply]
    by_cases h : k = j
    · simp only [h, ↓reduceIte]
      exact measurable_const
    · simp only [h, ↓reduceIte]
      exact hM k l
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hdet.inv.mul hadj

/-- **The entries of `a*(U)` are measurable** in the coefficient field. -/
theorem measurable_coarseDualMatrix_apply {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (i j : Fin d) :
    Measurable fun a : CoefficientField d Λ => coarseDualMatrix a U i j :=
  measurable_inv_apply_of_apply (fun k l => measurable_coarseDualInvMatrix_apply hU0 hU hΛ k l) i j

theorem measurable_frobeniusNorm_coarseDualMatrix_sub (hΛ : 0 ≤ Λ) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (A : Mat d) :
    Measurable fun a : CoefficientField d Λ => frobeniusNorm (coarseDualMatrix a U - A) := by
  unfold frobeniusNorm frobeniusSq
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  simp only [Matrix.sub_apply]
  exact ((measurable_coarseDualMatrix_apply hU0 hU hΛ i j).sub_const _).mul
    ((measurable_coarseDualMatrix_apply hU0 hU hΛ i j).sub_const _)

/-! ## Elementary facts -/

theorem abs_apply_le_frobeniusNorm (A : Mat d) (i j : Fin d) : |A i j| ≤ frobeniusNorm A := by
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  unfold frobeniusSq
  have h1 : A i j ^ 2 ≤ ∑ l, A i l * A i l := by
    rw [sq]
    exact Finset.single_le_sum (f := fun l => A i l * A i l) (fun l _ => mul_self_nonneg _)
      (Finset.mem_univ j)
  exact h1.trans (Finset.single_le_sum (f := fun k => ∑ l, A k l * A k l)
    (fun k _ => Finset.sum_nonneg fun l _ => mul_self_nonneg _) (Finset.mem_univ i))

theorem three_pow_rpow_eq (n : ℕ) (x : ℝ) : ((3 : ℝ) ^ n) ^ x = ((3 : ℝ) ^ x) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

theorem tendsto_three_pow_rpow_neg {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ (-x)) atTop (𝓝 0) := by
  simp only [three_pow_rpow_eq]
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) _) ?_
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem isOpen_triadicCube' (n : ℕ) : IsOpen (triadicCube d n) :=
  (isOpenBoundedConvexDomain_triadicCube (d := d) n).1

theorem convex_triadicCube (n : ℕ) : Convex ℝ (triadicCube d n) :=
  (isOpenBoundedConvexDomain_triadicCube (d := d) n).2.2

theorem triadicCube_nonempty (n : ℕ) : (triadicCube d n).Nonempty :=
  ⟨0, mem_triadicCube_iff.mpr fun i => by simp⟩

theorem three_pow_le_cubeBallRadius (hd : 1 ≤ d) (n : ℕ) : (3 : ℝ) ^ n ≤ cubeBallRadius d n := by
  rw [cubeBallRadius]
  exact le_mul_of_one_le_left (by positivity) (Real.one_le_sqrt.mpr (by exact_mod_cast hd))

/-! ## The matrices on a cube from a family of correctors -/

/-- **The matrices `a(□_n)` and `a*(□_n)` from a family of correctors**: under the hypotheses of
`dualityDefect_triadicCube_le_of_family`, `|a(□_n) - D| + |a*(□_n) - D| ≤ C √K (3ⁿ)^{-μ/3}` with
`C = 3 d² √(32 Λ)`. -/
theorem frobeniusNorm_sub_add_le_of_family (hd : 1 ≤ d) (a : CoefficientField d Λ)
    {D : Mat d} {μ C₁ R₀ : ℝ} (F : SublinearCorrectorFamily a D μ C₁ R₀) (hμ : 0 < μ)
    (hC₁ : 0 ≤ C₁) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ v : Vec d, euclideanSq (D.mulVec v) ≤ B * euclideanSq v) {n : ℕ}
    (hn : R₀ ≤ cubeBallRadius d n) :
    frobeniusNorm (coarseMatrix a (triadicCube d n) - D) +
        frobeniusNorm (coarseDualMatrix a (triadicCube d n) - D) ≤
      3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) *
        (Real.sqrt (cubeCorrectorConst d Λ C₁ B) * ((3 : ℝ) ^ n) ^ (-(μ / 3))) := by
  have : NeZero d := ⟨by omega⟩
  have hK0 : 0 ≤ cubeCorrectorConst d Λ C₁ B := by
    have := cubeBallRatio_nonneg d
    have : 0 ≤ cutoffGradConst d := by unfold cutoffGradConst; positivity
    unfold cubeCorrectorConst
    positivity
  have hρ0 : 0 ≤ ((3 : ℝ) ^ n) ^ (-(μ / 3)) := Real.rpow_nonneg (by positivity) _
  refine frobeniusNorm_sub_add_le_of_dualityDefect_le a (isOpen_triadicCube' n)
    (isBounded_triadicCube n) (convex_triadicCube n) (triadicCube_nonempty n) D
    (mul_nonneg (Real.sqrt_nonneg _) hρ0) fun p hp => ?_
  have h := dualityDefect_triadicCube_le_of_family hd a F hμ hC₁ hB hn p
  have hp1 := euclideanSq_le_one_of_mem_originBall hp
  rw [mul_pow, Real.sq_sqrt hK0]
  refine h.trans ?_
  have hρ2 : 0 ≤ (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 2 := sq_nonneg _
  calc cubeCorrectorConst d Λ C₁ B * euclideanSq p * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 2
      ≤ cubeCorrectorConst d Λ C₁ B * 1 * (((3 : ℝ) ^ n) ^ (-(μ / 3))) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 hK0) hρ2
    _ = _ := by ring

/-! ## The structural bound -/

theorem homogenizedMatrix_dot_bounds {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (v : Vec d) :
    0 ≤ dot v ((homogenizedMatrix P).mulVec v) ∧
      dot v ((homogenizedMatrix P).mulVec v) ≤ Λ * euclideanSq v := by
  have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ v
  have h0 := limitDirichletEnergy_nonneg P v
  have h1 := limitDirichletEnergy_le hP hΛ v
  constructor <;> linarith

/-- The constant `3 d² √(32 Λ) √(½ Λ + ½ Λ²)` of `frobeniusNorm_sub_homogenizedMatrix_add_le`. -/
def structuralMatrixConst (d : ℕ) (Λ : ℝ) : ℝ :=
  3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) * Real.sqrt ((1 / 2 : ℝ) * Λ + (1 / 2 : ℝ) * Λ ^ 2)

theorem structuralMatrixConst_nonneg (d : ℕ) (Λ : ℝ) : 0 ≤ structuralMatrixConst d Λ := by
  unfold structuralMatrixConst
  positivity

/-- **The structural bound** `|a(U) - ā| + |a*(U) - ā| ≤ C(d, Λ)`. -/
theorem frobeniusNorm_sub_homogenizedMatrix_add_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) :
    frobeniusNorm (coarseMatrix a U - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix a U - homogenizedMatrix P) ≤ structuralMatrixConst d Λ := by
  have hΛ1 : 1 ≤ Λ := one_le_of_coefficientField a
  have hΛ : 0 ≤ Λ := zero_le_one.trans hΛ1
  have hb := homogenizedMatrix_dot_bounds hP hΛ
  have hδ0 : 0 ≤ Real.sqrt ((1 / 2 : ℝ) * Λ + (1 / 2 : ℝ) * Λ ^ 2) := Real.sqrt_nonneg _
  have h := frobeniusNorm_sub_add_le_of_dualityDefect_le a hUo hUb hUc hne
    (homogenizedMatrix P) hδ0 fun p hp => by
      rw [Real.sq_sqrt (by positivity)]
      exact dualityDefect_le_of_bounds a hUo hUb hUc hne (homogenizedMatrix_transpose hP hΛ)
        (fun v => (hb v).1) (fun v => (hb v).2) hp
  refine h.trans (le_of_eq ?_)
  unfold structuralMatrixConst
  ring

/-! ## The identification of the homogenized matrix -/

/-- **The matrix of the correctors is `ā`**: if almost surely there is a family of correctors with
matrix `D` above a random scale `R ≤ O_s(θ)`, then `D = ā`. -/
theorem eq_homogenizedMatrix_of_ae_family (hd : 1 ≤ d) {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) {D : Mat d} {μ C₁ : ℝ} (hμ : 0 < μ) (hC₁ : 0 ≤ C₁)
    {R : CoefficientField d Λ → ℝ} {s θ : ℝ} (hR : OsBound P R s θ) (hR0 : ∀ a, 0 ≤ R a)
    (hF : ∀ᵐ a ∂P, Nonempty (SublinearCorrectorFamily a D μ C₁ (R a))) :
    D = homogenizedMatrix P := by
  have : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure P := hP.1
  have hΛ1 : 1 ≤ Λ := by
    obtain ⟨a, -⟩ := hF.exists
    exact one_le_of_coefficientField a
  have hΛ : 0 ≤ Λ := zero_le_one.trans hΛ1
  set A := homogenizedMatrix P with hA
  set B := frobeniusSq D with hBdef
  have hB0 : 0 ≤ B := frobeniusSq_nonneg D
  have hB : ∀ v : Vec d, euclideanSq (D.mulVec v) ≤ B * euclideanSq v :=
    euclideanSq_mulVec_le_frobeniusSq D
  set Kf := 3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) * Real.sqrt (cubeCorrectorConst d Λ C₁ B)
    with hKf
  obtain ⟨C7, hC7, h17⟩ := proposition_1_7 (d := d) (Λ := Λ)
  have hs := hR.exponent_pos
  have hθ := hR.scale_pos
  have hs1 : s / s = 1 := div_self hs.ne'
  -- the probability of `{R ≥ 3ⁿ}`
  set ind : ℕ → CoefficientField d Λ → ℝ := fun n =>
    Set.indicator {a | (3 : ℝ) ^ n ≤ R a} (fun _ => (1 : ℝ)) with hind
  have hindOs : ∀ n : ℕ, OsBound P (ind n) 1 ((θ / (3 : ℝ) ^ n) ^ s) := fun n => by
    have h := hR.indicator_le_of hR0 (by positivity : (0 : ℝ) < (3 : ℝ) ^ n) hs
    rw [hs1] at h
    exact h
  have hind0 : ∀ n a, 0 ≤ ind n a := fun n a =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) a
  have hindE : ∀ n, Integrable (ind n) P ∧ ∫ a, ind n a ∂P ≤ 2 * (θ / (3 : ℝ) ^ n) ^ s :=
    fun n => (hindOs n).integrable_and_integral_le le_rfl (hind0 n)
  have htθ : Tendsto (fun n : ℕ => 2 * (θ / (3 : ℝ) ^ n) ^ s) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => θ / (3 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have h2 := h1.rpow_const (Or.inr hs.le)
    rw [Real.zero_rpow hs.ne'] at h2
    have h3 := h2.const_mul 2
    rw [mul_zero] at h3
    exact h3
  -- the expectation of `|a(□_n) - ā|`
  set Z : ℕ → CoefficientField d Λ → ℝ := fun n a =>
    frobeniusNorm (coarseMatrix a (triadicCube d n) - A) with hZ
  have hZE : ∀ n, Integrable (Z n) P ∧ ∫ a, Z n a ∂P ≤
      C7 * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) + C7 * omegaModulus P ((n + 1) / 2) := fun n =>
    h17 P hP n
  have htZ : Tendsto (fun n : ℕ => C7 * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) +
      C7 * omegaModulus P ((n + 1) / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (3 : ℝ) ^ (-((d : ℝ) * n) / 4)) atTop (𝓝 0) := by
      have hd0 : (0 : ℝ) < d / 4 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have h := tendsto_three_pow_rpow_neg hd0
      refine h.congr fun n => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have h2 : Tendsto (fun n : ℕ => omegaModulus P ((n + 1) / 2)) atTop (𝓝 0) :=
      (tendsto_omegaModulus hP hΛ).comp
        (tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩)
    have h3 := (h1.const_mul C7).add (h2.const_mul C7)
    rw [mul_zero, add_zero] at h3
    exact h3
  have hρ : Tendsto (fun n : ℕ => Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3))) atTop (𝓝 0) := by
    have h := (tendsto_three_pow_rpow_neg (by positivity : (0 : ℝ) < μ / 3)).const_mul Kf
    rw [mul_zero] at h
    exact h
  -- every entry
  ext i j
  set c := |D i j - A i j| with hc
  have hc0 : 0 ≤ c := abs_nonneg _
  have hle : ∀ n : ℕ, c ≤ Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) +
      (C7 * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) + C7 * omegaModulus P ((n + 1) / 2)) +
      c * (2 * (θ / (3 : ℝ) ^ n) ^ s) := fun n => by
    have hae : ∀ᵐ a ∂P, c ≤ Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) + Z n a + c * ind n a := by
      filter_upwards [hF] with a ⟨F⟩
      have hZ0 : 0 ≤ Z n a := Real.sqrt_nonneg _
      by_cases h : (3 : ℝ) ^ n ≤ R a
      · have h1 : ind n a = 1 := Set.indicator_of_mem (show a ∈ {a | (3 : ℝ) ^ n ≤ R a} from h) _
        rw [h1, mul_one]
        have : 0 ≤ Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) := by
          have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n) (-(μ / 3))
          rw [hKf]
          positivity
        linarith
      · have hRn : R a ≤ cubeBallRadius d n :=
          (le_of_lt (not_le.mp h)).trans (three_pow_le_cubeBallRadius hd n)
        have hfam := frobeniusNorm_sub_add_le_of_family hd a F hμ hC₁ hB0 hB hRn
        have hD := abs_apply_le_frobeniusNorm (coarseMatrix a (triadicCube d n) - D) i j
        have hA' := abs_apply_le_frobeniusNorm (coarseMatrix a (triadicCube d n) - A) i j
        have hdual := Real.sqrt_nonneg (frobeniusSq (coarseDualMatrix a (triadicCube d n) - D))
        have hind := hind0 n a
        have htri : c ≤ |(coarseMatrix a (triadicCube d n) - D) i j| +
            |(coarseMatrix a (triadicCube d n) - A) i j| := by
          rw [hc]
          simp only [Matrix.sub_apply]
          calc |D i j - A i j| = |(coarseMatrix a (triadicCube d n) i j - A i j) -
                (coarseMatrix a (triadicCube d n) i j - D i j)| := by congr 1; ring
            _ ≤ |coarseMatrix a (triadicCube d n) i j - A i j| +
                |coarseMatrix a (triadicCube d n) i j - D i j| := abs_sub _ _
            _ = _ := add_comm _ _
        have e : 3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) *
            (Real.sqrt (cubeCorrectorConst d Λ C₁ B) * ((3 : ℝ) ^ n) ^ (-(μ / 3))) =
            Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) := by
          rw [hKf]
          ring
        rw [e] at hfam
        have hdual' : 0 ≤ frobeniusNorm (coarseDualMatrix a (triadicCube d n) - D) := hdual
        have hci := mul_nonneg hc0 hind
        have hZa : Z n a = frobeniusNorm (coarseMatrix a (triadicCube d n) - A) := rfl
        rw [hZa]
        linarith
    have hi1 : Integrable (fun a => Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) + Z n a) P :=
      (integrable_const _).add (hZE n).1
    have hi2 : Integrable (fun a => c * ind n a) P := (hindE n).1.const_mul c
    have hint : Integrable (fun a => Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) + Z n a + c * ind n a) P :=
      hi1.add hi2
    have h := integral_mono_ae (integrable_const c) hint hae
    rw [integral_const, integral_add hi1 hi2, integral_add (integrable_const _) (hZE n).1,
      integral_const, integral_const_mul] at h
    simp only [probReal_univ, one_smul] at h
    have h2 := mul_le_mul_of_nonneg_left (hindE n).2 hc0
    linarith [(hZE n).2]
  have hlim : Tendsto (fun n : ℕ => Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) +
      (C7 * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) + C7 * omegaModulus P ((n + 1) / 2)) +
      c * (2 * (θ / (3 : ℝ) ^ n) ^ s)) atTop (𝓝 0) := by
    have h := (hρ.add htZ).add (htθ.const_mul c)
    rw [mul_zero, add_zero, add_zero] at h
    exact h
  have hc' : c ≤ 0 := ge_of_tendsto' hlim hle
  have : c = 0 := le_antisymm hc' hc0
  rw [hc, abs_eq_zero, sub_eq_zero] at this
  exact this

/-! ## Theorem 2.4 -/

/-- **Theorem 2.4**, (2.21): for `d ≥ 2` and `Λ > 1` there is `α(d, Λ) ∈ (0, ½]` such that for every
`s ∈ (0, d)` there is `C(s, d, Λ) < ∞` with, for every law satisfying (0.10)–(0.11) and every
`n ∈ ℕ`, `|a(□_n) - ā| + |a*(□_n) - ā| ≤ C 3^{-nα(d-s)} + O₁(C 3^{-ns})`, for the Frobenius norm. -/
theorem theorem_2_4 (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 2 ∧ ∀ s : ℝ, 0 < s → s < d → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ n : ℕ,
        OsBound P (fun a =>
          frobeniusNorm (coarseMatrix a (triadicCube d n) - homogenizedMatrix P) +
            frobeniusNorm (coarseDualMatrix a (triadicCube d n) - homogenizedMatrix P) -
            C * (3 : ℝ) ^ (-((n : ℝ) * α * ((d : ℝ) - s)))) 1 (C * (3 : ℝ) ^ (-((n : ℝ) * s))) := by
  have : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨β, C₀, hβ, hC₀, hfam⟩ := exists_ae_sublinearCorrectorFamily hd hΛ
  refine ⟨min (β / 3) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _,
    fun s hs hsd => ?_⟩
  obtain ⟨Cs, hCs, hP'⟩ := hfam s hs hsd
  set α := min (β / 3) (1 / 2) with hα
  set μ := β * ((d : ℝ) - s) with hμdef
  have hds : 0 < (d : ℝ) - s := by linarith
  have hμ : 0 < μ := mul_pos hβ hds
  set C₁ := (1 + (d : ℝ) ^ 2) * C₀ with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  set Kf := 3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) * Real.sqrt (cubeCorrectorConst d Λ C₁ (Λ ^ 2))
    with hKf
  have hKf0 : 0 ≤ Kf := by rw [hKf]; positivity
  set Cst := structuralMatrixConst d Λ with hCst
  have hCst0 : 0 ≤ Cst := structuralMatrixConst_nonneg d Λ
  set C := max (max Kf ((Cst + 1) * Cs ^ s)) 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCKf : Kf ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCst' : (Cst + 1) * Cs ^ s ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C, by linarith, fun P hP n => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨D, R, -, -, hRos, hR1, hF⟩ := hP' P hP
  have hR0 : ∀ a, 0 ≤ R a := fun a => zero_le_one.trans (hR1 a)
  have hDA : D = homogenizedMatrix P :=
    eq_homogenizedMatrix_of_ae_family hd1 hP hμ hC₁ hRos hR0 hF
  rw [hDA] at hF
  set A := homogenizedMatrix P with hA
  have hb := homogenizedMatrix_dot_bounds hP hΛ0
  have hAB : ∀ v, euclideanSq (A.mulVec v) ≤ Λ ^ 2 * euclideanSq v :=
    euclideanSq_mulVec_le_of_dot_le (homogenizedMatrix_transpose hP hΛ0) (fun v => (hb v).1)
      (fun v => (hb v).2)
  set ind := Set.indicator {a | (3 : ℝ) ^ n ≤ R a} (fun _ => (1 : ℝ)) with hind
  have hind0 : ∀ a, 0 ≤ ind a := fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a
  -- the exponents
  have hρα : ((3 : ℝ) ^ n) ^ (-(μ / 3)) ≤ (3 : ℝ) ^ (-((n : ℝ) * α * ((d : ℝ) - s))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hαβ : α ≤ β / 3 := min_le_left _ _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := mul_le_mul_of_nonneg_right hαβ (mul_nonneg hn0 hds.le)
    rw [hμdef]
    nlinarith
  have h3α : 0 ≤ (3 : ℝ) ^ (-((n : ℝ) * α * ((d : ℝ) - s))) := Real.rpow_nonneg (by norm_num) _
  -- the bound on each event
  have hae : ∀ᵐ a ∂P, frobeniusNorm (coarseMatrix a (triadicCube d n) - A) +
      frobeniusNorm (coarseDualMatrix a (triadicCube d n) - A) -
      C * (3 : ℝ) ^ (-((n : ℝ) * α * ((d : ℝ) - s))) ≤ (Cst + 1) * ind a := by
    filter_upwards [hF] with a ⟨F⟩
    have hXst := frobeniusNorm_sub_homogenizedMatrix_add_le hP a (isOpen_triadicCube' n)
      (isBounded_triadicCube n) (convex_triadicCube n) (triadicCube_nonempty n)
    by_cases h : (3 : ℝ) ^ n ≤ R a
    · have h1 : ind a = 1 := Set.indicator_of_mem (show a ∈ {a | (3 : ℝ) ^ n ≤ R a} from h) _
      rw [h1, mul_one]
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ C) h3α
      linarith
    · have h0 : ind a = 0 :=
        Set.indicator_of_notMem (show a ∉ {a | (3 : ℝ) ^ n ≤ R a} from h) _
      rw [h0, mul_zero]
      have hRn : R a ≤ cubeBallRadius d n :=
        (le_of_lt (not_le.mp h)).trans (three_pow_le_cubeBallRadius hd1 n)
      have hfam' := frobeniusNorm_sub_add_le_of_family hd1 a F hμ hC₁ (sq_nonneg Λ) hAB hRn
      have e : 3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) *
          (Real.sqrt (cubeCorrectorConst d Λ C₁ (Λ ^ 2)) * ((3 : ℝ) ^ n) ^ (-(μ / 3))) =
          Kf * ((3 : ℝ) ^ n) ^ (-(μ / 3)) := by
        rw [hKf]
        ring
      rw [e] at hfam'
      have := mul_le_mul hCKf hρα (Real.rpow_nonneg (by positivity) _) (by linarith)
      linarith
  -- the indicator of `{R ≥ 3ⁿ}`
  have hindOs : OsBound P ind 1 ((Cs / (3 : ℝ) ^ n) ^ s) := by
    have h := hRos.indicator_le_of hR0 (by positivity : (0 : ℝ) < (3 : ℝ) ^ n) hs
    rwa [div_self hs.ne'] at h
  have hCind : OsBound P (fun a => (Cst + 1) * ind a) 1 ((Cst + 1) * (Cs / (3 : ℝ) ^ n) ^ s) :=
    hindOs.const_mul (by linarith)
  have hscale : (Cst + 1) * (Cs / (3 : ℝ) ^ n) ^ s ≤ C * (3 : ℝ) ^ (-((n : ℝ) * s)) := by
    have e3 : ((3 : ℝ) ^ n) ^ s = (3 : ℝ) ^ ((n : ℝ) * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e4 : (3 : ℝ) ^ (-((n : ℝ) * s)) = ((3 : ℝ) ^ ((n : ℝ) * s))⁻¹ :=
      Real.rpow_neg (by norm_num) _
    rw [Real.div_rpow hCs.le (by positivity), e3, e4, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hCst' (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num) _))
  refine (hCind.mono_scale hscale).of_le_ae ?_ hae
  exact ((measurable_frobeniusNorm_coarseMatrix_sub hΛ0 (volume_triadicCube_ne_top d n) A).add
    (measurable_frobeniusNorm_coarseDualMatrix_sub hΛ0 (volume_triadicCube_ne_zero d n)
      (volume_triadicCube_ne_top d n) A)).sub_const _

end QSH
