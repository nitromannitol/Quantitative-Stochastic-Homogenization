import QuantitativeStochasticHomogenization.Ch02.Sec01.Theorem24

/-!
# Proposition 2.11: the rate of `E[J(□_n, p, ā p)]`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Proposition 2.11, (2.29): for `d ≥ 2` there are `α(d, Λ) ∈ (0, ½]` and `C(d, Λ) < ∞`
such that, for every law satisfying (0.10)–(0.11) and every `n ∈ ℕ`,
`sup_{p ∈ B₁} E[J(□_n, p, ā p)] ≤ C 3^{-nα}` (`proposition_2_11`).

The book proves Proposition 2.11 first and deduces Theorem 2.4 from it. Here Theorem 2.4 is proved
from the first-order correctors (`theorem_2_4`), and Proposition 2.11 follows from it: by the
completed square (2.12), `J(U, p, ā p) ≤ ½ (1 + C) (|a(U) - ā| + |a*(U) - ā|)` for `p ∈ B₁`
(`dualityDefect_homogenizedMatrix_le`), and `X ≤ A + O₁(θ)` gives `E[X] ≤ A + 2θ`
(`OsBound.integral_le_add_two_mul`); Theorem 2.4 is applied with `s = d/2`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The expectation from `X ≤ A + O₁(θ)`**: `E[X] ≤ A + 2θ`. -/
theorem OsBound.integral_le_add_two_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {A θ : ℝ} (h : OsBound P (fun ω => X ω - A) 1 θ)
    (hX : Integrable X P) : ∫ ω, X ω ∂P ≤ A + 2 * θ := by
  obtain ⟨hm, hs, hθ, hint⟩ := h
  have e : ∀ ω, max (max (X ω - A) 0) 0 = max (X ω - A) 0 := fun ω =>
    max_eq_left (le_max_right _ _)
  have hY : OsBound P (fun ω => max (X ω - A) 0) 1 θ :=
    ⟨hm.max measurable_const, hs, hθ, by simpa only [e] using hint⟩
  obtain ⟨hYi, hYle⟩ := hY.integrable_and_integral_le le_rfl fun ω => le_max_right _ _
  have hle : ∀ ω, X ω ≤ A + max (X ω - A) 0 := fun ω => by
    have := le_max_left (X ω - A) 0
    linarith
  have hAY : Integrable (fun ω => A + max (X ω - A) 0) P := (integrable_const A).add hYi
  have h2 := integral_mono hX hAY hle
  rw [integral_add (integrable_const A) hYi, integral_const, probReal_univ,
    one_smul] at h2
  linarith

theorem measurable_dualityDefect {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (hΛ : 0 ≤ Λ) (p q : Vec d) :
    Measurable fun a : CoefficientField d Λ => dualityDefect a U p q :=
  ((measurable_dirichletEnergy hU hΛ p).add (measurable_dualEnergy hU0 hU hΛ q)).sub_const _

/-- **`J(U, p, ā p)` by the matrices**: for `p ∈ B₁`,
`0 ≤ J(U, p, ā p) ≤ ½ (1 + C) (|a(U) - ā| + |a*(U) - ā|)` with `C = structuralMatrixConst d Λ`. -/
theorem dualityDefect_homogenizedMatrix_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) {p : Vec d}
    (hp : p ∈ originBall d 1) :
    0 ≤ dualityDefect a U p ((homogenizedMatrix P).mulVec p) ∧
      dualityDefect a U p ((homogenizedMatrix P).mulVec p) ≤
        (1 / 2 : ℝ) * (1 + structuralMatrixConst d Λ) *
          (frobeniusNorm (coarseMatrix a U - homogenizedMatrix P) +
            frobeniusNorm (coarseDualMatrix a U - homogenizedMatrix P)) := by
  set A := homogenizedMatrix P with hA
  set M := coarseMatrix a U with hM
  set N := coarseDualMatrix a U with hN
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have h0 : 0 ≤ dualityDefect a U p (A.mulVec p) := by
    have := dot_le_dirichletEnergy_add_dualEnergy a hUb hU0 p (A.mulVec p)
    unfold dualityDefect
    linarith
  refine ⟨h0, ?_⟩
  have hJ := dualityDefect_eq_completedSquare a hUo hUb hUc hne p (A.mulVec p)
  have hp1 := euclideanSq_le_one_of_mem_originBall hp
  have hp0 := euclideanSq_nonneg p
  have e1 : dot p (M.mulVec p) - dot p (N.mulVec p) =
      dot p ((M - A).mulVec p) - dot p ((N - A).mulVec p) := by
    simp only [Matrix.sub_mulVec, dot_sub_right_eq]
    ring
  have h1 := abs_dot_mulVec_le_frobeniusNorm (M - A) p
  have h2 := abs_dot_mulVec_le_frobeniusNorm (N - A) p
  have h3 := dot_coarseDualInvMatrix_le a hUo hUb hUc hne (A.mulVec p - N.mulVec p)
  have e2 : euclideanSq (A.mulVec p - N.mulVec p) = euclideanSq ((N - A).mulVec p) := by
    simp only [euclideanSq, dot, Matrix.sub_mulVec, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h4 := euclideanSq_mulVec_le_frobeniusSq (N - A) p
  have hfN : frobeniusSq (N - A) = frobeniusNorm (N - A) ^ 2 :=
    (Real.sq_sqrt (frobeniusSq_nonneg _)).symm
  have hst := frobeniusNorm_sub_homogenizedMatrix_add_le hP a hUo hUb hUc hne
  have hfM0 : 0 ≤ frobeniusNorm (M - A) := Real.sqrt_nonneg _
  have hfN0 : 0 ≤ frobeniusNorm (N - A) := Real.sqrt_nonneg _
  have hNst : frobeniusNorm (N - A) ^ 2 ≤ structuralMatrixConst d Λ * frobeniusNorm (N - A) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (by linarith) hfN0
  have hfirst : dot p (M.mulVec p) - dot p (N.mulVec p) ≤
      frobeniusNorm (M - A) + frobeniusNorm (N - A) := by
    rw [e1]
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).1
    nlinarith
  have hsecond : dot (A.mulVec p - N.mulVec p)
      ((coarseDualInvMatrix a U).mulVec (A.mulVec p - N.mulVec p)) ≤
      structuralMatrixConst d Λ * frobeniusNorm (N - A) := by
    refine h3.trans ?_
    rw [e2]
    refine h4.trans ?_
    rw [hfN]
    have := mul_le_mul_of_nonneg_left hp1 (sq_nonneg (frobeniusNorm (N - A)))
    nlinarith
  rw [hJ]
  have hC0 := structuralMatrixConst_nonneg d Λ
  nlinarith

/-- **Proposition 2.11**, (2.29): for `d ≥ 2` and `Λ > 1` there are `α(d, Λ) ∈ (0, ½]` and
`C(d, Λ) < ∞` such that, for every law satisfying (0.10)–(0.11) and every `n ∈ ℕ`,
`sup_{p ∈ B₁} E[J(□_n, p, ā p)] ≤ C 3^{-nα}`, the supremum of a set bounded above of
expectations of integrable variables. -/
theorem proposition_2_11 (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 2 ∧ 0 ≤ C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ n : ℕ,
        (∀ p ∈ originBall d 1, Integrable (fun a =>
          dualityDefect a (triadicCube d n) p ((homogenizedMatrix P).mulVec p)) P) ∧
        BddAbove (Set.range fun p : originBall d 1 =>
          ∫ a, dualityDefect a (triadicCube d n) p ((homogenizedMatrix P).mulVec p) ∂P) ∧
        ⨆ p : originBall d 1,
            ∫ a, dualityDefect a (triadicCube d n) p ((homogenizedMatrix P).mulVec p) ∂P ≤
          C * (3 : ℝ) ^ (-((n : ℝ) * α)) := by
  have : NeZero d := ⟨by omega⟩
  have hΛ0 : 0 ≤ Λ := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨α, hα, hα2, h24⟩ := theorem_2_4 hd hΛ
  obtain ⟨C, hC, hC24⟩ := h24 ((d : ℝ) / 2) (by positivity) (by linarith)
  set Cst := structuralMatrixConst d Λ with hCst
  have hCst0 : 0 ≤ Cst := structuralMatrixConst_nonneg d Λ
  set K := (1 / 2 : ℝ) * (1 + Cst) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨α, K * (3 * C), hα, hα2, by positivity, fun P hP n => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  set A := homogenizedMatrix P with hA
  set U := triadicCube d n with hU
  have hUo := isOpen_triadicCube' (d := d) n
  have hUb := isBounded_triadicCube (d := d) n
  have hUc := convex_triadicCube (d := d) n
  have hne := triadicCube_nonempty (d := d) n
  set X := fun a : CoefficientField d Λ => frobeniusNorm (coarseMatrix a U - A) +
    frobeniusNorm (coarseDualMatrix a U - A) with hX
  have hXm : Measurable X :=
    (measurable_frobeniusNorm_coarseMatrix_sub hΛ0 (volume_triadicCube_ne_top d n) A).add
      (measurable_frobeniusNorm_coarseDualMatrix_sub hΛ0 (volume_triadicCube_ne_zero d n)
        (volume_triadicCube_ne_top d n) A)
  have hXst : ∀ a, X a ≤ Cst := fun a =>
    frobeniusNorm_sub_homogenizedMatrix_add_le hP a hUo hUb hUc hne
  have hX0 : ∀ a, 0 ≤ X a := fun a =>
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hXi : Integrable X P := by
    refine Integrable.of_bound (C := Cst) hXm.aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [Real.norm_of_nonneg (hX0 a)]
    exact hXst a
  -- the expectation of `X` by Theorem 2.4 with `s = d/2`
  have hEX : ∫ a, X a ∂P ≤ 3 * C * (3 : ℝ) ^ (-((n : ℝ) * α)) := by
    have h := (hC24 P hP n).integral_le_add_two_mul hXi
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 : (3 : ℝ) ^ (-((n : ℝ) * α * ((d : ℝ) - (d : ℝ) / 2))) ≤
        (3 : ℝ) ^ (-((n : ℝ) * α)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (n : ℝ) * α * 1 ≤ (n : ℝ) * α * ((d : ℝ) - (d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hn0 hα.le)
      linarith
    have e2 : (3 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) / 2))) ≤ (3 : ℝ) ^ (-((n : ℝ) * α)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (n : ℝ) * α ≤ (n : ℝ) * ((d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hn0
      linarith
    have := mul_le_mul_of_nonneg_left e1 hC.le
    have := mul_le_mul_of_nonneg_left e2 hC.le
    linarith
  have hJb : ∀ p ∈ originBall d 1, ∀ a, 0 ≤ dualityDefect a U p (A.mulVec p) ∧
      dualityDefect a U p (A.mulVec p) ≤ K * X a := fun p hp a => by
    have h := dualityDefect_homogenizedMatrix_le hP a hUo hUb hUc hne hp
    exact ⟨h.1, by rw [hK]; exact h.2⟩
  have hJi : ∀ p ∈ originBall d 1, Integrable (fun a => dualityDefect a U p (A.mulVec p)) P :=
    fun p hp => by
      refine Integrable.of_bound (C := K * Cst)
        (measurable_dualityDefect (volume_triadicCube_ne_zero d n)
          (volume_triadicCube_ne_top d n) hΛ0 p (A.mulVec p)).aestronglyMeasurable
        (Eventually.of_forall fun a => ?_)
      rw [Real.norm_of_nonneg (hJb p hp a).1]
      exact (hJb p hp a).2.trans (mul_le_mul_of_nonneg_left (hXst a) hK0)
  have hEJ : ∀ p ∈ originBall d 1, ∫ a, dualityDefect a U p (A.mulVec p) ∂P ≤
      K * (3 * C) * (3 : ℝ) ^ (-((n : ℝ) * α)) := fun p hp => by
    have h := integral_mono (hJi p hp) (hXi.const_mul K) fun a => (hJb p hp a).2
    rw [integral_const_mul] at h
    have := mul_le_mul_of_nonneg_left hEX hK0
    linarith
  refine ⟨hJi, ⟨K * (3 * C) * (3 : ℝ) ^ (-((n : ℝ) * α)), ?_⟩, ciSup_le fun p => hEJ p p.2⟩
  rintro _ ⟨p, rfl⟩
  exact hEJ p p.2

end QSH
