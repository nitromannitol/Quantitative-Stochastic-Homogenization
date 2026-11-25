import QuantitativeStochasticHomogenization.Ch02.Sec02.Proposition211

/-!
# The lower bound and the inverse of the homogenized matrix

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(1.25): `|e|² ≤ e · ā e`. Consequently `ā` is invertible, `ā (ā⁻¹ q) = q`, and
`|ā⁻¹ q| ≤ |q|`, as used for `ā⁻¹ q` in the proof of Theorem 2.17.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The lower bound of (1.25)**: `|e|² ≤ e · ā e`. -/
theorem euclideanSq_le_dot_homogenizedMatrix {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (e : Vec d) :
    euclideanSq e ≤ dot e ((homogenizedMatrix P).mulVec e) := by
  have : IsProbabilityMeasure P := hP.1
  have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ e
  have hle : (1 / 2 : ℝ) * euclideanSq e ≤ limitDirichletEnergy P e := by
    refine le_ciInf fun n => ?_
    have h1 : ∫ _a : CoefficientField d Λ, (1 / 2 : ℝ) * euclideanSq e ∂P ≤
        expectedDirichletEnergy P n e :=
      integral_mono (integrable_const _) (integrable_dirichletEnergy_triadicCube hΛ n e)
        fun a => le_dirichletEnergy a (volume_triadicCube_ne_zero d n)
          (volume_triadicCube_ne_top d n) e
    rwa [integral_const, probReal_univ, one_smul] at h1
  linarith

theorem euclideanSq_le_euclideanSq_homogenizedMatrix_mulVec {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (e : Vec d) :
    euclideanSq e ≤ euclideanSq ((homogenizedMatrix P).mulVec e) := by
  have h1 := euclideanSq_le_dot_homogenizedMatrix hP hΛ e
  have hcs : dot e ((homogenizedMatrix P).mulVec e) ^ 2 ≤
      euclideanSq e * euclideanSq ((homogenizedMatrix P).mulVec e) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e ((homogenizedMatrix P).mulVec e)
    simpa only [euclideanSq, dot, sq] using h
  have h0 : 0 ≤ euclideanSq e := euclideanSq_nonneg e
  rcases h0.eq_or_lt with he | he
  · rw [← he]
    exact euclideanSq_nonneg _
  · nlinarith

theorem eq_zero_of_euclideanSq_nonpos {x : Vec d} (h : euclideanSq x ≤ 0) : x = 0 := by
  funext i
  have h1 : x i * x i ≤ euclideanSq x :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  have : x i * x i = 0 := le_antisymm (h1.trans h) (mul_self_nonneg _)
  simpa using mul_self_eq_zero.1 this

/-- `ā (ā⁻¹ q) = q`. -/
theorem homogenizedMatrix_mulVec_inv_mulVec {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (q : Vec d) :
    (homogenizedMatrix P).mulVec ((homogenizedMatrix P)⁻¹.mulVec q) = q := by
  have hinj : Function.Injective (homogenizedMatrix P).mulVec := by
    intro x y hxy
    have h := euclideanSq_le_euclideanSq_homogenizedMatrix_mulVec hP hΛ (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self] at h
    have h0 : euclideanSq (0 : Vec d) = 0 := by simp [euclideanSq, dot]
    rw [h0] at h
    exact sub_eq_zero.1 (eq_zero_of_euclideanSq_nonpos h)
  have hu : IsUnit (homogenizedMatrix P) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
    Matrix.one_mulVec]

/-- `|ā⁻¹ q| ≤ |q|`. -/
theorem euclideanSq_homogenizedMatrix_inv_mulVec_le {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (q : Vec d) :
    euclideanSq ((homogenizedMatrix P)⁻¹.mulVec q) ≤ euclideanSq q := by
  have h := euclideanSq_le_euclideanSq_homogenizedMatrix_mulVec hP hΛ
    ((homogenizedMatrix P)⁻¹.mulVec q)
  rwa [homogenizedMatrix_mulVec_inv_mulVec hP hΛ q] at h

end QSH
