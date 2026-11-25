import QuantitativeStochasticHomogenization.Ch10.Sec01.Proposition103
import QuantitativeStochasticHomogenization.Ch02.Sec01.DualMaximizer
import Homogenization.Book.Ch02.Theorems.DoubledResponse
import Homogenization.Book.Ch02.Theorems.DoubledMu

/-!
# Fields of `Ω` (10.2) as coefficient fields of the coarse-graining library

Armstrong–Kuusi–Mourrat, Chapter 10, Section 10.2. The double-variable framework of the
coarse-graining library (Armstrong and Kuusi, `Homogenization.Book.Ch02`, the doubled fields,
`S(U)`, `μ` and `J` for not necessarily symmetric coefficients on bounded open convex domains) is
used in this section. This file gives:

* `GeneralCoefficientField.isEllipticMatrix`: a field of `Ω` satisfies the ellipticity condition of
  the library with constants `1` and `max(Λ², 1)` (`|a ξ|² ≤ Λ² |ξ|² ≤ Λ² ξ·aξ`);
* `GeneralCoefficientField.toCGCoeffOn`: the field as a `CoeffOn D` on a domain `D` of the library;
* `blockVecDot_blockMatrixField`: the block pairing `X'·A(x) X` of the library is the bilinear form
  `representativePairing` of (10.7) (the matrix `A(x)` displayed before (10.19)).
-/

open MeasureTheory Matrix Filter

namespace QSH

variable {d : ℕ} {Λ : ℝ}

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ)

/-- `a(x)` is invertible. -/
theorem isUnit_det (x : Vec d) : IsUnit (a x).det :=
  isUnit_det_of_euclideanSq_le (fun ξ => (a.elliptic x ξ).1)

/-- **The ellipticity of a field of `Ω` in the form of the coarse-graining library**:
`|ξ|² ≤ ξ·a(x)ξ` and `max(Λ², 1)⁻¹ |ξ|² ≤ ξ·a(x)⁻¹ξ`. -/
theorem isEllipticMatrix (x : Vec d) :
    _root_.Homogenization.IsEllipticMatrix 1 (max (Λ ^ 2) 1) (a.field x) := by
  have hL : (0 : ℝ) < max (Λ ^ 2) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨one_pos, le_max_right _ _, fun ξ => ?_, fun ξ => ?_⟩
  · have h := (a.elliptic x ξ).1
    simpa [_root_.Homogenization.vecDot, _root_.Homogenization.vecNormSq,
      _root_.Homogenization.matVecMul, euclideanSq, dot, Matrix.mulVec, dotProduct] using h
  · -- `η = a⁻¹ ξ` has `a η = ξ`, so `ξ·a⁻¹ξ = η·aη ≥ |η|² ≥ Λ⁻²|aη|²`
    set η : Vec d := (a x)⁻¹.mulVec ξ with hη
    have hdet := a.isUnit_det x
    have hξ : (a x).mulVec η = ξ := by
      rw [hη, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have h1 := (a.elliptic x η).1
    have h2 := (a.elliptic x η).2
    rw [hξ] at h1 h2
    have hsq : euclideanSq ξ ≤ Λ ^ 2 * euclideanSq η := by
      have hn0 := euclideanNorm_nonneg ξ
      have hΛn : 0 ≤ Λ * euclideanNorm η := hn0.trans h2
      rw [← euclideanNorm_mul_self ξ, ← euclideanNorm_mul_self η]
      nlinarith [mul_le_mul h2 h2 hn0 hΛn]
    have hsq' : euclideanSq ξ ≤ max (Λ ^ 2) 1 * euclideanSq η :=
      hsq.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (euclideanSq_nonneg _))
    have hcomm : dot η ξ = dot ξ η := dotProduct_comm _ _
    have hgoal : (max (Λ ^ 2) 1)⁻¹ * euclideanSq ξ ≤ dot ξ η := by
      rw [inv_mul_le_iff₀ hL]
      rw [← hcomm]
      nlinarith
    simpa [_root_.Homogenization.vecDot, _root_.Homogenization.vecNormSq,
      _root_.Homogenization.matVecMul, euclideanSq, dot, Matrix.mulVec, dotProduct, hη] using hgoal

/-- **A field of `Ω` as a coefficient field of the coarse-graining library** on a domain `D`, with
the ellipticity constants `1` and `max(Λ², 1)`. -/
def toCGCoeffOn (D : _root_.Homogenization.Book.Ch02.Domain d) :
    _root_.Homogenization.Book.Ch02.CoeffOn D where
  toCoeffField := a.field
  lam := 1
  Lam := max (Λ ^ 2) 1
  lam_pos := one_pos
  lam_le_Lam := le_max_right _ _
  aeStronglyMeasurable := fun i j => by
    refine ((a.aestronglyMeasurable i j).restrict).congr ?_
    filter_upwards [ae_restrict_mem D.measurableSet] with x hx
    rw [_root_.Homogenization.restrictCoeffField_apply_of_mem hx]
  aeElliptic := Eventually.of_forall fun x => a.isEllipticMatrix x

@[simp] theorem toCGCoeffOn_apply (D : _root_.Homogenization.Book.Ch02.Domain d) (x : Vec d) :
    (a.toCGCoeffOn D).toCoeffField x = a x :=
  rfl

theorem symmPart_eq (M : Mat d) : _root_.Homogenization.symmPart M = symmetricPart M := by
  ext i j
  simp only [_root_.Homogenization.symmPart, symmetricPart, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

theorem skewPart_eq (M : Mat d) : _root_.Homogenization.skewPart M = antisymmetricPart M := by
  ext i j
  simp only [_root_.Homogenization.skewPart, antisymmetricPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

end GeneralCoefficientField

/-- **The block matrix of (10.19)**: for a matrix `a` with invertible symmetric part, the block
pairing `(p', q')·A (p, q)` with `A = [[s - m s⁻¹ m, m s⁻¹], [-s⁻¹ m, s⁻¹]]` (the library's
`blockMatrixField`, written with `k = m` and `kᵀ = -m`) is `representativePairing a p' q' p q`. -/
theorem blockVecDot_blockMatrixField {D : _root_.Homogenization.Book.Ch02.Domain d}
    (a : GeneralCoefficientField d Λ) (x p' q' p q : Vec d) :
    _root_.Homogenization.blockVecDot (p', q')
        (_root_.Homogenization.blockMatVecMul
          (_root_.Homogenization.Book.Ch02.blockMatrixField (a.toCGCoeffOn D) x) (p, q)) =
      representativePairing (a x) p' q' p q := by
  simp only [_root_.Homogenization.Book.Ch02.blockMatrixField, a.toCGCoeffOn_apply,
    GeneralCoefficientField.symmPart_eq, GeneralCoefficientField.skewPart_eq,
    _root_.Homogenization.blockVecDot, _root_.Homogenization.blockMatVecMul,
    representativePairing]
  set s := symmetricPart (a x)
  set m := antisymmetricPart (a x)
  have hmT : (m : Mat d).transpose = -m := by
    simp only [m, antisymmetricPart, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.transpose_transpose]
    rw [← smul_neg, neg_sub]
  change _root_.Homogenization.vecDot p' (_root_.Homogenization.matVecMul
        (s + _root_.Homogenization.matTranspose m * s⁻¹ * m) p +
          _root_.Homogenization.matVecMul (-(_root_.Homogenization.matTranspose m * s⁻¹)) q) +
      _root_.Homogenization.vecDot q' (_root_.Homogenization.matVecMul (-(s⁻¹ * m)) p +
          _root_.Homogenization.matVecMul s⁻¹ q) =
    dot p' (s.mulVec p) + dot (q' - m.mulVec p') (s⁻¹.mulVec (q - m.mulVec p))
  have hmv : ∀ (M : Mat d) (v : Vec d), _root_.Homogenization.matVecMul M v = M.mulVec v :=
    fun M v => rfl
  have hvd : ∀ (v w : Vec d), _root_.Homogenization.vecDot v w = v ⬝ᵥ w := fun v w => rfl
  have hdd : ∀ (v w : Vec d), dot v w = v ⬝ᵥ w := fun v w => rfl
  simp only [hmv, hvd, hdd, _root_.Homogenization.matTranspose, hmT]
  have htr : ∀ (M : Mat d) (u v : Vec d), (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (M.transpose *ᵥ v) :=
    fun M u v => by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.neg_mul, Matrix.mulVec_sub, dotProduct_add, dotProduct_neg, dotProduct_sub,
    sub_dotProduct]
  have h1 : (m *ᵥ p') ⬝ᵥ (s⁻¹ *ᵥ (m *ᵥ p)) = -(p' ⬝ᵥ (m *ᵥ (s⁻¹ *ᵥ (m *ᵥ p)))) := by
    rw [htr, hmT, Matrix.neg_mulVec, dotProduct_neg]
  have h2 : (m *ᵥ p') ⬝ᵥ (s⁻¹ *ᵥ q) = -(p' ⬝ᵥ (m *ᵥ (s⁻¹ *ᵥ q))) := by
    rw [htr, hmT, Matrix.neg_mulVec, dotProduct_neg]
  rw [h1, h2]
  ring

end QSH
