import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouvilleReduction
import HCPoly.Geometry.OperatorOrder

/-!
# The harmonic expansion for every invertible change of variables

`harmonicExpansionOfRootStatement` is the expansion of `M Mᵀ`-harmonic functions on the ellipsoids
`E_b = M B_b` for every invertible matrix `M`; after the change of variables `x = M y` it is the
expansion of harmonic functions on balls. It implies `harmonicExpansionStatement`, since the
symmetric part `B = ½(D + Dᵀ)` of a matrix with positive quadratic form is positive definite and
its positive definite square root `M` satisfies `M Mᵀ = M M = B`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The harmonic expansion on ellipsoids** for every invertible change of variables
(deterministic). -/
def harmonicExpansionOfRootStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ M : Mat d, M.det ≠ 0 →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → ∀ h : Vec d → ℝ,
    IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M b) h →
    ∃ (c : ℝ) (p : Vec d),
      (∀ t : ℝ, 0 < t → t < b →
        scalarRms volume (matrixEllipsoid M t) (fun x => h x - (c + dot p x)) ≤
          (t / b) ^ 2 * scalarRms volume (matrixEllipsoid M b) h) ∧
      euclideanNorm p ≤ C / b * scalarRms volume (matrixEllipsoid M b) h

/-- The symmetric part of a matrix with positive quadratic form has an invertible square root. -/
theorem exists_mul_transpose_eq_symmPart {D : Mat d}
    (hD : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (D.mulVec ξ)) :
    ∃ M : Mat d, M.det ≠ 0 ∧ M * M.transpose = (1 / 2 : ℝ) • (D + D.transpose) := by
  set B : Mat d := (1 / 2 : ℝ) • (D + D.transpose) with hB
  have hBt : B.transpose = B := by
    rw [hB, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hDt : ∀ ξ : Vec d, dot ξ (D.transpose.mulVec ξ) = dot ξ (D.mulVec ξ) := by
    intro ξ
    change dotProduct ξ (D.transpose.mulVec ξ) = dotProduct ξ (D.mulVec ξ)
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have hBq : ∀ ξ : Vec d, dot ξ (B.mulVec ξ) = dot ξ (D.mulVec ξ) := by
    intro ξ
    have h := hDt ξ
    change dotProduct ξ (D.transpose.mulVec ξ) = dotProduct ξ (D.mulVec ξ) at h
    change dotProduct ξ (B.mulVec ξ) = dotProduct ξ (D.mulVec ξ)
    rw [hB, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, h,
      smul_eq_mul]
    ring
  have hBpd : B.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hBt
    · rw [star_trivial]
      have h := hD x hx
      rw [← hBq] at h
      exact h
  obtain ⟨hMpsd, hMM⟩ := _root_.Homogenization.HighContrast.matSqrt_spec hBpd.posSemidef
  have hMt : (_root_.Homogenization.HighContrast.matSqrt B).transpose =
      _root_.Homogenization.HighContrast.matSqrt B := by
    have h := hMpsd.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  refine ⟨_root_.Homogenization.HighContrast.matSqrt B, ?_, ?_⟩
  · exact ((Matrix.isUnit_iff_isUnit_det _).1
      (_root_.Homogenization.HighContrast.isUnit_matSqrt hBpd)).ne_zero
  · rw [hMt, hMM]

/-- The harmonic expansion on the ellipsoids of the symmetric part follows from the expansion for
every invertible change of variables. -/
theorem harmonicExpansion_of_root (h : harmonicExpansionOfRootStatement) :
    harmonicExpansionStatement := by
  intro d hd D hD
  obtain ⟨M, hdet, hMM⟩ := exists_mul_transpose_eq_symmPart hD
  obtain ⟨C, hC, hH⟩ := h d hd M hdet
  exact ⟨M, hdet, hMM, C, hC, hH⟩

/-- **Theorem 3.8, `k = 1`, from the harmonic approximation (2) and the expansion of harmonic
functions on ellipsoids.** -/
theorem firstOrderLiouville_of_harmonicApproximation_of_root
    (h2 : harmonicApproximationStatement) (hH : harmonicExpansionOfRootStatement) :
    firstOrderLiouvilleStatement :=
  firstOrderLiouville_of_harmonicApproximation h2 (harmonicExpansion_of_root hH)

end QSH
