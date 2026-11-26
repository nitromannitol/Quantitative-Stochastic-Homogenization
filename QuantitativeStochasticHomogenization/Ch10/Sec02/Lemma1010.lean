import QuantitativeStochasticHomogenization.Ch10.Sec02.QuantitiesBridge

/-!
# Lemma 10.10: basic properties of `J`

Armstrong–Kuusi–Mourrat, Chapter 10, Section 10.2, on a bounded open convex domain `D`, from the
block-matrix theory of the coarse-graining library (Armstrong and Kuusi,
`BlockCoarseMatrixTheory`, `DoubledResponseTheory`):

* the representation as a quadratic form (10.41), with the matrices `A(D)` (`coarseMatrix`) and
  `A*(D)⁻¹` (`coarseStarInv`), both positive definite, `A*(D)⁻¹` the inverse of `A*(D)`
  (`coarseStar`);
* existence and uniqueness (a.e.) of the maximizer `S(·, D, X, X*)`;
* the first variation (10.45) of the maximizer.

The matrices are 2×2 block matrices of `d×d` matrices (`Homogenization.BlockMat d`), that is,
`2d×2d` matrices, and `X = (p, q)`, `X* = (q*, p*)` as in (10.21).
-/

open MeasureTheory

namespace QSH

variable {d : ℕ} {Λ : ℝ}

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ) (D : _root_.Homogenization.Book.Ch02.Domain d)

/-- The coarse-grained matrix `A(D)` of (10.40)–(10.41). -/
noncomputable def coarseMatrix : _root_.Homogenization.BlockMat d :=
  _root_.Homogenization.Book.Ch02.coarseBlockMatrix D (a.toCGCoeffOn D)

/-- The matrix `A*(D)⁻¹` of (10.41). -/
noncomputable def coarseStarInv : _root_.Homogenization.BlockMat d :=
  _root_.Homogenization.Book.Ch02.coarseStarredBlockMatrixInv D (a.toCGCoeffOn D)

/-- The matrix `A*(D)` of (10.40). -/
noncomputable def coarseStar : _root_.Homogenization.BlockMat d :=
  _root_.Homogenization.Book.Ch02.coarseStarredBlockMatrix D (a.toCGCoeffOn D)

/-- **Lemma 10.10, (10.41)**: `J(D, X, X*) = ½ X·A(D)X + ½ X*·A*(D)⁻¹X* - X·X*`. -/
theorem lemma_10_10_quadratic (p q qs ps : Vec d) :
    a.doubleJ D p q qs ps =
      (1 / 2 : ℝ) * _root_.Homogenization.blockVecDot (p, q)
          (_root_.Homogenization.blockMatVecMul (a.coarseMatrix D) (p, q)) +
        (1 / 2 : ℝ) * _root_.Homogenization.blockVecDot (qs, ps)
          (_root_.Homogenization.blockMatVecMul (a.coarseStarInv D) (qs, ps)) -
        (dot p qs + dot q ps) := by
  rw [a.doubleJ_eq D,
    (_root_.Homogenization.Book.Ch02.blockCoarseMatrixTheory D
      (a.toCGCoeffOn D)).doubled_response_splitting]
  rfl

/-- **Lemma 10.10**: `A(D)`, `A*(D)` and `A*(D)⁻¹` are positive definite, and `A*(D)⁻¹` is the
inverse of `A*(D)`. -/
theorem lemma_10_10_posDef :
    _root_.Homogenization.Book.Ch02.BlockPosDef (a.coarseMatrix D) ∧
      _root_.Homogenization.Book.Ch02.BlockPosDef (a.coarseStar D) ∧
      _root_.Homogenization.Book.Ch02.BlockPosDef (a.coarseStarInv D) ∧
      _root_.Homogenization.Book.Ch02.blockMatMul (a.coarseStar D) (a.coarseStarInv D) =
        _root_.Homogenization.Book.Ch02.blockIdentity d ∧
      _root_.Homogenization.Book.Ch02.blockMatMul (a.coarseStarInv D) (a.coarseStar D) =
        _root_.Homogenization.Book.Ch02.blockIdentity d :=
  let h := _root_.Homogenization.Book.Ch02.blockCoarseMatrixTheory D (a.toCGCoeffOn D)
  ⟨h.block_matrix_posDef, h.starred_matrix_posDef, h.starred_inverse_posDef,
    h.starred_left_inverse, h.starred_right_inverse⟩

/-- **Lemma 10.10**: the maximizer `S(·, D, X, X*)` of (10.20) exists. -/
theorem exists_isResponseMaximizer (p q qs ps : Vec d) :
    ∃ S₁ S₂ : Vec d → Vec d, a.IsResponseMaximizer D p q qs ps S₁ S₂ := by
  obtain ⟨X, hX⟩ :=
    (_root_.Homogenization.Book.Ch02.doubledResponseTheory D (a.toCGCoeffOn D)).maximizer_exists
      (p, q) (qs, ps)
  exact ⟨X.potential, X.flux, (a.isResponseMaximizer_iff D _ _ _ _ _ _).2 hX⟩

/-- **Lemma 10.10**: the maximizer of (10.20) is unique up to null sets. -/
theorem isResponseMaximizer_unique {p q qs ps : Vec d} {S₁ S₂ T₁ T₂ : Vec d → Vec d}
    (hS : a.IsResponseMaximizer D p q qs ps S₁ S₂) (hT : a.IsResponseMaximizer D p q qs ps T₁ T₂) :
    S₁ =ᵐ[volume.restrict D] T₁ ∧ S₂ =ᵐ[volume.restrict D] T₂ :=
  (_root_.Homogenization.Book.Ch02.doubledResponseTheory D (a.toCGCoeffOn D)).maximizer_unique_ae
    (p, q) (qs, ps) ⟨S₁, S₂⟩ ⟨T₁, T₂⟩ ((a.isResponseMaximizer_iff D _ _ _ _ _ _).1 hS)
    ((a.isResponseMaximizer_iff D _ _ _ _ _ _).1 hT)

/-- **Lemma 10.10, first variation (10.45)**: for the maximizer `S = S(·, D, X, X*)` and every
`T ∈ S(D)`, `⨍_D T·AS = ⨍_D (-X·AT + X*·T)`. -/
theorem lemma_10_10_firstVariation {p q qs ps : Vec d} {S₁ S₂ T₁ T₂ : Vec d → Vec d}
    (hS : a.IsResponseMaximizer D p q qs ps S₁ S₂) (hT : a.IsResponseField D T₁ T₂) :
    ⨍ x in (D : Set (Vec d)), representativePairing (a x) (T₁ x) (T₂ x) (S₁ x) (S₂ x) =
      ⨍ x in (D : Set (Vec d)), (-representativePairing (a x) p q (T₁ x) (T₂ x) +
        (dot qs (T₁ x) + dot ps (T₂ x))) := by
  have h := (_root_.Homogenization.Book.Ch02.doubledResponseTheory D
    (a.toCGCoeffOn D)).first_variation (p, q) (qs, ps) ⟨S₁, S₂⟩ ⟨T₁, T₂⟩
    ((a.isResponseMaximizer_iff D _ _ _ _ _ _).1 hS) ((a.isResponseField_iff D _ _).1 hT)
  rw [cgAverage_eq_setAverage, cgAverage_eq_setAverage] at h
  simp only [_root_.Homogenization.Book.Ch02.DoubledField.eval, blockVecDot_blockMatrixField a] at h
  rw [← h]
  congr 1
  funext x
  simp only [_root_.Homogenization.blockVecDot]
  unfold _root_.Homogenization.vecDot dot
  ring

end GeneralCoefficientField

end QSH
