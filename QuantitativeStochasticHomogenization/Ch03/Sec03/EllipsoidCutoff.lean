import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBallProof
import PDEFoundation.Sobolev.Cutoff.Ball

/-!
# Smooth cutoffs between ellipsoids

For an invertible matrix `M` and `0 < r < R`, the ball cutoff `χ` between `B_r` and `B_R`
composed with `M⁻¹` is a smooth cutoff between the ellipsoids `E_r = M B_r` and `E_R`, with
gradient `(M⁻¹)ᵀ ∇χ(M⁻¹ x)` of size at most `‖(M⁻¹)ᵀ‖_F · 32 / (R - r)`. This is the cutoff of the
Caccioppoli inequality on ellipsoids used in the harmonic approximation (2).
-/

open MeasureTheory Set Filter

noncomputable section

namespace QSH

variable {d : ℕ}

theorem matrixCLE_symm_apply {M : Mat d} (hdet : M.det ≠ 0) (x : Vec d) :
    (matrixCLE M hdet).symm x = M⁻¹.mulVec x := by
  have h : matrixCLE M hdet (M⁻¹.mulVec x) = x := by
    rw [matrixCLE_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  calc (matrixCLE M hdet).symm x = (matrixCLE M hdet).symm (matrixCLE M hdet (M⁻¹.mulVec x)) := by
        rw [h]
    _ = M⁻¹.mulVec x := ContinuousLinearEquiv.symm_apply_apply _ _

/-- The smooth cutoff between the ellipsoids `E_r` and `E_R`. -/
def ellipsoidCutoff {M : Mat d} (hdet : M.det ≠ 0) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    PDE.QuantitativeSmoothCutoff (matrixEllipsoid M r) (matrixEllipsoid M R)
      (Real.sqrt (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) * (32 / (R - r))) where
  toFun := (PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR).toFun ∘ (matrixCLE M hdet).symm
  smooth := (PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR).smooth.comp
    (matrixCLE M hdet).symm.contDiff
  hasCompactSupport := by
    set χ := PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR
    set L := matrixCLE M hdet
    have hsupp : Function.support (χ.toFun ∘ L.symm) = L.toHomeomorph '' Function.support χ.toFun := by
      ext x
      constructor
      · intro hx
        exact ⟨L.symm x, hx, L.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change χ.toFun (L.symm (L y)) ≠ 0
        rw [L.symm_apply_apply]
        exact hy
    show IsCompact (tsupport (χ.toFun ∘ L.symm))
    unfold tsupport
    rw [hsupp, ← L.toHomeomorph.image_closure]
    exact χ.hasCompactSupport.image L.toHomeomorph.continuous
  tsupport_subset := by
    set χ := PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR
    set L := matrixCLE M hdet
    have hsupp : Function.support (χ.toFun ∘ L.symm) = L.toHomeomorph '' Function.support χ.toFun := by
      ext x
      constructor
      · intro hx
        exact ⟨L.symm x, hx, L.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change χ.toFun (L.symm (L y)) ≠ 0
        rw [L.symm_apply_apply]
        exact hy
    unfold tsupport
    rw [hsupp, ← L.toHomeomorph.image_closure]
    have h : tsupport χ.toFun ⊆ ball 0 R := by
      rw [ball_zero_eq_pdeEuclideanBall (hr.trans hrR)]
      exact χ.tsupport_subset
    exact Set.image_mono h
  nonneg := fun x => (PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR).nonneg _
  le_one := fun x => (PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR).le_one _
  eq_one_on_inner := by
    rintro _ ⟨y, hy, rfl⟩
    change (PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR).toFun
      ((matrixCLE M hdet).symm (matrixCLE M hdet y)) = 1
    rw [ContinuousLinearEquiv.symm_apply_apply]
    refine (PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR).eq_one_on_inner y ?_
    rw [← ball_zero_eq_pdeEuclideanBall hr]
    exact hy
  gradient_bound := by
    intro x
    set χ := PDE.quantitativeBallCutoff (0 : Vec d) hr.le hrR
    have hdet' : (M⁻¹).det ≠ 0 :=
      (Matrix.isUnit_nonsing_inv_det M (isUnit_iff_ne_zero.2 hdet)).ne_zero
    have hfun : χ.toFun ∘ (matrixCLE M hdet).symm = fun y => χ.toFun (M⁻¹.mulVec y) := by
      funext y
      simp only [Function.comp, matrixCLE_symm_apply]
    have hg : PDE.classicalGradient (χ.toFun ∘ (matrixCLE M hdet).symm) x =
        (M⁻¹).transpose.mulVec (gradient χ.toFun (M⁻¹.mulVec x)) := by
      rw [hfun]
      exact gradient_comp_mulVec hdet' χ.toFun x
    have hb := χ.gradient_bound (M⁻¹.mulVec x)
    change euclideanNorm _ ≤ _
    rw [hg]
    refine (euclideanNorm_mulVec_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

end QSH
