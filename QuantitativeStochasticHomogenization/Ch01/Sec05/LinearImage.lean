import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBall
import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipsoidSmoothTransfer

/-!
# Weak derivatives under a linear change of variables on open sets

For an invertible matrix `M` and an open set `S`, the map `y ↦ M y` sends `S` onto `M S`, and
`∫_{M S} g = |det M| ∫_S g ∘ M` (`setIntegral_linearImage`). A weak gradient `g` of `h` on `M S`
gives the weak gradient `Mᵀ g(M ·)` of `h(M ·)` on `S`, and a weakly `M Mᵀ`-harmonic function on
`M S` gives a weakly harmonic function on `S`. These are the statements of
`HasWeakGradient.comp_matrixEllipsoid` and `HasWeakDivergence.comp_matrixEllipsoid` for the
ellipsoids `M B_R`, with the ball replaced by an open set; the proofs are the same. They reduce the
interior estimates (1.61) of Theorem 1.17 for the homogenized matrix to those of harmonic
functions.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ}

theorem linearImage_eq_image {M : Mat d} (hdet : M.det ≠ 0) (S : Set (Vec d)) :
    Matrix.toLin' M '' S = matrixMeasurableEquiv M hdet '' S := rfl

/-- **Change of variables** `∫_{M S} g = |det M| ∫_S g ∘ M`. -/
theorem setIntegral_linearImage {M : Mat d} (hdet : M.det ≠ 0) (S : Set (Vec d))
    (g : Vec d → ℝ) :
    ∫ x in Matrix.toLin' M '' S, g x = |M.det| * ∫ y in S, g (M.mulVec y) := by
  set e := matrixMeasurableEquiv M hdet
  have h := integral_map_equiv e (μ := volume.restrict S) g
  rw [map_restrict_matrixMeasurableEquiv hdet, integral_smul_measure,
    ← linearImage_eq_image hdet, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  have hdet0 : |M.det| ≠ 0 := abs_ne_zero.2 hdet
  rw [abs_inv] at h
  have h2 : ∫ x in Matrix.toLin' M '' S, g x =
      |M.det| * ((|M.det|)⁻¹ • ∫ x in Matrix.toLin' M '' S, g x) := by
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hdet0, one_mul]
  rw [h2, h]
  rfl

theorem LocallyIntegrableOn.comp_linearImage {M : Mat d} (hdet : M.det ≠ 0) {S : Set (Vec d)}
    (hS : IsOpen S) {h : Vec d → ℝ}
    (hh : LocallyIntegrableOn h (Matrix.toLin' M '' S) volume) :
    LocallyIntegrableOn (fun y => h (M.mulVec y)) S volume := by
  set e := matrixMeasurableEquiv M hdet
  rw [locallyIntegrableOn_iff hS.isLocallyClosed]
  intro K hK hKc
  have hsub : e '' K ⊆ Matrix.toLin' M '' S := Set.image_mono hK
  have hcont : Continuous e := (Matrix.toLin' M).continuous_of_finiteDimensional
  have hc : IsCompact (e '' K) := hKc.image hcont
  exact IntegrableOn.comp_matrixEllipsoid hdet (hh.integrableOn_compact_subset hsub hc)

theorem locallyIntegrableOn_sum_mul_linearImage {M : Mat d} (hdet : M.det ≠ 0)
    {S : Set (Vec d)} (hS : IsOpen S) {g : Vec d → Vec d}
    (hg : ∀ k, LocallyIntegrableOn (fun x => g x k) (Matrix.toLin' M '' S) volume)
    (w : Fin d → ℝ) :
    LocallyIntegrableOn (fun y => ∑ k, w k * g (M.mulVec y) k) S volume := by
  rw [locallyIntegrableOn_iff hS.isLocallyClosed]
  intro K hK hKc
  refine integrable_finsetSum _ fun k _ => ?_
  exact ((LocallyIntegrableOn.comp_linearImage hdet hS (hg k)).integrableOn_compact_subset
    hK hKc).const_mul (w k)

/-- Tests on `S` correspond to tests on `M S`. -/
theorem isSpatialTest_comp_symm_linearImage {M : Mat d} (hdet : M.det ≠ 0) {S : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest S ψ) :
    IsSpatialTest (Matrix.toLin' M '' S) (ψ ∘ (matrixCLE M hdet).symm) := by
  set L := matrixCLE M hdet
  have hsupp : Function.support (ψ ∘ L.symm) = L.toHomeomorph '' Function.support ψ := by
    ext x
    constructor
    · intro hx
      exact ⟨L.symm x, hx, L.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change ψ (L.symm (L y)) ≠ 0
      rw [L.symm_apply_apply]
      exact hy
  have hts : tsupport (ψ ∘ L.symm) = L.toHomeomorph '' tsupport ψ := by
    unfold tsupport
    rw [hsupp, L.toHomeomorph.image_closure]
  refine ⟨hψ.1.comp L.symm.contDiff, ?_, ?_⟩
  · show IsCompact (tsupport (ψ ∘ L.symm))
    rw [hts]
    exact hψ.2.1.image L.toHomeomorph.continuous
  · rw [hts]
    exact Set.image_mono hψ.2.2

/-- **Weak gradients under `y ↦ M y`** on an open set. -/
theorem HasWeakGradient.comp_linearImage {M : Mat d} (hdet : M.det ≠ 0) {S : Set (Vec d)}
    (hS : IsOpen S) {h : Vec d → ℝ} {g : Vec d → Vec d}
    (hh : HasWeakGradient (Matrix.toLin' M '' S) h g) :
    HasWeakGradient S (fun y => h (M.mulVec y))
      (fun y => M.transpose.mulVec (g (M.mulVec y))) := by
  intro i
  have hcomp : (fun y => (M.transpose.mulVec (g (M.mulVec y))) i) =
      fun y => ∑ k, M k i * g (M.mulVec y) k := by
    funext y
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine ⟨LocallyIntegrableOn.comp_linearImage hdet hS (hh i).1, ?_, fun ψ hψ => ?_⟩
  · rw [hcomp]
    exact locallyIntegrableOn_sum_mul_linearImage hdet hS (fun k => (hh k).2.1) _
  set χ := ψ ∘ (matrixCLE M hdet).symm with hχdef
  have hχ := isSpatialTest_comp_symm_linearImage hdet hψ
  have hψχ := comp_symm_mulVec hdet ψ
  have hdet0 : |M.det| ≠ 0 := abs_ne_zero.2 hdet
  have hcv : ∀ G : Vec d → ℝ, ∫ y in S, G (M.mulVec y) =
      (|M.det|)⁻¹ * ∫ x in Matrix.toLin' M '' S, G x := by
    intro G
    rw [setIntegral_linearImage hdet S G, ← mul_assoc, inv_mul_cancel₀ hdet0, one_mul]
  have hint1 : ∀ k, Integrable (fun x => h x * coordinateDerivative k χ x)
      (volume.restrict (Matrix.toLin' M '' S)) := fun k =>
    integrableOn_mul_spatialTest (hh k).1 (isSpatialTest_coordinateDerivative hχ k)
  have hint2 : ∀ k, Integrable (fun x => g x k * χ x)
      (volume.restrict (Matrix.toLin' M '' S)) :=
    fun k => integrableOn_mul_spatialTest (hh k).2.1 hχ
  have hL : ∫ y in S, h (M.mulVec y) * coordinateDerivative i ψ y =
      (|M.det|)⁻¹ * ∑ k, M k i *
        ∫ x in Matrix.toLin' M '' S, h x * coordinateDerivative k χ x := by
    have e : (fun y => h (M.mulVec y) * coordinateDerivative i ψ y) = fun y =>
        (fun x => ∑ k, M k i * (h x * coordinateDerivative k χ x)) (M.mulVec y) := by
      funext y
      rw [← hψχ, coordinateDerivative_comp_mulVec hdet, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hcv (fun x => ∑ k, M k i * (h x * coordinateDerivative k χ x)),
      integral_finsetSum _ fun k _ => (hint1 k).const_mul (M k i)]
    simp only [integral_const_mul]
  have hR : ∫ y in S, (M.transpose.mulVec (g (M.mulVec y))) i * ψ y =
      (|M.det|)⁻¹ * ∑ k, M k i * ∫ x in Matrix.toLin' M '' S, g x k * χ x := by
    have e : (fun y => (M.transpose.mulVec (g (M.mulVec y))) i * ψ y) = fun y =>
        (fun x => ∑ k, M k i * (g x k * χ x)) (M.mulVec y) := by
      funext y
      conv_lhs => rw [← hψχ]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hcv (fun x => ∑ k, M k i * (g x k * χ x)),
      integral_finsetSum _ fun k _ => (hint2 k).const_mul (M k i)]
    simp only [integral_const_mul]
  have hk : ∀ k, ∫ x in Matrix.toLin' M '' S, h x * coordinateDerivative k χ x =
      -∫ x in Matrix.toLin' M '' S, g x k * χ x := fun k => (hh k).2.2 χ hχ
  rw [hL, hR]
  simp only [hk, mul_neg, Finset.sum_neg_distrib]

/-- **Weak `M Mᵀ`-harmonicity on `M S` is weak harmonicity of `h ∘ M` on `S`.** -/
theorem HasWeakDivergence.comp_linearImage {M : Mat d} (hdet : M.det ≠ 0) {S : Set (Vec d)}
    (hS : IsOpen S) {g : Vec d → Vec d}
    (hg : ∀ k, LocallyIntegrableOn (fun x => g x k) (Matrix.toLin' M '' S) volume)
    (hh : HasWeakDivergence (Matrix.toLin' M '' S) (fun x => (M * M.transpose).mulVec (g x))
      (fun _ => 0)) :
    HasWeakDivergence S (fun y => (1 : Mat d).mulVec (M.transpose.mulVec (g (M.mulVec y))))
      (fun _ => 0) := by
  refine ⟨fun i => ?_, locallyIntegrableOn_zero, fun ψ hψ => ?_⟩
  · have hcomp : (fun y => ((1 : Mat d).mulVec (M.transpose.mulVec (g (M.mulVec y)))) i) =
        fun y => ∑ k, M k i * g (M.mulVec y) k := by
      funext y
      rw [Matrix.one_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [hcomp]
    exact locallyIntegrableOn_sum_mul_linearImage hdet hS hg _
  set χ := ψ ∘ (matrixCLE M hdet).symm with hχdef
  have hχ := isSpatialTest_comp_symm_linearImage hdet hψ
  have hψχ := comp_symm_mulVec hdet ψ
  have hdet0 : |M.det| ≠ 0 := abs_ne_zero.2 hdet
  have h0 := hh.2.2 χ hχ
  simp only [zero_mul, integral_zero, neg_zero] at h0 ⊢
  have e : (fun y => dot ((1 : Mat d).mulVec (M.transpose.mulVec (g (M.mulVec y))))
      (gradient ψ y)) = fun y =>
        (fun x => dot ((M * M.transpose).mulVec (g x)) (gradient χ x)) (M.mulVec y) := by
    funext y
    rw [← hψχ, gradient_comp_mulVec hdet, Matrix.one_mulVec]
    change dotProduct _ _ = dotProduct _ _
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec]
  have h1 : ∫ y in S, (fun x => dot ((M * M.transpose).mulVec (g x)) (gradient χ x))
      (M.mulVec y) = (|M.det|)⁻¹ * ∫ x in Matrix.toLin' M '' S,
        dot ((M * M.transpose).mulVec (g x)) (gradient χ x) := by
    rw [setIntegral_linearImage hdet S
      (fun x => dot ((M * M.transpose).mulVec (g x)) (gradient χ x)), ← mul_assoc,
      inv_mul_cancel₀ hdet0, one_mul]
  rw [e, h1, h0, mul_zero]

/-- The weak equation of an `H¹` function, as an `H¹` function of the elliptic regularity library
which is weakly harmonic on an open set. -/
theorem isWeakDivergenceFormSolutionOn_toH1FunctionOn {U : Set (Vec d)} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g)
    (hdiv : HasWeakDivergence U (fun x => (1 : Mat d).mulVec (g x)) (fun _ => 0)) :
    PDE.IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) U
      (toH1FunctionOn hu hg hw) 0 0 := by
  intro φ
  have hdata : PDE.DivergenceFormL2DataOn (fun _ => (1 : Mat d)) U
      (toH1FunctionOn hu hg hw) 0 0 := by
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have h := (toH1FunctionOn hu hg hw).gradMemL2 i
      refine h.ae_eq (Eventually.of_forall fun x => ?_)
      simp [PDE.matVecMul, Matrix.one_apply, toH1FunctionOn]
    · exact MemLp.zero
    · exact MemLp.zero
  refine ⟨hdata.testable φ, ?_⟩
  have htest : IsSpatialTest U φ.toFun := ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  have h := hdiv.2.2 φ.toFun htest
  simp only [zero_mul, integral_zero, neg_zero] at h
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  have e : ∫ x in U,
      PDE.vecDot (PDE.matVecMul ((fun _ => (1 : Mat d)) x) ((toH1FunctionOn hu hg hw).grad x))
        (φ.grad x) =
      ∫ x in U, dot ((1 : Mat d).mulVec (g x)) (gradient φ.toFun x) :=
    rfl
  rw [e, h]
  simp [PDE.vecDot]

end TwoScale

end QSH
