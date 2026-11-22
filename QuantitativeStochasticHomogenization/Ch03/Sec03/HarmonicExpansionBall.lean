import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionRoot
import QuantitativeStochasticHomogenization.Ch03.Sec03.LinearChangeOfVariables
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct

/-!
# The harmonic expansion on balls

`harmonicExpansionBallStatement` is the expansion of square-integrable weakly harmonic functions
on balls: the part of degree at least two decays like `(t/b)²` in the normalized `L²` norm, and the
slope of the first-order part is at most `C b⁻¹` times the norm. Under `x = M y`, a weakly
`M Mᵀ`-harmonic function `h` on `E_b = M B_b` becomes the weakly harmonic function `h ∘ M` on
`B_b` with weak gradient `Mᵀ (∇h) ∘ M`; normalized `L²` norms are preserved and
`(M⁻¹)ᵀ q · M y = q · y`. Hence the ball statement implies `harmonicExpansionOfRootStatement`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The harmonic expansion on balls** (deterministic). -/
def harmonicExpansionBallStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → ∀ u : Vec d → ℝ,
    IsL2HarmonicOn 1 (ball 0 b) u →
    ∃ (c : ℝ) (q : Vec d),
      (∀ t : ℝ, 0 < t → t < b →
        scalarRms volume (ball 0 t) (fun y => u y - (c + dot q y)) ≤
          (t / b) ^ 2 * scalarRms volume (ball 0 b) u) ∧
      euclideanNorm q ≤ C / b * scalarRms volume (ball 0 b) u

/-- The continuous linear equivalence `y ↦ M y` of an invertible matrix. -/
def matrixCLE (M : Mat d) (hdet : M.det ≠ 0) : Vec d ≃L[ℝ] Vec d :=
  (Matrix.toLinearEquiv' M (M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hdet))).toContinuousLinearEquiv

theorem matrixCLE_apply {M : Mat d} (hdet : M.det ≠ 0) (y : Vec d) :
    matrixCLE M hdet y = M.mulVec y := rfl

theorem fderiv_apply_eq_sum {χ : Vec d → ℝ} (x v : Vec d) :
    fderiv ℝ χ x v = ∑ k, v k * coordinateDerivative k χ x := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : Pi.single k (v k) = v k • unitVector (d := d) k := by
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp [unitVector]
    · simp [unitVector, hjk]
  rw [hs, map_smul, smul_eq_mul]
  rfl

/-- The chain rule for `y ↦ χ (M y)`. -/
theorem coordinateDerivative_comp_mulVec {M : Mat d} (hdet : M.det ≠ 0) (χ : Vec d → ℝ)
    (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun y => χ (M.mulVec y)) y =
      ∑ k, M k i * coordinateDerivative k χ (M.mulVec y) := by
  have h := (matrixCLE M hdet).comp_right_fderiv (f := χ) (x := y)
  unfold coordinateDerivative
  change fderiv ℝ (χ ∘ matrixCLE M hdet) y (unitVector i) = _
  rw [h]
  change fderiv ℝ χ (M.mulVec y) (M.mulVec (unitVector i)) = _
  rw [fderiv_apply_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem gradient_comp_mulVec {M : Mat d} (hdet : M.det ≠ 0) (χ : Vec d → ℝ) (y : Vec d) :
    gradient (fun y => χ (M.mulVec y)) y = M.transpose.mulVec (gradient χ (M.mulVec y)) := by
  funext i
  rw [gradient, coordinateDerivative_comp_mulVec hdet]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, gradient]

/-- Tests on `B_R` correspond to tests on `E_R`. -/
theorem isSpatialTest_comp_symm {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ} {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest (ball 0 R) ψ) :
    IsSpatialTest (matrixEllipsoid M R) (ψ ∘ (matrixCLE M hdet).symm) := by
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

theorem comp_symm_mulVec {M : Mat d} (hdet : M.det ≠ 0) (ψ : Vec d → ℝ) :
    (fun y => (ψ ∘ (matrixCLE M hdet).symm) (M.mulVec y)) = ψ := by
  funext y
  change ψ ((matrixCLE M hdet).symm (matrixCLE M hdet y)) = ψ y
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem locallyIntegrableOn_ball_sum_mul {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ}
    {g : Vec d → Vec d} (hg : ∀ k, LocallyIntegrableOn (fun x => g x k) (matrixEllipsoid M R) volume)
    (w : Fin d → ℝ) :
    LocallyIntegrableOn (fun y => ∑ k, w k * g (M.mulVec y) k) (ball 0 R) volume := by
  rw [locallyIntegrableOn_iff (isOpen_ball_zero R).isLocallyClosed]
  intro K hK hKc
  refine integrable_finsetSum _ fun k _ => ?_
  exact ((LocallyIntegrableOn.comp_matrixEllipsoid hdet (hg k)).integrableOn_compact_subset
    hK hKc).const_mul (w k)

/-- Weak gradients under `y ↦ M y`. -/
theorem HasWeakGradient.comp_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ}
    {h : Vec d → ℝ} {g : Vec d → Vec d} (hh : HasWeakGradient (matrixEllipsoid M R) h g) :
    HasWeakGradient (ball 0 R) (fun y => h (M.mulVec y))
      (fun y => M.transpose.mulVec (g (M.mulVec y))) := by
  intro i
  have hcomp : (fun y => (M.transpose.mulVec (g (M.mulVec y))) i) =
      fun y => ∑ k, M k i * g (M.mulVec y) k := by
    funext y
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine ⟨LocallyIntegrableOn.comp_matrixEllipsoid hdet (hh i).1, ?_, fun ψ hψ => ?_⟩
  · rw [hcomp]
    exact locallyIntegrableOn_ball_sum_mul hdet (fun k => (hh k).2.1) _
  set χ := ψ ∘ (matrixCLE M hdet).symm with hχdef
  have hχ := isSpatialTest_comp_symm hdet hψ
  have hψχ := comp_symm_mulVec hdet ψ
  have hdet0 : |M.det| ≠ 0 := abs_ne_zero.2 hdet
  have hcv : ∀ G : Vec d → ℝ, ∫ y in ball 0 R, G (M.mulVec y) =
      (|M.det|)⁻¹ * ∫ x in matrixEllipsoid M R, G x := by
    intro G
    rw [setIntegral_matrixEllipsoid hdet R G, ← mul_assoc, inv_mul_cancel₀ hdet0, one_mul]
  have hint1 : ∀ k, Integrable (fun x => h x * coordinateDerivative k χ x)
      (volume.restrict (matrixEllipsoid M R)) := fun k =>
    integrableOn_mul_spatialTest (hh k).1 (isSpatialTest_coordinateDerivative hχ k)
  have hint2 : ∀ k, Integrable (fun x => g x k * χ x) (volume.restrict (matrixEllipsoid M R)) :=
    fun k => integrableOn_mul_spatialTest (hh k).2.1 hχ
  have hL : ∫ y in ball 0 R, h (M.mulVec y) * coordinateDerivative i ψ y =
      (|M.det|)⁻¹ * ∑ k, M k i * ∫ x in matrixEllipsoid M R, h x * coordinateDerivative k χ x := by
    have e : (fun y => h (M.mulVec y) * coordinateDerivative i ψ y) = fun y =>
        (fun x => ∑ k, M k i * (h x * coordinateDerivative k χ x)) (M.mulVec y) := by
      funext y
      rw [← hψχ, coordinateDerivative_comp_mulVec hdet, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hcv (fun x => ∑ k, M k i * (h x * coordinateDerivative k χ x)),
      integral_finsetSum _ fun k _ => (hint1 k).const_mul (M k i)]
    simp only [integral_const_mul]
  have hR : ∫ y in ball 0 R, (M.transpose.mulVec (g (M.mulVec y))) i * ψ y =
      (|M.det|)⁻¹ * ∑ k, M k i * ∫ x in matrixEllipsoid M R, g x k * χ x := by
    have e : (fun y => (M.transpose.mulVec (g (M.mulVec y))) i * ψ y) = fun y =>
        (fun x => ∑ k, M k i * (g x k * χ x)) (M.mulVec y) := by
      funext y
      conv_lhs => rw [← hψχ]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hcv (fun x => ∑ k, M k i * (g x k * χ x)),
      integral_finsetSum _ fun k _ => (hint2 k).const_mul (M k i)]
    simp only [integral_const_mul]
  have hk : ∀ k, ∫ x in matrixEllipsoid M R, h x * coordinateDerivative k χ x =
      -∫ x in matrixEllipsoid M R, g x k * χ x := fun k => (hh k).2.2 χ hχ
  rw [hL, hR]
  simp only [hk, mul_neg, Finset.sum_neg_distrib]

/-- Weak `M Mᵀ`-harmonicity on `E_R` is weak harmonicity of `h ∘ M` on `B_R`. -/
theorem HasWeakDivergence.comp_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ}
    {g : Vec d → Vec d}
    (hg : ∀ k, LocallyIntegrableOn (fun x => g x k) (matrixEllipsoid M R) volume)
    (hh : HasWeakDivergence (matrixEllipsoid M R) (fun x => (M * M.transpose).mulVec (g x))
      (fun _ => 0)) :
    HasWeakDivergence (ball 0 R) (fun y => (1 : Mat d).mulVec (M.transpose.mulVec (g (M.mulVec y))))
      (fun _ => 0) := by
  refine ⟨fun i => ?_, locallyIntegrableOn_zero, fun ψ hψ => ?_⟩
  · have hcomp : (fun y => ((1 : Mat d).mulVec (M.transpose.mulVec (g (M.mulVec y)))) i) =
        fun y => ∑ k, M k i * g (M.mulVec y) k := by
      funext y
      rw [Matrix.one_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [hcomp]
    exact locallyIntegrableOn_ball_sum_mul hdet hg _
  set χ := ψ ∘ (matrixCLE M hdet).symm with hχdef
  have hχ := isSpatialTest_comp_symm hdet hψ
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
  have h1 : ∫ y in ball 0 R, (fun x => dot ((M * M.transpose).mulVec (g x)) (gradient χ x))
      (M.mulVec y) = (|M.det|)⁻¹ * ∫ x in matrixEllipsoid M R,
        dot ((M * M.transpose).mulVec (g x)) (gradient χ x) := by
    rw [setIntegral_matrixEllipsoid hdet R
      (fun x => dot ((M * M.transpose).mulVec (g x)) (gradient χ x)), ← mul_assoc,
      inv_mul_cancel₀ hdet0, one_mul]
  rw [e, h1, h0, mul_zero]

/-- `M Mᵀ`-harmonic functions on `E_R` give harmonic functions on `B_R`. -/
theorem IsL2HarmonicOn.comp_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ}
    {h : Vec d → ℝ} (hh : IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M R) h) :
    IsL2HarmonicOn 1 (ball 0 R) (fun y => h (M.mulVec y)) := by
  obtain ⟨hL2, gh, hgL2, hgrad, hdiv⟩ := hh
  rw [matrixEllipsoid_eq_image hdet] at hL2 hgL2
  refine ⟨MemLp.comp_matrixEllipsoid hdet hL2, fun y => M.transpose.mulVec (gh (M.mulVec y)),
    fun i => ?_, hgrad.comp_matrixEllipsoid hdet,
    hdiv.comp_matrixEllipsoid hdet (fun k => (hgrad k).2.1)⟩
  have h : MemLp (fun y => ∑ k, M k i * gh (M.mulVec y) k) 2 (volume.restrict (ball (0 : Vec d) R)) :=
    memLp_finsetSum _ fun k _ => (MemLp.comp_matrixEllipsoid hdet (hgL2 k)).const_mul (M k i)
  refine h.ae_eq (Eventually.of_forall fun y => ?_)
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem dot_inv_transpose_mulVec {M : Mat d} (hdet : M.det ≠ 0) (q y : Vec d) :
    dot ((M⁻¹).transpose.mulVec q) (M.mulVec y) = dot q y := by
  change dotProduct _ _ = dotProduct _ _
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

/-- **The harmonic expansion on ellipsoids from the expansion on balls.** -/
theorem harmonicExpansionOfRoot_of_ball (h : harmonicExpansionBallStatement) :
    harmonicExpansionOfRootStatement := by
  intro d hd M hdet
  obtain ⟨C, hC, hball⟩ := h d hd
  refine ⟨Real.sqrt (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) * C,
    mul_nonneg (Real.sqrt_nonneg _) hC, fun b hb f hf => ?_⟩
  obtain ⟨c, q, hdec, hq⟩ := hball b hb _ (hf.comp_matrixEllipsoid hdet)
  refine ⟨c, (M⁻¹).transpose.mulVec q, fun t ht htb => ?_, ?_⟩
  · rw [scalarRms_matrixEllipsoid_eq hdet t, scalarRms_matrixEllipsoid_eq hdet b]
    have e : (fun y => f (M.mulVec y) - (c + dot ((M⁻¹).transpose.mulVec q) (M.mulVec y))) =
        fun y => f (M.mulVec y) - (c + dot q y) := by
      funext y
      rw [dot_inv_transpose_mulVec hdet]
    rw [e]
    exact hdec t ht htb
  · rw [scalarRms_matrixEllipsoid_eq hdet b]
    calc euclideanNorm ((M⁻¹).transpose.mulVec q)
        ≤ Real.sqrt (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) * euclideanNorm q :=
          euclideanNorm_mulVec_le _ q
      _ ≤ Real.sqrt (∑ i, ∑ j, (M⁻¹).transpose i j ^ 2) *
            (C / b * scalarRms volume (ball 0 b) (fun y => f (M.mulVec y))) :=
          mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
      _ = _ := by ring

/-- **Theorem 3.8, `k = 1`, from the harmonic approximation (2) and the harmonic expansion on
balls.** -/
theorem firstOrderLiouville_of_harmonicApproximation_of_ball
    (h2 : harmonicApproximationStatement) (hB : harmonicExpansionBallStatement) :
    firstOrderLiouvilleStatement :=
  firstOrderLiouville_of_harmonicApproximation_of_root h2 (harmonicExpansionOfRoot_of_ball hB)

end QSH
