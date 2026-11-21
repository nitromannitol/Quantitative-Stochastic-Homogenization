import QuantitativeStochasticHomogenization.Ch03.Sec03.ScalarRmsCalculus

/-!
# Linear changes of variables on ellipsoids

For an invertible matrix `M`, the map `y ↦ M y` sends the ball `B_R` onto the ellipsoid
`E_R = M B_R` and the restriction of the Lebesgue measure to `B_R` to `|det M|⁻¹` times its
restriction to `E_R`. Hence `∫_{E_R} g = |det M| ∫_{B_R} g ∘ M`, normalized `L²` norms agree,
`‖f‖_{L̲²(E_R)} = ‖f ∘ M‖_{L̲²(B_R)}`, and square integrability and local integrability pass from
`E_R` to `B_R`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The measurable equivalence `y ↦ M y` of an invertible matrix. -/
def matrixMeasurableEquiv (M : Mat d) (hdet : M.det ≠ 0) : Vec d ≃ᵐ Vec d :=
  ((Matrix.toLinearEquiv' M (M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hdet))).toContinuousLinearEquiv.toHomeomorph).toMeasurableEquiv

theorem matrixMeasurableEquiv_apply {M : Mat d} (hdet : M.det ≠ 0) (y : Vec d) :
    matrixMeasurableEquiv M hdet y = M.mulVec y := rfl

theorem matrixEllipsoid_eq_image {M : Mat d} (hdet : M.det ≠ 0) (R : ℝ) :
    matrixEllipsoid M R = matrixMeasurableEquiv M hdet '' ball 0 R := by
  unfold matrixEllipsoid
  rfl

/-- The image of the restricted Lebesgue measure under `y ↦ M y`. -/
theorem map_restrict_matrixMeasurableEquiv {M : Mat d} (hdet : M.det ≠ 0) (S : Set (Vec d)) :
    Measure.map (matrixMeasurableEquiv M hdet) (volume.restrict S) =
      ENNReal.ofReal |(M.det)⁻¹| • volume.restrict (matrixMeasurableEquiv M hdet '' S) := by
  set e := matrixMeasurableEquiv M hdet
  have hpre : e ⁻¹' (e '' S) = S := Set.preimage_image_eq S e.injective
  have hmap : Measure.map e volume = ENNReal.ofReal |(M.det)⁻¹| • volume := by
    have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (volume : Measure (Vec d))) (f := Matrix.toLin' M)
      (by rw [LinearMap.det_toLin']; exact hdet)
    rw [LinearMap.det_toLin'] at h
    exact h
  rw [← Measure.restrict_smul, ← hmap, e.restrict_map, hpre]

/-- **Change of variables** `∫_{E_R} g = |det M| ∫_{B_R} g ∘ M`. -/
theorem setIntegral_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) (R : ℝ) (g : Vec d → ℝ) :
    ∫ x in matrixEllipsoid M R, g x = |M.det| * ∫ y in ball 0 R, g (M.mulVec y) := by
  set e := matrixMeasurableEquiv M hdet
  have h := integral_map_equiv e (μ := volume.restrict (ball (0 : Vec d) R)) g
  rw [map_restrict_matrixMeasurableEquiv hdet, integral_smul_measure,
    ← matrixEllipsoid_eq_image hdet, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  have hdet0 : |M.det| ≠ 0 := abs_ne_zero.2 hdet
  rw [abs_inv] at h
  have h2 : ∫ x in matrixEllipsoid M R, g x = |M.det| * ((|M.det|)⁻¹ • ∫ x in matrixEllipsoid M R, g x) := by
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hdet0, one_mul]
  rw [h2, h]
  rfl

/-- Normalized `L²` norms under `y ↦ M y`. -/
theorem scalarRms_matrixEllipsoid_eq {M : Mat d} (hdet : M.det ≠ 0) (R : ℝ) (f : Vec d → ℝ) :
    scalarRms volume (matrixEllipsoid M R) f =
      scalarRms volume (ball 0 R) (fun y => f (M.mulVec y)) := by
  unfold scalarRms
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
    setIntegral_matrixEllipsoid hdet R (fun x => f x ^ 2), measureReal_def, measureReal_def,
    volume_matrixEllipsoid, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hdet0 : |M.det| ≠ 0 := abs_ne_zero.2 hdet
  congr 1
  calc (|M.det| * (volume (ball (0 : Vec d) R)).toReal)⁻¹ *
        (|M.det| * ∫ y in ball 0 R, f (M.mulVec y) ^ 2)
      = (|M.det|⁻¹ * |M.det|) * ((volume (ball (0 : Vec d) R)).toReal⁻¹ *
          ∫ y in ball 0 R, f (M.mulVec y) ^ 2) := by
        rw [mul_inv]
        ring
    _ = _ := by rw [inv_mul_cancel₀ hdet0, one_mul]

/-- Square integrability passes from `E_R` to `B_R`. -/
theorem MemLp.comp_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {S : Set (Vec d)}
    {h : Vec d → ℝ} (hh : MemLp h 2 (volume.restrict (matrixMeasurableEquiv M hdet '' S))) :
    MemLp (fun y => h (M.mulVec y)) 2 (volume.restrict S) := by
  set e := matrixMeasurableEquiv M hdet
  have h1 : MemLp h 2 (Measure.map e (volume.restrict S)) := by
    rw [map_restrict_matrixMeasurableEquiv hdet]
    exact hh.smul_measure ENNReal.ofReal_ne_top
  exact (e.measurableEmbedding.memLp_map_measure_iff.1 h1)

/-- Integrability passes from `M S` to `S`. -/
theorem IntegrableOn.comp_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {S : Set (Vec d)}
    {h : Vec d → ℝ} (hh : IntegrableOn h (matrixMeasurableEquiv M hdet '' S)) :
    IntegrableOn (fun y => h (M.mulVec y)) S := by
  set e := matrixMeasurableEquiv M hdet
  have h1 : Integrable h (Measure.map e (volume.restrict S)) := by
    rw [map_restrict_matrixMeasurableEquiv hdet]
    exact hh.smul_measure ENNReal.ofReal_ne_top
  exact (e.measurableEmbedding.integrable_map_iff.1 h1)

/-- Local integrability passes from `E_R` to `B_R`. -/
theorem LocallyIntegrableOn.comp_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) {R : ℝ}
    {h : Vec d → ℝ} (hh : LocallyIntegrableOn h (matrixEllipsoid M R) volume) :
    LocallyIntegrableOn (fun y => h (M.mulVec y)) (ball 0 R) volume := by
  set e := matrixMeasurableEquiv M hdet
  rw [locallyIntegrableOn_iff (isOpen_ball_zero R).isLocallyClosed]
  intro K hK hKc
  have hsub : e '' K ⊆ matrixEllipsoid M R := by
    rw [matrixEllipsoid_eq_image hdet]
    exact Set.image_mono hK
  have hcont : Continuous e := (Matrix.toLin' M).continuous_of_finiteDimensional
  have hc : IsCompact (e '' K) := hKc.image hcont
  exact IntegrableOn.comp_matrixEllipsoid hdet (hh.integrableOn_compact_subset hsub hc)

end QSH
