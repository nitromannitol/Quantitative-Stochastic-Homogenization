import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestScaleDerivative
import QuantitativeStochasticHomogenization.Ch03.Sec03.LinearChangeOfVariables

/-!
# The adapted profile pair and its bounds

For a matrix `D` with `|ξ|² ≤ ξ · D ξ ≤ K |ξ|²`, the profile `ρ` and the partner `χ` adapted to the
symmetric part of `D` (`adaptedRho`, `adaptedChi` for a frame `A` of the symmetric part) form a
compact profile pair: `ρ ≥ 0`, `∫ ρ = 1` by the linear change of variables `y ↦ A' y`, and the
scale identity holds. The derivatives of order `j` of `ρ` and `χ` are bounded by constants
depending only on `d`, `K` and `j` (`exists_adaptedPair_bounds`): the entries of `A' = 2√K A` are
at most `2√K`, `|det A'| ≤ d! (2√K)^d`, and the derivatives of the base pair are fixed. This is
the compact profile of the finite-ball estimate of the proof of
Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*.
-/

open MeasureTheory Filter Set
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ} {D A : Mat d} {K : ℝ}

theorem integral_comp_mulVec {M : Mat d} (hdet : M.det ≠ 0) (g : Vec d → ℝ) :
    ∫ y, g (M.mulVec y) = |M.det|⁻¹ * ∫ x, g x := by
  have h := integral_map_equiv (matrixMeasurableEquiv M hdet) (μ := volume) g
  have hmap := map_restrict_matrixMeasurableEquiv hdet (Set.univ : Set (Vec d))
  rw [Measure.restrict_univ, Set.image_univ_of_surjective
    (matrixMeasurableEquiv M hdet).surjective, Measure.restrict_univ] at hmap
  calc ∫ y, g (M.mulVec y) = ∫ y, g (matrixMeasurableEquiv M hdet y) := rfl
    _ = ∫ y, g y ∂(Measure.map (matrixMeasurableEquiv M hdet) volume) := h.symm
    _ = |M.det|⁻¹ * ∫ x, g x := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
          abs_inv]

theorem frameConst_nonneg' (A : Mat d) (K : ℝ) : 0 ≤ frameConst A K :=
  div_nonneg (abs_nonneg _) (integral_nonneg baseRho_nonneg)

theorem adaptedRho_nonneg (A : Mat d) (K : ℝ) (y : Vec d) : 0 ≤ adaptedRho A K y :=
  mul_nonneg (frameConst_nonneg' A K) (baseRho_nonneg _)

theorem integral_adaptedRho (hd : 0 < d) (hA : ProfileFrame D A K) (hK : 0 < K) :
    ∫ y, adaptedRho A K y = 1 := by
  have hdet := frameMatrix_det_ne hA hK
  unfold adaptedRho
  rw [integral_const_mul, integral_comp_mulVec hdet, frameConst]
  have hm := integral_baseRho_pos (d := d) hd
  have hdet' : 0 < |(frameMatrix A K).det| := abs_pos.2 hdet
  field_simp

/-- **The adapted pair is a compact profile pair.** -/
theorem compactProfilePair_adapted (hd : 0 < d) {D : Mat d}
    (hA : ProfileFrame (symmPart' D) A K) (hK : 0 < K) :
    CompactProfilePair D (adaptedRho A K) (adaptedChi A K) where
  smooth_rho := contDiff_adaptedRho A K
  smooth_chi := contDiff_adaptedChi A K
  vanish_rho := fun _ hy => adaptedRho_eq_zero hA hK hy
  vanish_chi := fun _ hy => adaptedChi_eq_zero hA hK hy
  nonneg := adaptedRho_nonneg A K
  integral_eq_one := integral_adaptedRho hd hA hK
  scale := scaleIdentity_adapted hA hK

theorem abs_frameMatrix_entry_le (hA : ProfileFrame D A K) (hK : 0 < K) (l i : Fin d) :
    |frameMatrix A K l i| ≤ (frameRadius K)⁻¹ := by
  unfold frameMatrix
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 (frameRadius_pos hK))]
  exact mul_le_of_le_one_right (inv_pos.2 (frameRadius_pos hK)).le (hA.entry l i)

theorem frameConst_le (hA : ProfileFrame D A K) (hK : 0 < K) :
    frameConst A K ≤ (Nat.factorial d * (frameRadius K)⁻¹ ^ d) / ∫ y : Vec d, baseRho y := by
  unfold frameConst
  refine div_le_div_of_nonneg_right ?_ (integral_nonneg baseRho_nonneg)
  have h := Matrix.det_le (A := frameMatrix A K) (abv := AbsoluteValue.abs)
    (x := (frameRadius K)⁻¹) (fun l i => by
      simpa using abs_frameMatrix_entry_le hA hK l i)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

/-- **Uniform bounds** of the derivatives of the adapted pair: constants depending only on `d`,
`K` and the order. -/
theorem exists_adaptedPair_bounds (hK : 0 < K) (j : ℕ) :
    ∃ Kρ Kχ : ℝ, 0 ≤ Kρ ∧ 0 ≤ Kχ ∧ ∀ {D A : Mat d}, ProfileFrame D A K →
      (∀ (β : Fin j → Fin d) y, |iterDeriv β (adaptedRho A K) y| ≤ Kρ) ∧
      (∀ (β : Fin j → Fin d) y, |iterDeriv β (adaptedChi A K) y| ≤ Kχ) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_iterDeriv_le (d := d) contDiff_baseRho
    hasCompactSupport_baseRho j
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_abs_iterDeriv_le (d := d) contDiff_baseChi
    hasCompactSupport_baseChi j
  set c := (Nat.factorial d * (frameRadius K)⁻¹ ^ d) / ∫ y : Vec d, baseRho y with hc
  have hc0 : 0 ≤ c := div_nonneg (by have := (inv_pos.2 (frameRadius_pos hK)).le; positivity)
    (integral_nonneg baseRho_nonneg)
  set q := (d : ℝ) * (frameRadius K)⁻¹ with hq
  have hq0 : 0 ≤ q := mul_nonneg (Nat.cast_nonneg d) (inv_pos.2 (frameRadius_pos hK)).le
  refine ⟨c * (q ^ j * K₁), frameRadius K ^ 2 * c * (q ^ j * K₂), by positivity, by positivity,
    fun {D A} hA => ⟨fun β y => ?_, fun β y => ?_⟩⟩
  · have hdet := frameMatrix_det_ne hA hK
    have e : adaptedRho A K = fun y => frameConst A K * baseRho ((frameMatrix A K).mulVec y) := rfl
    rw [e, iterDeriv_const_mul β (contDiff_comp_mulVec contDiff_baseRho _), abs_mul,
      abs_of_nonneg (frameConst_nonneg' A K)]
    exact mul_le_mul (frameConst_le hA hK)
      (abs_iterDeriv_comp_mulVec_le hdet (inv_pos.2 (frameRadius_pos hK)).le
        (abs_frameMatrix_entry_le hA hK) contDiff_baseRho hK₁ β y) (abs_nonneg _) hc0
  · have hdet := frameMatrix_det_ne hA hK
    have e : adaptedChi A K = fun y => frameRadius K ^ 2 * frameConst A K *
        baseChi ((frameMatrix A K).mulVec y) := rfl
    rw [e, iterDeriv_const_mul β (contDiff_comp_mulVec contDiff_baseChi _), abs_mul,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (frameConst_nonneg' A K))]
    refine mul_le_mul ?_ (abs_iterDeriv_comp_mulVec_le hdet (inv_pos.2 (frameRadius_pos hK)).le
        (abs_frameMatrix_entry_le hA hK) contDiff_baseChi hK₂ β y) (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (frameConst_le hA hK) (sq_nonneg _)

end QSH
