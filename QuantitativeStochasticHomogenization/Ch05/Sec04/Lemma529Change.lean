import QuantitativeStochasticHomogenization.Ch05.Sec04.Lemma529Boundary

/-!
# Lemma 5.29 (iii): change of the scale of a block

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29 (iii), for centered local additive fields: for `β ∈ [η₁, 1)` there is
`ε > 0` with `R^{-d} ∫_{□_R} X(r) = R^{-d} ∫_{□_R} X(R^{η₁}) + 𝒪_s(C R^{-d/2-ε})` for
`r ∈ [R^{η₁}, R^β]`. By Step 1 of Proposition 4.12 with `r₁ = R^{η₁}`, the left side is
`R^{-d} ∫ g X(R^{η₁})` with `g = 1_{□_R} ∗ Φ_{√(r²-r₁²)}`, up to `𝒪_s(C R^{-η₁ α})`. The difference
`g - 1_{□_R}` is tiny inside `□_{R-R^b}`, bounded by one in the layers `□_R \ □_{R-R^b}` and
`□_{R+R^b} \ □_R`, and has a Gaussian tail outside `□_{R+R^b}`; the layers are handled by
Lemma 5.29 (ii).

The width of the layers is `R^b` with `b = max((1+β)/2, (1+η₁(1+δ))/2)`. The book takes
`b = (1+β)/2`; Lemma 5.29 (ii) at the scale `R^{η₁}` needs `η₁(1+δ) ≤ b`, which `b = (1+β)/2`
gives only when `η₁(1+2δ) ≤ 1`.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {F : Set (Vec d) → MeasurableSpace Ω} {s δ α : ℝ}

/-- **Small blocks**: a block with a weight bounded by `τ` and vanishing off a closed cube of side
`R` is `𝒪_s(C(s) B τ)`. -/
theorem exists_centeredOsBound_small_block {B A : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (hB0 : 0 < B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : Measure Ω) [IsProbabilityMeasure P]
      (X : CenteredLocalFields P F s δ α B A) (r : ℝ) {z : Vec d} {R τ : ℝ}, 0 < R → 0 < τ →
      ∀ w : Vec d → ℝ, Measurable w → (∀ x, |w x| ≤ τ) → (∀ x ∉ closedCube z R, w x = 0) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, w x * X.field r a x) s (C₀ * (B * τ)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_abs_le hs1 hs2
  refine ⟨C₀, hC₀, fun P _ X r z R τ hR hτ w hw hwτ hwz => ?_⟩
  have hwi : Integrable w := by
    have he : w = (closedCube z R).indicator w := by
      funext x
      by_cases hx : x ∈ closedCube z R
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hwz x hx]
    rw [he, integrable_indicator_iff (measurableSet_closedCube z R)]
    have : IsFiniteMeasure (volume.restrict (closedCube z R)) :=
      ⟨by rw [Measure.restrict_apply_univ, volume_closedCube z hR.le]; exact ENNReal.ofReal_lt_top⟩
    exact Integrable.of_bound hw.aestronglyMeasurable τ
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hwτ x)
  have hint : ∫ x, |w x| ≤ τ * R ^ d := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedCube z R)
      (fun x hx => by rw [hwz x hx, abs_zero])]
    calc ∫ x in closedCube z R, |w x| ≤ ∫ _x in closedCube z R, τ :=
          setIntegral_mono_on hwi.abs.integrableOn (integrableOn_const (by
            rw [volume_closedCube z hR.le]; exact ENNReal.ofReal_ne_top))
            (measurableSet_closedCube z R) fun x _ => hwτ x
      _ = τ * R ^ d := by
          rw [setIntegral_const, smul_eq_mul, volume_real_closedCube z hR.le, mul_comm]
  have hY : ∀ a, |R ^ (-(d : ℝ)) * ∫ x, w x * X.field r a x| ≤ B * τ := by
    intro a
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hR _)]
    calc R ^ (-(d : ℝ)) * |∫ x, w x * X.field r a x| ≤ R ^ (-(d : ℝ)) * (B * (τ * R ^ d)) :=
          mul_le_mul_of_nonneg_left ((abs_integral_mul_le (X.abs_le r) hwi a).trans
            (mul_le_mul_of_nonneg_left hint hB0.le)) (Real.rpow_nonneg hR.le _)
      _ = B * τ := by
          have h1 : R ^ (-(d : ℝ)) * R ^ d = 1 := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
          calc R ^ (-(d : ℝ)) * (B * (τ * R ^ d)) = B * τ * (R ^ (-(d : ℝ)) * R ^ d) := by ring
            _ = B * τ := by rw [h1, mul_one]
  exact h₀ P _ (B * τ) (measurable_block X r hw _) (mul_pos hB0 hτ) hY
    (integral_block_eq_zero X r hwi _)

end QSH
