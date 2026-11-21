import QuantitativeStochasticHomogenization.Ch04.Sec06.HeatAverageBounds

/-!
# Section 4.6: Gaussian square averages of `O_1` fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6 and Appendix A. If `|X(u)| ≤ O_1(θ)` at every point `u` for a jointly measurable random
field `X`, then `(∫ e^{-‖u‖²/32} |X(u)|² du)^{1/2} ≤ O_1(K_d θ)` (`osBound_rpow_integral_sq`): the
squares are `O_{1/2}(θ²)` (`OsBound.rpow`), their Gaussian average is `O_{1/2}` by the averaging
property of `O_s` for `s < 1` (`osBound_integral_of_lt_one`), and the square root is `O_1`.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The Gaussian weight `e^{-‖u‖²/32}`. -/
def gaussWeight (u : Vec d) : ℝ := Real.exp (-(‖u‖ ^ 2) / 32)

theorem gaussWeight_pos (u : Vec d) : 0 < gaussWeight u := Real.exp_pos _

theorem measurable_gaussWeight : Measurable (gaussWeight (d := d)) := by
  unfold gaussWeight
  fun_prop

theorem euclideanSq_le_card_mul_norm_sq (u : Vec d) : euclideanSq u ≤ d * ‖u‖ ^ 2 := by
  unfold euclideanSq dot
  calc ∑ i, u i * u i ≤ ∑ _i : Fin d, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm u i
        rw [Real.norm_eq_abs] at h
        nlinarith [abs_nonneg (u i), abs_mul_abs_self (u i)]
    _ = d * ‖u‖ ^ 2 := by simp

theorem integrable_gaussWeight (hd : 1 ≤ d) : Integrable (gaussWeight (d := d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : (0 : ℝ) < 8 * d := by positivity
  set c := (4 * Real.pi * (8 * d)) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  refine ((integrable_euclideanHeatKernel (d := d) ht).const_mul c⁻¹).mono'
    measurable_gaussWeight.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (gaussWeight_pos u)]
  unfold gaussWeight euclideanHeatKernel
  rw [← hc, ← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  refine Real.exp_le_exp.mpr ?_
  have h1 := euclideanSq_le_card_mul_norm_sq u
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- The constant `K_d = ((1 + 1/log 2)^2 ∫ e^{-‖u‖²/32} du)^{1/2}`. -/
def gaussSquareConstant (d : ℕ) : ℝ :=
  ((1 + (1 - 1 / 2) / (1 / 2 * Real.log 2)) ^ (1 / 2 : ℝ)⁻¹ * ∫ u, gaussWeight (d := d) u) ^
    (1 / 2 : ℝ)

theorem integral_gaussWeight_pos (hd : 1 ≤ d) : 0 < ∫ u, gaussWeight (d := d) u :=
  (integral_pos_iff_support_of_nonneg (fun u => (gaussWeight_pos u).le)
    (integrable_gaussWeight hd)).mpr (by
      have h : Function.support (gaussWeight (d := d)) = univ :=
        eq_univ_of_forall fun u => (gaussWeight_pos u).ne'
      rw [h]
      exact isOpen_univ.measure_pos volume univ_nonempty)

/-- **Gaussian square averages of `O_1` fields.** -/
theorem osBound_rpow_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : 1 ≤ d) {X : Vec d → Ω → ℝ}
    (hXm : Measurable (Function.uncurry X)) {θ : ℝ} (hθ : 0 < θ)
    (hX : ∀ u, OsBound P (fun a => |X u a|) 1 θ) :
    (∀ᵐ a ∂P, Integrable (fun u => gaussWeight u * |X u a| ^ (2 : ℝ))) ∧
      OsBound P (fun a => (∫ u, gaussWeight u * |X u a| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) 1
        (gaussSquareConstant d * θ) := by
  have hY : ∀ u, OsBound P (fun a => gaussWeight u * |X u a| ^ (2 : ℝ)) (1 / 2)
      (gaussWeight u * θ ^ (2 : ℝ)) := fun u => by
    have h := (hX u).rpow (fun a => abs_nonneg _) (by norm_num : (0 : ℝ) < 2)
    exact h.const_mul (gaussWeight_pos u)
  have hYm : Measurable (Function.uncurry fun u a => gaussWeight u * |X u a| ^ (2 : ℝ)) :=
    (measurable_gaussWeight.comp measurable_fst).mul (hXm.abs.pow_const _)
  have hY0 : ∀ u a, 0 ≤ gaussWeight u * |X u a| ^ (2 : ℝ) := fun u a =>
    mul_nonneg (gaussWeight_pos u).le (Real.rpow_nonneg (abs_nonneg _) _)
  have hθm : Measurable (fun u : Vec d => gaussWeight u * θ ^ (2 : ℝ)) :=
    measurable_gaussWeight.mul_const _
  have hθi : Integrable (fun u : Vec d => gaussWeight u * θ ^ (2 : ℝ)) :=
    (integrable_gaussWeight hd).mul_const _
  have hθpos : 0 < ∫ u, gaussWeight (d := d) u * θ ^ (2 : ℝ) := by
    rw [integral_mul_const]
    exact mul_pos (integral_gaussWeight_pos hd) (Real.rpow_pos_of_pos hθ _)
  obtain ⟨hint, hV⟩ := osBound_integral_of_lt_one (by norm_num : (1 / 2 : ℝ) < 1) hYm hY0 hθm
    hθi hθpos hY
  refine ⟨hint, ?_⟩
  have hV0 : ∀ a, 0 ≤ ∫ u, gaussWeight u * |X u a| ^ (2 : ℝ) := fun a =>
    integral_nonneg fun u => hY0 u a
  have h := hV.rpow hV0 (by norm_num : (0 : ℝ) < 1 / 2)
  have h1 : (1 / 2 : ℝ) / (1 / 2) = 1 := by norm_num
  rw [h1] at h
  refine h.mono_scale (le_of_eq ?_)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK0 : 0 ≤ (1 + (1 - 1 / 2) / (1 / 2 * Real.log 2)) ^ (1 / 2 : ℝ)⁻¹ *
      ∫ u, gaussWeight (d := d) u :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (integral_nonneg fun u => (gaussWeight_pos u).le)
  rw [integral_mul_const, ← mul_assoc, Real.mul_rpow hK0 (Real.rpow_nonneg hθ.le _),
    ← Real.rpow_mul hθ.le]
  unfold gaussSquareConstant
  norm_num

end QSH
