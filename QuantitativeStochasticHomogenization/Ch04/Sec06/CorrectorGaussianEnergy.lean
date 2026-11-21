import QuantitativeStochasticHomogenization.Ch04.Sec06.RescaledGaussianAverages
import QuantitativeStochasticHomogenization.Ch04.Sec01.GramSpace

/-!
# Section 4.6: (4.126) from the Gaussian energy of the corrected field

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126). The components of `∇φ_e(·/ε)` and of `a(·/ε)(e + ∇φ_e(·/ε)) - ā e` are bounded pointwise by
`|e + ∇φ_e(·/ε)|`, `Λ` and `|ā e|`, so that their Gaussian energy estimates follow from the
Gaussian energy estimate of the corrected field `e + ∇φ_e(·/ε)` at the unit scale
(`gaussianEnergyEstimate_of_vector`). This gives the frozen statement from (4.2), (4.3), the bound of
`|ā e|` and the Gaussian energy estimate of the corrected field
(`negativeSobolevCorrector_of_corrector_energy`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The Gaussian energy `∫ |G|² e^{-‖x‖²/32}` of a vector field. -/
def vectorGaussianEnergy (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (euclideanSq (G x)) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))

theorem lintegral_gaussWeight_eq (hd : 1 ≤ d) :
    ∫⁻ x : Vec d, ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) =
      ENNReal.ofReal (∫ x, gaussWeight (d := d) x) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_gaussWeight hd)
    (Eventually.of_forall fun x => (gaussWeight_pos x).le)).symm

/-- **Pointwise domination of the energy**: if `F² ≤ A |G|² + c`, then
`(∫ F² e^{-‖x‖²/32})^{1/2} ≤ √A (∫ |G|² e^{-‖x‖²/32})^{1/2} + √c (∫ e^{-‖x‖²/32})^{1/2}`. -/
theorem energy_le_of_sq_le (hd : 1 ≤ d) {F : Vec d → ℝ} {G : Vec d → Vec d} {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (h : ∀ x, F x ^ 2 ≤ A * euclideanSq (G x) + c) :
    (∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt A) * vectorGaussianEnergy G ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (Real.sqrt c * Real.sqrt (∫ x, gaussWeight (d := d) x)) := by
  have hW0 : 0 ≤ ∫ x, gaussWeight (d := d) x := integral_nonneg fun x => (gaussWeight_pos x).le
  have hpt : ∀ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) ≤
      ENNReal.ofReal A * (ENNReal.ofReal (euclideanSq (G x)) *
        ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) +
      ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) := fun x => by
    have hG0 : 0 ≤ euclideanSq (G x) := le_trans (sq_nonneg _) (norm_sq_le_euclideanSq _)
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs, ← mul_assoc, ← ENNReal.ofReal_mul hA, ← add_mul,
      ← ENNReal.ofReal_add (mul_nonneg hA hG0) hc]
    gcongr
    exact h x
  have hwm : Measurable (fun x : Vec d => ENNReal.ofReal c *
      ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_gaussWeight)
  calc (∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal A * vectorGaussianEnergy G +
          ENNReal.ofReal c * ENNReal.ofReal (∫ x, gaussWeight (d := d) x)) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        refine (lintegral_mono hpt).trans (le_of_eq ?_)
        rw [lintegral_add_right _ hwm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gaussWeight_eq hd]
        rfl
    _ ≤ (ENNReal.ofReal A * vectorGaussianEnergy G) ^ (1 / 2 : ℝ) +
          (ENNReal.ofReal c * ENNReal.ofReal (∫ x, gaussWeight (d := d) x)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ENNReal.ofReal_rpow_of_nonneg hc (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hW0 (by norm_num), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- **Gaussian energy estimates of dominated fields.** -/
theorem gaussianEnergyEstimate_of_vector {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : 1 ≤ d) {F : Ω → Vec d → ℝ} {G : Ω → Vec d → Vec d}
    {A c C₁ : ℝ} (hA : 0 < A) (hc : 0 ≤ c) (hFG : ∀ a x, F a x ^ 2 ≤ A * euclideanSq (G a x) + c)
    {R : Ω → ℝ} (hRo : OsBound P R 1 C₁)
    (hR : ∀ᵐ a ∂P, vectorGaussianEnergy (G a) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)) :
    GaussianEnergyEstimate P F (Real.sqrt A * C₁ +
      (Real.sqrt c * Real.sqrt (∫ x, gaussWeight (d := d) x) + 1) / Real.log 2 ^ (1 : ℝ)⁻¹) := by
  have hW0 : 0 ≤ ∫ x, gaussWeight (d := d) x := integral_nonneg fun x => (gaussWeight_pos x).le
  set K₀ := Real.sqrt c * Real.sqrt (∫ x, gaussWeight (d := d) x) + 1 with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  refine ⟨fun a => Real.sqrt A * max (R a) 0 + K₀, ?_, ?_⟩
  · have hRm : Measurable R := hRo.1
    have h1 : OsBound P (fun a => Real.sqrt A * max (R a) 0) 1 (Real.sqrt A * C₁) :=
      hRo.max_zero.const_mul (Real.sqrt_pos.mpr hA)
    exact osBound_add h1 (osBound_of_le_const measurable_const one_pos hK₀pos
      (Eventually.of_forall fun _ => le_rfl)) le_rfl
  · filter_upwards [hR] with a ha
    refine (energy_le_of_sq_le hd hA.le hc (hFG a)).trans ?_
    calc ENNReal.ofReal (Real.sqrt A) * vectorGaussianEnergy (G a) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (Real.sqrt c * Real.sqrt (∫ x, gaussWeight (d := d) x))
        ≤ ENNReal.ofReal (Real.sqrt A) * ENNReal.ofReal (max (R a) 0) + ENNReal.ofReal K₀ := by
          gcongr
          · exact ha.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          · rw [hK₀]
            linarith
      _ = ENNReal.ofReal (Real.sqrt A * max (R a) 0 + K₀) := by
          rw [ENNReal.ofReal_add (mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)) hK₀pos.le,
            ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

theorem sq_apply_le_euclideanSq (v : Vec d) (j : Fin d) : v j ^ 2 ≤ euclideanSq v := by
  have h := abs_apply_le_euclideanNorm v j
  have h0 : 0 ≤ euclideanSq v := le_trans (sq_nonneg _) (norm_sq_le_euclideanSq v)
  calc v j ^ 2 = |v j| ^ 2 := (sq_abs _).symm
    _ ≤ euclideanNorm v ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = euclideanSq v := Real.sq_sqrt h0

/-- **(4.126) from (4.2), (4.3), the bound of `|ā e|` and the Gaussian energy estimate of the
corrected field** `e + ∇φ_e(·/ε)` at the unit scale. -/
theorem negativeSobolevCorrector_of_corrector_energy
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C C₀ C₁ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < C₁ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y)) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y))
              1 (C * r ^ (-(d : ℝ) / 2))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y •
              ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e))) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y •
              ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e))) 1
                (C * r ^ (-(d : ℝ) / 2))) ∧
          euclideanNorm (S.homogenized.mulVec e) ≤ C₀ ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ R : CoefficientField d Λ → ℝ, OsBound P R 1 C₁ ∧
            ∀ᵐ a ∂P, vectorGaussianEnergy (fun x => e + (S.corrector e).grad a (ε⁻¹ • x)) ^
              (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_flux_averages fun d hd Λ hΛ => ?_
  obtain ⟨C, C₀, C₁, hC, hC₀, hC₁, hP⟩ := h d hd Λ hΛ
  have hd1 : 1 ≤ d := by omega
  set A : ℝ := 2 * Λ ^ 2 + 2 with hAdef
  set c : ℝ := 2 + 2 * C₀ ^ 2 with hcdef
  have hA : 0 < A := by positivity
  have hc : 0 ≤ c := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hW0 : 0 ≤ ∫ x, gaussWeight (d := d) x := integral_nonneg fun x => (gaussWeight_pos x).le
  refine ⟨C, Real.sqrt A * C₁ + (Real.sqrt c * Real.sqrt (∫ x, gaussWeight (d := d) x) + 1) /
    Real.log 2 ^ (1 : ℝ)⁻¹, hC, by positivity, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨S, hS⟩ := hP P hPl
  refine ⟨S, fun e he => ?_⟩
  obtain ⟨hE2, hE3, hā, hen⟩ := hS e he
  refine ⟨hE2, hE3, fun ε hε hε2 j => ?_⟩
  obtain ⟨R, hRo, hR⟩ := hen ε hε hε2
  have he1 : euclideanSq e ≤ 1 := by
    have h0 : 0 ≤ euclideanSq e := le_trans (sq_nonneg _) (norm_sq_le_euclideanSq e)
    have h1 : euclideanNorm e ^ 2 = euclideanSq e := Real.sq_sqrt h0
    have h2 : 0 ≤ euclideanNorm e := Real.sqrt_nonneg _
    nlinarith
  constructor
  · refine gaussianEnergyEstimate_of_vector hd1 hA hc (fun a x => ?_) hRo hR
    set ξ := e + (S.corrector e).grad a (ε⁻¹ • x) with hξ
    have h1 : (S.corrector e).grad a (ε⁻¹ • x) j = ξ j - e j := by
      rw [hξ, Pi.add_apply]
      ring
    rw [h1]
    have h2 := sq_apply_le_euclideanSq ξ j
    have h3 := sq_apply_le_euclideanSq e j
    have hξ0 : 0 ≤ euclideanSq ξ := le_trans (sq_nonneg _) (norm_sq_le_euclideanSq ξ)
    nlinarith [sq_nonneg (ξ j + e j), sq_nonneg Λ, sq_nonneg C₀]
  · refine gaussianEnergyEstimate_of_vector hd1 hA hc (fun a x => ?_) hRo hR
    set ξ := e + (S.corrector e).grad a (ε⁻¹ • x) with hξ
    have h1 : ((a (ε⁻¹ • x)).mulVec ξ - S.homogenized.mulVec e) j =
        (a (ε⁻¹ • x)).mulVec ξ j - S.homogenized.mulVec e j := rfl
    rw [h1]
    have h2 := sq_apply_le_euclideanSq ((a (ε⁻¹ • x)).mulVec ξ) j
    have h3 := euclideanSq_mulVec_le a (ε⁻¹ • x) ξ
    have h4 : (S.homogenized.mulVec e j) ^ 2 ≤ C₀ ^ 2 := by
      have h5 := (abs_apply_le_euclideanNorm (S.homogenized.mulVec e) j).trans hā
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h5 2
    have hξ0 : 0 ≤ euclideanSq ξ := le_trans (sq_nonneg _) (norm_sq_le_euclideanSq ξ)
    nlinarith [sq_nonneg ((a (ε⁻¹ • x)).mulVec ξ j + S.homogenized.mulVec e j)]

end QSH
