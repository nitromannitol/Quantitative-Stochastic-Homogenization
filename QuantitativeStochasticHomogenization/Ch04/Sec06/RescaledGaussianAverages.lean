import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevGaussian
import QuantitativeStochasticHomogenization.Front.Assumptions.MeasurableVersion

/-!
# Section 4.6: Gaussian averages of rescaled vector fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6. If a jointly measurable random vector field `G` satisfies the estimate (4.2) in the
form `|∫ Φ_{z,r} G| ≤ O_1(C r^{-d/2})` at every center `z` and radius `r ≥ 1` (the form of the
frozen statement of Theorem 4.1), then the Gaussian averages of the components of `G(·/ε)` satisfy
`|A_t(G(·/ε)_j)(u)| ≤ O_1(C ε^{d/2} t^{-d/4})` for `t ≥ ε²` (`osBound_abs_heatAverage_rescaled`):
`A_t(G(·/ε)_j)(u)` is the `j`-th component of the average of `G` at the center `u/ε` and the radius
`√t/ε ≥ 1`. With the Gaussian moments and the Gaussian energy estimate of the rescaled fields
(`GaussianEnergyEstimate`), this gives the frozen statement (4.126) from (4.2) and (4.3) in the form
of the frozen statement of Theorem 4.1 (`negativeSobolevCorrector_of_averages`). The jointly
measurable version of the flux is obtained from the jointly measurable version of the coefficient
field (`coefficientVersion`), so that (4.3) and the energy estimate of the flux may be stated for
the flux itself (`negativeSobolevCorrector_of_flux_averages`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem measurable_heatAverage_apply {Ω : Type*} [MeasurableSpace Ω] {F : Ω → Vec d → ℝ}
    (hFm : Measurable (Function.uncurry F)) (t : ℝ) (u : Vec d) :
    Measurable (fun a => heatAverage t (F a) u) := by
  have hK : Continuous (euclideanHeatKernel (d := d) t) :=
    (contDiff_euclideanHeatKernel t).continuous
  have h : StronglyMeasurable (fun p : Ω × Vec d => F p.1 p.2 * euclideanHeatKernel t (p.2 - u)) :=
    (hFm.mul (hK.measurable.comp (measurable_snd.sub_const u))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- **Gaussian averages of rescaled vector fields** from the estimate (4.2) at radii `r ≥ 1`. -/
theorem osBound_abs_heatAverage_rescaled {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : Ω → Vec d → Vec d} (hGm : Measurable (fun p : Ω × Vec d => G p.1 p.2)) {C : ℝ}
    (hE : ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • G a y)) ∧
      OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • G a y)) 1
        (C * r ^ (-(d : ℝ) / 2)))
    {ε : ℝ} (hε : 0 < ε) (j : Fin d) {t : ℝ} (ht : ε ^ 2 ≤ t) (u : Vec d) :
    OsBound P (fun a => |heatAverage t (fun x => G a (ε⁻¹ • x) j) u|) 1
      (C * ε ^ ((d : ℝ) / 2) * t ^ (-(d : ℝ) / 4)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  set r := ε⁻¹ * Real.sqrt t with hr
  have hr1 : 1 ≤ r := by
    rw [hr, inv_mul_eq_div, le_div_iff₀ hε, one_mul]
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  obtain ⟨hint, hos⟩ := hE (ε⁻¹ • u) r hr1
  have hF : Measurable (Function.uncurry fun (a : Ω) (x : Vec d) => G a (ε⁻¹ • x) j) :=
    (measurable_pi_apply j).comp (hGm.comp (measurable_fst.prodMk
      (measurable_snd.const_smul ε⁻¹)))
  have hm : Measurable (fun a => |heatAverage t (fun x => G a (ε⁻¹ • x) j) u|) :=
    (measurable_heatAverage_apply hF t u).abs
  refine (hos.of_le_ae hm ?_).mono_scale (le_of_eq ?_)
  · filter_upwards [hint] with a ha
    have h2 := ha.comp_smul (μ := volume) hεi.ne'
    have h3 : (fun y => heatKernel u (Real.sqrt t) y • G a (ε⁻¹ • y)) = fun y =>
        ((ε⁻¹) ^ (-(d : ℝ)))⁻¹ • (heatKernel (ε⁻¹ • u) r (ε⁻¹ • y) • G a (ε⁻¹ • y)) := by
      funext y
      rw [hr, heatKernel_smul u y hεi hst, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos hεi _).ne', one_mul]
    have hint' : Integrable (fun y => heatKernel u (Real.sqrt t) y • G a (ε⁻¹ • y)) := by
      rw [h3]
      exact h2.smul ((ε⁻¹) ^ (-(d : ℝ)))⁻¹
    have h1 : heatAverage t (fun x => G a (ε⁻¹ • x) j) u =
        (∫ y, heatKernel u (Real.sqrt t) y • G a (ε⁻¹ • y)) j := by
      have h4 := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => ℝ) j) hint'
      simp only [ContinuousLinearMap.proj_apply] at h4
      rw [← h4]
      unfold heatAverage
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, heatKernel, Real.sq_sqrt ht0.le]
      ring
    rw [h1, integral_heatKernel_rescale (fun y => G a y) u hε hst]
    exact abs_apply_le_euclideanNorm _ j
  · rw [hr, Real.mul_rpow hεi.le hst.le, Real.inv_rpow hε.le, ← Real.rpow_neg hε.le,
      Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le,
      show -(-(d : ℝ) / 2) = (d : ℝ) / 2 by ring,
      show (1 : ℝ) / 2 * (-(d : ℝ) / 2) = -(d : ℝ) / 4 by ring]
    ring

/-- **The Gaussian energy estimate** of a random field: Gaussian moments at every center and a
Gaussian `L²` norm `O_1(C₁)` at the unit scale. -/
def GaussianEnergyEstimate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → Vec d → ℝ)
    (C₁ : ℝ) : Prop :=
  (∀ᵐ a ∂P, ∀ τ : ℝ, 0 < τ → ∀ y,
    Integrable (fun x => F a x * euclideanHeatKernel τ (x - y))) ∧
  ∃ R : Ω → ℝ, OsBound P R 1 C₁ ∧ ∀ᵐ a ∂P, (∫⁻ x, ‖F a x‖ₑ ^ (2 : ℝ) *
    ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)

/-- **(4.126) from (4.2), (4.3) and the Gaussian energy estimates** of the rescaled corrector
gradient and flux, (4.3) being stated for a jointly measurable version of the flux. -/
theorem negativeSobolevCorrector_of_averages
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C C₁ : ℝ, 0 < C ∧ 0 < C₁ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y)) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y))
              1 (C * r ^ (-(d : ℝ) / 2))) ∧
          ∃ Fl : CoefficientField d Λ → Vec d → Vec d,
            Measurable (fun p : CoefficientField d Λ × Vec d => Fl p.1 p.2) ∧
            (∀ a, ∀ᵐ y ∂volume,
              Fl a y = (a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e) ∧
            (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
              (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • Fl a y)) ∧
              OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • Fl a y)) 1
                (C * r ^ (-(d : ℝ) / 2))) ∧
            ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ j : Fin d,
              GaussianEnergyEstimate P (fun a x => (S.corrector e).grad a (ε⁻¹ • x) j) C₁ ∧
              GaussianEnergyEstimate P (fun a x => Fl a (ε⁻¹ • x) j) C₁) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_gaussian fun d hd Λ hΛ => ?_
  obtain ⟨C, C₁, hC, hC₁, hP⟩ := h d hd Λ hΛ
  refine ⟨C₁, C, hC₁, hC, fun P hPl => ?_⟩
  obtain ⟨S, hS⟩ := hP P hPl
  refine ⟨S, fun e he ε hε hε2 j => ?_⟩
  obtain ⟨hE1, Fl, hFlm, hFl, hE3, hen⟩ := hS e he
  obtain ⟨⟨hGg, hGe⟩, ⟨hFg, hFe⟩⟩ := hen ε hε hε2 j
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  constructor
  · refine ⟨fun a x => (S.corrector e).grad a (ε⁻¹ • x) j, ?_, fun a => ae_eq_refl _, hGg, hGe,
      fun t ht _ u => osBound_abs_heatAverage_rescaled (S.corrector e).measurable_grad hE1 hε j ht u⟩
    exact (measurable_pi_apply j).comp ((S.corrector e).measurable_grad.comp
      (measurable_fst.prodMk (measurable_snd.const_smul ε⁻¹)))
  · refine ⟨fun a x => Fl a (ε⁻¹ • x) j, ?_, fun a => ?_, hFg, hFe,
      fun t ht _ u => osBound_abs_heatAverage_rescaled hFlm hE3 hε j ht u⟩
    · exact (measurable_pi_apply j).comp (hFlm.comp
        (measurable_fst.prodMk (measurable_snd.const_smul ε⁻¹)))
    · have h1 := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure (Vec d))) hεi).ae
        (hFl a)
      filter_upwards [h1] with x hx
      simp only [hx]

/-- **(4.126) from (4.2), (4.3) and the Gaussian energy estimates** of the rescaled corrector
gradient and flux, all stated for the corrector gradient and the flux themselves. -/
theorem negativeSobolevCorrector_of_flux_averages
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C C₁ : ℝ, 0 < C ∧ 0 < C₁ ∧
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
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ j : Fin d,
            GaussianEnergyEstimate P (fun a x => (S.corrector e).grad a (ε⁻¹ • x) j) C₁ ∧
            GaussianEnergyEstimate P (fun a x => ((a (ε⁻¹ • x)).mulVec
              (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) j) C₁) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_averages fun d hd Λ hΛ => ?_
  obtain ⟨C, C₁, hC, hC₁, hP⟩ := h d hd Λ hΛ
  refine ⟨C, C₁, hC, hC₁, fun P hPl => ?_⟩
  obtain ⟨S, hS⟩ := hP P hPl
  refine ⟨S, fun e he => ?_⟩
  obtain ⟨hE1, hE3, hen⟩ := hS e he
  set Fl : CoefficientField d Λ → Vec d → Vec d := fun a y =>
    (coefficientVersion a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e
    with hFldef
  have hFlm : Measurable (fun p : CoefficientField d Λ × Vec d => Fl p.1 p.2) := by
    have hmv : Continuous (fun q : Mat d × Vec d => q.1.mulVec q.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    refine Measurable.sub ?_ measurable_const
    exact hmv.measurable.comp (measurable_coefficientVersion.prodMk
      (measurable_const.add (S.corrector e).measurable_grad))
  have hFl : ∀ a : CoefficientField d Λ, ∀ᵐ y ∂(volume : Measure (Vec d)),
      Fl a y = (a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e := fun a => by
    filter_upwards [ae_coefficientVersion_eq a] with y hy
    simp only [hFldef, hy]
  refine ⟨hE1, Fl, hFlm, hFl, fun z r hr => ?_, fun ε hε hε2 j => ?_⟩
  · obtain ⟨hint, hos⟩ := hE3 z r hr
    have heq : ∀ a : CoefficientField d Λ, (fun y => heatKernel z r y • Fl a y) =ᵐ[volume]
        fun y => heatKernel z r y •
          ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e) := fun a => by
      filter_upwards [hFl a] with y hy
      rw [hy]
    refine ⟨?_, ?_⟩
    · filter_upwards [hint] with a ha
      exact ha.congr (heq a).symm
    · have hfun : (fun a => euclideanNorm (∫ y, heatKernel z r y • Fl a y)) = fun a =>
          euclideanNorm (∫ y, heatKernel z r y •
            ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e)) := by
        funext a
        rw [integral_congr_ae (heq a)]
      rw [hfun]
      exact hos
  · obtain ⟨hG, ⟨hFg, R, hRo, hR⟩⟩ := hen ε hε hε2 j
    have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
    have heq : ∀ a : CoefficientField d Λ, (fun x => Fl a (ε⁻¹ • x) j) =ᵐ[volume] fun x =>
        ((a (ε⁻¹ • x)).mulVec (e + (S.corrector e).grad a (ε⁻¹ • x)) -
          S.homogenized.mulVec e) j := fun a => by
      have h1 := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure (Vec d))) hεi).ae
        (hFl a)
      filter_upwards [h1] with x hx
      simp only [hx]
    refine ⟨hG, ⟨?_, R, hRo, ?_⟩⟩
    · filter_upwards [hFg] with a ha τ hτ y
      refine (ha τ hτ y).congr ?_
      filter_upwards [heq a] with x hx
      rw [hx]
    · filter_upwards [hR] with a ha
      refine le_of_eq_of_le ?_ ha
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [heq a] with x hx
      rw [hx]

end QSH
