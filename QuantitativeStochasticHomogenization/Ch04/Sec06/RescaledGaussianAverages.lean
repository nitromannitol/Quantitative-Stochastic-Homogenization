import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevGaussian

/-!
# Section 4.6: Gaussian averages of rescaled vector fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6. If a jointly measurable random vector field `G` satisfies the estimate (4.2) in the
form `|∫ Φ_{z,r} G| ≤ O_1(C r^{-d/2})` at every center `z` and radius `r ≥ 1` (the form of the
frozen statement of Theorem 4.1), then the Gaussian averages of the components of `G(·/ε)` satisfy
`|A_t(G(·/ε)_j)(u)| ≤ O_1(C ε^{d/2} t^{-d/4})` for `t ≥ ε²` (`osBound_abs_heatAverage_rescaled`):
`A_t(G(·/ε)_j)(u)` is the `j`-th component of the average of `G` at the center `u/ε` and the radius
`√t/ε ≥ 1`.
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

end QSH
