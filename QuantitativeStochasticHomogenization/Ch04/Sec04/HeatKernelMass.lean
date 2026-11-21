import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationPerturbation

/-!
# Mass and tails of the heat kernel masks

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.1) and the proof of Lemma 4.22, (4.104): the mask `Φ_{z,r}` has mass one, so
`‖Φ_{z,r}^{1/2}‖_{L²(B_T(z))} ≤ 1`, and its mass outside `B_T(z)` is at most
`2^{d/2} exp(-T²/(8r²))`. The Gaussian integral is Mathlib's `integral_rexp_neg_mul_sq_norm` on
`EuclideanSpace ℝ (Fin d)`, transported to `Fin d → ℝ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanSq_eq_norm_sq (x : Vec d) :
    euclideanSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [← euclideanNorm_eq_norm, euclideanNorm_sq]

/-- The Gaussian integral `∫ exp(-b |x|²) dx = (π/b)^{d/2}`. -/
theorem integral_exp_neg_mul_euclideanSq {b : ℝ} (hb : 0 < b) :
    ∫ x : Vec d, Real.exp (-b * euclideanSq x) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin d)) hb
  rw [finrank_euclideanSpace_fin] at h
  rw [← h]
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.toLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  rw [← hmp.integral_comp hemb]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp only [euclideanSq_eq_norm_sq])

theorem integrable_exp_neg_mul_euclideanSq {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Vec d => Real.exp (-b * euclideanSq x)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_euclideanSq hb]
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne'

theorem heatKernel_eq_exp (z : Vec d) (r : ℝ) (x : Vec d) :
    heatKernel z r x =
      heatKernelPeak d r * Real.exp (-(1 / (4 * r ^ 2)) * euclideanSq (x - z)) := by
  rw [heatKernel_eq]
  congr 2
  ring

/-- **The mask has mass one.** -/
theorem integral_heatKernel (z : Vec d) {r : ℝ} (hr : r ≠ 0) :
    ∫ x, heatKernel z r x = 1 := by
  have hb : 0 < 1 / (4 * r ^ 2) := by positivity
  simp_rw [heatKernel_eq_exp]
  rw [integral_const_mul]
  have htr := integral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun x => Real.exp (-(1 / (4 * r ^ 2)) * euclideanSq x)) z

  rw [htr, integral_exp_neg_mul_euclideanSq hb, heatKernelPeak]
  have hpos : 0 < 4 * Real.pi * r ^ 2 := by positivity
  rw [show Real.pi / (1 / (4 * r ^ 2)) = 4 * Real.pi * r ^ 2 by field_simp,
    neg_div, Real.rpow_neg hpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hpos _).ne']

theorem integrable_heatKernel (z : Vec d) {r : ℝ} (hr : r ≠ 0) :
    Integrable (heatKernel z r) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_heatKernel z hr]
  exact one_ne_zero

theorem norm_sqrtHeatLp_le_one (z : Vec d) (T : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ‖sqrtHeatLp z T hr‖ ≤ 1 := by
  have h : ‖sqrtHeatLp z T hr‖ ^ 2 ≤ 1 := by
    rw [sqrtHeatLp, norm_toLp_sq]
    have e : (fun x => sqrtHeat z r x ^ 2) = heatKernel z r := by
      funext x; rw [sq, sqrtHeat_mul_self hr]
    rw [e, ← integral_heatKernel z hr]
    exact setIntegral_le_integral (integrable_heatKernel z hr)
      (Eventually.of_forall fun x => (heatKernel_pos z hr x).le)
  nlinarith [norm_nonneg (sqrtHeatLp z T hr)]

/-- **The mass of the mask outside `B_T(z)`** is at most `2^{d/2} exp(-T²/(8r²))`. -/
theorem setIntegral_compl_ball_heatKernel_le (z : Vec d) {r : ℝ} (hr : r ≠ 0) (T : ℝ)
    (hT : 0 ≤ T) :
    ∫ x in (ball z T)ᶜ, heatKernel z r x ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) := by
  have hb : 0 < 1 / (8 * r ^ 2) := by positivity
  have hmajor : ∀ x ∈ (ball z T)ᶜ, heatKernel z r x ≤
      Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
        (heatKernelPeak d r * Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))) := by
    intro x hx
    have hxT : T ≤ euclideanNorm (x - z) := not_lt.1 hx
    have hsq : T ^ 2 ≤ euclideanSq (x - z) := by
      rw [← euclideanNorm_sq]; exact pow_le_pow_left₀ hT hxT 2
    rw [heatKernel_eq_exp]
    have hpk := (heatKernelPeak_pos (d := d) hr).le
    calc heatKernelPeak d r * Real.exp (-(1 / (4 * r ^ 2)) * euclideanSq (x - z))
        = heatKernelPeak d r * (Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z)) *
            Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))) := by
          rw [← Real.exp_add]; congr 2; field_simp; ring
      _ ≤ heatKernelPeak d r * (Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
            Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hpk
          refine Real.exp_le_exp.2 ?_
          have h8 : 0 < 8 * r ^ 2 := by positivity
          rw [neg_div, neg_mul, neg_le_neg_iff, div_le_iff₀ h8]
          field_simp
          linarith
      _ = _ := by ring
  have hint : Integrable (fun x => Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      (heatKernelPeak d r * Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z)))) := by
    have h1 := (integrable_exp_neg_mul_euclideanSq (d := d) hb).comp_sub_right z
    exact (h1.const_mul _).const_mul _
  calc ∫ x in (ball z T)ᶜ, heatKernel z r x
      ≤ ∫ x in (ball z T)ᶜ, Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
          (heatKernelPeak d r * Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))) :=
        setIntegral_mono_on (integrable_heatKernel z hr).integrableOn hint.integrableOn
          (measurableSet_ball z T).compl hmajor
    _ ≤ ∫ x, Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
          (heatKernelPeak d r * Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))) :=
        setIntegral_le_integral hint (Eventually.of_forall fun x =>
          mul_nonneg (Real.exp_pos _).le (mul_nonneg (heatKernelPeak_pos hr).le
            (Real.exp_pos _).le))
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) := by
        rw [integral_const_mul, integral_const_mul]
        have htr := integral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
          (fun x => Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq x)) z

        rw [htr, integral_exp_neg_mul_euclideanSq hb, heatKernelPeak]
        have hpos : 0 < 4 * Real.pi * r ^ 2 := by positivity
        rw [show Real.pi / (1 / (8 * r ^ 2)) = 2 * (4 * Real.pi * r ^ 2) by field_simp; ring,
          Real.mul_rpow (by norm_num) hpos.le]
        have key : (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) * (4 * Real.pi * r ^ 2) ^ ((d : ℝ) / 2) =
            1 := by
          rw [← Real.rpow_add hpos, show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
        calc Real.exp (-(T ^ 2) / (8 * r ^ 2)) * ((4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) *
              ((2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * r ^ 2) ^ ((d : ℝ) / 2)))
            = (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
                ((4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) * (4 * Real.pi * r ^ 2) ^ ((d : ℝ) / 2)) := by
              ring
          _ = _ := by rw [key, mul_one]

end QSH
