import QuantitativeStochasticHomogenization.AppD.HeatSmoothing

/-!
# Appendix D: the heat equation for the heat kernel

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D (Sobolev norms and heat flow): the one-dimensional heat kernel
`Φ₁(t, y) = (4πt)^{-1/2} e^{-y²/(4t)}` satisfies `∂ₜ Φ₁ = ∂_y² Φ₁` for `t > 0`
(`hasDerivAt_heatKernel1_time`, `iteratedDeriv_two_heatKernel1`).
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace QSH

/-- The factor `y²/(4t²) - 1/(2t)` of `∂ₜ Φ₁ = ∂_y² Φ₁`. -/
def heatFactor (t y : ℝ) : ℝ := y ^ 2 / (4 * t ^ 2) - 1 / (2 * t)

theorem hasDerivAt_heatKernel1_space {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (heatKernel1 t) (-(y / (2 * t)) * heatKernel1 t y) y := by
  unfold heatKernel1
  have h1 : HasDerivAt (fun y : ℝ => -(y * y) / (4 * t)) (-(2 * y) / (4 * t)) y := by
    have := ((hasDerivAt_id' y).mul (hasDerivAt_id' y)).neg.div_const (4 * t)
    convert this using 1
    ring
  have h2 := h1.exp.const_mul ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2))
  convert h2 using 1
  field_simp
  ring

theorem deriv_heatKernel1 {t : ℝ} (ht : 0 < t) :
    deriv (heatKernel1 t) = fun y => -(y / (2 * t)) * heatKernel1 t y :=
  funext fun y => (hasDerivAt_heatKernel1_space ht y).deriv

theorem hasDerivAt_deriv_heatKernel1 {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (deriv (heatKernel1 t)) (heatFactor t y * heatKernel1 t y) y := by
  rw [deriv_heatKernel1 ht]
  have h1 : HasDerivAt (fun y : ℝ => -(y / (2 * t))) (-(1 / (2 * t))) y :=
    ((hasDerivAt_id' y).div_const (2 * t)).neg
  have := h1.mul (hasDerivAt_heatKernel1_space ht y)
  convert this using 1
  unfold heatFactor
  field_simp
  ring

/-- **`∂_y² Φ₁ = (y²/(4t²) - 1/(2t)) Φ₁`.** -/
theorem iteratedDeriv_two_heatKernel1 {t : ℝ} (ht : 0 < t) (y : ℝ) :
    iteratedDeriv 2 (heatKernel1 t) y = heatFactor t y * heatKernel1 t y := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_heatKernel1 ht y).deriv

/-- **`∂ₜ Φ₁ = (y²/(4t²) - 1/(2t)) Φ₁`.** -/
theorem hasDerivAt_heatKernel1_time {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => heatKernel1 s y) (heatFactor t y * heatKernel1 t y) t := by
  unfold heatKernel1
  have hc : 0 < 4 * Real.pi * t := by positivity
  have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * Real.pi)
  have h1 := hlin.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hc.ne')
  have h2 : HasDerivAt (fun s : ℝ => -(y * y) / (4 * s)) ((y * y) / (4 * t ^ 2)) t := by
    have := (hasDerivAt_inv ht.ne').const_mul (-(y * y) / 4)
    convert this using 1
    · funext s
      ring
    · ring
  refine (h1.mul h2.exp).congr_deriv ?_
  have hr : (4 * Real.pi * t) ^ (-(1 : ℝ) / 2 - 1) =
      (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * t)⁻¹ := by
    rw [Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv]
  rw [hr]
  unfold heatFactor
  field_simp
  ring

end QSH
