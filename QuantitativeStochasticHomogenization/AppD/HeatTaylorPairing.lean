import QuantitativeStochasticHomogenization.AppD.HeatPairing

/-!
# Appendix D: the Taylor formula of the heat semigroup paired with a field

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: for `0 < s ≤ 1` and `f` bounded by `M` and vanishing outside the unit ball,
`|Φ(s) ∗ f (x)| ≤ 2^{d/2} M exp(-(‖x‖ - 1)₊² / 8)` (`abs_heatSmooth_le`), uniformly in `s`.
Hence a field `F` with `F exp(-‖x‖²/16)` integrable can be paired with the Taylor formula of the
heat semigroup, the remainder being exchanged with the spatial integral by Fubini's theorem
(`integral_mul_heatTaylor`).
-/

open MeasureTheory Filter Set
open scoped ContDiff Topology Convolution Nat

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanHeatKernel_eq_mul {s : ℝ} (hs : 0 < s) (y : Vec d) :
    euclideanHeatKernel s y = 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
      Real.exp (-(euclideanSq y) / (8 * s)) := by
  unfold euclideanHeatKernel
  have h1 : (4 * Real.pi * (2 * s)) = 2 * (4 * Real.pi * s) := by ring
  rw [h1, Real.mul_rpow (x := 2) (y := 4 * Real.pi * s) (by norm_num) (by positivity)]
  have h2 : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp [neg_div]
  have h3 : Real.exp (-(euclideanSq y) / (4 * s)) = Real.exp (-(euclideanSq y) / (4 * (2 * s))) *
      Real.exp (-(euclideanSq y) / (8 * s)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h3]
  calc _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) * ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) *
        (Real.exp (-(euclideanSq y) / (4 * (2 * s))) * Real.exp (-(euclideanSq y) / (8 * s)))) := by
        rw [h2]; ring
    _ = _ := by ring

theorem heatSmooth_eq_integral (s : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    heatSmooth s f x = ∫ y, euclideanHeatKernel s y * f (x - y) := by
  simp [heatSmooth, convolution_def]

/-- The positive part `(‖x‖ - 1)₊`. -/
def distUnitBall (x : Vec d) : ℝ := max (‖x‖ - 1) 0

theorem distUnitBall_sq_ge (x : Vec d) : ‖x‖ ^ 2 / 2 - 1 ≤ distUnitBall x ^ 2 := by
  unfold distUnitBall
  rcases le_or_gt 1 ‖x‖ with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (‖x‖ - 2)]
  · rw [max_eq_right (by linarith)]
    nlinarith [norm_nonneg x]

theorem exp_distUnitBall_le (x : Vec d) :
    Real.exp (-(distUnitBall x ^ 2) / 8) ≤ Real.exp (1 / 8) * Real.exp (-(‖x‖ ^ 2) / 16) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := distUnitBall_sq_ge x
  linarith

/-- **Uniform Gaussian decay of heat-smoothed functions supported in the unit ball.** -/
theorem abs_heatSmooth_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {f : Vec d → ℝ} {M : ℝ}
    (hM : ∀ z, |f z| ≤ M)
    (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ 1) (x : Vec d) :
    |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) := by
  rw [heatSmooth_eq_integral]
  have hs2 : 0 < 2 * s := by positivity
  have hpt : ∀ y, ‖euclideanHeatKernel s y * f (x - y)‖ ≤
      M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) *
        euclideanHeatKernel (2 * s) y := fun y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg hs.le y)]
    by_cases hz : f (x - y) = 0
    · rw [hz, abs_zero, mul_zero]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      have := euclideanHeatKernel_nonneg hs2.le y
      positivity
    have hxy := hsupp _ hz
    have hy : distUnitBall x ≤ ‖y‖ := by
      unfold distUnitBall
      refine max_le ?_ (norm_nonneg y)
      have h2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      linarith
    have hsq : distUnitBall x ^ 2 ≤ euclideanSq y := by
      have h0 : 0 ≤ distUnitBall x := le_max_right _ _
      calc distUnitBall x ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ h0 hy 2
        _ ≤ euclideanSq y := norm_sq_le_euclideanSq y
    have hexp : Real.exp (-(euclideanSq y) / (8 * s)) ≤ Real.exp (-(distUnitBall x ^ 2) / 8) := by
      refine Real.exp_le_exp.mpr ?_
      have h0 : 0 ≤ distUnitBall x ^ 2 := sq_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [euclideanHeatKernel_eq_mul hs y]
    have hK := euclideanHeatKernel_nonneg hs2.le y
    have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := by positivity
    calc 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
          Real.exp (-(euclideanSq y) / (8 * s)) * |f (x - y)|
        ≤ 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
          Real.exp (-(distUnitBall x ^ 2) / 8) * M := by
          gcongr
          exact hM _
      _ = _ := by ring
  calc |∫ y, euclideanHeatKernel s y * f (x - y)|
      ≤ ∫ y, M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) *
        euclideanHeatKernel (2 * s) y :=
        norm_integral_le_of_norm_le ((integrable_euclideanHeatKernel hs2).const_mul _)
          (Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul, integral_euclideanHeatKernel hs2, mul_one]

end QSH
