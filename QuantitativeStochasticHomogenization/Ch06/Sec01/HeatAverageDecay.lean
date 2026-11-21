import QuantitativeStochasticHomogenization.Ch06.Sec01.GaussianTestPairing
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatKernelThirdDerivative

/-!
# Large-time decay of the heat averages of a field with a pairing bound

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1: a field `F` with a pairing bound at the scales above `R₀` and Gaussian moments has
heat averages `∫ Φ_t(x - y) F(y) dy = O(t^{-κ/2})` on the parabolic region `|x|² ≤ t`, `t ≥ R₀²`;
in particular they tend to zero as `t → ∞`. This is the large-time part of the divergence
identity (6.6) of the flux corrector, applied to the flux defect `a(e + ∇φ_e) - ā e`.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem sqrt_rpow_mul_rpow_eq' {t R₀ κ : ℝ} (ht : 0 < t) (hR₀ : 0 < R₀) :
    Real.sqrt t ^ ((d : ℝ) / 2 + 1) * (Real.sqrt t / R₀) ^ (-κ) * (Real.sqrt t)⁻¹ *
      (8 * Real.pi * t) ^ (-(d : ℝ) / 4) =
      R₀ ^ κ * (8 * Real.pi) ^ (-(d : ℝ) / 4) * t ^ (-(κ / 2)) := by
  rw [Real.sqrt_eq_rpow]
  have e1 : (t ^ (1 / 2 : ℝ)) ^ ((d : ℝ) / 2 + 1) = t ^ ((d : ℝ) / 4 + 1 / 2) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have e2 : (t ^ (1 / 2 : ℝ) / R₀) ^ (-κ) = R₀ ^ κ * t ^ (-κ / 2) := by
    rw [Real.div_rpow (by positivity) hR₀.le, ← Real.rpow_mul ht.le, Real.rpow_neg hR₀.le,
      div_inv_eq_mul, mul_comm]
    congr 2
    ring
  have e3 : (t ^ (1 / 2 : ℝ))⁻¹ = t ^ (-(1 / 2 : ℝ)) := (Real.rpow_neg ht.le _).symm
  have e4 : (8 * Real.pi * t) ^ (-(d : ℝ) / 4) =
      (8 * Real.pi) ^ (-(d : ℝ) / 4) * t ^ (-(d : ℝ) / 4) :=
    Real.mul_rpow (by positivity) ht.le
  rw [e1, e2, e3, e4]
  have e5 : t ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (-κ / 2) * t ^ (-(1 / 2 : ℝ)) * t ^ (-(d : ℝ) / 4) =
      t ^ (-(κ / 2)) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  rw [← e5]
  ring

/-- **Large-time decay of the heat averages of a field with a pairing bound.** -/
theorem exists_heatConv_le (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 ≤ κ → Measurable F → HasGaussianMoments F →
      ∀ (t : ℝ) (x : Vec d), R₀ ^ 2 ≤ t → euclideanNorm x ^ 2 ≤ t →
        |∫ y, euclideanHeatKernel t (x - y) * F y| ≤ C * A * R₀ ^ κ * t ^ (-(κ / 2)) := by
  obtain ⟨C, hC, hpair⟩ := exists_gaussianPairing_const d
  refine ⟨C * ((2 : ℝ) ^ ((d : ℝ) / 2) * (1 + Real.sqrt d * 2)) *
    (8 * Real.pi) ^ (-(d : ℝ) / 4), by positivity, ?_⟩
  intro F R₀ A κ hF hR₀ hA hκ hFm hmom t x hRt hxt
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hRt
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  obtain ⟨Bm, hBm⟩ := hmom (2 * t) (by positivity) (euclideanNorm x)
  have hint := (hBm x le_rfl).1
  have hR : R₀ ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hRt
  have hxR : euclideanNorm x ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hxt
  have hΨ : ∀ z : Vec d, |euclideanHeatKernel t z| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * t) z := by
    intro z
    rw [abs_of_nonneg (euclideanHeatKernel_nonneg ht.le z)]
    have h := euclideanHeatKernel_le_mul (d := d) ht (by linarith : t ≤ 2 * t) z
    rwa [show 2 * t / t = 2 by field_simp] at h
  have hgrad : ∀ z : Vec d, euclideanNorm (gradient (euclideanHeatKernel t) z) ≤
      Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t)) *
        euclideanHeatKernel (2 * t) z := by
    intro z
    rw [mul_assoc]
    exact euclideanNorm_le_sqrt_mul_of_abs_le fun l => abs_heatGrad_le ht l z
  have h := hpair hF hR₀ hA hκ hFm (contDiff_euclideanHeatKernel t) ht
    (B := (2 : ℝ) ^ ((d : ℝ) / 2))
    (B' := Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t)))
    (by positivity) (by positivity) hΨ hgrad x hint hR hxR
    (by rw [Real.sq_sqrt ht.le])
  have hsum : (2 : ℝ) ^ ((d : ℝ) / 2) / Real.sqrt t +
      Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t)) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * (1 + Real.sqrt d * 2) * (Real.sqrt t)⁻¹ := by
    field_simp
  have hkey := sqrt_rpow_mul_rpow_eq' (d := d) (κ := κ) ht hR₀
  calc |∫ y, euclideanHeatKernel t (x - y) * F y|
      ≤ C * A * Real.sqrt t ^ ((d : ℝ) / 2 + 1) * (Real.sqrt t / R₀) ^ (-κ) *
          ((2 : ℝ) ^ ((d : ℝ) / 2) / Real.sqrt t +
            Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t))) *
          (8 * Real.pi * t) ^ (-(d : ℝ) / 4) := h
    _ = C * A * ((2 : ℝ) ^ ((d : ℝ) / 2) * (1 + Real.sqrt d * 2)) *
          (Real.sqrt t ^ ((d : ℝ) / 2 + 1) * (Real.sqrt t / R₀) ^ (-κ) * (Real.sqrt t)⁻¹ *
            (8 * Real.pi * t) ^ (-(d : ℝ) / 4)) := by
        rw [hsum]
        ring
    _ = C * ((2 : ℝ) ^ ((d : ℝ) / 2) * (1 + Real.sqrt d * 2)) * (8 * Real.pi) ^ (-(d : ℝ) / 4) *
          A * R₀ ^ κ * t ^ (-(κ / 2)) := by
        rw [hkey]
        ring

/-- The heat averages of a field with a pairing bound and Gaussian moments tend to zero. -/
theorem HasScalePairingBound.tendsto_heatConv {F : Vec d → ℝ} {R₀ A κ : ℝ}
    (hF : HasScalePairingBound F R₀ A κ) (hR₀ : 0 < R₀) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hFm : Measurable F) (hmom : HasGaussianMoments F) (x : Vec d) :
    Tendsto (fun t : ℝ => ∫ y, euclideanHeatKernel t (x - y) * F y) atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := exists_heatConv_le d
  have hlim : Tendsto (fun t : ℝ => C * A * R₀ ^ κ * t ^ (-(κ / 2))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < κ / 2 by positivity)).const_mul (C * A * R₀ ^ κ)
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max (R₀ ^ 2) (euclideanNorm x ^ 2))] with t ht
  rw [Real.norm_eq_abs]
  exact h hF hR₀ hA hκ.le hFm hmom t x ((le_max_left _ _).trans ht) ((le_max_right _ _).trans ht)

end QSH
