import QuantitativeStochasticHomogenization.Ch04.Opening.Theorem41

/-!
# Section 4.6: Gaussian averages of rescaled fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6, preliminaries for Theorem 4.24 and (4.126).

The heat kernel average of a rescaled field `F(·/ε)` at the center `x` and the radius `ρ` is the
average of `F` at the center `x/ε` and the radius `ρ/ε` (`integral_heatKernel_rescale`). With the
estimate (4.2) at every center, the heat kernel averages of `∇φ_e(·/ε)` at radii `ρ ≥ ε` are
`O_s(C (ρ/ε)^{-d/2})` (`osBound_rescaled_gradient_average`). The test functions of the normalized
norm `H^{-m}(U)` have derivatives of order `|β| ≤ m` bounded in `L²(U)`
(`scalarRms_multiIndexDerivative_le`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem euclideanSq_smul_eq (c : ℝ) (v : Vec d) : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `Φ_{εz, εr}(εy) = ε^{-d} Φ_{z,r}(y)`. -/
theorem heatKernel_smul (z y : Vec d) {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    heatKernel (ε • z) (ε * r) (ε • y) = ε ^ (-(d : ℝ)) * heatKernel z r y := by
  unfold heatKernel euclideanHeatKernel
  rw [← smul_sub, euclideanSq_smul_eq]
  have h1 : (4 * Real.pi * (ε * r) ^ 2) ^ (-(d : ℝ) / 2) =
      ε ^ (-(d : ℝ)) * (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (ε * r) ^ 2 = ε ^ 2 * (4 * Real.pi * r ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast ε 2,
      ← Real.rpow_mul hε.le]
    congr 2
    push_cast
    ring
  have h2 : -(ε ^ 2 * euclideanSq (y - z)) / (4 * (ε * r) ^ 2) =
      -euclideanSq (y - z) / (4 * r ^ 2) := by
    field_simp
  rw [h1, h2]
  ring

/-- **Rescaling of heat kernel averages**: `∫ Φ_{z,r}(y) F(y/ε) dy = ∫ Φ_{z/ε, r/ε}(y) F(y) dy`. -/
theorem integral_heatKernel_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Vec d → E) (z : Vec d) {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∫ y, heatKernel z r y • F (ε⁻¹ • y) = ∫ y, heatKernel (ε⁻¹ • z) (ε⁻¹ * r) y • F y := by
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  have hk : ∀ y, heatKernel (ε⁻¹ • z) (ε⁻¹ * r) (ε⁻¹ • y) = ε ^ (d : ℝ) * heatKernel z r y :=
    fun y => by
      rw [heatKernel_smul z y hεi hr, Real.inv_rpow hε.le, ← Real.rpow_neg_one,
        ← Real.rpow_mul hε.le]
      congr 2
      ring
  have hcomp := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun y => heatKernel (ε⁻¹ • z) (ε⁻¹ * r) y • F y) ε⁻¹
  rw [Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (by positivity)] at hcomp
  simp only [hk, mul_smul] at hcomp
  rw [integral_smul] at hcomp
  have hεd : (ε : ℝ) ^ (d : ℝ) = ε ^ d := Real.rpow_natCast ε d
  rw [hεd] at hcomp
  exact smul_right_injective E (pow_pos hε d).ne' hcomp

end QSH
