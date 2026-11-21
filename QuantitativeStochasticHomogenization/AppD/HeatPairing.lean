import QuantitativeStochasticHomogenization.AppD.HeatSemigroupDerivatives

/-!
# Appendix D: pairing a field with heat-smoothed test functions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: the derivatives of the heat kernel have Gaussian decay uniformly in translations by a
bounded vector (`abs_foldr_euclideanHeatKernel_sub_le`), so that a field `F` with Gaussian moments
can be paired with `∂^l Φ(s) ∗ φ`, `φ` continuous with compact support, by Fubini's theorem:
`∫ F (∂^l Φ(s) ∗ φ) = ∫ φ(y) ∫ F(x) ∂^l Φ(s)(x - y) dx dy` (`integral_mul_convolution_eq`).
-/

open MeasureTheory Filter
open scoped ContDiff Topology Convolution

noncomputable section

namespace QSH

variable {d : ℕ}

theorem abs_iteratedDeriv_stdGaussian1_le_exp (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |iteratedDeriv k stdGaussian1 u| ≤ C * Real.exp (-(u ^ 2 / 4)) := by
  obtain ⟨K, hK, hb⟩ := abs_eval_le ((Polynomial.hermite k).map (algebraMap ℤ ℝ))
  refine ⟨2 * K, by positivity, fun u => ?_⟩
  rw [iteratedDeriv_stdGaussian1, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    stdGaussian1, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (-(u ^ 2 / 2)) ≤ Real.exp (-(u ^ 2 / 4)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have e2 : Real.exp (u ^ 2 / 4) * Real.exp (-(u ^ 2 / 2)) = Real.exp (-(u ^ 2 / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |((Polynomial.hermite k).map (algebraMap ℤ ℝ)).eval u| * Real.exp (-(u ^ 2 / 2))
      ≤ K * (1 + Real.exp (u ^ 2 / 4)) * Real.exp (-(u ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
    _ = K * (Real.exp (-(u ^ 2 / 2)) + Real.exp (u ^ 2 / 4) * Real.exp (-(u ^ 2 / 2))) := by ring
    _ ≤ K * (Real.exp (-(u ^ 2 / 4)) + Real.exp (-(u ^ 2 / 4))) := by
        rw [e2]; gcongr
    _ = 2 * K * Real.exp (-(u ^ 2 / 4)) := by ring

theorem abs_iteratedDeriv_heatKernel1_sub_le {s : ℝ} (hs : 0 < s) (k : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |y| ≤ R →
      |iteratedDeriv k (heatKernel1 s) (x - y)| ≤ C * Real.exp (-(x ^ 2 / (16 * s))) := by
  obtain ⟨C, hC, hb⟩ := abs_iteratedDeriv_stdGaussian1_le_exp k
  have hq : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.mpr (by positivity)
  set c := (4 * Real.pi * s) ^ (-(1 : ℝ) / 2) * (Real.sqrt (2 * s))⁻¹ ^ k with hcdef
  have hc : 0 ≤ c := by positivity
  refine ⟨c * C * Real.exp (R ^ 2 / (8 * s)), by positivity, fun x y hy => ?_⟩
  rw [iteratedDeriv_heatKernel1 hs, ← mul_assoc, abs_mul, abs_of_nonneg hc]
  have h1 := hb ((Real.sqrt (2 * s))⁻¹ * (x - y))
  have hsq : ((Real.sqrt (2 * s))⁻¹ * (x - y)) ^ 2 / 4 = (x - y) ^ 2 / (8 * s) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [hsq] at h1
  have h2 : Real.exp (-((x - y) ^ 2 / (8 * s))) ≤
      Real.exp (R ^ 2 / (8 * s)) * Real.exp (-(x ^ 2 / (16 * s))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hy2 : y ^ 2 ≤ R ^ 2 := by
      have := abs_nonneg y
      nlinarith [abs_mul_abs_self y, sq_abs y]
    have hxy : x ^ 2 / 2 - y ^ 2 ≤ (x - y) ^ 2 := by nlinarith [sq_nonneg (x - 2 * y)]
    have key : -(x - y) ^ 2 ≤ R ^ 2 - x ^ 2 / 2 := by linarith
    calc -((x - y) ^ 2 / (8 * s)) = (-(x - y) ^ 2) / (8 * s) := by ring
      _ ≤ (R ^ 2 - x ^ 2 / 2) / (8 * s) := div_le_div_of_nonneg_right key (by positivity)
      _ = R ^ 2 / (8 * s) + -(x ^ 2 / (16 * s)) := by field_simp; ring
  calc c * |iteratedDeriv k stdGaussian1 ((Real.sqrt (2 * s))⁻¹ * (x - y))|
      ≤ c * (C * Real.exp (-((x - y) ^ 2 / (8 * s)))) := mul_le_mul_of_nonneg_left h1 hc
    _ ≤ c * (C * (Real.exp (R ^ 2 / (8 * s)) * Real.exp (-(x ^ 2 / (16 * s))))) := by gcongr
    _ = c * C * Real.exp (R ^ 2 / (8 * s)) * Real.exp (-(x ^ 2 / (16 * s))) := by ring

end QSH
