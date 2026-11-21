import QuantitativeStochasticHomogenization.AppD.LaplacianExpansion

/-!
# Appendix D: derivatives of the heat semigroup identity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: the derivatives of the heat kernel are bounded (`abs_foldr_euclideanHeatKernel_le`),
and the semigroup identity `Φ(t + s) = Φ(t) ∗ Φ(s)` can be differentiated on the first factor:
`∂^l Φ(t + s)(x - z) = ∫ ∂^l Φ(t)(x - y) Φ(s)(y - z) dy` (`foldr_euclideanHeatKernel_semigroup`).
-/

open MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Bounds on the derivatives -/

theorem abs_iteratedDeriv_stdGaussian1_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |iteratedDeriv k stdGaussian1 u| ≤ C := by
  obtain ⟨K, hK, hb⟩ := abs_eval_le ((Polynomial.hermite k).map (algebraMap ℤ ℝ))
  refine ⟨2 * K, by positivity, fun u => ?_⟩
  rw [iteratedDeriv_stdGaussian1, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    stdGaussian1, abs_of_pos (Real.exp_pos _)]
  have h1 : (1 + Real.exp (u ^ 2 / 4)) * Real.exp (-(u ^ 2 / 2)) ≤ 2 := by
    have e1 : Real.exp (-(u ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
    have e2 : Real.exp (u ^ 2 / 4) * Real.exp (-(u ^ 2 / 2)) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
    nlinarith
  calc |((Polynomial.hermite k).map (algebraMap ℤ ℝ)).eval u| * Real.exp (-(u ^ 2 / 2))
      ≤ K * (1 + Real.exp (u ^ 2 / 4)) * Real.exp (-(u ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
    _ = K * ((1 + Real.exp (u ^ 2 / 4)) * Real.exp (-(u ^ 2 / 2))) := by ring
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left h1 hK
    _ = 2 * K := by ring

theorem abs_iteratedDeriv_heatKernel1_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |iteratedDeriv k (heatKernel1 t) y| ≤ C := by
  obtain ⟨C, hC, hb⟩ := abs_iteratedDeriv_stdGaussian1_le k
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  set c := (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * (Real.sqrt (2 * t))⁻¹ ^ k with hcdef
  have hc : 0 ≤ c := by positivity
  refine ⟨c * C, by positivity, fun y => ?_⟩
  rw [iteratedDeriv_heatKernel1 ht, ← mul_assoc, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hb _) hc

/-- **The derivatives of the heat kernel are bounded.** -/
theorem abs_foldr_euclideanHeatKernel_le {t : ℝ} (ht : 0 < t) (l : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, |l.foldr coordinateDerivative (euclideanHeatKernel (d := d) t) v| ≤ C := by
  have hb := fun i : Fin d => abs_iteratedDeriv_heatKernel1_le ht (l.count i)
  choose C hC hCb using hb
  refine ⟨∏ i, C i, Finset.prod_nonneg fun i _ => hC i, fun v => ?_⟩
  rw [euclideanHeatKernel_eq_prodFun ht, foldr_coordinateDerivative_prodFun
    (fun _ => contDiff_heatKernel1 t), prodFun, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hCb i (v i)

end QSH
