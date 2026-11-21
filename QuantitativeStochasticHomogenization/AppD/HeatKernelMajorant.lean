import QuantitativeStochasticHomogenization.AppD.HeatPairing

/-!
# Appendix D: Gaussian majorants of the derivatives of the heat kernel

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: `|∂^β Φ(t)(x)| ≤ C_β (2t)^{-|β|/2} Φ(2t)(x)` for all `t > 0`
(`abs_multiIndexDerivative_euclideanHeatKernel_le`), and the semigroup identity with the derivatives
on the second factor, `∂^β Φ(t + s)(x - z) = ∫ Φ(s)(x - u) ∂^β Φ(t)(u - z) du`
(`multiIndexDerivative_euclideanHeatKernel_semigroup`).
-/

open MeasureTheory Filter
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

theorem abs_iteratedDeriv_heatKernel1_le_gauss (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ y : ℝ,
      |iteratedDeriv k (heatKernel1 t) y| ≤
        C * (Real.sqrt (2 * t))⁻¹ ^ k * heatKernel1 (2 * t) y := by
  obtain ⟨C, hC, hb⟩ := abs_iteratedDeriv_stdGaussian1_le_exp k
  refine ⟨Real.sqrt 2 * C, by positivity, fun t ht y => ?_⟩
  have hq : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  set A := (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) with hAdef
  set B := (Real.sqrt (2 * t))⁻¹ ^ k with hBdef
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hB : 0 < B := pow_pos (inv_pos.mpr hq) k
  rw [iteratedDeriv_heatKernel1 ht, ← hAdef, ← hBdef, abs_mul, abs_of_pos hA, abs_mul,
    abs_of_pos hB]
  have h1 := hb ((Real.sqrt (2 * t))⁻¹ * y)
  have hsq : ((Real.sqrt (2 * t))⁻¹ * y) ^ 2 / 4 = y ^ 2 / (8 * t) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [hsq] at h1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hK : heatKernel1 (2 * t) y = A * (Real.sqrt 2)⁻¹ * Real.exp (-(y ^ 2 / (8 * t))) := by
    unfold heatKernel1
    have h4 : 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) := by ring
    rw [h4, Real.mul_rpow (x := 2) (y := 4 * Real.pi * t) (by norm_num) (by positivity)]
    have h2 : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]
      norm_num
    have h3 : -(y * y) / (4 * (2 * t)) = -(y ^ 2 / (8 * t)) := by ring
    rw [h2, h3, hAdef]
    ring
  rw [hK]
  calc A * (B * |iteratedDeriv k stdGaussian1 ((Real.sqrt (2 * t))⁻¹ * y)|)
      ≤ A * (B * (C * Real.exp (-(y ^ 2 / (8 * t))))) := by gcongr
    _ = Real.sqrt 2 * C * B * (A * (Real.sqrt 2)⁻¹ * Real.exp (-(y ^ 2 / (8 * t)))) := by
        field_simp

/-- **Gaussian majorant of the derivatives of the heat kernel**:
`|∂^β Φ(t)(x)| ≤ C_β (2t)^{-|β|/2} Φ(2t)(x)` for every `t > 0`. -/
theorem abs_multiIndexDerivative_euclideanHeatKernel_le {k : ℕ} (β : Fin d → Fin (k + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      |multiIndexDerivative β (euclideanHeatKernel (d := d) t) x| ≤
        C * (Real.sqrt (2 * t))⁻¹ ^ (∑ i, (β i).val) * euclideanHeatKernel (2 * t) x := by
  have hb := fun i : Fin d => abs_iteratedDeriv_heatKernel1_le_gauss (β i).val
  choose C hC hCb using hb
  refine ⟨∏ i, C i, Finset.prod_nonneg fun i _ => hC i, fun t ht x => ?_⟩
  rw [euclideanHeatKernel_eq_prodFun ht, multiIndexDerivative_prodFun
    (fun _ => contDiff_heatKernel1 t), prodFun, Finset.abs_prod,
    euclideanHeatKernel_eq_prodFun (by positivity : (0 : ℝ) < 2 * t), prodFun,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hCb i t ht (x i)

/-- **The semigroup identity with the derivatives on the second factor**. -/
theorem multiIndexDerivative_euclideanHeatKernel_semigroup {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {k : ℕ} (β : Fin d → Fin (k + 1)) (x z : Vec d) :
    multiIndexDerivative β (euclideanHeatKernel (d := d) (t + s)) (x - z) =
      ∫ u, euclideanHeatKernel s (x - u) *
        multiIndexDerivative β (euclideanHeatKernel (d := d) t) (u - z) := by
  unfold multiIndexDerivative
  rw [foldr_euclideanHeatKernel_semigroup ht hs _ x z]
  set l := (List.finRange d).flatMap fun j => List.replicate (β j).val j
  have h := integral_sub_left_eq_self (fun y : Vec d =>
    l.foldr coordinateDerivative (euclideanHeatKernel (d := d) t) (x - y) *
      euclideanHeatKernel s (y - z)) (volume : Measure (Vec d)) (x + z)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have h1 : x - (x + z - u) = u - z := by abel
  have h2 : x + z - u - z = x - u := by abel
  simp only
  rw [h1, h2, mul_comm]

end QSH
