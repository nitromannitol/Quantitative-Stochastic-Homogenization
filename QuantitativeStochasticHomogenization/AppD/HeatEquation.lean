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

/-! ## The heat equation in dimension `d` -/

variable {d : ℕ}

/-- `∂ₜ Φ(t, s) = (∑ⱼ (sⱼ²/(4t²) - 1/(2t))) Φ(t, s)`. -/
def kernelTimeDeriv (t : ℝ) (s : Vec d) : ℝ :=
  (∑ j, heatFactor t (s j)) * euclideanHeatKernel t s

theorem hasDerivAt_euclideanHeatKernel_time {t : ℝ} (ht : 0 < t) (s : Vec d) :
    HasDerivAt (fun τ => euclideanHeatKernel τ s) (kernelTimeDeriv t s) t := by
  classical
  have hev : (fun τ => euclideanHeatKernel τ s) =ᶠ[nhds t] fun τ => ∏ i, heatKernel1 τ (s i) := by
    filter_upwards [lt_mem_nhds ht] with τ hτ
    rw [euclideanHeatKernel_eq_prodFun hτ, prodFun]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := t)
    (f := fun i τ => heatKernel1 τ (s i)) fun i _ => hasDerivAt_heatKernel1_time ht (s i)
  refine hp.congr_deriv ?_
  rw [kernelTimeDeriv, euclideanHeatKernel_eq_prodFun ht, prodFun, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, ← Finset.mul_prod_erase Finset.univ (fun j => heatKernel1 t (s j))
    (Finset.mem_univ i)]
  ring

/-- The Laplacian `∑ⱼ ∂ⱼ∂ⱼ χ` in coordinates. -/
def coordLaplacian (χ : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ j, coordinateDerivative j (coordinateDerivative j χ) x

theorem coordLaplacian_euclideanHeatKernel {t : ℝ} (ht : 0 < t) (s : Vec d) :
    coordLaplacian (euclideanHeatKernel t) s = kernelTimeDeriv t s := by
  classical
  unfold coordLaplacian kernelTimeDeriv
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := foldr_coordinateDerivative_prodFun (fun _ => contDiff_heatKernel1 t) [j, j]
  simp only [List.foldr_cons, List.foldr_nil] at h
  rw [euclideanHeatKernel_eq_prodFun ht, h, prodFun, prodFun,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => heatKernel1 t (s i)) (Finset.mem_univ j)]
  have hcj : List.count j [j, j] = 2 := by simp
  rw [hcj, iteratedDeriv_two_heatKernel1 ht]
  have hrest : ∏ x ∈ Finset.univ.erase j, iteratedDeriv (List.count x [j, j]) (heatKernel1 t) (s x) =
      ∏ x ∈ Finset.univ.erase j, heatKernel1 t (s x) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have : List.count i [j, j] = 0 := by simp [List.count_cons, Ne.symm hij]
    rw [this, iteratedDeriv_zero]
  rw [hrest]
  ring

end QSH
