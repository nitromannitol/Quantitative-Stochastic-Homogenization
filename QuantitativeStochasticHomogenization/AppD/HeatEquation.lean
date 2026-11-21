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
    have : List.count i [j, j] = 0 := by simp [Ne.symm hij]
    rw [this, iteratedDeriv_zero]
  rw [hrest]
  ring

/-! ## The heat equation for the heat smoothing of a test function -/

theorem abs_heatFactor_le {t₀ t y : ℝ} (ht₀ : 0 < t₀) (ht : t ∈ Set.Ioo (t₀ / 2) (2 * t₀)) :
    |heatFactor t y| ≤ y ^ 2 / t₀ ^ 2 + 1 / t₀ := by
  have ht0 : 0 < t := lt_trans (by positivity) ht.1
  unfold heatFactor
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  have h1 : y ^ 2 / (4 * t ^ 2) ≤ y ^ 2 / t₀ ^ 2 := by
    apply div_le_div_of_nonneg_left (sq_nonneg y) (by positivity)
    nlinarith [ht.1]
  have h2 : 1 / (2 * t) ≤ 1 / t₀ := by
    apply one_div_le_one_div_of_le ht₀
    linarith [ht.1]
  linarith

theorem euclideanHeatKernel_le_of_mem {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t ∈ Set.Ioo (t₀ / 2) (2 * t₀))
    (s : Vec d) : euclideanHeatKernel t s ≤ (2 * Real.pi * t₀) ^ (-(d : ℝ) / 2) := by
  have ht0 : 0 < t := lt_trans (by positivity) ht.1
  unfold euclideanHeatKernel
  have he : Real.exp (-euclideanSq s / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ euclideanSq s := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr this) (by positivity)
  have hb : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) ≤ (2 * Real.pi * t₀) ^ (-(d : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · nlinarith [Real.pi_pos, ht.1]
    · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
  calc (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-euclideanSq s / (4 * t))
      ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := by rw [mul_one]; exact hb

/-- **The heat equation for the heat smoothing**: `∂ₜ (Φ(t) ∗ χ) = Φ(t) ∗ Δχ` for a smooth compactly
supported `χ`. -/
theorem hasDerivAt_heatSmooth {t : ℝ} (ht : 0 < t) {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (x : Vec d) :
    HasDerivAt (fun τ => heatSmooth τ χ x) (heatSmooth t (coordLaplacian χ) x) t := by
  have hconv : ∀ τ (ψ : Vec d → ℝ), heatSmooth τ ψ x = ∫ s, euclideanHeatKernel τ s * ψ (x - s) :=
    fun τ ψ => by simp [heatSmooth, convolution_def]
  have hcG : ∀ τ, Continuous (euclideanHeatKernel (d := d) τ) := fun τ =>
    (contDiff_euclideanHeatKernel τ).continuous
  have hcF : Continuous (heatFactor t) := by unfold heatFactor; fun_prop
  have hcT : Continuous (kernelTimeDeriv (d := d) t) := by
    unfold kernelTimeDeriv
    exact (continuous_finsetSum _ fun j _ => hcF.comp (continuous_apply j)).mul (hcG t)
  have habs : HasCompactSupport (fun y => |χ y|) := hcχ.comp_left (g := abs) abs_zero
  set c := (2 * Real.pi * t) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hset : Set.Ioo (t / 2) (2 * t) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun τ s => euclideanHeatKernel τ s * χ (x - s))
    (F' := fun τ s => kernelTimeDeriv τ s * χ (x - s))
    (bound := fun s => (∑ j, ((s j) ^ 2 / t ^ 2 + 1 / t)) * c * |χ (x - s)|) hset
    (Filter.Eventually.of_forall fun τ =>
      ((hcG τ).mul (hχ.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (integrable_mul_comp_sub_of_compact (hcG t) hχ.continuous hcχ x)
    ((hcT.mul (hχ.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s τ hτ => by
      rw [Real.norm_eq_abs, abs_mul, kernelTimeDeriv, abs_mul]
      have hτ0 : 0 < τ := lt_trans (by positivity) hτ.1
      have h1 : |∑ j, heatFactor τ (s j)| ≤ ∑ j, ((s j) ^ 2 / t ^ 2 + 1 / t) :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => abs_heatFactor_le ht hτ)
      have h2 : |euclideanHeatKernel τ s| ≤ c := by
        rw [abs_of_nonneg (euclideanHeatKernel_nonneg hτ0.le s)]
        exact euclideanHeatKernel_le_of_mem ht hτ s
      have h3 := abs_nonneg (χ (x - s))
      have h4 : 0 ≤ |∑ j, heatFactor τ (s j)| := abs_nonneg _
      have h5 := abs_nonneg (euclideanHeatKernel τ s)
      calc |∑ j, heatFactor τ (s j)| * |euclideanHeatKernel τ s| * |χ (x - s)|
          ≤ (∑ j, ((s j) ^ 2 / t ^ 2 + 1 / t)) * c * |χ (x - s)| := by gcongr)
    (by
      have hK : Continuous (fun s : Vec d => (∑ j, ((s j) ^ 2 / t ^ 2 + 1 / t)) * c) := by
        fun_prop
      have := integrable_mul_comp_sub_of_compact hK (continuous_abs.comp hχ.continuous) habs x
      exact this)
    (Filter.Eventually.of_forall fun s τ hτ =>
      (hasDerivAt_euclideanHeatKernel_time (lt_trans (by positivity) hτ.1) s).mul_const _)
  have hfun : (fun τ => heatSmooth τ χ x) =
      fun τ => ∫ s, euclideanHeatKernel τ s * χ (x - s) := funext fun τ => hconv τ χ
  rw [hfun]
  refine hmain.2.congr_deriv ?_
  rw [hconv t (coordLaplacian χ)]
  have hjj : ∀ j : Fin d,
      ∫ s, coordinateDerivative j (coordinateDerivative j (euclideanHeatKernel t)) s * χ (x - s) =
        ∫ s, euclideanHeatKernel t s * coordinateDerivative j (coordinateDerivative j χ) (x - s) :=
    fun j => by
      have h := congrFun (convolution_foldr_coordinateDerivative hχ hcχ [j, j]
        (contDiff_euclideanHeatKernel (d := d) t)) x
      simp only [List.foldr_cons, List.foldr_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, convolution_def, ContinuousLinearMap.lsmul_apply,
        smul_eq_mul] at h
      exact h.symm
  have hint1 : ∀ j : Fin d, Integrable (fun s =>
      coordinateDerivative j (coordinateDerivative j (euclideanHeatKernel t)) s * χ (x - s)) :=
    fun j => integrable_mul_comp_sub_of_compact
      (contDiff_coordinateDerivative (contDiff_coordinateDerivative
        (contDiff_euclideanHeatKernel t) j) j).continuous hχ.continuous hcχ x
  have hint2 : ∀ j : Fin d, Integrable (fun s =>
      euclideanHeatKernel t s * coordinateDerivative j (coordinateDerivative j χ) (x - s)) :=
    fun j => integrable_mul_comp_sub_of_compact (hcG t)
      (contDiff_coordinateDerivative (contDiff_coordinateDerivative hχ j) j).continuous
      (hasCompactSupport_coordinateDerivative (hasCompactSupport_coordinateDerivative hcχ j) j) x
  have hlap : ∀ s, kernelTimeDeriv t s * χ (x - s) = ∑ j,
      coordinateDerivative j (coordinateDerivative j (euclideanHeatKernel t)) s * χ (x - s) :=
    fun s => by rw [← coordLaplacian_euclideanHeatKernel ht s, coordLaplacian, Finset.sum_mul]
  simp only [hlap]
  rw [integral_finsetSum _ fun j _ => hint1 j]
  simp only [hjj]
  rw [← integral_finsetSum _ fun j _ => hint2 j]
  congr 1
  funext s
  rw [coordLaplacian, Finset.mul_sum]

end QSH
