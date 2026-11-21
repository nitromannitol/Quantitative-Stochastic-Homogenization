import QuantitativeStochasticHomogenization.AppD.ProductDerivatives
import QuantitativeStochasticHomogenization.Ch04.Opening

/-!
# Appendix D: derivatives of the heat kernel

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D (Sobolev norms and heat flow): the derivatives of the heat kernel
`Φ(t, x) = (4πt)^{-d/2} e^{-|x|²/(4t)}` satisfy `‖∂^β Φ(t, ·)‖_{L¹} = C_β t^{-|β|/2}`.

The heat kernel is the product of the one-dimensional kernels `(4πt)^{-1/2} e^{-y²/(4t)}`, a rescaled
standard Gaussian `γ(u) = e^{-u²/2}`, whose derivatives `γ^{(k)} = (-1)^k Heₖ γ` are integrable.
-/

open MeasureTheory Polynomial
open scoped ContDiff Nat

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The standard Gaussian -/

/-- The standard Gaussian `γ(u) = e^{-u²/2}`. -/
def stdGaussian1 (u : ℝ) : ℝ := Real.exp (-(u ^ 2 / 2))

theorem contDiff_stdGaussian1 : ContDiff ℝ ∞ stdGaussian1 := by
  unfold stdGaussian1
  fun_prop

theorem abs_pow_le_one_add_exp (u : ℝ) (j : ℕ) :
    |u| ^ j ≤ 1 + 4 ^ j * (j ! : ℝ) * Real.exp (u ^ 2 / 4) := by
  have h1 : |u| ^ j ≤ 1 + (u ^ 2) ^ j := by
    rcases le_or_gt |u| 1 with h | h
    · have := pow_le_one₀ (n := j) (abs_nonneg u) h
      have : 0 ≤ (u ^ 2) ^ j := by positivity
      linarith
    · have h2 : |u| ^ j ≤ (|u| ^ 2) ^ j := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ h.le (by omega)
      rw [sq_abs] at h2
      linarith
  have h3 : (u ^ 2 / 4) ^ j / (j ! : ℝ) ≤ Real.exp (u ^ 2 / 4) :=
    Real.pow_div_factorial_le_exp (u ^ 2 / 4) (by positivity) j
  have hfac : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have h4 : (u ^ 2) ^ j = 4 ^ j * (u ^ 2 / 4) ^ j := by
    rw [div_pow, mul_div_cancel₀ _ (by positivity)]
  have h5 : (u ^ 2 / 4) ^ j ≤ (j ! : ℝ) * Real.exp (u ^ 2 / 4) := by
    rw [div_le_iff₀ hfac] at h3
    linarith
  have h6 : (u ^ 2) ^ j ≤ 4 ^ j * (j ! : ℝ) * Real.exp (u ^ 2 / 4) := by
    rw [h4, mul_assoc]
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  linarith

theorem abs_eval_le (p : ℝ[X]) : ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
    |p.eval u| ≤ K * (1 + Real.exp (u ^ 2 / 4)) := by
  refine ⟨∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j| * (1 + 4 ^ j * (j ! : ℝ)),
    Finset.sum_nonneg fun j _ => by positivity, fun u => ?_⟩
  rw [eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_pow]
  have hj := abs_pow_le_one_add_exp u j
  have he : 0 ≤ Real.exp (u ^ 2 / 4) := (Real.exp_pos _).le
  have hc := abs_nonneg (p.coeff j)
  calc |p.coeff j| * |u| ^ j ≤ |p.coeff j| * (1 + 4 ^ j * (j ! : ℝ) * Real.exp (u ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left hj hc
    _ ≤ |p.coeff j| * (1 + 4 ^ j * (j ! : ℝ)) * (1 + Real.exp (u ^ 2 / 4)) := by
        have : 0 ≤ (4 : ℝ) ^ j * (j ! : ℝ) := by positivity
        nlinarith [mul_nonneg hc this, mul_nonneg hc he, mul_nonneg (mul_nonneg hc this) he]

theorem iteratedDeriv_stdGaussian1 (k : ℕ) (u : ℝ) :
    iteratedDeriv k stdGaussian1 u =
      (-1 : ℝ) ^ k * ((hermite k).map (algebraMap ℤ ℝ)).eval u * stdGaussian1 u := by
  rw [iteratedDeriv_eq_iterate, eval_map, ← aeval_def]
  exact deriv_gaussian_eq_hermite_mul_gaussian k u

theorem integrable_iteratedDeriv_stdGaussian1 (k : ℕ) :
    Integrable (iteratedDeriv k stdGaussian1) := by
  obtain ⟨K, hK, hb⟩ := abs_eval_le ((hermite k).map (algebraMap ℤ ℝ))
  have hg1 : Integrable (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hg2 : Integrable (fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine Integrable.mono' ((hg1.add hg2).const_mul K)
    ((contDiff_stdGaussian1.continuous_iteratedDeriv k (by simp)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, iteratedDeriv_stdGaussian1, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, stdGaussian1, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (u ^ 2 / 4) * Real.exp (-(u ^ 2 / 2)) = Real.exp (-(1 / 4 : ℝ) * u ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-(u ^ 2 / 2)) = Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by congr 1; ring
  calc |((hermite k).map (algebraMap ℤ ℝ)).eval u| * Real.exp (-(u ^ 2 / 2))
      ≤ K * (1 + Real.exp (u ^ 2 / 4)) * Real.exp (-(u ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
    _ = K * (Real.exp (-(1 / 2 : ℝ) * u ^ 2) + Real.exp (-(1 / 4 : ℝ) * u ^ 2)) := by
        rw [mul_assoc, add_mul, one_mul, he, he2]

/-! ## The one-dimensional heat kernel -/

/-- The one-dimensional heat kernel `(4πt)^{-1/2} e^{-y²/(4t)}`. -/
def heatKernel1 (t y : ℝ) : ℝ := (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(y * y) / (4 * t))

theorem heatKernel1_eq {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatKernel1 t y = (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) *
      stdGaussian1 ((Real.sqrt (2 * t))⁻¹ * y) := by
  unfold heatKernel1 stdGaussian1
  congr 2
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem euclideanHeatKernel_eq_prodFun {t : ℝ} (ht : 0 < t) :
    euclideanHeatKernel (d := d) t = prodFun (fun _ => heatKernel1 t) := by
  funext x
  rw [euclideanHeatKernel_eq_prod, prodFun]
  unfold heatKernel1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  ring

theorem contDiff_heatKernel1 (t : ℝ) : ContDiff ℝ ∞ (heatKernel1 t) := by
  unfold heatKernel1
  fun_prop

theorem iteratedDeriv_heatKernel1 {t : ℝ} (ht : 0 < t) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (heatKernel1 t) y = (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) *
      ((Real.sqrt (2 * t))⁻¹ ^ k * iteratedDeriv k stdGaussian1 ((Real.sqrt (2 * t))⁻¹ * y)) := by
  have hfun : heatKernel1 t = fun y => (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) *
      stdGaussian1 ((Real.sqrt (2 * t))⁻¹ * y) := funext (heatKernel1_eq ht)
  rw [hfun, iteratedDeriv_const_mul _ (by
      have := (contDiff_stdGaussian1.comp (contDiff_const.mul contDiff_id) :
        ContDiff ℝ ∞ (fun y => stdGaussian1 ((Real.sqrt (2 * t))⁻¹ * y)))
      exact (contDiff_infty.mp this k).contDiffAt),
    iteratedDeriv_comp_const_mul (contDiff_infty.mp contDiff_stdGaussian1 k)]

/-- `∫ |∂ᵏ Φ₁(t, ·)| = (2π)^{-1/2} (2t)^{-k/2} ∫ |γ^{(k)}|`. -/
theorem integral_abs_iteratedDeriv_heatKernel1 {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∫ y, |iteratedDeriv k (heatKernel1 t) y| =
      (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.sqrt (2 * t) * (Real.sqrt (2 * t))⁻¹ ^ k *
        ∫ u, |iteratedDeriv k stdGaussian1 u| := by
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  simp only [iteratedDeriv_heatKernel1 ht, abs_mul]
  rw [integral_const_mul, integral_const_mul]
  have hc := Measure.integral_comp_mul_left (fun u => |iteratedDeriv k stdGaussian1 u|)
    (Real.sqrt (2 * t))⁻¹
  rw [hc, inv_inv, abs_of_pos hs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
    abs_of_pos (pow_pos (inv_pos.mpr hs) _), smul_eq_mul]
  ring

theorem integrable_iteratedDeriv_heatKernel1 {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (iteratedDeriv k (heatKernel1 t)) := by
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  have h := ((integrable_iteratedDeriv_stdGaussian1 k).comp_mul_left'
    (inv_ne_zero hs.ne')).const_mul ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * (Real.sqrt (2 * t))⁻¹ ^ k)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  rw [iteratedDeriv_heatKernel1 ht]
  ring

/-! ## The heat kernel in dimension `d` -/

/-- **`∂^β Φ(t, ·)` is integrable**, as a product of integrable one-dimensional derivatives. -/
theorem integrable_multiIndexDerivative_euclideanHeatKernel {m : ℕ} {t : ℝ} (ht : 0 < t)
    (β : Fin d → Fin (m + 1)) :
    Integrable (multiIndexDerivative β (euclideanHeatKernel (d := d) t)) := by
  rw [euclideanHeatKernel_eq_prodFun ht,
    multiIndexDerivative_prodFun (fun _ => contDiff_heatKernel1 t) β]
  exact Integrable.fintype_prod (f := fun i => iteratedDeriv (β i).val (heatKernel1 t))
    (μ := fun _ => volume) fun i => integrable_iteratedDeriv_heatKernel1 ht _

/-- **`‖∂^β Φ(t, ·)‖_{L¹} = ∏ᵢ ‖∂^{βᵢ} Φ₁(t, ·)‖_{L¹}`.** -/
theorem integral_abs_multiIndexDerivative_euclideanHeatKernel {m : ℕ} {t : ℝ} (ht : 0 < t)
    (β : Fin d → Fin (m + 1)) :
    ∫ x, |multiIndexDerivative β (euclideanHeatKernel (d := d) t) x| =
      ∏ i, ∫ y, |iteratedDeriv (β i).val (heatKernel1 t) y| := by
  rw [euclideanHeatKernel_eq_prodFun ht,
    multiIndexDerivative_prodFun (fun _ => contDiff_heatKernel1 t) β]
  simp only [prodFun, Finset.abs_prod]
  exact integral_fintype_prod_eq_prod (μ := fun _ => volume)
    (fun i y => |iteratedDeriv (β i).val (heatKernel1 t) y|)

end QSH
