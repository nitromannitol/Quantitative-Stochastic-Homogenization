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

/-! ## Differentiation under the integral -/

theorem norm_clm_le_sum_coordinate (L : Vec d →L[ℝ] ℝ) : ‖L‖ ≤ ∑ j, |L (unitVector j)| := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _)
    fun u => ?_
  have hu : u = ∑ j, u j • unitVector j := by
    funext k
    simp [unitVector, Pi.single_apply]
  rw [hu, map_sum, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  have hj : |u j| ≤ ‖∑ j, u j • unitVector (d := d) j‖ := by
    rw [← hu]
    exact (Real.norm_eq_abs (u j)) ▸ norm_le_pi_norm u j
  exact mul_le_mul_of_nonneg_left hj (abs_nonneg _)

theorem coordinateDerivative_integral_comp_sub {K : Vec d → ℝ} (hK : ContDiff ℝ ∞ K)
    (hK0 : ∃ C, ∀ v, |K v| ≤ C) (hK1 : ∀ j, ∃ C, ∀ v, |coordinateDerivative j K v| ≤ C)
    {w : Vec d → ℝ} (hw : Integrable w) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (fun x => ∫ y, K (x - y) * w y) x =
      ∫ y, coordinateDerivative j K (x - y) * w y := by
  obtain ⟨C0, hC0⟩ := hK0
  choose C1 hC1 using hK1
  have hdiff : ∀ v, HasFDerivAt K (fderiv ℝ K v) v := fun v =>
    ((hK.differentiable (by simp)) v).hasFDerivAt
  have hcontd : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by simp)
  have hF : ∀ x y, HasFDerivAt (fun x => K (x - y) * w y) (w y • fderiv ℝ K (x - y)) x :=
    fun x y => by
      have h1 : HasFDerivAt (fun x => K (x - y)) (fderiv ℝ K (x - y)) x :=
        (hasFDerivAt_comp_sub y).mpr (hdiff (x - y))
      have := h1.mul_const (w y)
      simpa [mul_comm] using this
  have hbound : ∀ x y, ‖w y • fderiv ℝ K (x - y)‖ ≤ (∑ j, C1 j) * |w y| := fun x y => by
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_right ((norm_clm_le_sum_coordinate _).trans
      (Finset.sum_le_sum fun j _ => hC1 j (x - y))) (abs_nonneg _)
  have hFint : Integrable (fun y => K (x - y) * w y) := by
    refine (hw.abs.const_mul C0).mono' ((hK.continuous.comp (continuous_const.sub
      continuous_id)).aestronglyMeasurable.mul hw.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC0 _) (abs_nonneg _)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (x₀ := x)
    (F := fun x y => K (x - y) * w y) (F' := fun x y => w y • fderiv ℝ K (x - y))
    (bound := fun y => (∑ j, C1 j) * |w y|) Filter.univ_mem
    (Eventually.of_forall fun x =>
      ((hK.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
        hw.aestronglyMeasurable))
    hFint
    (hw.aestronglyMeasurable.smul
      (hcontd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun y x _ => hbound x y)
    ((hw.abs).const_mul _)
    (Eventually.of_forall fun y x _ => hF x y)
  unfold coordinateDerivative
  rw [hmain.fderiv]
  have hint : Integrable (fun y => w y • fderiv ℝ K (x - y)) :=
    ((hw.abs).const_mul (∑ j, C1 j)).mono'
      (hw.aestronglyMeasurable.smul
        (hcontd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => hbound x y)
  rw [ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_apply, smul_eq_mul]
  ring

theorem foldr_integral_comp_sub_heatKernel {t : ℝ} (ht : 0 < t) {w : Vec d → ℝ}
    (hw : Integrable w) (l : List (Fin d)) :
    l.foldr coordinateDerivative (fun x => ∫ y, euclideanHeatKernel t (x - y) * w y) =
      fun x => ∫ y, l.foldr coordinateDerivative (euclideanHeatKernel (d := d) t) (x - y) * w y := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih]
    funext x
    have hK := foldr_coordinateDerivative_contDiff (contDiff_euclideanHeatKernel (d := d) t) l
    obtain ⟨C0, -, hC0⟩ := abs_foldr_euclideanHeatKernel_le (d := d) ht l
    have hK1 : ∀ i, ∃ C, ∀ v, |coordinateDerivative i
        (l.foldr coordinateDerivative (euclideanHeatKernel (d := d) t)) v| ≤ C := fun i => by
      obtain ⟨C, -, hC⟩ := abs_foldr_euclideanHeatKernel_le (d := d) ht (i :: l)
      exact ⟨C, fun v => by simpa using hC v⟩
    exact coordinateDerivative_integral_comp_sub hK ⟨C0, hC0⟩ hK1 hw j x

theorem foldr_comp_sub (l : List (Fin d)) (f : Vec d → ℝ) (z : Vec d) :
    l.foldr coordinateDerivative (fun x => f (x - z)) =
      fun x => l.foldr coordinateDerivative f (x - z) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih]
    funext x
    unfold coordinateDerivative
    rw [fderiv_comp_sub z]
    rfl

/-- **The derivatives of the semigroup identity**: `∂^l Φ(t + s)(x - z) = ∫ ∂^l Φ(t)(x - y) Φ(s)(y - z) dy`. -/
theorem foldr_euclideanHeatKernel_semigroup {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (l : List (Fin d)) (x z : Vec d) :
    l.foldr coordinateDerivative (euclideanHeatKernel (d := d) (t + s)) (x - z) =
      ∫ y, l.foldr coordinateDerivative (euclideanHeatKernel (d := d) t) (x - y) *
        euclideanHeatKernel s (y - z) := by
  have hw : Integrable (fun y => euclideanHeatKernel (d := d) s (y - z)) :=
    (integrable_euclideanHeatKernel hs).comp_sub_right z
  have h1 := congrFun (foldr_integral_comp_sub_heatKernel ht hw l) x
  have h2 : (fun x => ∫ y, euclideanHeatKernel (d := d) t (x - y) *
      euclideanHeatKernel s (y - z)) = fun x => euclideanHeatKernel (t + s) (x - z) :=
    funext fun x => integral_euclideanHeatKernel_mul ht hs x z
  rw [h2, foldr_comp_sub l (euclideanHeatKernel (t + s)) z] at h1
  exact h1

end QSH
