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

/-- **Gaussian decay of the derivatives of the heat kernel**: for `‖y‖ ≤ R`,
`|∂^l Φ(s)(x - y)| ≤ C Φ(4s)(x)`. -/
theorem abs_foldr_euclideanHeatKernel_sub_le {s : ℝ} (hs : 0 < s) (l : List (Fin d)) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Vec d, ‖y‖ ≤ R →
      |l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s) (x - y)| ≤
        C * euclideanHeatKernel (4 * s) x := by
  have hb := fun i : Fin d => abs_iteratedDeriv_heatKernel1_sub_le hs (l.count i) R
  choose C hC hCb using hb
  set c := (4 * Real.pi * (4 * s)) ^ (-(d : ℝ) / 2) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hCp : 0 ≤ ∏ i, C i := Finset.prod_nonneg fun i _ => hC i
  refine ⟨(∏ i, C i) * c⁻¹, by positivity, fun x y hy => ?_⟩
  rw [euclideanHeatKernel_eq_prodFun hs, foldr_coordinateDerivative_prodFun
    (fun _ => contDiff_heatKernel1 s), prodFun, Finset.abs_prod]
  have hprod : ∏ i, |iteratedDeriv (l.count i) (heatKernel1 s) ((x - y) i)| ≤
      ∏ i, (C i * Real.exp (-((x i) ^ 2 / (16 * s)))) :=
    Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ =>
      hCb i (x i) (y i) (by
        have := (norm_le_pi_norm y i).trans hy
        rwa [Real.norm_eq_abs] at this)
  refine hprod.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  unfold euclideanHeatKernel
  rw [mul_assoc]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  congr 1
  simp only [euclideanSq, dot, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem integrable_uncurry_mul_comp_sub {s : ℝ} (hs : 0 < s) (l : List (Fin d)) {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * euclideanHeatKernel (4 * s) x)) {φ : Vec d → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (Function.uncurry fun x y =>
      F x * (l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s) (x - y) * φ y))
      ((volume : Measure (Vec d)).prod volume) := by
  set K := l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s) with hK
  have hKc : Continuous K :=
    (foldr_coordinateDerivative_contDiff (contDiff_euclideanHeatKernel s) l).continuous
  obtain ⟨R, hR⟩ := hcφ.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC, hb⟩ := abs_foldr_euclideanHeatKernel_sub_le hs l R
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hcφ
  have hg : Integrable (fun p : Vec d × Vec d => (C * |F p.1 * euclideanHeatKernel (4 * s) p.1|) *
      |φ p.2|) ((volume : Measure (Vec d)).prod volume) :=
    ((hF.abs.const_mul C)).mul_prod hφi.abs
  refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (hFm.comp_fst).mul ((hKc.comp (continuous_fst.sub continuous_snd)).mul
      (hφ.comp continuous_snd)).aestronglyMeasurable
  · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    by_cases hy : p.2 ∈ tsupport φ
    · have hyR : ‖p.2‖ ≤ R := by
        have := hR hy
        simpa [Metric.mem_closedBall, dist_zero_right] using this
      have h1 := hb p.1 p.2 hyR
      have h2 := euclideanHeatKernel_nonneg (by positivity : (0 : ℝ) ≤ 4 * s) p.1
      rw [abs_of_nonneg h2]
      have h3 := abs_nonneg (F p.1)
      have h4 := abs_nonneg (φ p.2)
      calc |F p.1| * (|K (p.1 - p.2)| * |φ p.2|)
          ≤ |F p.1| * (C * euclideanHeatKernel (4 * s) p.1 * |φ p.2|) := by gcongr
        _ = C * (|F p.1| * euclideanHeatKernel (4 * s) p.1) * |φ p.2| := by ring
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp

theorem convolution_eq_integral_comp_sub (K φ : Vec d → ℝ) (x : Vec d) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x = ∫ y, K (x - y) * φ y := by
  simp [convolution_eq_swap]

theorem integrable_mul_convolution {s : ℝ} (hs : 0 < s) (l : List (Fin d)) {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * euclideanHeatKernel (4 * s) x)) {φ : Vec d → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => F x * ((l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s)) ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x) := by
  refine (integrable_uncurry_mul_comp_sub hs l hFm hF hφ hcφ).integral_prod_left.congr
    (Eventually.of_forall fun x => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [convolution_eq_integral_comp_sub, integral_const_mul]

/-- **Pairing a field with a heat-smoothed test function**:
`∫ F (∂^l Φ(s) ∗ φ) = ∫ φ(y) ∫ F(x) ∂^l Φ(s)(x - y) dx dy` for a field with the Gaussian moment
`∫ |F| Φ(4s) < ∞` and a continuous compactly supported `φ`. -/
theorem integral_mul_convolution_eq {s : ℝ} (hs : 0 < s) (l : List (Fin d)) {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * euclideanHeatKernel (4 * s) x)) {φ : Vec d → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    ∫ x, F x * ((l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s)) ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x =
      ∫ y, φ y * ∫ x, F x * l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s) (x - y) := by
  set K := l.foldr coordinateDerivative (euclideanHeatKernel (d := d) s) with hK
  have hint := integrable_uncurry_mul_comp_sub hs l hFm hF hφ hcφ
  calc ∫ x, F x * (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x
      = ∫ x, ∫ y, F x * (K (x - y) * φ y) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [convolution_eq_integral_comp_sub, integral_const_mul]
    _ = ∫ y, ∫ x, F x * (K (x - y) * φ y) := integral_integral_swap hint
    _ = ∫ y, φ y * ∫ x, F x * K (x - y) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        ring

end QSH
