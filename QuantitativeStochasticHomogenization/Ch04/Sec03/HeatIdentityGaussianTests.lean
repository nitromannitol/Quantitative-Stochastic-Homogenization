import QuantitativeStochasticHomogenization.Ch06.Sec01.DivergenceFreeGaussianTest
import QuantitativeStochasticHomogenization.AppD.DerivativeCommutation
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianSmoothL2
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses
import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43
import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification
import QuantitativeStochasticHomogenization.AppD.HeatSmoothing

/-!
# Weak identities against Gaussian-decaying tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the heat identity (H) of the route of Proposition 4.10.

If `∫ f η + ∫ G · ∇η = 0` for every smooth compactly supported `η`, and `f` and `G` are integrable
against a heat kernel `Φ(s, x₀ - ·)`, then the identity holds for every smooth `ψ` such that `ψ` and
`∇ψ` are bounded by multiples of `Φ(s, x₀ - ·)` (`integral_mul_add_dot_gradient_eq_zero`). The
proof cuts `ψ` off with the dilations `χ(·/R)` of a bump function and lets `R → ∞`, as in
`integral_dot_gradient_eq_zero_of_hasWeakDivergence`. Consequences for a weak gradient `g` of `φ`:
`∫ φ ∂_j ψ = -∫ g_j ψ` (`HasWeakPartialDerivative.integral_mul_coordinateDerivative_eq`) and the
symmetry `∫ g_j ∂_l ψ = ∫ g_l ∂_j ψ` (`HasWeakGradient.integral_mul_coordinateDerivative_comm`);
for a weakly divergence-free field `F`, `∫ F · ∇ψ = 0`; for a constant vector `c`, `∫ c · ∇ψ = 0`.
-/

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

theorem abs_dot_le_sum_abs (u v : Vec d) : |dot u v| ≤ ∑ k, |u k| * |v k| := by
  unfold dot
  calc |∑ k, u k * v k| ≤ ∑ k, |u k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |u k| * |v k| := Finset.sum_congr rfl fun k _ => abs_mul _ _

theorem abs_component_le_euclideanNorm (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem coordinateDerivative_mul_apply {f g : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (k : Fin d) (y : Vec d) :
    coordinateDerivative k (fun z => f z * g z) y =
      f y * coordinateDerivative k g y + g y * coordinateDerivative k f y := by
  unfold coordinateDerivative
  show (fderiv ℝ (f * g) y) (unitVector k) = _
  rw [((hf y).hasFDerivAt.mul (hg y).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- **Weak identities against Gaussian-decaying tests.** -/
theorem integral_mul_add_dot_gradient_eq_zero {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hfm : AEStronglyMeasurable f volume)
    (hGm : ∀ k, AEStronglyMeasurable (fun y => G y k) volume)
    (hweak : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ y, f y * η y) + ∫ y, dot (G y) (gradient η y) = 0)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y))
    (hfi : Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |f y|))
    (hGi : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |G y k|)) :
    (∫ y, f y * ψ y) + ∫ y, dot (G y) (gradient ψ y) = 0 := by
  let χb : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χb : Vec d → ℝ) := χb.contDiff
  have hχd : Differentiable ℝ (χb : Vec d → ℝ) :=
    (χb.contDiff (n := 1)).differentiable one_ne_zero
  have hψd : Differentiable ℝ ψ := (hψ.of_le (by simp)).differentiable one_ne_zero
  have hψc : Continuous ψ := hψ.continuous
  have hk0 : ∀ y, 0 < euclideanHeatKernel s (x₀ - y) := fun y => by
    unfold euclideanHeatKernel
    positivity
  have hB' : 0 ≤ B' := by
    have h := (Real.sqrt_nonneg _).trans (hψg x₀)
    exact nonneg_of_mul_nonneg_left h (hk0 x₀)
  have hB : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hψb x₀)
    exact nonneg_of_mul_nonneg_left h (hk0 x₀)
  obtain ⟨A, hA⟩ : ∃ A, ∀ k y, |coordinateDerivative k (χb : Vec d → ℝ) y| ≤ A := by
    have h := fun k : Fin d =>
      (contDiff_coordinateDerivative_top hχ k).continuous.bounded_above_of_compact_support
        ((χb.hasCompactSupport).fderiv_apply ℝ (unitVector k))
    choose A hA using h
    refine ⟨∑ k, |A k|, fun k y => ?_⟩
    have h1 := hA k y
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |A k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)))
  set Q : Vec d → ℝ := fun y => ∑ k, euclideanHeatKernel s (x₀ - y) * |G y k| with hQ
  have hQint : Integrable Q := integrable_finsetSum _ fun k _ => hGi k
  have hgradm : ∀ k, Continuous fun y => coordinateDerivative k ψ y := fun k =>
    (contDiff_coordinateDerivative_top hψ k).continuous
  have hdotm : AEStronglyMeasurable (fun y => dot (G y) (gradient ψ y)) volume := by
    unfold dot
    exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (hGm k).mul (hgradm k).aestronglyMeasurable
  have hdotb : ∀ y, |dot (G y) (gradient ψ y)| ≤ B' * Q y := by
    intro y
    refine (abs_dot_le_sum_abs _ _).trans ?_
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := (abs_component_le_euclideanNorm (gradient ψ y) k).trans (hψg y)
    calc |G y k| * |gradient ψ y k| ≤ |G y k| * (B' * euclideanHeatKernel s (x₀ - y)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = B' * (euclideanHeatKernel s (x₀ - y) * |G y k|) := by ring
  have hdotint : Integrable fun y => dot (G y) (gradient ψ y) :=
    (hQint.const_mul B').mono' hdotm
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hdotb y)
  have hfψb : ∀ y, |f y * ψ y| ≤ B * (euclideanHeatKernel s (x₀ - y) * |f y|) := by
    intro y
    rw [abs_mul]
    calc |f y| * |ψ y| ≤ |f y| * (B * euclideanHeatKernel s (x₀ - y)) :=
          mul_le_mul_of_nonneg_left (hψb y) (abs_nonneg _)
      _ = _ := by ring
  -- the cut-off identity at radius `R = n + 1`
  have hcut : ∀ n : ℕ, (∫ y, f y * (χb (((n : ℝ) + 1)⁻¹ • y) * ψ y)) +
      (∫ y, χb (((n : ℝ) + 1)⁻¹ • y) * dot (G y) (gradient ψ y)) =
      -∫ y, ψ y * ∑ k, G y k * (((n : ℝ) + 1)⁻¹ *
        coordinateDerivative k (χb : Vec d → ℝ) (((n : ℝ) + 1)⁻¹ • y)) := by
    intro n
    set c : ℝ := ((n : ℝ) + 1)⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun y => χb (c • y)) := hχ.comp (contDiff_const_smul c)
    have hχcd : Differentiable ℝ (fun y => χb (c • y)) :=
      hχd.comp (differentiable_id.const_smul c)
    have h := hweak (fun y => χb (c • y) * ψ y) (hχc.mul hψ)
      (χb.hasCompactSupport.comp_smul hc0.ne').mul_right
    have hgr : ∀ y, dot (G y) (gradient (fun y => χb (c • y) * ψ y) y) =
        χb (c • y) * dot (G y) (gradient ψ y) +
          ψ y * ∑ k, G y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y)) := by
      intro y
      unfold dot gradient
      simp only [coordinateDerivative_mul_apply hχcd hψd]
      have hder : ∀ k, coordinateDerivative k (fun y => χb (c • y)) y =
          c * coordinateDerivative k (χb : Vec d → ℝ) (c • y) := fun k => by
        simp only [coordinateDerivative]
        exact fderiv_comp_smul_apply hχd c y (unitVector k)
      simp only [hder, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hgr] at h
    have hi1 : Integrable fun y => χb (c • y) * dot (G y) (gradient ψ y) := by
      refine hdotint.norm.mono' ((hχ.continuous.comp (continuous_const_smul c)).aestronglyMeasurable.mul
        hdotm) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg χb.nonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) χb.le_one
    have hi2 : Integrable fun y => ψ y * ∑ k, G y k *
        (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y)) := by
      refine (hQint.const_mul (B * (c * A))).mono' ?_ (Eventually.of_forall fun y => ?_)
      · refine hψc.aestronglyMeasurable.mul (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (hGm k).mul (continuous_const.mul ((contDiff_coordinateDerivative_top hχ k).continuous.comp
            (continuous_const_smul c))).aestronglyMeasurable)
      · rw [Real.norm_eq_abs, abs_mul]
        calc |ψ y| * |∑ k, G y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))|
            ≤ (B * euclideanHeatKernel s (x₀ - y)) * ∑ k, |G y k| * (c * A) := by
              refine mul_le_mul (hψb y) ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _) (mul_nonneg hB (hk0 y).le)
              rw [abs_mul, abs_mul, abs_of_pos hc0]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA k _) hc0.le)
                (abs_nonneg _)
          _ = B * (c * A) * Q y := by
              simp only [hQ, Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
    have hi0 : Integrable fun y => f y * (χb (c • y) * ψ y) := by
      refine (hfi.const_mul B).mono' (hfm.mul ((hχ.continuous.comp
        (continuous_const_smul c)).mul hψc).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      calc |f y * (χb (c • y) * ψ y)| = χb (c • y) * |f y * ψ y| := by
            rw [abs_mul, abs_mul, abs_of_nonneg χb.nonneg, abs_mul]
            ring
        _ ≤ 1 * |f y * ψ y| := mul_le_mul_of_nonneg_right χb.le_one (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hfψb y
    rw [integral_add hi1 hi2] at h
    linarith
  -- the limits
  have hlim0 : Tendsto (fun n : ℕ => ∫ y, f y * (χb (((n : ℝ) + 1)⁻¹ • y) * ψ y))
      atTop (𝓝 (∫ y, f y * ψ y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => B * (euclideanHeatKernel s (x₀ - y) * |f y|)) (fun n => ?_)
      (hfi.const_mul B) (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · exact hfm.mul ((hχ.continuous.comp (continuous_const_smul _)).mul hψc).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      calc |f y * (χb (((n : ℝ) + 1)⁻¹ • y) * ψ y)| =
            χb (((n : ℝ) + 1)⁻¹ • y) * |f y * ψ y| := by
            rw [abs_mul, abs_mul, abs_of_nonneg χb.nonneg, abs_mul]
            ring
        _ ≤ 1 * |f y * ψ y| := mul_le_mul_of_nonneg_right χb.le_one (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hfψb y
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hmem : ((n : ℝ) + 1)⁻¹ • y ∈ Metric.closedBall (0 : Vec d) χb.rIn := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos)]
        change ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
        rw [inv_mul_le_iff₀ hpos]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [χb.one_of_mem_closedBall hmem, one_mul]
  have hlim1 : Tendsto (fun n : ℕ => ∫ y, χb (((n : ℝ) + 1)⁻¹ • y) * dot (G y) (gradient ψ y))
      atTop (𝓝 (∫ y, dot (G y) (gradient ψ y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => B' * Q y) (fun n => ?_)
      (hQint.const_mul B') (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · exact (hχ.continuous.comp (continuous_const_smul _)).aestronglyMeasurable.mul hdotm
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg χb.nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) χb.le_one).trans (hdotb y)
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hmem : ((n : ℝ) + 1)⁻¹ • y ∈ Metric.closedBall (0 : Vec d) χb.rIn := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos)]
        change ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
        rw [inv_mul_le_iff₀ hpos]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [χb.one_of_mem_closedBall hmem, one_mul]
  have hlim2 : Tendsto (fun n : ℕ => -∫ y, ψ y * ∑ k, G y k * (((n : ℝ) + 1)⁻¹ *
      coordinateDerivative k (χb : Vec d → ℝ) (((n : ℝ) + 1)⁻¹ • y))) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, |-∫ y, ψ y * ∑ k, G y k * (((n : ℝ) + 1)⁻¹ *
        coordinateDerivative k (χb : Vec d → ℝ) (((n : ℝ) + 1)⁻¹ • y))| ≤
        ((n : ℝ) + 1)⁻¹ * (B * A * ∫ y, Q y) := by
      intro n
      set c : ℝ := ((n : ℝ) + 1)⁻¹ with hc
      have hc0 : 0 < c := by positivity
      rw [abs_neg]
      calc |∫ y, ψ y * ∑ k, G y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))|
          ≤ ∫ y, |ψ y * ∑ k, G y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ y, c * (B * A) * Q y := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
              ((hQint.const_mul _)) (Eventually.of_forall fun y => ?_)
            dsimp only
            rw [abs_mul]
            calc |ψ y| * |∑ k, G y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))|
                ≤ (B * euclideanHeatKernel s (x₀ - y)) * ∑ k, |G y k| * (c * A) := by
                  refine mul_le_mul (hψb y) ((Finset.abs_sum_le_sum_abs _ _).trans
                    (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _) (mul_nonneg hB (hk0 y).le)
                  rw [abs_mul, abs_mul, abs_of_pos hc0]
                  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA k _) hc0.le)
                    (abs_nonneg _)
              _ = c * (B * A) * Q y := by
                  simp only [hQ, Finset.mul_sum]
                  exact Finset.sum_congr rfl fun k _ => by ring
        _ = c * (B * A * ∫ y, Q y) := by rw [integral_const_mul]; ring
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * (B * A * ∫ y, Q y)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (B * A * ∫ y, Q y)
      simpa [one_div] using this
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hbound n) h0
  have h3 : Tendsto (fun n : ℕ => (∫ y, f y * (χb (((n : ℝ) + 1)⁻¹ • y) * ψ y)) +
      ∫ y, χb (((n : ℝ) + 1)⁻¹ • y) * dot (G y) (gradient ψ y)) atTop (𝓝 0) :=
    hlim2.congr fun n => (hcut n).symm
  exact tendsto_nhds_unique (hlim0.add hlim1) h3

/-! ## Consequences -/

theorem integrable_heatKernel_mul_abs_of_le {s : ℝ} (hs : 0 < s) {x₀ : Vec d} {u v : Vec d → ℝ}
    (hv : Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |v y|))
    (hum : AEStronglyMeasurable u volume) (huv : ∀ y, |u y| ≤ |v y|) :
    Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |u y|) := by
  refine hv.mono' (((continuous_euclideanHeatKernel s).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
    (continuous_abs.comp_aestronglyMeasurable hum)) (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ euclideanHeatKernel s (x₀ - y) := euclideanHeatKernel_nonneg hs.le _
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (huv y) h0

theorem integrable_mul_of_gaussian {s : ℝ} {x₀ : Vec d} {u v : Vec d → ℝ} {B : ℝ}
    (hu : Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |u y|))
    (hum : AEStronglyMeasurable u volume) (hvm : AEStronglyMeasurable v volume)
    (hv : ∀ y, |v y| ≤ B * euclideanHeatKernel s (x₀ - y)) :
    Integrable (fun y => u y * v y) := by
  refine (hu.const_mul B).mono' (hum.mul hvm) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |u y| * |v y| ≤ |u y| * (B * euclideanHeatKernel s (x₀ - y)) :=
        mul_le_mul_of_nonneg_left (hv y) (abs_nonneg _)
    _ = B * (euclideanHeatKernel s (x₀ - y) * |u y|) := by ring

theorem dot_smul_unitVector_gradient (c : ℝ) (j : Fin d) (η : Vec d → ℝ) (y : Vec d) :
    dot (c • unitVector j) (gradient η y) = c * coordinateDerivative j η y := by
  classical
  simp only [dot, Pi.smul_apply, smul_eq_mul, unitVector, Pi.single_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, gradient]

theorem abs_smul_unitVector_apply_le (c : ℝ) (j k : Fin d) : |(c • unitVector j) k| ≤ |c| := by
  classical
  simp only [Pi.smul_apply, smul_eq_mul, unitVector, Pi.single_apply, abs_mul]
  split_ifs <;> simp

/-- **Weak partial derivatives against Gaussian tests**: `∫ φ ∂_j ψ = -∫ g ψ`. -/
theorem HasWeakPartialDerivative.integral_mul_coordinateDerivative_eq {φ g : Vec d → ℝ}
    {j : Fin d} (h : HasWeakPartialDerivative Set.univ j φ g)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y))
    (hφi : Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |φ y|))
    (hgi : Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |g y|)) :
    ∫ y, φ y * coordinateDerivative j ψ y = -∫ y, g y * ψ y := by
  have hφm : AEStronglyMeasurable φ volume :=
    (locallyIntegrableOn_univ.mp h.1).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g volume :=
    (locallyIntegrableOn_univ.mp h.2.1).aestronglyMeasurable
  have hGm : ∀ k, AEStronglyMeasurable (fun y => (φ y • unitVector j : Vec d) k) volume :=
    fun k => hφm.mul_const _
  have hGi : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) *
      |(φ y • unitVector j : Vec d) k|) := fun k =>
    integrable_heatKernel_mul_abs_of_le hs hφi (hGm k) fun y => abs_smul_unitVector_apply_le _ _ _
  have hweak : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ y, g y * η y) + ∫ y, dot (φ y • unitVector j) (gradient η y) = 0 := by
    intro η hη hηc
    simp only [dot_smul_unitVector_gradient]
    have h2 := h.2.2 η ⟨hη, hηc, Set.subset_univ _⟩
    simp only [Measure.restrict_univ] at h2
    linarith
  have key := integral_mul_add_dot_gradient_eq_zero (f := g) (G := fun y => φ y • unitVector j)
    hgm hGm hweak hψ hs hψb hψg hgi hGi
  simp only [dot_smul_unitVector_gradient] at key
  linarith

/-- **The symmetry of the weak second derivatives against Gaussian tests**:
`∫ g_j ∂_l ψ = ∫ g_l ∂_j ψ` for a weak gradient `g`. -/
theorem HasWeakGradient.integral_mul_coordinateDerivative_comm {φ : Vec d → ℝ}
    {g : Vec d → Vec d} (h : HasWeakGradient Set.univ φ g)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y))
    (hgi : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |g y k|)) (j l : Fin d) :
    ∫ y, g y j * coordinateDerivative l ψ y = ∫ y, g y l * coordinateDerivative j ψ y := by
  have hgloc : ∀ k, LocallyIntegrable (fun y => g y k) volume := fun k =>
    locallyIntegrableOn_univ.mp (h k).2.1
  have hgm : ∀ k, AEStronglyMeasurable (fun y => g y k) volume := fun k =>
    (hgloc k).aestronglyMeasurable
  set G : Vec d → Vec d := fun y => g y j • unitVector l - g y l • unitVector j with hG
  have hdotG : ∀ (η : Vec d → ℝ) (y : Vec d), dot (G y) (gradient η y) =
      g y j * coordinateDerivative l η y - g y l * coordinateDerivative j η y := by
    intro η y
    have hsub : dot (G y) (gradient η y) = dot (g y j • unitVector l) (gradient η y) -
        dot (g y l • unitVector j) (gradient η y) := by
      simp only [hG, dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hsub, dot_smul_unitVector_gradient, dot_smul_unitVector_gradient]
  have hGm : ∀ k, AEStronglyMeasurable (fun y => G y k) volume := fun k =>
    ((hgm j).mul_const _).sub ((hgm l).mul_const _)
  have hGi : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |G y k|) := by
    intro k
    refine ((hgi j).add (hgi l)).mono' (((continuous_euclideanHeatKernel s).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      (continuous_abs.comp_aestronglyMeasurable (hGm k))) (Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ euclideanHeatKernel s (x₀ - y) := euclideanHeatKernel_nonneg hs.le _
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg h0]
    have h1 : |G y k| ≤ |g y j| + |g y l| := by
      simp only [hG, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (abs_smul_unitVector_apply_le _ _ _)
        (abs_smul_unitVector_apply_le _ _ _))
    refine le_of_le_of_eq (mul_le_mul_of_nonneg_left h1 h0) ?_
    simp only [Pi.add_apply]
    ring
  have hweak : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ y, (0 : ℝ) * η y) + ∫ y, dot (G y) (gradient η y) = 0 := by
    intro η hη hηc
    simp only [hdotG, zero_mul, integral_zero, zero_add]
    have hl := contDiff_coordinateDerivative_top hη l
    have hj := contDiff_coordinateDerivative_top hη j
    have hlc := hasCompactSupport_coordinateDerivative hηc l
    have hjc := hasCompactSupport_coordinateDerivative hηc j
    have hi1 : Integrable fun y => g y j * coordinateDerivative l η y :=
      (hgloc j).integrable_smul_right_of_hasCompactSupport hl.continuous hlc
    have hi2 : Integrable fun y => g y l * coordinateDerivative j η y :=
      (hgloc l).integrable_smul_right_of_hasCompactSupport hj.continuous hjc
    rw [integral_sub hi1 hi2]
    have e1 := (h j).2.2 (coordinateDerivative l η) ⟨hl, hlc, Set.subset_univ _⟩
    have e2 := (h l).2.2 (coordinateDerivative j η) ⟨hj, hjc, Set.subset_univ _⟩
    simp only [Measure.restrict_univ] at e1 e2
    rw [coordinateDerivative_comm (hη.of_le (by simp)) j l] at e1
    linarith
  have key := integral_mul_add_dot_gradient_eq_zero (f := fun _ => (0 : ℝ)) (G := G)
    aestronglyMeasurable_const hGm hweak hψ hs hψb hψg (by simp) hGi
  simp only [hdotG, zero_mul, integral_zero, zero_add] at key
  have hψgk : ∀ k y, |coordinateDerivative k ψ y| ≤ B' * euclideanHeatKernel s (x₀ - y) :=
    fun k y => (abs_component_le_euclideanNorm (gradient ψ y) k).trans (hψg y)
  have hdm : ∀ k, AEStronglyMeasurable (fun y => coordinateDerivative k ψ y) volume := fun k =>
    (contDiff_coordinateDerivative_top hψ k).continuous.aestronglyMeasurable
  rw [integral_sub (integrable_mul_of_gaussian (hgi j) (hgm j) (hdm l) (hψgk l))
    (integrable_mul_of_gaussian (hgi l) (hgm l) (hdm j) (hψgk j))] at key
  linarith

/-- **Divergence-free fields against Gaussian tests**: `∫ F · ∇ψ = 0`. -/
theorem HasWeakDivergence.integral_dot_gradient_eq_zero_of_gaussian {F : Vec d → Vec d}
    (h : HasWeakDivergence Set.univ F (fun _ => 0))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y))
    (hFi : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |F y k|)) :
    ∫ y, dot (F y) (gradient ψ y) = 0 := by
  have hFm : ∀ k, AEStronglyMeasurable (fun y => F y k) volume := fun k =>
    (locallyIntegrableOn_univ.mp (h.1 k)).aestronglyMeasurable
  have hweak : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ y, (0 : ℝ) * η y) + ∫ y, dot (F y) (gradient η y) = 0 := by
    intro η hη hηc
    have h2 := h.2.2 η ⟨hη, hηc, Set.subset_univ _⟩
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h2
    simp only [zero_mul, integral_zero, zero_add]
    exact h2
  have key := integral_mul_add_dot_gradient_eq_zero (f := fun _ => (0 : ℝ)) (G := F)
    aestronglyMeasurable_const hFm hweak hψ hs hψb hψg (by simp) hFi
  simpa using key

/-- **Constant fields against Gaussian tests**: `∫ c · ∇ψ = 0`. -/
theorem integral_dot_const_gradient_eq_zero (c : Vec d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y)) :
    ∫ y, dot c (gradient ψ y) = 0 := by
  have hψd : Differentiable ℝ ψ := (hψ.of_le (by simp)).differentiable one_ne_zero
  have hK : Integrable (fun y => euclideanHeatKernel s (x₀ - y)) :=
    (integrable_euclideanHeatKernel hs).comp_sub_left x₀
  have hcm : AEStronglyMeasurable (fun y => dot c (gradient ψ y)) volume := by
    unfold dot gradient
    exact Finset.aestronglyMeasurable_fun_sum _ fun k _ => aestronglyMeasurable_const.mul
      (contDiff_coordinateDerivative_top hψ k).continuous.aestronglyMeasurable
  have hfd : ∀ y, fderiv ℝ ψ y c = dot c (gradient ψ y) := by
    intro y
    rw [fderiv_apply_eq_sum_coordinateDerivative (χ := ψ) y c]
    rfl
  have hint : Integrable (fun y => dot c (gradient ψ y)) := by
    refine (hK.const_mul (euclideanNorm c * B')).mono' hcm (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    calc |dot c (gradient ψ y)| ≤ euclideanNorm c * euclideanNorm (gradient ψ y) :=
          BaseExponent.abs_dot_le _ _
      _ ≤ euclideanNorm c * (B' * euclideanHeatKernel s (x₀ - y)) :=
          mul_le_mul_of_nonneg_left (hψg y) (BaseExponent.euclideanNorm_nonneg _)
      _ = _ := by ring
  have hψi : Integrable ψ :=
    (hK.const_mul B).mono' hψ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hψb y)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Vec d => (1 : ℝ)) (g := ψ) (v := c)
    (by simp) (by simpa [hfd] using hint) (by simpa using hψi)
    (fun x _ => differentiableAt_const _) (fun x _ => hψd x)
  simpa [hfd] using h

/-- **The symmetry of the weak second derivatives in directions `v`, `w`**:
`∫ (v · g) D_w ψ = ∫ (w · g) D_v ψ`. -/
theorem HasWeakGradient.integral_dot_mul_fderiv_comm {φ : Vec d → ℝ}
    {g : Vec d → Vec d} (h : HasWeakGradient Set.univ φ g)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y))
    (hgi : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |g y k|)) (v w : Vec d) :
    ∫ y, dot v (g y) * fderiv ℝ ψ y w = ∫ y, dot w (g y) * fderiv ℝ ψ y v := by
  have hexp : ∀ (v w : Vec d) (y : Vec d), dot v (g y) * fderiv ℝ ψ y w =
      ∑ j, ∑ l, v j * w l * (g y j * coordinateDerivative l ψ y) := by
    intro v w y
    rw [fderiv_apply_eq_sum_coordinateDerivative (χ := ψ) y w]
    simp only [dot, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hgm : ∀ k, AEStronglyMeasurable (fun y => g y k) volume := fun k =>
    (locallyIntegrableOn_univ.mp (h k).2.1).aestronglyMeasurable
  have hψgk : ∀ k y, |coordinateDerivative k ψ y| ≤ B' * euclideanHeatKernel s (x₀ - y) :=
    fun k y => (abs_component_le_euclideanNorm (gradient ψ y) k).trans (hψg y)
  have hdm : ∀ k, AEStronglyMeasurable (fun y => coordinateDerivative k ψ y) volume := fun k =>
    (contDiff_coordinateDerivative_top hψ k).continuous.aestronglyMeasurable
  have hint : ∀ j l, Integrable (fun y => g y j * coordinateDerivative l ψ y) := fun j l =>
    integrable_mul_of_gaussian (hgi j) (hgm j) (hdm l) (hψgk l)
  have hcomm := h.integral_mul_coordinateDerivative_comm hψ hs hψb hψg hgi
  have hL : ∀ v w : Vec d, ∫ y, dot v (g y) * fderiv ℝ ψ y w =
      ∑ j, ∑ l, v j * w l * ∫ y, g y j * coordinateDerivative l ψ y := by
    intro v w
    rw [integral_congr_ae (Eventually.of_forall (hexp v w)), integral_finsetSum _
      (fun j _ => integrable_finsetSum _ fun l _ => (hint j l).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun l _ => (hint j l).const_mul _)]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  rw [hL v w, hL w v, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcomm j l]
  ring

end QSH
