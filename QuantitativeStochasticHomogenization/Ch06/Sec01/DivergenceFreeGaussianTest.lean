import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatAverageDecay
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientDilation

/-!
# Divergence-free fields against Gaussian-decaying tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1: a weakly divergence-free field `q` on `ℝ^d` with Gaussian moments satisfies
`∫ q·∇ψ = 0` for every smooth `ψ` such that `ψ` and `∇ψ` are bounded by multiples of a heat kernel.
The proof cuts `ψ` off with the dilations `χ(·/R)` of a bump function and lets `R → ∞`.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem abs_dot_le_sum (u v : Vec d) : |dot u v| ≤ ∑ k, |u k| * |v k| := by
  unfold dot
  calc |∑ k, u k * v k| ≤ ∑ k, |u k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |u k| * |v k| := Finset.sum_congr rfl fun k _ => abs_mul _ _

private theorem abs_apply_le_euclideanNorm' (v : Vec d) (k : Fin d) : |v k| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ k)

private theorem coordinateDerivative_mul {f g : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (k : Fin d) (y : Vec d) :
    coordinateDerivative k (fun z => f z * g z) y =
      f y * coordinateDerivative k g y + g y * coordinateDerivative k f y := by
  unfold coordinateDerivative
  show (fderiv ℝ (f * g) y) (unitVector k) = _
  rw [((hf y).hasFDerivAt.mul (hg y).hasFDerivAt).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]

/-- **A divergence-free field annihilates gradients of Gaussian-decaying tests.** -/
theorem integral_dot_gradient_eq_zero_of_hasWeakDivergence {q : Vec d → Vec d}
    (hq : HasWeakDivergence Set.univ q (fun _ => 0)) (hqm : ∀ k, Measurable fun y => q y k)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d} {s B B' : ℝ} (hs : 0 < s)
    (hψb : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x₀ - y))
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y))
    (hint : ∀ k, Integrable (fun y => euclideanHeatKernel s (x₀ - y) * |q y k|)) :
    ∫ y, dot (q y) (gradient ψ y) = 0 := by
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
      (contDiff_coordinateDerivative hχ k).continuous.bounded_above_of_compact_support
        ((χb.hasCompactSupport).fderiv_apply ℝ (unitVector k))
    choose A hA using h
    refine ⟨∑ k, |A k|, fun k y => ?_⟩
    have h1 := hA k y
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |A k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)))
  -- the integrable majorant
  set Q : Vec d → ℝ := fun y => ∑ k, euclideanHeatKernel s (x₀ - y) * |q y k| with hQ
  have hQint : Integrable Q := integrable_finsetSum _ fun k _ => hint k
  have hQ0 : ∀ y, 0 ≤ Q y := fun y =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hk0 y).le (abs_nonneg _)
  have hgradm : ∀ k, Continuous fun y => coordinateDerivative k ψ y := fun k =>
    (contDiff_coordinateDerivative hψ k).continuous
  have hdotm : Measurable fun y => dot (q y) (gradient ψ y) := by
    unfold dot
    exact Finset.measurable_sum _ fun k _ => (hqm k).mul (hgradm k).measurable
  have hdotb : ∀ y, |dot (q y) (gradient ψ y)| ≤ B' * Q y := by
    intro y
    refine (abs_dot_le_sum _ _).trans ?_
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := (abs_apply_le_euclideanNorm' (gradient ψ y) k).trans (hψg y)
    calc |q y k| * |gradient ψ y k| ≤ |q y k| * (B' * euclideanHeatKernel s (x₀ - y)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = B' * (euclideanHeatKernel s (x₀ - y) * |q y k|) := by ring
  have hdotint : Integrable fun y => dot (q y) (gradient ψ y) :=
    (hQint.const_mul B').mono' hdotm.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hdotb y)
  -- the cut-off identity at radius `R = n + 1`
  have hcut : ∀ n : ℕ, (∫ y, χb (((n : ℝ) + 1)⁻¹ • y) * dot (q y) (gradient ψ y)) =
      -∫ y, ψ y * ∑ k, q y k * (((n : ℝ) + 1)⁻¹ *
        coordinateDerivative k (χb : Vec d → ℝ) (((n : ℝ) + 1)⁻¹ • y)) := by
    intro n
    set c : ℝ := ((n : ℝ) + 1)⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun y => χb (c • y)) := hχ.comp (contDiff_const_smul c)
    have hχcd : Differentiable ℝ (fun y => χb (c • y)) :=
      hχd.comp (differentiable_id.const_smul c)
    have htest : IsSpatialTest Set.univ (fun y => χb (c • y) * ψ y) :=
      ⟨hχc.mul hψ, (χb.hasCompactSupport.comp_smul hc0.ne').mul_right, Set.subset_univ _⟩
    have h := hq.2.2 _ htest
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h
    have hgr : ∀ y, dot (q y) (gradient (fun y => χb (c • y) * ψ y) y) =
        χb (c • y) * dot (q y) (gradient ψ y) +
          ψ y * ∑ k, q y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y)) := by
      intro y
      unfold dot gradient
      simp only [coordinateDerivative_mul hχcd hψd]
      have hder : ∀ k, coordinateDerivative k (fun y => χb (c • y)) y =
          c * coordinateDerivative k (χb : Vec d → ℝ) (c • y) := fun k => by
        simp only [coordinateDerivative]
        exact fderiv_comp_smul_apply hχd c y (unitVector k)
      simp only [hder, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hgr] at h
    have hi1 : Integrable fun y => χb (c • y) * dot (q y) (gradient ψ y) := by
      refine hdotint.norm.mono' ((hχ.continuous.comp (continuous_const_smul c)).measurable.mul
        hdotm).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg χb.nonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) χb.le_one
    have hi2 : Integrable fun y => ψ y * ∑ k, q y k *
        (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y)) := by
      refine (hQint.const_mul (B * (c * A))).mono' ?_ (Eventually.of_forall fun y => ?_)
      · refine (hψc.measurable.mul (Finset.measurable_sum _ fun k _ =>
          (hqm k).mul (measurable_const.mul ((contDiff_coordinateDerivative hχ k).continuous.comp
            (continuous_const_smul c)).measurable))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        calc |ψ y| * |∑ k, q y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))|
            ≤ (B * euclideanHeatKernel s (x₀ - y)) * ∑ k, |q y k| * (c * A) := by
              refine mul_le_mul (hψb y) ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _) (mul_nonneg hB (hk0 y).le)
              rw [abs_mul, abs_mul, abs_of_pos hc0]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA k _) hc0.le)
                (abs_nonneg _)
          _ = B * (c * A) * Q y := by
              simp only [hQ, Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
    rw [integral_add hi1 hi2] at h
    linarith
  -- the limits
  have hlim1 : Tendsto (fun n : ℕ => ∫ y, χb (((n : ℝ) + 1)⁻¹ • y) * dot (q y) (gradient ψ y))
      atTop (𝓝 (∫ y, dot (q y) (gradient ψ y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => B' * Q y) (fun n => ?_)
      (hQint.const_mul B') (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · exact ((hχ.continuous.comp (continuous_const_smul _)).measurable.mul
        hdotm).aestronglyMeasurable
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
  have hlim2 : Tendsto (fun n : ℕ => -∫ y, ψ y * ∑ k, q y k * (((n : ℝ) + 1)⁻¹ *
      coordinateDerivative k (χb : Vec d → ℝ) (((n : ℝ) + 1)⁻¹ • y))) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, |-∫ y, ψ y * ∑ k, q y k * (((n : ℝ) + 1)⁻¹ *
        coordinateDerivative k (χb : Vec d → ℝ) (((n : ℝ) + 1)⁻¹ • y))| ≤
        ((n : ℝ) + 1)⁻¹ * (B * A * ∫ y, Q y) := by
      intro n
      set c : ℝ := ((n : ℝ) + 1)⁻¹ with hc
      have hc0 : 0 < c := by positivity
      rw [abs_neg]
      calc |∫ y, ψ y * ∑ k, q y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))|
          ≤ ∫ y, |ψ y * ∑ k, q y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ y, c * (B * A) * Q y := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
              ((hQint.const_mul _)) (Eventually.of_forall fun y => ?_)
            dsimp only
            rw [abs_mul]
            calc |ψ y| * |∑ k, q y k * (c * coordinateDerivative k (χb : Vec d → ℝ) (c • y))|
                ≤ (B * euclideanHeatKernel s (x₀ - y)) * ∑ k, |q y k| * (c * A) := by
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
  have h3 : Tendsto (fun n : ℕ => ∫ y, χb (((n : ℝ) + 1)⁻¹ • y) * dot (q y) (gradient ψ y))
      atTop (𝓝 0) := hlim2.congr fun n => (hcut n).symm
  exact tendsto_nhds_unique hlim1 h3

end QSH
