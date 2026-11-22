import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatSmoothingLimits
import QuantitativeStochasticHomogenization.Ch06.Sec01.DivergenceFreeGaussianTest
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatSelectedFluxPotential

/-!
# The divergence of the heat-selected flux potential

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1, (6.6), deterministic form: let `g` be a weakly divergence-free field satisfying the
hypotheses of the heat formula (6.7), with gradient `G` selected by (6.7), and let `σ` have weak
gradients `G`. If `g - c` has a pairing bound at large scales for a constant vector `c`, then the
rows of `σ` have weak divergence `g - c`. Tested against `ψ`, the trace of the truncation
`∫_{1/(m+1)}^{n+1}` of (6.7) is `∫ g (Φ_{1/(m+1)} * ψ) - ∫ g (Φ_{n+1} * ψ)`, whose limits are
`∫ g ψ` and `c ∫ ψ`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem ball_subset_ball_origin {r s : ℝ} (h : r ≤ s) :
    ball (0 : Vec d) r ⊆ ball (0 : Vec d) s := fun x hx => by
  simp only [ball, mem_ofPred_eq] at hx ⊢
  linarith

private theorem memLp_ball_of_nat {u : Vec d → ℝ}
    (h : ∀ N : ℕ, MemLp u 2 (volume.restrict (ball 0 ((N : ℝ) + 1)))) :
    ∀ R : ℝ, MemLp u 2 (volume.restrict (ball 0 R)) := by
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt R
  exact (h N).mono_measure (Measure.restrict_mono (ball_subset_ball_origin (by linarith)) le_rfl)

/-- **Lemma 6.1, (6.6), deterministic form.** -/
theorem hasWeakDivergence_row_of_isHeatSelectedFluxGradient {g : Vec d → Vec d}
    (hg : HeatFormulaHypotheses g) (hdiv : HasWeakDivergence Set.univ g (fun _ => 0))
    {G : Fin d → Fin d → Vec d → Vec d} (hG : IsHeatSelectedFluxGradient g G)
    {σ : Vec d → Mat d} (hσ : ∀ j k, HasWeakGradient Set.univ (fun x => σ x j k) (G j k))
    {c : Vec d} {R₀ A κ : ℝ} (hpair : ∀ j, HasScalePairingBound (fun y => g y j - c j) R₀ A κ)
    (hR₀ : 0 < R₀) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hmomc : ∀ j, HasGaussianMoments fun y => g y j - c j) (j : Fin d) :
    HasWeakDivergence Set.univ (fun x k => σ x j k) (fun x => g x j - c j) := by
  have hloc : LocallyIntegrable (fun x => g x j - c j) volume :=
    (locallyIntegrable_of_memLp_ball (hg.memLp_ball j)).sub (locallyIntegrable_const _)
  refine ⟨fun k => ((hσ j k) j).1, hloc.locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  have hψs : IsSmoothCompact ψ := ⟨hψ.1, hψ.2.1⟩
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨ρ, hρ0, hρ⟩ := hψs.exists_support_ball
  obtain ⟨R, hR⟩ := exists_nat_gt ρ
  have htsupp : tsupport ψ ⊆ ball 0 ((R : ℝ) + 1) := by
    have hcl : IsClosed {x : Vec d | euclideanNorm x ≤ ρ} :=
      isClosed_le (by unfold euclideanNorm euclideanSq dot; fun_prop) continuous_const
    refine (closure_minimal (fun x hx => hρ x hx) hcl).trans fun x hx => ?_
    have hx' : euclideanNorm x ≤ ρ := hx
    show euclideanNorm (x - 0) < (R : ℝ) + 1
    rw [sub_zero]
    linarith
  -- convergence of the tested truncations along the diagonal
  set T : ℕ → Fin d → Vec d → ℝ := fun n k x =>
    iteratedHeatGradientTruncation g n n j k k x with hT
  have hconvk : ∀ k, Tendsto (fun n => ∫ x, T n k x * ψ x) atTop
      (𝓝 (∫ x, G j k x k * ψ x)) := by
    intro k
    have hdiag := (hG j k k R).2.2.2.comp tendsto_atTop_diagonal
    refine tendsto_integral_mul_of_eLpNorm (memLp_ball_of_nat fun N => (hG j k k N).2.2.1)
      (fun n => memLp_ball_of_nat fun N => (hG j k k N).2.1 n n) hψc hψ.2.1 htsupp ?_
    exact hdiag
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun k _ => hconvk k
  -- the trace identity at finite truncations
  have hgjm : Measurable fun y => g y j := hg.measurable j
  have hident : ∀ n : ℕ, ∑ k, ∫ x, T n k x * ψ x =
      (∫ y, g y j * heatConv (((n + 1 : ℕ) : ℝ)⁻¹) ψ y) -
        ∫ y, g y j * heatConv ((n + 1 : ℕ) : ℝ) ψ y := by
    intro n
    have hε₁ := natCast_succ_inv_pos n
    have hε := natCast_succ_inv_le_natCast_succ n n
    have hint : ∀ k, Integrable fun x => T n k x * ψ x := by
      intro k
      have hmem := (hG j k k R).2.1 n n
      have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))) :=
        isFiniteMeasure_restrict_ball _
      obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψ.2.1
      have hon : IntegrableOn (fun x => T n k x * ψ x) (ball 0 ((R : ℝ) + 1)) := by
        refine ((hmem.integrable one_le_two).norm.mul_const M).mono' ?_ ?_
        · exact (hmem.aestronglyMeasurable.mul hψc.aestronglyMeasurable.restrict)
        · refine Eventually.of_forall fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
      refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
      intro x hx
      exact htsupp (subset_tsupport _ (right_ne_zero_of_mul hx))
    rw [← integral_finsetSum _ fun k _ => hint k]
    have hzero : ∀ x, ∑ k, heatHessianTruncation n n j k (fun y => g y k) x = 0 := by
      intro x
      unfold heatHessianTruncation heatHessianWindow
      rw [← integral_finsetSum _ fun k _ =>
        (hg.moments k).integrableOn_heatHessianConv hε₁ j k (hg.measurable k) x]
      have h0 : ∀ t ∈ Icc (((n + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ),
          ∑ k, heatHessianConv t j k (fun y => g y k) x = (fun _ => (0 : ℝ)) t := fun t ht =>
        sum_heatHessianConv_eq_zero_of_hasWeakDivergence hdiv hg.measurable hg.moments
          (lt_of_lt_of_le hε₁ ht.1) j x
      rw [setIntegral_congr_fun measurableSet_Icc h0]
      simp
    have hpt : ∀ x, ∑ k, T n k x * ψ x =
        -(ψ x * ∑ k, heatHessianWindow (((n + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ) k k
          (fun y => g y j) x) := by
      intro x
      have h := hzero x
      simp only [hT, hg.truncation_eq, sub_mul, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, h, zero_mul, zero_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by unfold heatHessianTruncation; ring
    simp only [hpt]
    rw [integral_neg, integral_mul_sum_heatHessianWindow hgjm (hg.moments j) hψs hε₁ hε]
    have hI : ∀ {s : ℝ}, 0 < s → Integrable fun y => g y j * heatConv s ψ y := by
      intro s hs
      refine (integrable_abs_mul_heatSmoothing hgjm (hg.moments j) hψs hs).mono' ?_
        (Eventually.of_forall fun y => ?_)
      · have hjoint : StronglyMeasurable fun p : Vec d × Vec d =>
            euclideanHeatKernel s (p.1 - p.2) * ψ p.2 :=
          (((measurable_euclideanHeatKernel_joint (d := d)).comp (measurable_const.prodMk
            (measurable_fst.sub measurable_snd))).mul
            (hψc.measurable.comp measurable_snd)).stronglyMeasurable
        exact hgjm.aestronglyMeasurable.mul hjoint.integral_prod_right'.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        unfold heatConv
        refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
        congr 1
        funext x
        rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg hs.le _)]
    simp only [mul_sub]
    rw [integral_sub (hI (by positivity)) (hI hε₁)]
    ring
  have hlimit : Tendsto (fun n : ℕ => (∫ y, g y j * heatConv (((n + 1 : ℕ) : ℝ)⁻¹) ψ y) -
      ∫ y, g y j * heatConv ((n + 1 : ℕ) : ℝ) ψ y) atTop
      (𝓝 ((∫ y, g y j * ψ y) - c j * ∫ x, ψ x)) :=
    (tendsto_integral_mul_heatConv_zero hgjm (hg.moments j) hψs).sub
      (tendsto_integral_mul_heatConv_atTop hgjm (hg.moments j) hψs (hpair j) hR₀ hA hκ
        (hmomc j))
  have hkey : ∑ k, ∫ x, G j k x k * ψ x = (∫ y, g y j * ψ y) - c j * ∫ x, ψ x :=
    tendsto_nhds_unique hsum (hlimit.congr fun n => (hident n).symm)
  -- conclusion
  have hgψ : Integrable fun x => g x j * ψ x := by
    have h := integrableOn_mul_spatialTest ((locallyIntegrable_of_memLp_ball
      (hg.memLp_ball j)).locallyIntegrableOn Set.univ) hψ
    rwa [integrableOn_univ] at h
  have hψint : Integrable ψ := hψc.integrable_of_hasCompactSupport hψ.2.1
  simp only [Measure.restrict_univ]
  unfold dot
  rw [integral_finsetSum _ fun k _ => by
    have h := integrableOn_mul_spatialTest ((hσ j k) k).1
      (isSpatialTest_coordinateDerivative hψ k)
    rwa [integrableOn_univ] at h]
  have hw : ∀ k, ∫ x, σ x j k * gradient ψ x k = -∫ x, G j k x k * ψ x := by
    intro k
    have h := ((hσ j k) k).2.2 ψ hψ
    simp only [Measure.restrict_univ] at h
    exact h
  simp only [hw, Finset.sum_neg_distrib, hkey]
  simp only [sub_mul]
  rw [integral_sub hgψ (hψint.const_mul (c j)), integral_const_mul]

end QSH
