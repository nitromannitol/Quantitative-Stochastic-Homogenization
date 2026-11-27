import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38Base
import QuantitativeStochasticHomogenization.Ch03.Sec03.HomogeneousParts

/-!
# The implication (3.48) of the proof of Theorem 3.8

Armstrong–Kuusi–Mourrat, Section 3.3, proof of (3.48): `(i)_k` and `(ii)_k` imply `(iii')_k`. The
statement here is deterministic, for one coefficient field `a`: from the estimate (3.50) on the
balls of radius at least `r₀` and from `(ii)_k` with a scale `r₀` large enough, every solution `u` in
`B_R`, `R ≥ r₀`, has some `φ ∈ A_k` with `‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)^{k+1-δ/2} ‖u‖_{L̲²(B_R)}` for
`r ∈ [r₀, R]`. The proof is the book's: the correction `φ` is the sum of the elements of `A_k` given by
`(ii)_k` for the near-minimizers in `Ā_k` along the radii `θ^j R`, and the growth of these elements,
which the book takes from `(i)_k`, follows here from `(ii)_k` and (3.27).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `u ∈ H¹(B_R)` is a weak solution of `-∇·(a∇u) = 0` in `B_R` (the space `A(B_R)`). -/
def IsSolutionBall (a : CoefficientField d Λ) (R : ℝ) (u : Vec d → ℝ) : Prop :=
  MemLp u 2 (volume.restrict (ball 0 R)) ∧ ∃ g : Vec d → Vec d,
    (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) ∧ HasWeakGradient (ball 0 R) u g ∧
    HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0)

theorem IsSolutionBall.mono {a : CoefficientField d Λ} {r R : ℝ} {u : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (hrR : r ≤ R) : IsSolutionBall a r u := by
  obtain ⟨hL2, g, hg, hgrad, hdiv⟩ := hu
  have hsub := ball_zero_subset_ball_zero (d := d) hrR
  exact ⟨hL2.mono_measure (Measure.restrict_mono hsub le_rfl), g,
    fun i => (hg i).mono_measure (Measure.restrict_mono hsub le_rfl), hgrad.mono hsub,
    hdiv.mono' hsub⟩

theorem IsSolutionBall.add {a : CoefficientField d Λ} {R : ℝ} {u v : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (hv : IsSolutionBall a R v) :
    IsSolutionBall a R (fun x => u x + v x) := by
  obtain ⟨hu1, gu, hgu, hu2, hu3⟩ := hu
  obtain ⟨hv1, gv, hgv, hv2, hv3⟩ := hv
  refine ⟨hu1.add hv1, fun x => gu x + gv x, fun i => (hgu i).add (hgv i),
    hasWeakGradient_add hu2 hv2, ?_⟩
  have h := hasWeakDivergence_add hu3 hv3
  convert h using 1
  · funext x; rw [Matrix.mulVec_add]
  · funext x; simp

theorem IsSolutionBall.const_mul {a : CoefficientField d Λ} {R : ℝ} {u : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (c : ℝ) : IsSolutionBall a R (fun x => c * u x) := by
  obtain ⟨hu1, gu, hgu, hu2, hu3⟩ := hu
  refine ⟨hu1.const_mul c, fun x => c • gu x, fun i => ?_, hu2.const_mul' c, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using (hgu i).const_mul c
  · convert hu3.const_smul' c using 2 with x
    rw [Matrix.mulVec_smul]

theorem IsSolutionBall.sub {a : CoefficientField d Λ} {R : ℝ} {u v : Vec d → ℝ}
    (hu : IsSolutionBall a R u) (hv : IsSolutionBall a R v) :
    IsSolutionBall a R (fun x => u x - v x) := by
  have h := hu.add (hv.const_mul (-1))
  convert h using 2 with x
  ring

theorem isSolutionBall_of_mem_solutionGrowthSpace {a : CoefficientField d Λ} {k : ℕ}
    {φ : Vec d → ℝ} (hφ : φ ∈ solutionGrowthSpace a k) {R : ℝ} (hR : 0 < R) :
    IsSolutionBall a R φ := hφ.1 R hR

theorem zero_mem_solutionGrowthSpace (a : CoefficientField d Λ) (k : ℕ) :
    (fun _ => (0 : ℝ)) ∈ solutionGrowthSpace a k := by
  refine ⟨fun R _ => ⟨MemLp.zero, fun _ => 0, fun _ => MemLp.zero,
    hasWeakGradient_mono (subset_univ _) (hasWeakGradient_const 0), ?_⟩, ?_⟩
  · simpa only [Matrix.mulVec_zero] using
      (hasWeakDivergence_const_field (0 : Vec d)).mono' (subset_univ (ball (0 : Vec d) R))
  · have h : (fun r : ℝ => (r ^ (k + 1))⁻¹ *
        scalarRms volume (ball (0 : Vec d) r) (fun _ => (0 : ℝ))) =
        fun _ => 0 := by
      funext r
      have : scalarRms volume (ball (0 : Vec d) r) (fun _ => (0 : ℝ)) = 0 := by
        unfold scalarRms; simp
      rw [this, mul_zero]
    rw [h]; exact tendsto_const_nhds

theorem add_mem_solutionGrowthSpace {a : CoefficientField d Λ} {k : ℕ} {φ ψ : Vec d → ℝ}
    (hφ : φ ∈ solutionGrowthSpace a k) (hψ : ψ ∈ solutionGrowthSpace a k) :
    (fun x => φ x + ψ x) ∈ solutionGrowthSpace a k := by
  refine ⟨fun R hR => (isSolutionBall_of_mem_solutionGrowthSpace hφ hR).add
    (isSolutionBall_of_mem_solutionGrowthSpace hψ hR), ?_⟩
  have hup := (hφ.2.add hψ.2)
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
  · filter_upwards [eventually_gt_atTop 0] with r hr
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact scalarRms_add_le (hφ.1 r hr).1 (hψ.1 r hr).1

theorem sum_mem_solutionGrowthSpace {a : CoefficientField d Λ} {k : ℕ} (s : Finset ℕ)
    {Φ : ℕ → Vec d → ℝ} (hΦ : ∀ m ∈ s, Φ m ∈ solutionGrowthSpace a k) :
    (fun x => ∑ m ∈ s, Φ m x) ∈ solutionGrowthSpace a k := by
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_solutionGrowthSpace a k
  | insert m s hm ih =>
    have h := add_mem_solutionGrowthSpace (hΦ m (Finset.mem_insert_self m s))
      (ih fun m' hm' => hΦ m' (Finset.mem_insert_of_mem hm'))
    simpa only [Finset.sum_insert hm] using h

end QSH
