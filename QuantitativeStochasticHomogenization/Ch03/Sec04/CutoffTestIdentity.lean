import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakGradientH10
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakRestriction
import QuantitativeStochasticHomogenization.Ch03.Sec03.KernelSmoothing
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests
import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# Smooth cutoffs of `H¹` functions as tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4: the correctors are tested against `η (φ - c)` with `η` smooth and compactly supported.

For `u ∈ H¹(U)` on an open bounded convex domain `U` and `η` smooth with compact support in `U`,
the product `η u` is a concrete `H¹₀(U)` function of the elliptic regularity library, with gradient
`η ∇u + u ∇η` (`cutoffH10`). Hence:

* `sum_integral_cutoff_eq_zero`: a weakly divergence-free field `q ∈ L²(U)` satisfies
  `∫_U q · (η ∇u + u ∇η) = 0`;
* `h01_cutoff_mul`: `η u ∈ H¹₀(U)` in the sense of (1.7), so it is a trial function for the
  Dirichlet energy `μ(U, e)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem ball_eq_pdeEuclideanBall (z : Vec d) {T : ℝ} (hT : 0 < T) :
    ball z T = PDE.euclideanBall z T := by
  ext x
  simp only [ball, PDE.euclideanBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot,
    euclideanNorm, euclideanSq, dot, Set.mem_ofPred_eq]
  exact Real.sqrt_lt' hT

theorem isOpenBoundedConvexDomain_ball (z : Vec d) {T : ℝ} (hT : 0 < T) :
    PDE.IsOpenBoundedConvexDomain (ball z T) := by
  rw [ball_eq_pdeEuclideanBall z hT]
  exact PDE.isOpenBoundedConvexDomain_euclideanBall z hT

theorem classicalGradient_eq_gradient (η : Vec d → ℝ) (x : Vec d) :
    PDE.classicalGradient η x = gradient η x := by
  funext i
  rfl

theorem sq_toReal_eLpNorm_two_eq {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← Lp.norm_toLp f hf, norm_toLp_eq_sqrt hf,
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

/-- Convergence in `L²` gives convergence of the square integrals to `0`. -/
theorem tendsto_integral_sq_of_eLpNorm {μ : Measure (Vec d)} {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hlim : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal) atTop (𝓝 (ENNReal.toReal 0)) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  rw [ENNReal.toReal_zero] at h0
  have h1 := h0.pow 2
  rw [zero_pow two_ne_zero] at h1
  exact h1.congr fun n => sq_toReal_eLpNorm_two_eq (hf n)

theorem volume_lt_top_of_isBoundedDomain {U : Set (Vec d)} (h : PDE.IsBoundedDomain U) :
    volume U < ⊤ := by
  obtain ⟨R, -, hR⟩ := h
  have hsub : U ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (-R) R) :=
    fun x hx i _ => abs_le.mp (hR x hx i)
  exact (measure_mono hsub).trans_lt (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

section Cutoff

variable {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d} {η : Vec d → ℝ}

/-- **The cutoff `η u` as a concrete `H¹₀(U)` function.** -/
def cutoffH10 (hU : PDE.IsOpenBoundedConvexDomain U) (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) (hw : HasWeakGradient U u g)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    PDE.H10Function U :=
  (toH1FunctionOn hu hg hw).mulContDiffHasCompactSupportToH10 hU hη hηc hηU

variable (hU : PDE.IsOpenBoundedConvexDomain U) (hu : MemLp u 2 (volume.restrict U))
  (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) (hw : HasWeakGradient U u g)
  (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)

theorem cutoffH10_toFun :
    (cutoffH10 hU hu hg hw hη hηc hηU).toH1Function.toFun = fun x => η x * u x := by
  unfold cutoffH10
  rw [PDE.H1Function.mulContDiffHasCompactSupportToH10_toFun]
  rfl

theorem cutoffH10_grad :
    (cutoffH10 hU hu hg hw hη hηc hηU).toH1Function.grad =
      fun x => η x • g x + u x • gradient η x := by
  unfold cutoffH10
  rw [PDE.H1Function.mulContDiffHasCompactSupportToH10_grad]
  funext x
  rw [classicalGradient_eq_gradient]
  rfl

theorem cutoffH10_grad_apply (x : Vec d) (i : Fin d) :
    (cutoffH10 hU hu hg hw hη hηc hηU).toH1Function.grad x i =
      η x * g x i + u x * coordinateDerivative i η x := by
  rw [cutoffH10_grad]
  rfl

theorem isSpatialTest_cutoffH10_approx (n : ℕ) :
    IsSpatialTest U ((cutoffH10 hU hu hg hw hη hηc hηU).approx n) :=
  ⟨(cutoffH10 hU hu hg hw hη hηc hηU).approx_smooth n,
    (cutoffH10 hU hu hg hw hη hηc hηU).approx_hasCompactSupport n,
    (cutoffH10 hU hu hg hw hη hηc hηU).approx_support_subset n⟩

include hU hu hg hw hη hηc hηU in
theorem memLp_cutoff_grad (i : Fin d) :
    MemLp (fun x => η x * g x i + u x * coordinateDerivative i η x) 2 (volume.restrict U) := by
  have h := (cutoffH10 hU hu hg hw hη hηc hηU).toH1Function.gradMemL2 i
  rw [cutoffH10_grad] at h
  exact h

include hU hu hg hw hη hηc hηU in
/-- **Divergence-free fields tested with cutoffs of `H¹` functions.** If `q ∈ L²(U)` is weakly
divergence-free in `ℝ^d`, then `∫_U q · (η ∇u + u ∇η) = 0`. -/
theorem sum_integral_cutoff_eq_zero {q : Vec d → Vec d}
    (hq : HasWeakDivergence Set.univ q (fun _ => 0))
    (hqU : ∀ i, MemLp (fun x => q x i) 2 (volume.restrict U)) :
    ∑ i, ∫ x in U, q x i * (η x * g x i + u x * coordinateDerivative i η x) = 0 := by
  set w := cutoffH10 hU hu hg hw hη hηc hηU with hwdef
  have : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr (volume_lt_top_of_isBoundedDomain hU.2.1).ne
  have hdv : ∀ n i, MemLp (fun x => coordinateDerivative i (w.approx n) x) 2
      (volume.restrict U) := fun n i =>
    ((((w.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.memLp_of_hasCompactSupport
        ((w.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (unitVector i))).restrict U
  have happrox : ∀ n, ∑ i, ∫ x in U, q x i * coordinateDerivative i (w.approx n) x = 0 := by
    intro n
    have htest := isSpatialTest_cutoffH10_approx hU hu hg hw hη hηc hηU n
    have h := hq.2.2 (w.approx n) ⟨htest.1, htest.2.1, Set.subset_univ _⟩
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h
    have hsupp : ∀ x ∉ U, dot (q x) (gradient (w.approx n) x) = 0 := by
      intro x hx
      have hg0 : gradient (w.approx n) x = 0 :=
        gradient_eq_zero_of_notMem_tsupport fun h' => hx (htest.2.2 h')
      rw [hg0]
      simp [dot]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp] at h
    rw [← h, ← integral_finsetSum _ fun i _ => integrable_mul_of_memLp_two (hqU i) (hdv n i)]
    rfl
  have hlim : ∀ i, Tendsto (fun n => ∫ x in U, q x i * coordinateDerivative i (w.approx n) x)
      atTop (𝓝 (∫ x in U, q x i * w.toH1Function.grad x i)) := fun i =>
    tendsto_integral_mul_of_eLpNorm_sub (hqU i) (w.toH1Function.gradMemL2 i) (fun n => hdv n i)
      (w.tendsto_approx_grad i)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hlim i
  have hzero : Tendsto (fun n => ∑ i, ∫ x in U, q x i * coordinateDerivative i (w.approx n) x)
      atTop (𝓝 0) := tendsto_const_nhds.congr fun n => (happrox n).symm
  have heq := tendsto_nhds_unique hsum hzero
  rw [← heq]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hwdef, cutoffH10_grad_apply]

include hU hu hg hw hη hηc hηU in
/-- **The cutoff `η u` lies in `H¹₀(U)`**, with gradient `η ∇u + u ∇η`. -/
theorem h01_cutoff_mul :
    H01 U (fun x => η x * u x) (fun x => η x • g x + u x • gradient η x) := by
  set w := cutoffH10 hU hu hg hw hη hηc hηU with hwdef
  have : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr (volume_lt_top_of_isBoundedDomain hU.2.1).ne
  have hfun := cutoffH10_toFun hU hu hg hw hη hηc hηU
  have hgrad := cutoffH10_grad hU hu hg hw hη hηc hηU
  have hmem : MemLp (fun x => η x * u x) 2 (volume.restrict U) := by
    have h := w.toH1Function.memL2
    rw [hfun] at h
    exact h
  have hmemg : ∀ i, MemLp (fun x => (η x • g x + u x • gradient η x) i) 2 (volume.restrict U) := by
    intro i
    have h := w.toH1Function.gradMemL2 i
    rw [hgrad] at h
    exact h
  have hv : ∀ n, IsSpatialTest U (w.approx n) := isSpatialTest_cutoffH10_approx hU hu hg hw hη hηc hηU
  have hvL2 : ∀ n, MemLp (w.approx n) 2 (volume.restrict U) := fun n => (hv n).memLp_two _
  have hdv : ∀ n i, MemLp (fun x => coordinateDerivative i (w.approx n) x) 2
      (volume.restrict U) := fun n i =>
    ((((w.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.memLp_of_hasCompactSupport
        ((w.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (unitVector i))).restrict U
  refine ⟨hmem, memLp_pi_iff.mpr hmemg, fun i => ⟨?_, ?_, fun φ hφ => ?_⟩, w.approx, hv, ?_, ?_⟩
  · exact IntegrableOn.locallyIntegrableOn (hmem.integrable one_le_two)
  · exact IntegrableOn.locallyIntegrableOn ((hmemg i).integrable one_le_two)
  · have h := w.toH1Function.hasWeakGradient i φ hφ.1 hφ.2.1 hφ.2.2
    rw [hfun, hgrad] at h
    exact h
  · have h := tendsto_integral_sq_of_eLpNorm (μ := volume.restrict U)
      (fun n => (hvL2 n).sub w.toH1Function.memL2) w.tendsto_approx
    rw [hfun] at h
    exact h
  · have hi : ∀ i, Tendsto (fun n => ∫ x in U,
        (coordinateDerivative i (w.approx n) x - (η x • g x + u x • gradient η x) i) ^ 2)
        atTop (𝓝 0) := by
      intro i
      have h := tendsto_integral_sq_of_eLpNorm (μ := volume.restrict U)
        (fun n => (hdv n i).sub (w.toH1Function.gradMemL2 i)) (w.tendsto_approx_grad i)
      rw [hgrad] at h
      exact h
    have hs := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hi i
    simp only [Finset.sum_const_zero] at hs
    refine hs.congr fun n => ?_
    rw [← integral_finsetSum (f := fun i x =>
      (coordinateDerivative i (w.approx n) x - (η x • g x + u x • gradient η x) i) ^ 2) _
      fun i _ => ((hdv n i).sub (hmemg i)).integrable_sq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [euclideanSq, dot, Pi.sub_apply, gradient]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end Cutoff

end QSH
