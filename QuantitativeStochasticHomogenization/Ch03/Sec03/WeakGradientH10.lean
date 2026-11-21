import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipticRepresentative
import QuantitativeStochasticHomogenization.Ch03.Sec03.SkewHessian

/-!
# Weak gradients tested with functions of `H¹₀`

If `v` has weak gradient `g` in `U` with `v, g ∈ L²(U)`, then `∫_U gⱼ φ = -∫_U v ∂ⱼφ` for every
`φ ∈ H¹₀(U)` of the elliptic regularity library: the identity holds for the smooth compactly
supported approximants of `φ` and passes to the limit by continuity of the `L²` pairing.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Continuity of the `L²` pairing along a sequence converging in `L²`. -/
theorem tendsto_integral_mul_of_eLpNorm_sub {μ : Measure (Vec d)} {f h : Vec d → ℝ}
    {hs : ℕ → Vec d → ℝ} (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) (hhs : ∀ n, MemLp (hs n) 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => hs n x - h x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * hs n x ∂μ) atTop (𝓝 (∫ x, f x * h x ∂μ)) := by
  have key : ∀ (g : Vec d → ℝ) (hg : MemLp g 2 μ),
      ∫ x, f x * g x ∂μ = inner ℝ (hf.toLp f) (hg.toLp g) := by
    intro g hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hconv : Tendsto (fun n => (hhs n).toLp (hs n)) atTop (𝓝 (hh.toLp h)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : ∀ n, dist ((hhs n).toLp (hs n)) (hh.toLp h) =
        (eLpNorm (fun x => hs n x - h x) 2 μ).toReal := by
      intro n
      rw [Lp.dist_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hhs n).coeFn_toLp, hh.coeFn_toLp] with x h1 h2
      rw [Pi.sub_apply, h1, h2]
    simp_rw [hd]
    have h0 : Tendsto (fun n => (eLpNorm (fun x => hs n x - h x) 2 μ).toReal) atTop
        (𝓝 (ENNReal.toReal 0)) := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rwa [ENNReal.toReal_zero] at h0
  have hlim' := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hf.toLp f)) hconv
  rw [← key h hh] at hlim'
  refine hlim'.congr fun n => ?_
  exact (key (hs n) (hhs n)).symm

/-- **Weak gradients tested with `H¹₀` functions.** -/
theorem integral_grad_mul_h10 {U : Set (Vec d)} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U v g) (φ : PDE.H10Function U) (j : Fin d) :
    ∫ x in U, g x j * φ.toH1Function.toFun x = -∫ x in U, v x * φ.toH1Function.grad x j := by
  have happ : ∀ n, ∫ x in U, v x * coordinateDerivative j (φ.approx n) x =
      -∫ x in U, g x j * φ.approx n x := fun n =>
    (hw j).2.2 _ ⟨φ.approx_smooth n, φ.approx_hasCompactSupport n, φ.approx_support_subset n⟩
  have hφn : ∀ n, MemLp (φ.approx n) 2 (volume.restrict U) := fun n =>
    ((φ.approx_smooth n).continuous.memLp_of_hasCompactSupport
      (φ.approx_hasCompactSupport n)).restrict U
  have hdφn : ∀ n, MemLp (fun x => coordinateDerivative j (φ.approx n) x) 2
      (volume.restrict U) := fun n =>
    (((φ.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.memLp_of_hasCompactSupport
        ((φ.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (unitVector j))).restrict U
  have t1 := tendsto_integral_mul_of_eLpNorm_sub (hg j) φ.toH1Function.memL2 hφn φ.tendsto_approx
  have t2 := tendsto_integral_mul_of_eLpNorm_sub hv (φ.toH1Function.gradMemL2 j) hdφn
    (φ.tendsto_approx_grad j)
  have t3 := t2.congr fun n => happ n
  have := tendsto_nhds_unique t3 t1.neg
  linarith

/-- For smooth compactly supported tests `Ξ_{jk}` in `U` with `Ξ_{kj} = -Ξ_{jk}`,
`∑_{j,k} ∫_U gⱼ ∂ₖ Ξ_{jk} = 0` for every weak gradient `g` of a locally integrable `v`. -/
theorem sum_integral_grad_mul_skew_test {U : Set (Vec d)} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient U v g) {Ξ : Fin d → Fin d → Vec d → ℝ}
    (hΞ : ∀ j k, IsSpatialTest U (Ξ j k)) (hskew : ∀ j k, Ξ k j = fun x => -Ξ j k x) :
    ∑ j, ∑ k, ∫ x in U, g x j * coordinateDerivative k (Ξ j k) x = 0 := by
  have h1 : ∀ j k, ∫ x in U, g x j * coordinateDerivative k (Ξ j k) x =
      -∫ x in U, v x * coordinateDerivative j (coordinateDerivative k (Ξ j k)) x := by
    intro j k
    have h := (hw j).2.2 _ (isSpatialTest_coordinateDerivative (hΞ j k) k)
    linarith
  simp only [h1, Finset.sum_neg_distrib]
  have hint : ∀ j k, IntegrableOn
      (fun x => v x * coordinateDerivative j (coordinateDerivative k (Ξ j k)) x) U := fun j k =>
    integrableOn_mul_spatialTest (hw j).1
      (isSpatialTest_coordinateDerivative (isSpatialTest_coordinateDerivative (hΞ j k) k) j)
  rw [neg_eq_zero]
  have e : ∫ x in U, v x * ∑ j, ∑ k, coordinateDerivative j (coordinateDerivative k (Ξ j k)) x =
      ∑ j, ∑ k, ∫ x in U, v x * coordinateDerivative j (coordinateDerivative k (Ξ j k)) x := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k]
  rw [← e]
  have hz : ∀ x, ∑ j, ∑ k, coordinateDerivative j (coordinateDerivative k (Ξ j k)) x = 0 :=
    sum_coordinateDerivative_skew_eq_zero (fun j k => (hΞ j k).1.of_le (by simp)) hskew
  simp only [hz, mul_zero, integral_zero]

end QSH
