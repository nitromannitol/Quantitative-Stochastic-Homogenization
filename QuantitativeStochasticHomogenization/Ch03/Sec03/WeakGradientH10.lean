import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipticRepresentative

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

end QSH
