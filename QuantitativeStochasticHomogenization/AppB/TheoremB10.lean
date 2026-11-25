import QuantitativeStochasticHomogenization.AppB.ConvexMorrey

/-!
# Theorem B.10: Morrey's inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix B, Theorem B.10 for `k = 1`: for `p ∈ (d, ∞]` there is `C(p, d)` such that, for every
`r > 0` and `v ∈ W^{1,p}(B_r)`, `inf_{w ∈ ℝ} ‖v - w‖_{L^∞(B_r)} ≤ C r ‖∇v‖_{L̲^p(B_r)}` (B.8),
`‖v‖_{L^∞(B_r)} ≤ C r ‖∇v‖_{L̲^p(B_r)}` if `v ∈ W^{1,p}_0(B_r)`, and
`‖v‖_{L^∞(ℝ^d)} ≤ C ‖v‖_{W^{1,p}(ℝ^d)}` for `v ∈ W^{1,p}(ℝ^d)` (B.9). As in Theorem B.9 the norm
of `∇v` is the volume-normalized one, and the balls may have any center.

The proofs (Gilbarg–Trudinger, Theorem 7.17; Evans, Section 5.6.2): (B.8) is Morrey's inequality
on bounded convex domains, `QSH.ae_abs_sub_integralAverage_le_of_convex`, with `w = (v)_{B_r}`;
for `W^{1,p}_0(B_r)` the `C¹` estimate on the ball `B_{2r}` bounds each test function by its
oscillation, which passes to the limit; (B.9) combines (B.8) on the balls `B_d(z)`, `z ∈ ℤ^d`,
which cover `ℝ^d`, with `|(v)_{B_d(z)}| ≤ ‖v‖_{L̲^p(B_d(z))}`. The exponent `p = ∞` reduces to
`p = d + 1`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem mem_ball_iff {z x : Vec d} {r : ℝ} : x ∈ ball z r ↔ euclideanNorm (x - z) < r :=
  Iff.rfl

theorem center_mem_ball (z : Vec d) {r : ℝ} (hr : 0 < r) : z ∈ ball z r := by
  rw [mem_ball_iff, sub_self]
  simpa [euclideanNorm, euclideanSq, dot] using hr

theorem isBounded_ball (z : Vec d) {r : ℝ} (hr : 0 < r) : Bornology.IsBounded (ball z r) := by
  rw [ball_eq_pdeEuclideanBall z hr]
  exact Metric.isBounded_ball.subset (PDE.euclideanBall_subset_supBall hr)

theorem norm_sub_le_of_mem_ball {z a b : Vec d} {r : ℝ} (ha : a ∈ ball z r) (hb : b ∈ ball z r) :
    ‖a - b‖ ≤ 2 * r := by
  have h1 : ‖a - b‖ ≤ PDE.vecEuclideanNorm (a - b) := PDE.norm_le_vecEuclideanNorm _
  have h2 : PDE.vecEuclideanNorm (a - b) ≤
      PDE.vecEuclideanNorm (a - z) + PDE.vecEuclideanNorm (z - b) := by
    have := PDE.vecEuclideanNorm_add_le (a - z) (z - b)
    rwa [sub_add_sub_cancel] at this
  rw [PDE.vecEuclideanNorm_sub_comm z b] at h2
  have ha' : PDE.vecEuclideanNorm (a - z) < r := ha
  have hb' : PDE.vecEuclideanNorm (b - z) < r := hb
  linarith

/-- The normalized norm of an `L^p(U)` function is finite. -/
theorem eLpMeanNormOn_ne_top {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {p : ℝ≥0∞} {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hf : MemLp f p (volume.restrict U)) : PDE.eLpMeanNormOn U p f ≠ ⊤ := by
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt)]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (ENNReal.inv_ne_top.2 hU0)) hf.eLpNorm_lt_top.ne

theorem IsW1p.memLp_euclideanNorm {U : Set (Vec d)} {p : ℝ≥0∞} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hv : IsW1p U p v g) :
    MemLp (fun x => euclideanNorm (g x)) p (volume.restrict U) :=
  PDE.GradMemLpOn.memLp_vecEuclideanNorm hv.toW1pFunction.gradMemLp

/-- (B.8) for `p ∈ (d, ∞)` with `w = (v)_{B_r(z)}`. -/
theorem eLpNorm_top_sub_integralAverage_ball_le (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p)
    (z : Vec d) {r : ℝ} (hr : 0 < r) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : IsW1p (ball z r) (ENNReal.ofReal p) v g) :
    eLpNorm (fun x => v x - PDE.integralAverage (ball z r) v) ⊤ (volume.restrict (ball z r)) ≤
      ENNReal.ofReal (2 * Real.sqrt d / (1 - d / p) * r) *
        PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x)) := by
  have hp0 : 0 < p := (Nat.cast_pos.2 hd).trans hdp
  have hc : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
    linarith
  have hB := isOpenBoundedConvexDomain_ball z hr
  haveI : IsFiniteMeasure (volume.restrict (ball z r)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top z hr)
  have hae := ae_abs_sub_integralAverage_le_of_convex hB.1 (isBounded_ball z hr) hB.2.2
    ⟨z, center_mem_ball z hr⟩ (fun a ha b hb => norm_sub_le_of_mem_ball ha hb) hd hdp
    hv.toW1pFunction
  have hfin := eLpMeanNormOn_ne_top (volume_ball_pos z hr).ne' (volume_ball_ne_top z hr)
    hv.memLp_euclideanNorm
  rw [eLpNorm_exponent_top (f := fun x => v x - PDE.integralAverage (ball z r) v)
    (hv.1.sub (memLp_const _)).aestronglyMeasurable]
  refine (eLpNormEssSup_le_of_ae_bound (C := 1 / (1 - d / p) * (2 * r) * Real.sqrt d *
      (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun y => euclideanNorm (g y))).toReal)
      ?_).trans (le_of_eq ?_)
  · filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    exact hx
  · rw [show 1 / (1 - (d : ℝ) / p) * (2 * r) * Real.sqrt d *
        (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun y => euclideanNorm (g y))).toReal =
        2 * Real.sqrt d / (1 - d / p) * r *
        (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun y => euclideanNorm (g y))).toReal by
        field_simp,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin]

end QSH
