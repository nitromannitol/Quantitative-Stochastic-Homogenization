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
  have : IsFiniteMeasure (volume.restrict (ball z r)) :=
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

theorem continuous_gradient {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous fun x => gradient φ x :=
  continuous_pi fun i => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- A test function in `B_r(z)` is bounded by `8 √d (1 - d/p)⁻¹ r ‖∇φ‖_{L̲^p(B_r(z))}`: the
`C¹` Morrey inequality on `B_{2r}(z)` bounds `|φ(x) - φ(y)|` for a point `y` with `φ(y) = 0`. -/
theorem abs_le_of_isSpatialTest_ball (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p) (z : Vec d) {r : ℝ}
    (hr : 0 < r) {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z r) φ) (x : Vec d) :
    |φ x| ≤ 8 * Real.sqrt d / (1 - d / p) * r *
      (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p)
        (fun y => euclideanNorm (gradient φ y))).toReal := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hc : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
    linarith
  have hr2 : 0 < 2 * r := by positivity
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hBK : ball z r ⊆ ball z (2 * r) := fun y hy => by
    have : euclideanNorm (y - z) < r := hy
    show euclideanNorm (y - z) < 2 * r
    linarith
  have hRHS : 0 ≤ 8 * Real.sqrt d / (1 - d / p) * r *
      (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p)
        (fun y => euclideanNorm (gradient φ y))).toReal := by positivity
  have h0 : ∀ y, y ∉ ball z r → φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hφ.2.2 h)
  by_cases hxK : x ∉ ball z (2 * r)
  · rw [h0 x fun h => hxK (hBK h), abs_zero]
    exact hRHS
  push_neg at hxK
  set i0 : Fin d := ⟨0, hd⟩
  set y : Vec d := z + (3 * r / 2) • PDE.basisVec i0 with hy
  have hyz : euclideanNorm (y - z) = 3 * r / 2 := by
    rw [hy, add_sub_cancel_left, euclideanNorm_eq_vecEuclideanNorm, PDE.vecEuclideanNorm_smul,
      PDE.vecEuclideanNorm_basisVec, mul_one, abs_of_pos (by positivity)]
  have hyK : y ∈ ball z (2 * r) := by
    show euclideanNorm (y - z) < 2 * r
    rw [hyz]
    linarith
  have hyB : y ∉ ball z r := by
    intro h
    have : euclideanNorm (y - z) < r := h
    rw [hyz] at this
    linarith
  have hK := isOpenBoundedConvexDomain_ball z hr2
  have hK0 : volume (ball z (2 * r)) ≠ 0 := (volume_ball_pos z hr2).ne'
  have hmor := ConvexMorrey.abs_sub_le_morrey volume hφ1 hK.1.measurableSet hK.2.2
    (isBounded_ball z hr2) hK0 (δ := 2 * (2 * r))
    (fun a ha b hb => norm_sub_le_of_mem_ball ha hb) hp1
    (by simpa [Module.finrank_fin_fun] using hdp) hxK hyK
  rw [Module.finrank_fin_fun, h0 y hyB, sub_zero] at hmor
  have hB := isOpenBoundedConvexDomain_ball z hr
  have hB0 : volume (ball z r) ≠ 0 := (volume_ball_pos z hr).ne'
  have hBt : volume (ball z r) ≠ ⊤ := volume_ball_ne_top z hr
  have hGm : MemLp (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y))
      (ENNReal.ofReal p) (volume.restrict (ball z r)) :=
    PDE.GradMemLpOn.memLp_vecEuclideanNorm
      (PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := ENNReal.ofReal p) hB hφ1).gradMemLp
  have hM := rpow_average_norm_fderiv_le hB0 hBt hp0 hφ1 hGm
  have hD0 : ∀ y, y ∉ ball z r → ‖fderiv ℝ φ y‖ ^ p = 0 := fun y hy => by
    rw [fderiv_of_notMem_tsupport ℝ fun h => hy (hφ.2.2 h), norm_zero,
      Real.zero_rpow hp0.ne']
  have hIK : ∫ y in ball z (2 * r), ‖fderiv ℝ φ y‖ ^ p = ∫ y in ball z r, ‖fderiv ℝ φ y‖ ^ p := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hD0 y fun h => hy (hBK h),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hD0 y hy]
  have hI0 : 0 ≤ ∫ y in ball z r, ‖fderiv ℝ φ y‖ ^ p :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _
  have hvol : (volume (ball z (2 * r))).toReal⁻¹ ≤ (volume (ball z r)).toReal⁻¹ :=
    inv_anti₀ (ENNReal.toReal_pos hB0 hBt)
      (ENNReal.toReal_mono (volume_ball_ne_top z hr2) (measure_mono hBK))
  have hKB : ((volume (ball z (2 * r))).toReal⁻¹ * ∫ y in ball z (2 * r), ‖fderiv ℝ φ y‖ ^ p) ^
      (1 / p) ≤ ((volume (ball z r)).toReal⁻¹ * ∫ y in ball z r, ‖fderiv ℝ φ y‖ ^ p) ^ (1 / p) := by
    rw [hIK]
    exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hI0)
      (mul_le_mul_of_nonneg_right hvol hI0) (by positivity)
  calc |φ x| ≤ 2 * (1 / (1 - (d : ℝ) / p)) * (2 * (2 * r)) *
        ((volume (ball z (2 * r))).toReal⁻¹ * ∫ y in ball z (2 * r), ‖fderiv ℝ φ y‖ ^ p) ^
          (1 / p) := hmor
    _ ≤ 2 * (1 / (1 - (d : ℝ) / p)) * (2 * (2 * r)) *
        (Real.sqrt d * (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p)
          (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y))).toReal) :=
        mul_le_mul_of_nonneg_left (hKB.trans hM) (by positivity)
    _ = _ := by
        change _ = 8 * Real.sqrt d / (1 - d / p) * r *
          (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p)
            (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y))).toReal
        field_simp
        ring

end QSH
