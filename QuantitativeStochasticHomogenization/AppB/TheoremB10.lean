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
  continuous_pi fun _ => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

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
  by_cases hxK : x ∈ ball z (2 * r)
  swap
  · rw [h0 x fun h => hxK (hBK h), abs_zero]
    exact hRHS
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

/-- (B.8) with `w = 0` for `v ∈ W^{1,p}_0(B_r(z))`, `p ∈ (d, ∞)`: the bound of
`abs_le_of_isSpatialTest_ball` passes to the limit along an almost everywhere convergent
subsequence of the approximating test functions. -/
theorem eLpNorm_top_ball_le_of_isW01p (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p) (z : Vec d)
    {r : ℝ} (hr : 0 < r) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : IsW01p (ball z r) (ENNReal.ofReal p) v g) :
    eLpNorm v ⊤ (volume.restrict (ball z r)) ≤
      ENNReal.ofReal (8 * Real.sqrt d / (1 - d / p) * r) *
        PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal (by linarith : 1 ≤ p)
  have hc : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
    linarith
  have hB0 : volume (ball z r) ≠ 0 := (volume_ball_pos z hr).ne'
  have hBt : volume (ball z r) ≠ ⊤ := volume_ball_ne_top z hr
  obtain ⟨φ, hφ, hlim⟩ := hv.2
  set B := ball z r with hBdef
  set μ := volume.restrict B with hμ
  set c : ℝ := 8 * Real.sqrt d / (1 - d / p) * r with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hval : Tendsto (fun n => eLpNorm (φ n - v) (ENNReal.ofReal p) μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      (fun n => eLpNorm_le_w1pNorm B _ (fun x => φ n x - v x) (fun x => gradient (φ n) x - g x))
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by simpa using hp0) hval).exists_seq_tendsto_ae
  set A := PDE.eLpMeanNormOn B (ENNReal.ofReal p) (fun x => euclideanNorm (g x)) with hA
  have hAfin : A ≠ ⊤ := eLpMeanNormOn_ne_top hB0 hBt hv.1.memLp_euclideanNorm
  set E : ℕ → ℝ≥0∞ := fun n =>
    PDE.eLpMeanNormOn B (ENNReal.ofReal p) (fun x => euclideanNorm (gradient (φ n) x - g x))
    with hE
  have hgm : AEStronglyMeasurable g μ := hv.1.2.1.aestronglyMeasurable
  have hEle : ∀ n, E n ≤ (volume B)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
      w1pNorm B (ENNReal.ofReal p) (fun x => φ n x - v x) (fun x => gradient (φ n) x - g x) := by
    intro n
    show PDE.eLpMeanNormOn B (ENNReal.ofReal p)
      (fun x => euclideanNorm (gradient (φ n) x - g x)) ≤ _
    rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hBt)]
    refine mul_le_mul' le_rfl ?_
    have hm : AEStronglyMeasurable (fun x => gradient (φ n) x - g x) μ :=
      (continuous_gradient ((hφ n).1.of_le (by exact_mod_cast le_top))).aestronglyMeasurable.sub
        hgm
    exact (eLpNorm_euclideanNorm_le_sum hp1 hm).trans le_add_self
  have hEt : Tendsto E atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (volume B)⁻¹ ^ (1 / ENNReal.ofReal p).toReal) hlim
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ENNReal.inv_ne_top.2 hB0)))
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hEle
  have hbound : ∀ n x, E n ≠ ⊤ → |φ n x| ≤ c * (A.toReal + (E n).toReal) := by
    intro n x hEn
    have hφ1 : ContDiff ℝ 1 (φ n) := (hφ n).1.of_le (by exact_mod_cast le_top)
    have h1 := abs_le_of_isSpatialTest_ball hd hdp z hr (hφ n) x
    have hN : PDE.eLpMeanNormOn B (ENNReal.ofReal p) (fun y => euclideanNorm (gradient (φ n) y)) ≤
        A + E n := by
      change eLpNorm _ _ (PDE.normalizedVolumeOn B) ≤
        eLpNorm _ _ (PDE.normalizedVolumeOn B) + eLpNorm _ _ (PDE.normalizedVolumeOn B)
      refine le_trans ?_ (eLpNorm_add_le hp1)
      refine eLpNorm_mono_real (PDE.continuous_vecEuclideanNorm.comp
        (continuous_gradient hφ1)).aestronglyMeasurable fun y => ?_
      rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm (gradient (φ n) y) from Real.sqrt_nonneg _),
        Pi.add_apply]
      have := PDE.vecEuclideanNorm_add_le (g y) (gradient (φ n) y - g y)
      rwa [add_sub_cancel] at this
    have hN' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAfin, hEn⟩) hN
    rw [ENNReal.toReal_add hAfin hEn] at hN'
    exact h1.trans (mul_le_mul_of_nonneg_left hN' hc0)
  have hEv : ∀ᶠ k in atTop, E (ns k) ≠ ⊤ :=
    (hEt.comp hns.tendsto_atTop).eventually (gt_mem_nhds zero_lt_one) |>.mono
      fun k hk => ne_top_of_lt hk
  have hlimE : Tendsto (fun k => c * (A.toReal + (E (ns k)).toReal)) atTop
      (𝓝 (c * (A.toReal + 0))) := by
    refine tendsto_const_nhds.mul (tendsto_const_nhds.add ?_)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hEt.comp hns.tendsto_atTop)
    rw [ENNReal.toReal_zero] at this
    exact this
  rw [add_zero] at hlimE
  have hvb : ∀ᵐ x ∂μ, ‖v x‖ ≤ c * A.toReal := by
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    exact le_of_tendsto_of_tendsto hx.abs hlimE (hEv.mono fun k hk => hbound (ns k) x hk)
  rw [eLpNorm_exponent_top hv.1.1.aestronglyMeasurable]
  refine (eLpNormEssSup_le_of_ae_bound hvb).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hAfin]

/-- Every point of `ℝ^d` lies in a ball `B_{√d}(z)` with `z ∈ ℤ^d`. -/
theorem exists_mem_ball_latticeShift (hd : 0 < d) (x : Vec d) :
    ∃ z : LatticeIndex d, x ∈ ball (latticeShift z) (Real.sqrt d) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  refine ⟨fun i => round (x i), ?_⟩
  show euclideanNorm (x - latticeShift fun i => round (x i)) < Real.sqrt d
  rw [euclideanNorm_eq_vecEuclideanNorm]
  have hn : ‖x - latticeShift fun i => round (x i)‖ ≤ 1 / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_sub_round (x i)
  calc PDE.vecEuclideanNorm (x - latticeShift fun i => round (x i))
      ≤ Real.sqrt d * ‖x - latticeShift fun i => round (x i)‖ :=
        PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _
    _ ≤ Real.sqrt d * (1 / 2) := mul_le_mul_of_nonneg_left hn hs.le
    _ < Real.sqrt d := by linarith

/-- The balls `B_{√d}(z)` have volume at least `1`. -/
theorem one_le_volume_ball_sqrt (hd : 0 < d) (z : Vec d) :
    1 ≤ volume (ball z (Real.sqrt d)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsub : Metric.ball z 1 ⊆ ball z (Real.sqrt d) := fun x hx => by
    show euclideanNorm (x - z) < Real.sqrt d
    rw [euclideanNorm_eq_vecEuclideanNorm]
    have h1 : ‖x - z‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    calc PDE.vecEuclideanNorm (x - z) ≤ Real.sqrt d * ‖x - z‖ :=
          PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _
      _ < Real.sqrt d * 1 := mul_lt_mul_of_pos_left h1 hs
      _ = Real.sqrt d := mul_one _
  calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * 1) ^ d) := by
        rw [ENNReal.one_le_ofReal]
        exact one_le_pow₀ (by norm_num)
    _ = volume (Metric.ball z 1) := by rw [Real.volume_pi_ball z one_pos, Fintype.card_fin]
    _ ≤ volume (ball z (Real.sqrt d)) := measure_mono hsub

/-- The normalized norm on a set of volume at least `1` is at most the norm on `ℝ^d`. -/
theorem eLpMeanNormOn_le_eLpNorm {U : Set (Vec d)} (hU1 : 1 ≤ volume U) (hUt : volume U ≠ ⊤)
    (p : ℝ≥0∞) {E : Type*} [NormedAddCommGroup E] (f : Vec d → E) :
    PDE.eLpMeanNormOn U p f ≤ eLpNorm f p volume := by
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt)]
  calc (volume U)⁻¹ ^ (1 / p).toReal * PDE.eLpNormOn U p f ≤ 1 * PDE.eLpNormOn U p f :=
        mul_le_mul' (ENNReal.rpow_le_one (ENNReal.inv_le_one.2 hU1) ENNReal.toReal_nonneg) le_rfl
    _ = eLpNorm f p (volume.restrict U) := one_mul _
    _ ≤ eLpNorm f p volume := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The average of `v` over `U` is bounded by its normalized `L^p(U)` norm, `p ≥ 1`. -/
theorem abs_integralAverage_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {v : Vec d → ℝ} (hv : MemLp v p (volume.restrict U)) :
    |PDE.integralAverage U v| ≤ (PDE.eLpMeanNormOn U p v).toReal := by
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (pos_iff_ne_zero.2 hU0)
      (lt_top_iff_ne_top.2 hUt)
  rw [← PDE.integral_normalizedVolumeOn_eq_integralAverage, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm v).trans ?_
  simp only [ofReal_norm]
  rw [← eLpNorm_one_eq_lintegral_enorm]
  · exact ENNReal.toReal_mono (eLpMeanNormOn_ne_top hU0 hUt hv)
      (eLpNorm_le_eLpNorm_of_exponent_le hp)
  · exact hv.aestronglyMeasurable.smul_measure (volume U)⁻¹

/-- (B.9) for `p ∈ (d, ∞)`: `‖v‖_{L^∞(ℝ^d)} ≤ C ‖v‖_{W^{1,p}(ℝ^d)}`. -/
theorem eLpNorm_top_le_w1pNorm_univ (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
      IsW1p Set.univ (ENNReal.ofReal p) v g →
        eLpNorm v ⊤ volume ≤ ENNReal.ofReal C * w1pNorm Set.univ (ENNReal.ofReal p) v g := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal (by linarith : 1 ≤ p)
  have hc : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
    linarith
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  set c : ℝ := 1 / (1 - d / p) * (2 * Real.sqrt d) * Real.sqrt d with hcdef
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c + 1, by positivity, fun v g hv => ?_⟩
  set W := w1pNorm Set.univ (ENNReal.ofReal p) v g with hW
  have hWfin : W ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨hv.1.eLpNorm_lt_top.ne, ?_⟩
    exact (ENNReal.sum_lt_top.2 fun i _ => (hv.2.1.eval i).eLpNorm_lt_top).ne
  have hball : ∀ z : LatticeIndex d, ∀ᵐ x ∂(volume.restrict (ball (latticeShift z) (Real.sqrt d))),
      |v x| ≤ (c + 1) * W.toReal := by
    intro z
    set B := ball (latticeShift z) (Real.sqrt d) with hB
    have hB1 := one_le_volume_ball_sqrt hd (latticeShift z)
    have hB0 : volume B ≠ 0 := (lt_of_lt_of_le zero_lt_one hB1).ne'
    have hBt : volume B ≠ ⊤ := volume_ball_ne_top _ hs
    have hBc := isOpenBoundedConvexDomain_ball (latticeShift z) hs
    have hvB : IsW1p B (ENNReal.ofReal p) v g := hv.mono (Set.subset_univ _)
    have hae := ae_abs_sub_integralAverage_le_of_convex hBc.1 (isBounded_ball _ hs) hBc.2.2
      ⟨_, center_mem_ball _ hs⟩ (fun a ha b hb => norm_sub_le_of_mem_ball ha hb) hd hdp
      hvB.toW1pFunction
    have hG : (PDE.eLpMeanNormOn B (ENNReal.ofReal p)
        (fun y => PDE.vecEuclideanNorm (g y))).toReal ≤ W.toReal := by
      refine ENNReal.toReal_mono hWfin ((eLpMeanNormOn_le_eLpNorm hB1 hBt _ _).trans ?_)
      have h := hv.eLpNorm_euclideanNorm_le_w1pNorm hp1
      rwa [Measure.restrict_univ] at h
    have hA : |PDE.integralAverage B v| ≤ W.toReal := by
      refine (abs_integralAverage_le hB0 hBt hp1 hvB.1).trans
        (ENNReal.toReal_mono hWfin ((eLpMeanNormOn_le_eLpNorm hB1 hBt _ _).trans ?_))
      have h := eLpNorm_le_w1pNorm Set.univ (ENNReal.ofReal p) v g
      rwa [Measure.restrict_univ] at h
    filter_upwards [hae] with x hx
    have hx' : |v x - PDE.integralAverage B v| ≤ c * W.toReal :=
      hx.trans (by rw [hcdef]; exact mul_le_mul_of_nonneg_left hG (by positivity))
    calc |v x| ≤ |v x - PDE.integralAverage B v| + |PDE.integralAverage B v| := by
          have := abs_add_le (v x - PDE.integralAverage B v) (PDE.integralAverage B v)
          rwa [sub_add_cancel] at this
      _ ≤ c * W.toReal + W.toReal := add_le_add hx' hA
      _ = (c + 1) * W.toReal := by ring
  have hall : ∀ᵐ x ∂volume, ∀ z : LatticeIndex d,
      x ∈ ball (latticeShift z) (Real.sqrt d) → |v x| ≤ (c + 1) * W.toReal :=
    ae_all_iff.2 fun z => (ae_restrict_iff' (isOpenBoundedConvexDomain_ball _ hs).1.measurableSet).1
      (hball z)
  have hvb : ∀ᵐ x ∂volume, ‖v x‖ ≤ (c + 1) * W.toReal := by
    filter_upwards [hall] with x hx
    obtain ⟨z, hz⟩ := exists_mem_ball_latticeShift hd x
    rw [Real.norm_eq_abs]
    exact hx z hz
  have hvm : AEStronglyMeasurable v volume := by
    have h := hv.1.aestronglyMeasurable
    rwa [Measure.restrict_univ] at h
  rw [eLpNorm_exponent_top hvm]
  refine (eLpNormEssSup_le_of_ae_bound hvb).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hWfin]

/-- **Theorem B.10** (Morrey's inequality), `k = 1`, for a finite exponent `p ∈ (d, ∞)`. -/
theorem theorem_B_10_one_ofReal (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
        (IsW1p (ball z r) (ENNReal.ofReal p) v g →
          ⨅ w : ℝ, eLpNorm (fun x => v x - w) ⊤ (volume.restrict (ball z r)) ≤
            ENNReal.ofReal (C * r) *
              PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x))) ∧
        (IsW01p (ball z r) (ENNReal.ofReal p) v g →
          eLpNorm v ⊤ (volume.restrict (ball z r)) ≤
            ENNReal.ofReal (C * r) *
              PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x)))) ∧
      ∀ (v : Vec d → ℝ) (g : Vec d → Vec d), IsW1p Set.univ (ENNReal.ofReal p) v g →
        eLpNorm v ⊤ volume ≤ ENNReal.ofReal C * w1pNorm Set.univ (ENNReal.ofReal p) v g := by
  have hp0 : 0 < p := (Nat.cast_pos.2 hd).trans hdp
  have hc : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
    linarith
  obtain ⟨Cg, hCg, hglob⟩ := eLpNorm_top_le_w1pNorm_univ hd hdp
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 8 * Real.sqrt d / (1 - d / p) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact div_nonneg (by positivity) hc.le
  have h28 : 2 * Real.sqrt d / (1 - d / p) ≤ a := by
    rw [ha]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.sqrt_nonneg (d : ℝ)]) hc.le
  refine ⟨a + Cg, by positivity, fun z r hr v g => ⟨fun hv => ?_, fun hv => ?_⟩, fun v g hv => ?_⟩
  · refine (iInf_le _ (PDE.integralAverage (ball z r) v)).trans
      ((eLpNorm_top_sub_integralAverage_ball_le hd hdp z hr hv).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
    exact mul_le_mul_of_nonneg_right (by linarith) hr.le
  · refine (eLpNorm_top_ball_le_of_isW01p hd hdp z hr hv).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [← ha]
    exact mul_le_mul_of_nonneg_right (by linarith) hr.le
  · exact (hglob v g hv).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)

theorem IsW1p.of_top {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {q : ℝ≥0∞} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hv : IsW1p U ⊤ v g) : IsW1p U q v g := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  exact ⟨hv.1.mono_exponent le_top, hv.2.1.mono_exponent le_top, hv.2.2⟩

theorem eLpMeanNormOn_le_eLpMeanNormOn_top {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) (q : ℝ≥0∞) {E : Type*} [NormedAddCommGroup E] (f : Vec d → E) :
    PDE.eLpMeanNormOn U q f ≤ PDE.eLpMeanNormOn U ⊤ f := by
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (pos_iff_ne_zero.2 hU0)
      (lt_top_iff_ne_top.2 hUt)
  exact eLpNorm_le_eLpNorm_of_exponent_le le_top

theorem w1pNorm_le_w1pNorm_top_mul {U : Set (Vec d)} (q : ℝ≥0∞) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : AEStronglyMeasurable u (volume.restrict U))
    (hg : AEStronglyMeasurable g (volume.restrict U)) :
    w1pNorm U q u g ≤ w1pNorm U ⊤ u g * volume U ^ (1 / q.toReal) := by
  have key : ∀ f : Vec d → ℝ, AEStronglyMeasurable f (volume.restrict U) →
      eLpNorm f q (volume.restrict U) ≤
        eLpNorm f ⊤ (volume.restrict U) * volume U ^ (1 / q.toReal) := fun f hf => by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (le_top : q ≤ ⊤) hf
    rwa [Measure.restrict_apply_univ, ENNReal.toReal_top, div_zero, sub_zero] at h
  unfold w1pNorm
  rw [add_mul, Finset.sum_mul]
  exact add_le_add (key u hu)
    (Finset.sum_le_sum fun i _ => key _ ((continuous_apply i).comp_aestronglyMeasurable hg))

theorem IsW01p.of_top {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {q : ℝ≥0∞} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hv : IsW01p U ⊤ v g) : IsW01p U q v g := by
  obtain ⟨φ, hφ, hlim⟩ := hv.2
  refine ⟨hv.1.of_top hUt, φ, hφ, ?_⟩
  have h := ENNReal.Tendsto.mul_const (b := volume U ^ (1 / q.toReal)) hlim
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity) hUt))
  rw [zero_mul] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => w1pNorm_le_w1pNorm_top_mul q ?_ ?_
  · exact (hφ n).1.continuous.aestronglyMeasurable.sub hv.1.1.aestronglyMeasurable
  · exact (continuous_gradient ((hφ n).1.of_le (by exact_mod_cast le_top))).aestronglyMeasurable.sub
      hv.1.2.1.aestronglyMeasurable

/-- **Theorem B.10** (Morrey's inequality), `k = 1`: for `d ≥ 1` and `p ∈ (d, ∞]` there is
`C(p, d)` such that for every ball `B_r(z)` and `v ∈ W^{1,p}(B_r(z))`,
`inf_{w ∈ ℝ} ‖v - w‖_{L^∞(B_r(z))} ≤ C r ‖∇v‖_{L̲^p(B_r(z))}` (B.8);
`‖v‖_{L^∞(B_r(z))} ≤ C r ‖∇v‖_{L̲^p(B_r(z))}` if `v ∈ W^{1,p}_0(B_r(z))`; and
`‖v‖_{L^∞(ℝ^d)} ≤ C ‖v‖_{W^{1,p}(ℝ^d)}` for `v ∈ W^{1,p}(ℝ^d)` (B.9). -/
theorem theorem_B_10_one (hd : 0 < d) (p : ℝ≥0∞) (hp : (d : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
        (IsW1p (ball z r) p v g →
          ⨅ w : ℝ, eLpNorm (fun x => v x - w) ⊤ (volume.restrict (ball z r)) ≤
            ENNReal.ofReal (C * r) *
              PDE.eLpMeanNormOn (ball z r) p (fun x => euclideanNorm (g x))) ∧
        (IsW01p (ball z r) p v g →
          eLpNorm v ⊤ (volume.restrict (ball z r)) ≤
            ENNReal.ofReal (C * r) *
              PDE.eLpMeanNormOn (ball z r) p (fun x => euclideanNorm (g x)))) ∧
      ∀ (v : Vec d → ℝ) (g : Vec d → Vec d), IsW1p Set.univ p v g →
        eLpNorm v ⊤ volume ≤ ENNReal.ofReal C * w1pNorm Set.univ p v g := by
  by_cases hpt : p = ⊤
  · subst hpt
    obtain ⟨C, hC, hball, hglob⟩ := theorem_B_10_one_ofReal hd (by linarith : (d : ℝ) < d + 1)
    refine ⟨C + 1, by positivity, fun z r hr v g => ⟨fun hv => ?_, fun hv => ?_⟩, fun v g hv => ?_⟩
    · have hBt := volume_ball_ne_top z hr
      exact ((hball z r hr v g).1 (hv.of_top hBt)).trans (mul_le_mul'
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hr.le))
        (eLpMeanNormOn_le_eLpMeanNormOn_top (volume_ball_pos z hr).ne' hBt _ _))
    · have hBt := volume_ball_ne_top z hr
      exact ((hball z r hr v g).2 (hv.of_top hBt)).trans (mul_le_mul'
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hr.le))
        (eLpMeanNormOn_le_eLpMeanNormOn_top (volume_ball_pos z hr).ne' hBt _ _))
    · have h := eLpNorm_le_w1pNorm Set.univ ⊤ v g
      rw [Measure.restrict_univ] at h
      exact h.trans (le_mul_of_one_le_left zero_le (by rw [ENNReal.one_le_ofReal]; linarith))
  · obtain ⟨q, rfl⟩ : ∃ q : ℝ, p = ENNReal.ofReal q := ⟨p.toReal, (ENNReal.ofReal_toReal hpt).symm⟩
    have hdq : (d : ℝ) < q := by
      have h := ENNReal.toReal_strict_mono hpt hp
      rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal] at h
      by_contra hq
      rw [ENNReal.ofReal_of_nonpos (by linarith)] at hp
      exact absurd hp (not_lt.2 zero_le)
    exact theorem_B_10_one_ofReal hd hdq

end QSH
