import QuantitativeStochasticHomogenization.AppB.PropositionB11
import QuantitativeStochasticHomogenization.AppB.ConvexMorreySmooth
import PDEFoundation.Sobolev.W1p.ConvexApprox.Density

/-!
# Morrey's inequality for `W^{1,p}` functions on bounded convex domains

For a bounded open convex `U ⊆ ℝ^d`, `d ≥ 1`, `p ∈ (d, ∞)`, a bound `δ` of the distances of
points of `U`, and `u ∈ W^{1,p}(U)`, almost every `x ∈ U` satisfies
`|u(x) - (u)_U| ≤ (1 - d/p)⁻¹ δ √d ‖∇u‖_{L̲^p(U)}`.

The proof is the `C¹` case `QSH.ConvexMorrey.abs_sub_average_le` (Gilbarg–Trudinger, Lemma 7.16)
applied to the smooth approximants of the elliptic regularity library on convex domains,
`PDE.W1pFunction.convexApproxSmoothW1p`, which converge in `L^p(U)`, in mean, and in the norm
`‖∇·‖_{L̲^p(U)}`; the bound passes to an almost everywhere convergent subsequence.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The operator norm of `Df(y)` for the supremum norm on `ℝ^d` is at most `√d |∇f(y)|`. -/
theorem norm_fderiv_le_sqrt_mul (f : Vec d → ℝ) (y : Vec d) :
    ‖fderiv ℝ f y‖ ≤ Real.sqrt d * PDE.vecEuclideanNorm (PDE.classicalGradient f y) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (PDE.vecEuclideanNorm_nonneg _)) fun v => ?_
  rw [Real.norm_eq_abs]
  calc |fderiv ℝ f y v|
      ≤ PDE.vecEuclideanNorm (PDE.classicalGradient f y) * PDE.vecEuclideanNorm v :=
        PDE.abs_fderiv_apply_le_vecEuclideanNorm_gradient_mul f y v
    _ ≤ PDE.vecEuclideanNorm (PDE.classicalGradient f y) * (Real.sqrt d * ‖v‖) :=
        mul_le_mul_of_nonneg_left (PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm v)
          (PDE.vecEuclideanNorm_nonneg _)
    _ = Real.sqrt d * PDE.vecEuclideanNorm (PDE.classicalGradient f y) * ‖v‖ := by ring

/-- The normalized norm of a nonnegative `L^p` function as a real number. -/
theorem toReal_eLpMeanNormOn_eq {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {p : ℝ} (hp : 0 < p)
    {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict U)) :
    (PDE.eLpMeanNormOn U (ENNReal.ofReal p) f).toReal =
      ((volume U).toReal⁻¹ * ∫ x in U, f x ^ p) ^ (1 / p) := by
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt),
    one_div_toReal_ofReal hp]
  change ((volume U)⁻¹ ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) (volume.restrict U)).toReal = _
  rw [hf.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top]
  simp only [Real.norm_of_nonneg (hf0 _)]
  have hI : 0 ≤ ∫ x in U, f x ^ p := integral_nonneg fun x => Real.rpow_nonneg (hf0 x) p
  rw [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),
    Real.mul_rpow (inv_nonneg.2 ENNReal.toReal_nonneg) hI, one_div p]

/-- **Morrey's inequality on a bounded convex domain**: for `p ∈ (d, ∞)` and
`u ∈ W^{1,p}(U)`, almost every `x ∈ U` satisfies
`|u(x) - (u)_U| ≤ (1 - d/p)⁻¹ δ √d ‖∇u‖_{L̲^p(U)}`, where `δ` bounds the distances in `U`. -/
theorem ae_abs_sub_integralAverage_le_of_convex {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hUne : U.Nonempty) {δ : ℝ}
    (hδ : ∀ a ∈ U, ∀ b ∈ U, ‖a - b‖ ≤ δ) (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p)
    (u : PDE.W1pFunction U (ENNReal.ofReal p)) :
    ∀ᵐ x ∂(volume.restrict U), |u.toFun x - PDE.integralAverage U u.toFun| ≤
      1 / (1 - d / p) * δ * Real.sqrt d *
        (PDE.eLpMeanNormOn U (ENNReal.ofReal p) (fun y => PDE.vecEuclideanNorm (u.grad y))).toReal := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hp1' : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp1.le
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hU := isOpenBoundedConvexDomain_of_isBounded hUo hUb hUc
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hUne).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hUpos : 0 < volume U := pos_iff_ne_zero.2 hU0
  obtain ⟨x0, hx0⟩ := hUne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo x0 hx0
  have hr : 0 < ε / 2 := half_pos hε
  have hball : Metric.closedBall x0 (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  set ψ : ℕ → PDE.W1pFunction U (ENNReal.ofReal p) := fun n =>
    PDE.W1pFunction.convexApproxSmoothW1p hU hp1' u x0 hr n with hψ
  have hlp : Tendsto (fun n => eLpNorm ((ψ n).toFun - u.toFun) (ENNReal.ofReal p)
      (volume.restrict U)) atTop (𝓝 0) :=
    PDE.W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp1' hpT u hball hr
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by simpa using hp0) hlp).exists_seq_tendsto_ae
  have havg := PDE.W1pFunction.tendsto_convexApproxSmoothW1p_integralAverage hU hp1' hpT u
    hball hr hUpos
  have hgrad := PDE.W1pFunction.tendsto_convexApproxSmoothW1p_grad_euclidean_eLpMeanNorm hU hp1'
    hpT u hball hr hUpos
  have hfin : PDE.eLpMeanNormOn U (ENNReal.ofReal p) (fun y => PDE.vecEuclideanNorm (u.grad y)) ≠
      ⊤ := by
    rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt)]
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.inv_ne_top.2 hU0)) ?_
    exact (PDE.GradMemLpOn.memLp_vecEuclideanNorm u.gradMemLp).eLpNorm_lt_top.ne
  set c : ℝ := 1 / (1 - d / p) * δ * Real.sqrt d with hc
  have hbound : ∀ n, ∀ x ∈ U, |(ψ n).toFun x - PDE.integralAverage U (ψ n).toFun| ≤
      c * (PDE.eLpMeanNormOn U (ENNReal.ofReal p)
        (fun y => PDE.vecEuclideanNorm ((ψ n).grad y))).toReal := by
    intro n x hx
    set f := (ψ n).toFun with hf
    have hfs : ContDiff ℝ 1 f :=
      (PDE.W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU hp1' u x0 hr n).of_le
        (by exact_mod_cast le_top)
    have h1 := ConvexMorrey.abs_sub_average_le volume hfs hUo.measurableSet hUc hUb hU0 hx
      (fun y hy => hδ y hy x hx) hp1 (by simpa [Module.finrank_fin_fun] using hdp)
    rw [Module.finrank_fin_fun] at h1
    have hgf : (ψ n).grad = PDE.classicalGradient f := rfl
    have hGm : MemLp (fun y => PDE.vecEuclideanNorm ((ψ n).grad y)) (ENNReal.ofReal p)
        (volume.restrict U) := PDE.GradMemLpOn.memLp_vecEuclideanNorm (ψ n).gradMemLp
    have hDm : MemLp (fun y => ‖fderiv ℝ f y‖) (ENNReal.ofReal p) (volume.restrict U) := by
      refine (hGm.const_mul (Real.sqrt d)).of_le
        (hfs.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [norm_norm, Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (PDE.vecEuclideanNorm_nonneg _)), hgf]
      exact norm_fderiv_le_sqrt_mul f y
    have hM : ((volume U).toReal⁻¹ * ∫ y in U, ‖fderiv ℝ f y‖ ^ p) ^ (1 / p) ≤
        Real.sqrt d * (PDE.eLpMeanNormOn U (ENNReal.ofReal p)
          (fun y => PDE.vecEuclideanNorm ((ψ n).grad y))).toReal := by
      rw [← toReal_eLpMeanNormOn_eq hUt hp0 (fun y => norm_nonneg _) hDm]
      have hle : PDE.eLpMeanNormOn U (ENNReal.ofReal p) (fun y => ‖fderiv ℝ f y‖) ≤
          ENNReal.ofReal (Real.sqrt d) * PDE.eLpMeanNormOn U (ENNReal.ofReal p)
            (fun y => PDE.vecEuclideanNorm ((ψ n).grad y)) := by
        rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt),
          PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt),
          mul_left_comm]
        refine mul_le_mul' le_rfl ?_
        change eLpNorm (fun y => ‖fderiv ℝ f y‖) (ENNReal.ofReal p) (volume.restrict U) ≤
          ENNReal.ofReal (Real.sqrt d) * eLpNorm (fun y => PDE.vecEuclideanNorm ((ψ n).grad y))
            (ENNReal.ofReal p) (volume.restrict U)
        calc eLpNorm (fun y => ‖fderiv ℝ f y‖) (ENNReal.ofReal p) (volume.restrict U)
            ≤ eLpNorm (fun y => Real.sqrt d * PDE.vecEuclideanNorm ((ψ n).grad y))
                (ENNReal.ofReal p) (volume.restrict U) := by
              refine eLpNorm_mono_real hDm.aestronglyMeasurable fun y => ?_
              rw [norm_norm, hgf]
              exact norm_fderiv_le_sqrt_mul f y
          _ = ENNReal.ofReal (Real.sqrt d) * eLpNorm
                (fun y => PDE.vecEuclideanNorm ((ψ n).grad y)) (ENNReal.ofReal p)
                (volume.restrict U) := by
              rw [show (fun y => Real.sqrt d * PDE.vecEuclideanNorm ((ψ n).grad y)) =
                Real.sqrt d • (fun y => PDE.vecEuclideanNorm ((ψ n).grad y)) from rfl,
                eLpNorm_const_smul, Real.enorm_of_nonneg (Real.sqrt_nonneg _)]
      have hfin' : ENNReal.ofReal (Real.sqrt d) * PDE.eLpMeanNormOn U (ENNReal.ofReal p)
          (fun y => PDE.vecEuclideanNorm ((ψ n).grad y)) ≠ ⊤ := by
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
        rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt)]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
          (ENNReal.inv_ne_top.2 hU0)) hGm.eLpNorm_lt_top.ne
      calc (PDE.eLpMeanNormOn U (ENNReal.ofReal p) (fun y => ‖fderiv ℝ f y‖)).toReal
          ≤ (ENNReal.ofReal (Real.sqrt d) * PDE.eLpMeanNormOn U (ENNReal.ofReal p)
              (fun y => PDE.vecEuclideanNorm ((ψ n).grad y))).toReal :=
            ENNReal.toReal_mono hfin' hle
        _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    have hc0 : 0 ≤ 1 / (1 - (d : ℝ) / p) * δ := by
      have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ x hx x hx)
      have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
      exact mul_nonneg (one_div_nonneg.2 (by linarith)) hδ0
    calc |f x - PDE.integralAverage U f|
        ≤ 1 / (1 - (d : ℝ) / p) * δ *
            ((volume U).toReal⁻¹ * ∫ y in U, ‖fderiv ℝ f y‖ ^ p) ^ (1 / p) := h1
      _ ≤ 1 / (1 - (d : ℝ) / p) * δ * (Real.sqrt d * (PDE.eLpMeanNormOn U (ENNReal.ofReal p)
            (fun y => PDE.vecEuclideanNorm ((ψ n).grad y))).toReal) :=
          mul_le_mul_of_nonneg_left hM hc0
      _ = _ := by rw [hc]; ring
  filter_upwards [hae, ae_restrict_mem hUo.measurableSet] with x hx hxU
  refine le_of_tendsto_of_tendsto' ((hx.sub (havg.comp hns.tendsto_atTop)).abs)
    (tendsto_const_nhds.mul ((ENNReal.tendsto_toReal hfin).comp
      (hgrad.comp hns.tendsto_atTop))) fun k => hbound (ns k) x hxU

end QSH
