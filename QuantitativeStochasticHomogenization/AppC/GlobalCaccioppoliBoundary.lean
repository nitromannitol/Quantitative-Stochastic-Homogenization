import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoli

/-!
# The global Caccioppoli estimate near the boundary

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.8, the estimate (C.18): for `u ∈ H¹₀(U)` solving `-∇·(a∇u) = h` in `U`,
`z ∈ ∂U` and `r > 0`,
`‖∇u‖_{L̲²(B_{r/2}(z) ∩ U)} ≤ C (r^{-1} ‖u‖_{L̲²(B_r(z) ∩ U)} + ‖h‖_{H̲^{-1}(B_r(z) ∩ U)})`.

The book's proof is that of Lemma C.2 with the test function `φ² u`, which lies in
`H¹₀(B_r(z) ∩ U)` because `u ∈ H¹₀(U)`. This file proves:
* `h10MulCutoff`: for `u ∈ H¹₀(U)`, a smooth compactly supported `θ` and an open `V ⊆ U` with
  `supp θ ∩ U ⊆ V`, the product `θ u` as an element of `H¹₀(V)`, with the approximants `θ uₙ`;
* `caccioppoli_of_cutoff`: the Caccioppoli computation of Lemma C.2 on an arbitrary set `V` of
  finite measure, for a solution `u ∈ H¹(V)`, a constant `c`, a cutoff `φ` equal to `1` on
  `W ⊆ V` with `|∇φ| ≤ 64/r`, and a test `φ² (u - c) ∈ H¹₀(V)`, with the constant explicit in
  `|V| / |W|` and `r |V|^{-1/d}`;
* `boundaryCaccioppoli`: (C.18) for every ball `B_r(z)` with `|B_{r/2}(z) ∩ U| > 0`, with this
  explicit constant.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The product `θ u ∈ H¹₀(V)` of `u ∈ H¹₀(U)` with a smooth compactly supported `θ`, for an open
`V ⊆ U` containing `supp θ ∩ U`; its approximants are `θ uₙ`. -/
def h10MulCutoff {U V : Set (Vec d)} (u : PDE.H10Function U) (hVo : IsOpen V) (hVU : V ⊆ U)
    {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθV : tsupport θ ∩ U ⊆ V) : PDE.H10Function V where
  toH1Function := (u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc
  approx n := fun x => θ x * u.approx n x
  approx_smooth n := hθ.mul (u.approx_smooth n)
  approx_hasCompactSupport n := (u.approx_hasCompactSupport n).mul_left
  approx_support_subset n :=
    (subset_inter tsupport_mul_subset_left
      (tsupport_mul_subset_right.trans (u.approx_support_subset n))).trans hθV
  tendsto_approx := by
    obtain ⟨M, hM⟩ := hθ.continuous.bounded_above_of_compact_support hθc
    have hres : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
    have hbound : ∀ n, eLpNorm (fun x => θ x * u.approx n x -
        ((u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc).toFun x) 2
          (volume.restrict V) ≤ ENNReal.ofReal M *
            eLpNorm (fun x => u.approx n x - u.toH1Function.toFun x) 2 (volume.restrict U) := by
      intro n
      simp only [PDE.H1Function.mulContDiffHasCompactSupport_toFun,
        PDE.H1Function.restrict_toFun]
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x => ?_) 2).trans
        (mul_le_mul_right (eLpNorm_mono_measure _ hres) _)
      · exact ((hθ.continuous.mul (u.approx_smooth n).continuous).aestronglyMeasurable.sub
          (hθ.continuous.aestronglyMeasurable.mul
            (u.toH1Function.memL2.aestronglyMeasurable.mono_measure hres)))
      · change ‖θ x * u.approx n x - θ x * u.toH1Function.toFun x‖ ≤
          M * ‖u.approx n x - u.toH1Function.toFun x‖
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    have h := ENNReal.Tendsto.const_mul u.tendsto_approx
      (Or.inr (ENNReal.ofReal_ne_top (r := M)))
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => zero_le) hbound
  tendsto_approx_grad := by
    intro i
    obtain ⟨M, hM⟩ := hθ.continuous.bounded_above_of_compact_support hθc
    have hDθc : Continuous fun x => fderiv ℝ θ x (PDE.basisVec i) :=
      (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨M', hM'⟩ := hDθc.bounded_above_of_compact_support
      (hθc.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i))
    have hres : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
    set a : ℕ → Vec d → ℝ := fun n x =>
      fderiv ℝ (u.approx n) x (PDE.basisVec i) - u.toH1Function.grad x i with ha
    set b : ℕ → Vec d → ℝ := fun n x => u.approx n x - u.toH1Function.toFun x with hb
    have hgm : AEStronglyMeasurable (fun x => u.toH1Function.grad x i) (volume.restrict U) :=
      (u.toH1Function.gradMemL2 i).aestronglyMeasurable
    have ham : ∀ n, AEStronglyMeasurable (a n) (volume.restrict U) := fun n =>
      (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.sub hgm
    have hbm : ∀ n, AEStronglyMeasurable (b n) (volume.restrict U) := fun n =>
      (u.approx_smooth n).continuous.aestronglyMeasurable.sub
        u.toH1Function.memL2.aestronglyMeasurable
    have hpt : ∀ n x, fderiv ℝ (fun y => θ y * u.approx n y) x (PDE.basisVec i) -
        ((u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc).grad x i =
          θ x * a n x + fderiv ℝ θ x (PDE.basisVec i) * b n x := by
      intro n x
      have hθd : DifferentiableAt ℝ θ x := hθ.differentiable (by simp) x
      have hud : DifferentiableAt ℝ (u.approx n) x :=
        (u.approx_smooth n).differentiable (by simp) x
      have e : (fun y => θ y * u.approx n y) = θ * u.approx n := rfl
      rw [e, fderiv_mul hθd hud, PDE.H1Function.mulContDiffHasCompactSupport_grad]
      change θ x * fderiv ℝ (u.approx n) x (PDE.basisVec i) +
          u.approx n x * fderiv ℝ θ x (PDE.basisVec i) -
          (θ x * u.toH1Function.grad x i +
            u.toH1Function.toFun x * fderiv ℝ θ x (PDE.basisVec i)) = _
      simp only [ha, hb]
      ring
    have hbound : ∀ n, eLpNorm (fun x => fderiv ℝ (fun y => θ y * u.approx n y) x
        (PDE.basisVec i) -
        ((u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc).grad x i) 2
          (volume.restrict V) ≤ ENNReal.ofReal M * eLpNorm (a n) 2 (volume.restrict U) +
            ENNReal.ofReal M' * eLpNorm (b n) 2 (volume.restrict U) := by
      intro n
      simp_rw [hpt n]
      have hsplit : (fun x => θ x * a n x + fderiv ℝ θ x (PDE.basisVec i) * b n x) =
          (fun x => θ x * a n x) + fun x => fderiv ℝ θ x (PDE.basisVec i) * b n x := rfl
      rw [hsplit]
      refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
      · refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hθ.continuous.aestronglyMeasurable.mul ((ham n).mono_measure hres))
          (Eventually.of_forall fun x => ?_) 2).trans
          (mul_le_mul_right (eLpNorm_mono_measure _ hres) _)
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
      · refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hDθc.aestronglyMeasurable.mul ((hbm n).mono_measure hres))
          (Eventually.of_forall fun x => ?_) 2).trans
          (mul_le_mul_right (eLpNorm_mono_measure _ hres) _)
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _)
    have h1 := ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i)
      (Or.inr (ENNReal.ofReal_ne_top (r := M)))
    have h2 := ENNReal.Tendsto.const_mul u.tendsto_approx
      (Or.inr (ENNReal.ofReal_ne_top (r := M')))
    have h3 := h1.add h2
    rw [mul_zero, mul_zero, add_zero] at h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
      (fun n => zero_le) hbound

theorem h10MulCutoff_apply {U V : Set (Vec d)} (u : PDE.H10Function U) (hVo : IsOpen V)
    (hVU : V ⊆ U) {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθV : tsupport θ ∩ U ⊆ V) (x : Vec d) :
    (h10MulCutoff u hVo hVU hθ hθc hθV).toH1Function x = θ x * u.toH1Function x := by
  exact (congrFun (PDE.H1Function.mulContDiffHasCompactSupport_toFun _ hθ hθc) x).trans rfl

theorem h10MulCutoff_grad {U V : Set (Vec d)} (u : PDE.H10Function U) (hVo : IsOpen V)
    (hVU : V ⊆ U) {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθV : tsupport θ ∩ U ⊆ V) (x : Vec d) :
    (h10MulCutoff u hVo hVU hθ hθc hθV).toH1Function.grad x =
      θ x • u.toH1Function.grad x + u.toH1Function x • PDE.classicalGradient θ x := by
  exact (congrFun (PDE.H1Function.mulContDiffHasCompactSupport_grad _ hθ hθc) x).trans rfl

end QSH
