import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatFormulaLargeTime
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianSmoothL2

/-!
# Duality for the heat Hessian

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1: the heat Hessian `∫ ∂ⱼ∂ᵢΦ_t(x - y) f(y) dy` of a field with Gaussian moments, paired
with a smooth compactly supported `ψ`, equals the pairing of `f` with the heat Hessian of `ψ`; the
same holds for the time windows `∫_{ε₁}^{ε₂}`. With two integrations by parts this moves the heat
Hessian of (6.7) onto the test function.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem euclideanNorm_le_card_mul_norm'' (v : Vec d) : euclideanNorm v ≤ d * ‖v‖ := by
  unfold euclideanNorm euclideanSq dot
  rw [Real.sqrt_le_left]
  · calc ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
          have h := norm_le_pi_norm v i
          rw [Real.norm_eq_abs] at h
          nlinarith [abs_nonneg (v i), abs_mul_abs_self (v i)]
      _ = d * (‖v‖ * ‖v‖) := by simp
      _ ≤ (d * ‖v‖) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · subst hd; simp
          · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith [norm_nonneg v, mul_nonneg (norm_nonneg v) (norm_nonneg v)]
  · positivity

private theorem heatHessianKernel_neg (t : ℝ) (i j : Fin d) (z : Vec d) :
    heatHessianKernel t i j (-z) = heatHessianKernel t i j z := by
  unfold heatHessianKernel
  rw [euclideanHeatKernel_neg]
  simp only [Pi.neg_apply, neg_mul_neg]

private theorem abs_heatHessianKernel_le_window {ε₁ ε₂ t : ℝ} (hε₁ : 0 < ε₁)
    (ht : t ∈ Icc ε₁ ε₂) (i j : Fin d) (z : Vec d) :
    |heatHessianKernel t i j z| ≤ windowHessianConst d ε₁ ε₂ * euclideanHeatKernel (2 * ε₂) z := by
  have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
  have h := abs_heatHessian_le_window hε₁ ht i j z
  rwa [heatHessian_eq ht0] at h

/-- **Duality at a fixed time.** -/
theorem integral_mul_heatHessianConv_comm {f ψ : Vec d → ℝ} (hfm : Measurable f)
    (hmom : HasGaussianMoments f) (hψ : IsSmoothCompact ψ) {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    ∫ x, ψ x * heatHessianConv t i j f x = ∫ y, f y * heatHessianConv t i j ψ y := by
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ∀ x, ψ x ≠ 0 → euclideanNorm x ≤ ρ := by
    obtain ⟨R, hR⟩ := hψ.2.isCompact.isBounded.subset_closedBall 0
    refine ⟨d * R, fun x hx => ?_⟩
    have hxR : ‖x‖ ≤ R := by
      have := hR (subset_tsupport _ hx)
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    refine (euclideanNorm_le_card_mul_norm'' x).trans ?_
    exact mul_le_mul_of_nonneg_left hxR (Nat.cast_nonneg d)
  obtain ⟨B, hB⟩ := hmom (2 * t) (by positivity) ρ
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψ.2
  set K : Vec d → ℝ := heatHessianKernel t i j with hK
  have hKm : Measurable K :=
    (measurable_heatHessianKernel i j).comp (measurable_const.prodMk measurable_id)
  have hKb : ∀ z, |K z| ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * euclideanHeatKernel (2 * t) z := by
    intro z
    have h := abs_heatHessian_le ht i j z
    rwa [heatHessian_eq ht] at h
  have hKeq : ∀ z, coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) z =
      K z := fun z => by rw [heatHessian_eq ht]; rfl
  set F : Vec d × Vec d → ℝ := fun p => ψ p.1 * K (p.1 - p.2) * f p.2 with hF
  have hFm : Measurable F :=
    ((hψc.measurable.comp measurable_fst).mul (hKm.comp (measurable_fst.sub measurable_snd))).mul
      (hfm.comp measurable_snd)
  have hFint : Integrable F (volume.prod volume) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · have h := (hmom.integrable_heatHessian_mul ht i j hfm x).const_mul (ψ x)
      refine h.congr (Eventually.of_forall fun y => ?_)
      simp only [hF]
      rw [hKeq]
      ring
    · set c : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * B with hc
      refine ((hψc.abs.integrable_of_hasCompactSupport hψ.2.abs).const_mul c).mono'
        ?_ (Eventually.of_forall fun x => ?_)
      · exact (hFm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
        by_cases hx : ψ x = 0
        · simp [hF, hx]
        have hxρ := hρ x hx
        have hint := (hB x hxρ).1
        calc ∫ y, ‖F (x, y)‖ ≤ ∫ y, |ψ x| * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) *
              (euclideanHeatKernel (2 * t) (x - y) * |f y|)) := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
                ((hint.const_mul _).const_mul _) (Eventually.of_forall fun y => ?_)
              simp only [hF, Real.norm_eq_abs, abs_mul]
              have := hKb (x - y)
              have h0 := abs_nonneg (ψ x)
              have h1 := abs_nonneg (f y)
              calc |ψ x| * |K (x - y)| * |f y| ≤ |ψ x| *
                  ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * euclideanHeatKernel (2 * t) (x - y)) *
                    |f y| := by gcongr
                _ = _ := by ring
          _ = |ψ x| * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) *
              ∫ y, euclideanHeatKernel (2 * t) (x - y) * |f y|) := by
              rw [integral_const_mul, integral_const_mul]
          _ ≤ |ψ x| * c := by
              rw [hc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB x hxρ).2
                (by positivity)) (abs_nonneg _)
          _ = c * |ψ x| := by ring
  have hswap := integral_integral_swap (f := fun x y => ψ x * K (x - y) * f y) hFint
  have hL : ∫ x, ψ x * heatHessianConv t i j f x = ∫ x, ∫ y, F (x, y) := by
    congr 1
    funext x
    rw [heatHessianConv_eq_kernel ht, ← integral_const_mul]
    congr 1
    funext y
    simp only [hF, hK]
    ring
  have hR : ∫ y, f y * heatHessianConv t i j ψ y = ∫ y, ∫ x, F (x, y) := by
    congr 1
    funext y
    rw [heatHessianConv_eq_kernel ht, ← integral_const_mul]
    congr 1
    funext x
    simp only [hF, hK]
    rw [show y - x = -(x - y) by abel, heatHessianKernel_neg]
    ring
  rw [hL, hR, hswap]

private theorem exists_support_bound {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    ∃ ρ : ℝ, ∀ x, ψ x ≠ 0 → euclideanNorm x ≤ ρ := by
  obtain ⟨R, hR⟩ := hψ.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨d * R, fun x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    have := hR (subset_tsupport _ hx)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  exact (euclideanNorm_le_card_mul_norm'' x).trans
    (mul_le_mul_of_nonneg_left hxR (Nat.cast_nonneg d))

/-- **Duality on a time window.** -/
theorem integral_mul_heatHessianWindow_comm {f ψ : Vec d → ℝ} (hfm : Measurable f)
    (hmom : HasGaussianMoments f) (hψ : IsSmoothCompact ψ) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁)
    (hε : ε₁ ≤ ε₂) (i j : Fin d) :
    ∫ x, ψ x * heatHessianWindow ε₁ ε₂ i j f x = ∫ y, f y * heatHessianWindow ε₁ ε₂ i j ψ y := by
  have hψc : Continuous ψ := hψ.1.continuous
  have hψm : Measurable ψ := hψc.measurable
  have hfin : IsFiniteMeasure (volume.restrict (Icc ε₁ ε₂)) := isFiniteMeasure_restrict_Icc ε₁ ε₂
  have hε₂ : 0 < 2 * ε₂ := by linarith
  obtain ⟨ρ, hρ⟩ := exists_support_bound hψ
  obtain ⟨B, hB⟩ := hmom (2 * ε₂) hε₂ ρ
  set W := windowHessianConst d ε₁ ε₂ with hW
  have hW0 : 0 ≤ W := windowHessianConst_nonneg hε₁ hε
  set h : ℝ × Vec d → ℝ := fun p => ∫ y, heatHessianKernel p.1 i j (p.2 - y) * f y with hh
  set k : ℝ × Vec d → ℝ := fun p => ∫ x, heatHessianKernel p.1 i j (p.2 - x) * ψ x with hk
  have hhm : StronglyMeasurable h := stronglyMeasurable_heatHessianKernelConv i j hfm
  have hkm : StronglyMeasurable k := stronglyMeasurable_heatHessianKernelConv i j hψm
  have hwin : ∀ (g : Vec d → ℝ) (x : Vec d), heatHessianWindow ε₁ ε₂ i j g x =
      ∫ t in Icc ε₁ ε₂, ∫ y, heatHessianKernel t i j (x - y) * g y := fun g x =>
    setIntegral_congr_fun measurableSet_Icc fun t ht =>
      heatHessianConv_eq_kernel (lt_of_lt_of_le hε₁ ht.1) i j g x
  -- bound of `h` on the support of `ψ`
  have hhb : ∀ t ∈ Icc ε₁ ε₂, ∀ x, euclideanNorm x ≤ ρ → |h (t, x)| ≤ W * B := by
    intro t ht x hx
    have hint := (hB x hx).1
    calc |h (t, x)| ≤ ∫ y, |heatHessianKernel t i j (x - y) * f y| := abs_integral_le_integral_abs
      _ ≤ ∫ y, W * (euclideanHeatKernel (2 * ε₂) (x - y) * |f y|) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hint.const_mul W) (Eventually.of_forall fun y => ?_)
          simp only
          rw [abs_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (abs_heatHessianKernel_le_window hε₁ ht i j _)
            (abs_nonneg _)
      _ = W * ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y| := integral_const_mul _ _
      _ ≤ W * B := mul_le_mul_of_nonneg_left (hB x hx).2 hW0
  -- first swap: `x` and `t`
  set G : Vec d × ℝ → ℝ := fun p => ψ p.1 * h (p.2, p.1) with hG
  have hGm : StronglyMeasurable G :=
    (hψc.measurable.comp measurable_fst).stronglyMeasurable.mul
      (hhm.comp_measurable (measurable_snd.prodMk measurable_fst))
  have hGint : Integrable G (volume.prod (volume.restrict (Icc ε₁ ε₂))) := by
    refine (integrable_prod_iff hGm.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · refine (integrable_const (|ψ x| * (W * B))).mono'
        (hGm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [hG, Real.norm_eq_abs, abs_mul]
      by_cases hx : ψ x = 0
      · simp [hx]
      exact mul_le_mul_of_nonneg_left (hhb t ht x (hρ x hx)) (abs_nonneg _)
    · refine ((hψc.abs.integrable_of_hasCompactSupport hψ.2.abs).const_mul
        ((volume.restrict (Icc ε₁ ε₂)).real univ * (W * B))).mono'
        (hGm.norm.integral_prod_right').aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      by_cases hx : ψ x = 0
      · simp [hG, hx]
      calc ∫ t in Icc ε₁ ε₂, ‖G (x, t)‖ ≤ ∫ t in Icc ε₁ ε₂, |ψ x| * (W * B) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
              (integrable_const _) ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            simp only [hG, Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left (hhb t ht x (hρ x hx)) (abs_nonneg _)
        _ = _ := by rw [integral_const, smul_eq_mul]; ring
  have hswap1 := integral_integral_swap (f := fun x t => ψ x * h (t, x)) hGint
  -- second swap: `t` and `y`
  set m : Vec d → ℝ := fun y => ∫ x, euclideanHeatKernel (2 * ε₂) (y - x) * |ψ x| with hm
  have hmint : Integrable fun y => |f y| * m y := by
    set E : Vec d × Vec d → ℝ := fun p => |f p.1| * (euclideanHeatKernel (2 * ε₂) (p.1 - p.2) *
      |ψ p.2|) with hE
    have hEm : Measurable E := (hfm.comp measurable_fst).abs.mul
      (((measurable_euclideanHeatKernel_joint (d := d)).comp (measurable_const.prodMk
        (measurable_fst.sub measurable_snd))).mul (hψc.measurable.comp measurable_snd).abs)
    have hEint : Integrable E (volume.prod volume) := by
      refine (integrable_prod_iff' hEm.aestronglyMeasurable).mpr
        ⟨Eventually.of_forall fun x => ?_, ?_⟩
      · obtain ⟨B', hB'⟩ := hmom (2 * ε₂) hε₂ (euclideanNorm x)
        refine ((hB' x le_rfl).1.mul_const |ψ x|).congr (Eventually.of_forall fun y => ?_)
        simp only [hE]
        rw [show x - y = -(y - x) by abel, euclideanHeatKernel_neg]
        ring
      · refine ((hψc.abs.integrable_of_hasCompactSupport hψ.2.abs).const_mul B).mono'
          (hEm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
          (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
        by_cases hx : ψ x = 0
        · simp [hE, hx]
        calc ∫ y, ‖E (y, x)‖ = |ψ x| * ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y| := by
              rw [← integral_const_mul]
              congr 1
              funext y
              simp only [hE, Real.norm_eq_abs]
              rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg
                (euclideanHeatKernel_nonneg hε₂.le _) (abs_nonneg _))),
                show y - x = -(x - y) by abel, euclideanHeatKernel_neg]
              ring
          _ ≤ |ψ x| * B := mul_le_mul_of_nonneg_left (hB x (hρ x hx)).2 (abs_nonneg _)
          _ = B * |ψ x| := by ring
    refine hEint.integral_prod_left.congr (Eventually.of_forall fun y => ?_)
    simp only [hE, hm]
    rw [integral_const_mul]
  have hkb : ∀ t ∈ Icc ε₁ ε₂, ∀ y, |k (t, y)| ≤ W * m y := by
    intro t ht y
    have hint : Integrable fun x => euclideanHeatKernel (2 * ε₂) (y - x) * |ψ x| :=
      (integrable_mul_of_hasCompactSupport_right
        ((continuous_euclideanHeatKernel (2 * ε₂)).comp (continuous_const.sub continuous_id))
        hψc.abs hψ.2.abs)
    calc |k (t, y)| ≤ ∫ x, |heatHessianKernel t i j (y - x) * ψ x| := abs_integral_le_integral_abs
      _ ≤ ∫ x, W * (euclideanHeatKernel (2 * ε₂) (y - x) * |ψ x|) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (hint.const_mul W) (Eventually.of_forall fun x => ?_)
          simp only
          rw [abs_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (abs_heatHessianKernel_le_window hε₁ ht i j _)
            (abs_nonneg _)
      _ = W * m y := integral_const_mul _ _
  set Hf : ℝ × Vec d → ℝ := fun p => f p.2 * k p with hHf
  have hHm : StronglyMeasurable Hf := (hfm.comp measurable_snd).stronglyMeasurable.mul hkm
  have hHint : Integrable Hf ((volume.restrict (Icc ε₁ ε₂)).prod volume) := by
    refine (integrable_prod_iff' hHm.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · refine (integrable_const (|f y| * (W * m y))).mono'
        (hHm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [hHf, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hkb t ht y) (abs_nonneg _)
    · refine (hmint.const_mul ((volume.restrict (Icc ε₁ ε₂)).real univ * W)).mono'
        (hHm.norm.integral_prod_left').aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      calc ∫ t in Icc ε₁ ε₂, ‖Hf (t, y)‖ ≤ ∫ t in Icc ε₁ ε₂, |f y| * (W * m y) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
              (integrable_const _) ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            simp only [hHf, Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left (hkb t ht y) (abs_nonneg _)
        _ = _ := by rw [integral_const, smul_eq_mul]; ring
  have hswap2 := integral_integral_swap (f := fun t y => f y * k (t, y)) hHint
  -- assembly
  have hL : ∫ x, ψ x * heatHessianWindow ε₁ ε₂ i j f x =
      ∫ x, ∫ t in Icc ε₁ ε₂, ψ x * h (t, x) := by
    congr 1
    funext x
    rw [hwin f x, ← integral_const_mul]
  have hR : ∫ y, f y * heatHessianWindow ε₁ ε₂ i j ψ y =
      ∫ y, ∫ t in Icc ε₁ ε₂, f y * k (t, y) := by
    congr 1
    funext y
    rw [hwin ψ y, ← integral_const_mul]
  have hmid : ∫ t in Icc ε₁ ε₂, ∫ x, ψ x * h (t, x) = ∫ t in Icc ε₁ ε₂, ∫ y, f y * k (t, y) := by
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
    have h1 := integral_mul_heatHessianConv_comm hfm hmom hψ ht0 i j
    simp only [heatHessianConv_eq_kernel ht0] at h1
    exact h1
  rw [hL, hR, hswap1, hmid, hswap2]

end QSH
