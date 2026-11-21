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

end QSH
