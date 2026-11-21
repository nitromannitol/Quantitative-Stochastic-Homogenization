import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianDuality
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatAverageDecay

/-!
# Small-time and large-time limits of tested heat smoothings

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1: for a field `f` with Gaussian moments and a smooth compactly supported test `ψ`,
`∫ f (Φ_t * ψ) → ∫ f ψ` as `t → 0`; and if `f - c` has a pairing bound at large scales then
`∫ f (Φ_t * ψ) → c ∫ ψ` as `t → ∞`. These are the two endpoints of the heat formula (6.7).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem euclideanSq_nonneg'' (v : Vec d) : 0 ≤ euclideanSq v := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun l _ => mul_self_nonneg _

/-- At small times the heat kernel is dominated by `Φ_2` away from the origin. -/
theorem euclideanHeatKernel_le_mul_two_of_le {t δ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ)
    {z : Vec d} (hz : δ ≤ euclideanNorm z) :
    euclideanHeatKernel t z ≤
      ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (d.factorial : ℝ) * (8 / δ ^ 2) ^ d *
        (8 * Real.pi) ^ ((d : ℝ) / 2)) * euclideanHeatKernel 2 z := by
  set S := euclideanSq z with hS
  have hS0 : 0 ≤ S := euclideanSq_nonneg'' z
  have hSδ : δ ^ 2 ≤ S := by
    have h := pow_le_pow_left₀ hδ.le hz 2
    rwa [euclideanNorm, Real.sq_sqrt hS0] at h
  set a : ℝ := δ ^ 2 / 8 with ha
  have ha0 : 0 < a := by positivity
  -- the exponential splits
  have hexp : Real.exp (-S / (4 * t)) ≤ Real.exp (-a / t) * Real.exp (-S / 8) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : a / t ≤ S / (8 * t) := by
      rw [ha, div_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : S / 8 ≤ S / (8 * t) := by
      exact div_le_div_of_nonneg_left hS0 (by positivity) (by nlinarith)
    have h3 : S / (4 * t) = S / (8 * t) + S / (8 * t) := by
      field_simp
      ring
    rw [neg_div, neg_div, neg_div]
    linarith
  -- the power of `t`
  have hpow : t ^ (-(d : ℝ) / 2) * Real.exp (-a / t) ≤ (d.factorial : ℝ) / a ^ d := by
    have hu : 0 ≤ a / t := by positivity
    have hfac := Real.pow_div_factorial_le_exp (a / t) hu d
    have h1 : t ^ (-(d : ℝ) / 2) ≤ (t⁻¹) ^ d := by
      rw [← Real.rpow_natCast, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
    have h2 : (t⁻¹) ^ d * Real.exp (-a / t) ≤ (d.factorial : ℝ) / a ^ d := by
      have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
      rw [div_pow, div_le_iff₀ (by positivity)] at hfac
      rw [le_div_iff₀ (by positivity), neg_div, Real.exp_neg]
      have hE : 0 < Real.exp (a / t) := Real.exp_pos _
      calc (t⁻¹) ^ d * (Real.exp (a / t))⁻¹ * a ^ d
          = (a ^ d / t ^ d) * (Real.exp (a / t))⁻¹ := by
            rw [inv_pow]; field_simp
        _ ≤ (d.factorial * Real.exp (a / t)) * (Real.exp (a / t))⁻¹ := by
            gcongr
            linarith [hfac]
        _ = d.factorial := by field_simp
    calc t ^ (-(d : ℝ) / 2) * Real.exp (-a / t) ≤ (t⁻¹) ^ d * Real.exp (-a / t) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := h2
  have hk2 : euclideanHeatKernel 2 z = (8 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-S / 8) := by
    unfold euclideanHeatKernel
    rw [← hS]
    congr 2 <;> ring
  rw [hk2]
  show (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-euclideanSq z / (4 * t)) ≤ _
  rw [← hS]
  have hfour : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) :=
    Real.mul_rpow (by positivity) ht.le
  rw [hfour]
  have hcancel : (8 * Real.pi) ^ ((d : ℝ) / 2) * (8 * Real.pi) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  have hfa : (d.factorial : ℝ) / a ^ d = d.factorial * (8 / δ ^ 2) ^ d := by
    rw [ha, div_pow, div_pow]
    have h8 : (0 : ℝ) < 8 ^ d := by positivity
    have hδd : (0 : ℝ) < (δ ^ 2) ^ d := by positivity
    field_simp
  calc (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-S / (4 * t))
      ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) *
          (Real.exp (-a / t) * Real.exp (-S / 8)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * (t ^ (-(d : ℝ) / 2) * Real.exp (-a / t)) *
          Real.exp (-S / 8) := by ring
    _ ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) / a ^ d) * Real.exp (-S / 8) := by
        gcongr
    _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * (8 / δ ^ 2) ^ d) *
          ((8 * Real.pi) ^ ((d : ℝ) / 2) * (8 * Real.pi) ^ (-(d : ℝ) / 2)) *
          Real.exp (-S / 8) := by rw [hfa, hcancel, mul_one]
    _ = _ := by ring

private theorem euclideanNorm_le_card_mul_norm''' (v : Vec d) : euclideanNorm v ≤ d * ‖v‖ := by
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

/-- A smooth compactly supported function vanishes outside a Euclidean ball of positive radius. -/
theorem IsSmoothCompact.exists_support_ball {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x, ψ x ≠ 0 → euclideanNorm x ≤ ρ := by
  obtain ⟨R, hR⟩ := hψ.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨d * |R| + 1, by positivity, fun x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    have := hR (subset_tsupport _ hx)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have h := euclideanNorm_le_card_mul_norm''' x
  have : (d : ℝ) * ‖x‖ ≤ d * |R| :=
    mul_le_mul_of_nonneg_left (hxR.trans (le_abs_self R)) (Nat.cast_nonneg d)
  linarith

/-- `|f| · (Φ_s * |ψ|)` is integrable for a field with Gaussian moments and a smooth compactly
supported `ψ`. -/
theorem integrable_abs_mul_heatSmoothing {f ψ : Vec d → ℝ} (hfm : Measurable f)
    (hmom : HasGaussianMoments f) (hψ : IsSmoothCompact ψ) {s : ℝ} (hs : 0 < s) :
    Integrable fun y => |f y| * ∫ x, euclideanHeatKernel s (y - x) * |ψ x| := by
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨ρ, -, hρ⟩ := hψ.exists_support_ball
  obtain ⟨B, hB⟩ := hmom s hs ρ
  set E : Vec d × Vec d → ℝ := fun p => |f p.1| * (euclideanHeatKernel s (p.1 - p.2) *
    |ψ p.2|) with hE
  have hEm : Measurable E := (hfm.comp measurable_fst).abs.mul
    (((measurable_euclideanHeatKernel_joint (d := d)).comp (measurable_const.prodMk
      (measurable_fst.sub measurable_snd))).mul (hψc.measurable.comp measurable_snd).abs)
  have hEint : Integrable E (volume.prod volume) := by
    refine (integrable_prod_iff' hEm.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · obtain ⟨B', hB'⟩ := hmom s hs (euclideanNorm x)
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
      calc ∫ y, ‖E (y, x)‖ = |ψ x| * ∫ y, euclideanHeatKernel s (x - y) * |f y| := by
            rw [← integral_const_mul]
            congr 1
            funext y
            simp only [hE, Real.norm_eq_abs]
            rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg
              (euclideanHeatKernel_nonneg hs.le _) (abs_nonneg _))),
              show y - x = -(x - y) by abel, euclideanHeatKernel_neg]
            ring
        _ ≤ |ψ x| * B := mul_le_mul_of_nonneg_left (hB x (hρ x hx)).2 (abs_nonneg _)
        _ = B * |ψ x| := by ring
  refine hEint.integral_prod_left.congr (Eventually.of_forall fun y => ?_)
  simp only [hE]
  rw [integral_const_mul]

/-- **Small-time limit.** `∫ f (Φ_t * ψ) → ∫ f ψ` along `t = 1/(m+1)`. -/
theorem tendsto_integral_mul_heatConv_zero {f ψ : Vec d → ℝ} (hfm : Measurable f)
    (hmom : HasGaussianMoments f) (hψ : IsSmoothCompact ψ) :
    Tendsto (fun m : ℕ => ∫ y, f y * heatConv (((m + 1 : ℕ) : ℝ)⁻¹) ψ y) atTop
      (𝓝 (∫ y, f y * ψ y)) := by
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨ρ, hρ0, hρ⟩ := hψ.exists_support_ball
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψ.2
  set C : ℝ := (4 * Real.pi) ^ (-(d : ℝ) / 2) * (d.factorial : ℝ) * (8 / ρ ^ 2) ^ d *
    (8 * Real.pi) ^ ((d : ℝ) / 2) with hC
  have hC0 : 0 ≤ C := by positivity
  set m₂ : Vec d → ℝ := fun y => ∫ x, euclideanHeatKernel 2 (y - x) * |ψ x| with hm₂
  have hm₂0 : ∀ y, 0 ≤ m₂ y := fun y =>
    integral_nonneg fun x => mul_nonneg (euclideanHeatKernel_nonneg (by norm_num) _) (abs_nonneg _)
  set E : Vec d → ℝ := fun y => |f y| * (M * (ball (0 : Vec d) (2 * ρ)).indicator 1 y + C * m₂ y)
    with hE
  -- integrability of the envelope
  have hball : Integrable fun y => |f y| * (ball (0 : Vec d) (2 * ρ)).indicator 1 y := by
    obtain ⟨B₁, hB₁⟩ := hmom 1 one_pos 0
    have hint := (hB₁ 0 (by simp [euclideanNorm, euclideanSq, dot])).1
    set c₀ : ℝ := (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(2 * ρ) ^ 2 / 4) with hc₀
    have hc₀pos : 0 < c₀ := by positivity
    refine (hint.const_mul c₀⁻¹).mono' ((hfm.abs.mul (measurable_const.indicator
      (isOpen_lt (by unfold euclideanNorm euclideanSq dot; fun_prop)
        continuous_const).measurableSet))).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (indicator_nonneg (fun _ _ => zero_le_one) _))]
    by_cases hy : y ∈ ball (0 : Vec d) (2 * ρ)
    · rw [indicator_of_mem hy, Pi.one_apply, mul_one]
      have hyn : euclideanNorm y < 2 * ρ := by simpa [ball] using hy
      have hk : c₀ ≤ euclideanHeatKernel 1 (0 - y) := by
        unfold euclideanHeatKernel
        rw [hc₀, mul_one]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have hsq : euclideanSq (0 - y) = euclideanNorm y ^ 2 := by
          rw [zero_sub, euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg'' y)]
          unfold euclideanSq dot
          simp
        rw [hsq]
        have : euclideanNorm y ^ 2 ≤ (2 * ρ) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hyn.le 2
        linarith
      calc |f y| = c₀⁻¹ * (c₀ * |f y|) := by field_simp
        _ ≤ c₀⁻¹ * (euclideanHeatKernel 1 (0 - y) * |f y|) := by gcongr
    · rw [indicator_of_notMem hy, mul_zero]
      exact mul_nonneg (inv_nonneg.mpr hc₀pos.le)
        (mul_nonneg (euclideanHeatKernel_nonneg zero_le_one _) (abs_nonneg _))
  have hEint : Integrable E := by
    have h2 := integrable_abs_mul_heatSmoothing hfm hmom hψ (s := 2) (by norm_num)
    refine ((hball.const_mul M).add (h2.const_mul C)).congr (Eventually.of_forall fun y => ?_)
    simp only [hE, hm₂, Pi.add_apply]
    ring
  -- the bound
  have hbound : ∀ m : ℕ, ∀ y, |f y * heatConv (((m + 1 : ℕ) : ℝ)⁻¹) ψ y| ≤ E y := by
    intro m y
    set t : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹ with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos m)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    unfold heatConv
    by_cases hy : y ∈ ball (0 : Vec d) (2 * ρ)
    · rw [indicator_of_mem hy, Pi.one_apply, mul_one]
      calc |∫ x, euclideanHeatKernel t (y - x) * ψ x|
          ≤ ∫ x, euclideanHeatKernel t (y - x) * M := by
            refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
              (Eventually.of_forall fun x => abs_nonneg _)
              ((integrable_euclideanHeatKernel_sub ht0 y).mul_const M)
              (Eventually.of_forall fun x => ?_))
            simp only
            rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ht0.le _)]
            exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM x)
              (euclideanHeatKernel_nonneg ht0.le _)
        _ = M := by rw [integral_mul_const, integral_euclideanHeatKernel_sub ht0, one_mul]
        _ ≤ M + C * m₂ y := le_add_of_nonneg_right (mul_nonneg hC0 (hm₂0 y))
    · rw [indicator_of_notMem hy, mul_zero, zero_add]
      have hyn : 2 * ρ ≤ euclideanNorm y := by simpa [ball, not_lt] using hy
      calc |∫ x, euclideanHeatKernel t (y - x) * ψ x|
          ≤ ∫ x, C * (euclideanHeatKernel 2 (y - x) * |ψ x|) := by
            refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
              (Eventually.of_forall fun x => abs_nonneg _)
              ((integrable_mul_of_hasCompactSupport_right
                ((continuous_euclideanHeatKernel 2).comp (continuous_const.sub continuous_id))
                hψc.abs hψ.2.abs).const_mul C)
              (Eventually.of_forall fun x => ?_))
            simp only
            rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ht0.le _)]
            by_cases hx : ψ x = 0
            · simp [hx]
            have hxρ := hρ x hx
            have hyx : ρ ≤ euclideanNorm (y - x) := by
              have h := euclideanNorm_add_le (y - x) x
              rw [sub_add_cancel] at h
              linarith
            have hk := euclideanHeatKernel_le_mul_two_of_le ht0 ht1 hρ0 hyx
            calc euclideanHeatKernel t (y - x) * |ψ x| ≤ (C * euclideanHeatKernel 2 (y - x)) *
                |ψ x| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
              _ = _ := by ring
        _ = C * m₂ y := by rw [integral_const_mul]
  refine tendsto_integral_of_dominated_convergence E (fun m => ?_) hEint
    (fun m => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbound m y)
    (Eventually.of_forall fun y => ?_)
  · have hjoint : StronglyMeasurable fun p : Vec d × Vec d =>
        euclideanHeatKernel (((m + 1 : ℕ) : ℝ)⁻¹) (p.1 - p.2) * ψ p.2 :=
      (((measurable_euclideanHeatKernel_joint (d := d)).comp (measurable_const.prodMk
        (measurable_fst.sub measurable_snd))).mul
        (hψc.measurable.comp measurable_snd)).stronglyMeasurable
    exact (hfm.aestronglyMeasurable.mul hjoint.integral_prod_right'.aestronglyMeasurable)
  · have hcont := continuousOn_heatKernelConvolution hψc hψ.2 y
    have h0 : heatKernelConvolution 0 ψ y = ψ y := by simp [heatKernelConvolution]
    have hlim : Tendsto (fun t => heatKernelConvolution t ψ y) (𝓝[Ici 0] 0) (𝓝 (ψ y)) := by
      rw [← h0]
      exact hcont 0 self_mem_Ici
    have hseq : Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => ?_⟩
      · have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [one_div, Nat.cast_add, Nat.cast_one] using this
      · exact Set.mem_Ici.mpr (by positivity)
    refine ((hlim.comp hseq).const_mul (f y)).congr fun m => ?_
    simp only [Function.comp]
    rw [heatConv_eq_heatKernelConvolution (by positivity)]

end QSH
