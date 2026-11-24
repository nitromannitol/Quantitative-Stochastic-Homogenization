import QuantitativeStochasticHomogenization.AppD.HeatGradientKernel
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianCauchy

/-!
# Appendix D: the derivatives of order `k` of the heat flow of an `L²` function

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Lemma D.3 for `α = 0`: for `g ∈ L²(ℝ^d)` and `k = m + 1 ≥ 1`,
`∫_0^∞ t^m ‖∇^k Φ(t, ·) ∗ g‖²_{L²} dt ≤ C ‖g‖²_{L²}` (`lintegral_heatGradSq_le`).

The estimate for smooth compactly supported functions (`lintegral_heatGradSq_le_of_smooth`) is
extended by density: for `ψₙ → g` in `L²`, `(∂^l Φ(t, ·) ∗ ψₙ)(x) → (∂^l Φ(t, ·) ∗ g)(x)` at every
`t > 0` and `x` by the Cauchy–Schwarz inequality (`tendsto_kconv_heatKernelDeriv`), and Fatou's lemma
in `x` and then in `t` gives the estimate for `g`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace QSH

variable {d : ℕ}

theorem memLp_heatKernelDeriv {t : ℝ} (ht : 0 < t) (l : List (Fin d)) :
    MemLp (heatKernelDeriv t l) 2 volume := by
  obtain ⟨CA, -, hCA⟩ := abs_foldr_euclideanHeatKernel_le (d := d) ht l
  have hm := (continuous_heatKernelDeriv t l).aestronglyMeasurable (μ := volume)
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine ((integrable_heatKernelDeriv ht l).abs.const_mul CA).mono' (hm.pow 2)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq]
  exact mul_le_mul_of_nonneg_right (hCA z) (abs_nonneg _)

/-- For a test function, the convolution with a derivative of the heat kernel is the heat flow of
the derivative of the test function. -/
theorem kconv_heatKernelDeriv_eq_heatSmooth {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (t : ℝ) (l : List (Fin d)) :
    kconv (heatKernelDeriv t l) ψ = heatSmooth t (l.reverse.foldr coordinateDerivative ψ) := by
  have h := convolution_foldr_coordinateDerivative hψ hcψ l.reverse (contDiff_euclideanHeatKernel t)
  rw [List.reverse_reverse] at h
  exact h.symm

/-- **The Cauchy–Schwarz inequality for the heat kernel derivatives**:
`|(∂^l Φ(t, ·) ∗ h)(x)|² ≤ M ‖h‖²_{L²}`. -/
theorem enorm_sq_kconv_heatKernelDeriv_le {t : ℝ} (ht : 0 < t) (l : List (Fin d)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : Vec d → ℝ, AEStronglyMeasurable h volume → ∀ x,
      ‖kconv (heatKernelDeriv t l) h x‖ₑ ^ 2 ≤ ENNReal.ofReal M * ∫⁻ y, ‖h y‖ₑ ^ 2 := by
  obtain ⟨CA, hCA0, hCA⟩ := abs_foldr_euclideanHeatKernel_le (d := d) ht l
  set L := ∫ z, ‖heatKernelDeriv t l z‖ with hL
  have hL0 : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  refine ⟨L * CA, mul_nonneg hL0 hCA0, fun h hh x => ?_⟩
  have hK := continuous_heatKernelDeriv t l
  have hKx : AEMeasurable (fun y => ‖heatKernelDeriv t l (x - y)‖ₑ) volume :=
    (hK.comp (continuous_const.sub continuous_id)).measurable.enorm.aemeasurable
  have hCS := sq_lintegral_mul_le hKx hh.enorm
  have hmass : ∫⁻ y, ‖heatKernelDeriv t l (x - y)‖ₑ = ENNReal.ofReal L := by
    rw [lintegral_sub_left_eq_self (fun z => ‖heatKernelDeriv t l z‖ₑ) x, hL,
      ofReal_integral_norm_eq_lintegral_enorm (integrable_heatKernelDeriv ht l)]
  calc ‖kconv (heatKernelDeriv t l) h x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖heatKernelDeriv t l (x - y)‖ₑ * ‖h y‖ₑ) ^ 2 := by
        gcongr
        rw [kconv_apply]
        refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        simp_rw [enorm_mul]
    _ ≤ (∫⁻ y, ‖heatKernelDeriv t l (x - y)‖ₑ) *
          ∫⁻ y, ‖heatKernelDeriv t l (x - y)‖ₑ * ‖h y‖ₑ ^ 2 := hCS
    _ ≤ ENNReal.ofReal L * ∫⁻ y, ENNReal.ofReal CA * ‖h y‖ₑ ^ 2 := by
        rw [hmass]
        gcongr with y
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hCA _)
    _ = ENNReal.ofReal (L * CA) * ∫⁻ y, ‖h y‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ENNReal.ofReal_mul hL0]

/-- `L²` convergence implies the pointwise convergence of the convolutions with the derivatives of
the heat kernel. -/
theorem tendsto_kconv_heatKernelDeriv {t : ℝ} (ht : 0 < t) (l : List (Fin d)) {g : Vec d → ℝ}
    (hg : MemLp g 2 volume) {ψ : ℕ → Vec d → ℝ} (hψ : ∀ n, MemLp (ψ n) 2 volume)
    (hψg : ∀ n : ℕ, eLpNorm (g - ψ n) 2 volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    (x : Vec d) :
    Tendsto (fun n => kconv (heatKernelDeriv t l) (ψ n) x) atTop
      (𝓝 (kconv (heatKernelDeriv t l) g x)) := by
  obtain ⟨M, hM0, hM⟩ := enorm_sq_kconv_heatKernelDeriv_le ht l
  have hK2 := memLp_heatKernelDeriv ht l
  have hsub : ∀ n, kconv (heatKernelDeriv t l) (ψ n) x - kconv (heatKernelDeriv t l) g x =
      kconv (heatKernelDeriv t l) (ψ n - g) x := fun n => by
    simp only [kconv_apply, Pi.sub_apply, mul_sub]
    rw [integral_sub (integrable_kernel_mul hK2 (hψ n) x) (integrable_kernel_mul hK2 hg x)]
  have hbound : ∀ n : ℕ, |kconv (heatKernelDeriv t l) (ψ n) x - kconv (heatKernelDeriv t l) g x| ≤
      Real.sqrt M * (1 / ((n : ℝ) + 1)) := by
    intro n
    rw [hsub n]
    have hmeas : AEStronglyMeasurable (ψ n - g) volume :=
      (hψ n).aestronglyMeasurable.sub hg.aestronglyMeasurable
    have h1 := hM (ψ n - g) hmeas x
    have h2 : ∫⁻ y, ‖(ψ n - g) y‖ₑ ^ 2 ≤ ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ 2) := by
      have hle : eLpNorm (ψ n - g) 2 volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        rw [eLpNorm_sub_comm]
        exact hψg n
      rw [eLpNorm_two_eq hmeas] at hle
      calc ∫⁻ y, ‖(ψ n - g) y‖ₑ ^ 2 = ((∫⁻ y, ‖(ψ n - g) y‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
            (rpow_half_sq _).symm
        _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 := by gcongr
        _ = _ := by rw [ENNReal.ofReal_pow (by positivity)]
    have h3 : ENNReal.ofReal (kconv (heatKernelDeriv t l) (ψ n - g) x ^ 2) ≤
        ENNReal.ofReal (M * (1 / ((n : ℝ) + 1)) ^ 2) := by
      rw [ofReal_sq_eq_enorm_sq, ENNReal.ofReal_mul hM0]
      exact h1.trans (by gcongr)
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
    calc Real.sqrt (kconv (heatKernelDeriv t l) (ψ n - g) x ^ 2)
        ≤ Real.sqrt (M * (1 / ((n : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt h4
      _ = Real.sqrt M * (1 / ((n : ℝ) + 1)) := by
          rw [Real.sqrt_mul hM0, Real.sqrt_sq (by positivity)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (Real.norm_eq_abs _).trans_le (hbound n)) ?_
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.sqrt M)
  rwa [mul_zero] at h

theorem lintegral_ofReal_sq_eq_eLpNorm_sq {g : Vec d → ℝ} (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ENNReal.ofReal (g x ^ 2) = eLpNorm g 2 volume ^ 2 := by
  simp_rw [ofReal_sq_eq_enorm_sq]
  rw [eLpNorm_two_eq hg, rpow_half_sq]

/-- **Lemma D.3 for `α = 0`**: for `g ∈ L²(ℝ^d)` and `k = m + 1 ≥ 1`,
`∫_0^∞ t^m ‖∇^k Φ(t, ·) ∗ g‖²_{L²} dt ≤ C ‖g‖²_{L²}`. -/
theorem lintegral_heatGradSq_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Vec d → ℝ, MemLp g 2 volume →
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ m) * ∫⁻ x, ENNReal.ofReal (heatGradSq (m + 1) t g x) ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := lintegral_heatGradSq_le_of_smooth (d := d) m
  refine ⟨C, hC0, fun g hg => ?_⟩
  have hex : ∀ n : ℕ, ∃ ψ : Vec d → ℝ, IsSmoothCompact ψ ∧
      eLpNorm (g - ψ) 2 volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    fun n => exists_smoothCompact_eLpNorm_sub_le hg (by positivity)
  choose ψ hψs hψg using hex
  set F : ℕ → ℝ → Vec d → ℝ≥0∞ := fun n t x =>
    ENNReal.ofReal (t ^ m) * ENNReal.ofReal (heatGradSq (m + 1) t (ψ n) x) with hF
  have hlim : ∀ t ∈ Ioi (0 : ℝ), ∀ x, Tendsto (fun n => F n t x) atTop
      (𝓝 (ENNReal.ofReal (t ^ m) * ENNReal.ofReal (heatGradSq (m + 1) t g x))) := by
    intro t ht x
    refine ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ?_) (Or.inr ENNReal.ofReal_ne_top)
    unfold heatGradSq
    exact tendsto_finset_sum _ fun w _ =>
      (tendsto_kconv_heatKernelDeriv ht _ hg (fun n => (hψs n).memLp) hψg x).pow 2
  have hFmeas : ∀ n, Measurable (Function.uncurry (F n)) := fun n => by
    have hw : ∀ w : Fin (m + 1) → Fin d, Measurable (fun p : ℝ × Vec d =>
        kconv (heatKernelDeriv p.1 (List.ofFn w)) (ψ n) p.2) := fun w => by
      set χ := (List.ofFn w).reverse.foldr coordinateDerivative (ψ n) with hχdef
      have hχ : ContDiff ℝ ∞ χ :=
        (foldr_coordinateDerivative_smooth (hψs n).1 (hψs n).2 (List.ofFn w).reverse).1
      have heq : (fun p : ℝ × Vec d => kconv (heatKernelDeriv p.1 (List.ofFn w)) (ψ n) p.2) =
          (fun p : Vec d × ℝ => heatSmooth p.2 χ p.1) ∘ Prod.swap := by
        funext p
        rw [kconv_heatKernelDeriv_eq_heatSmooth (hψs n).1 (hψs n).2]
        rfl
      have h : Measurable ((fun p : Vec d × ℝ => heatSmooth p.2 χ p.1) ∘ Prod.swap) :=
        (stronglyMeasurable_heatSmooth_uncurry hχ.continuous.measurable).measurable.comp
          measurable_swap
      rw [heq]
      exact h
    refine ((measurable_fst.pow_const m).ennreal_ofReal).mul (Measurable.ennreal_ofReal ?_)
    exact Finset.measurable_sum _ fun w _ => (hw w).pow_const 2
  have hnorm : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (ψ n x ^ 2) ≤
      (eLpNorm g 2 volume + ENNReal.ofReal (1 / ((n : ℝ) + 1))) ^ 2 := by
    intro n
    have h1 : eLpNorm (ψ n) 2 volume ≤ eLpNorm g 2 volume + ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      calc eLpNorm (ψ n) 2 volume = eLpNorm (g - (g - ψ n)) 2 volume := by rw [sub_sub_cancel]
        _ ≤ eLpNorm g 2 volume + eLpNorm (g - ψ n) 2 volume := eLpNorm_sub_le (by norm_num)
        _ ≤ _ := by gcongr; exact hψg n
    rw [lintegral_ofReal_sq_eq_eLpNorm_sq (hψs n).1.continuous.aestronglyMeasurable]
    gcongr
  have hlimR : Tendsto (fun n : ℕ => ENNReal.ofReal C *
      (eLpNorm g 2 volume + ENNReal.ofReal (1 / ((n : ℝ) + 1))) ^ 2) atTop
      (𝓝 (ENNReal.ofReal C * eLpNorm g 2 volume ^ 2)) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat)
      rwa [ENNReal.ofReal_zero] at h
    have h2 := (tendsto_const_nhds (x := eLpNorm g 2 volume)).add h1
    rw [add_zero] at h2
    exact ENNReal.Tendsto.const_mul (((ENNReal.continuous_pow 2).tendsto _).comp h2)
      (Or.inr ENNReal.ofReal_ne_top)
  calc ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ m) * ∫⁻ x, ENNReal.ofReal (heatGradSq (m + 1) t g x)
      = ∫⁻ t in Ioi 0, ∫⁻ x, liminf (fun n => F n t x) atTop := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun x => ((hlim t ht x).liminf_eq).symm
    _ ≤ ∫⁻ t in Ioi 0, liminf (fun n => ∫⁻ x, F n t x) atTop :=
        setLIntegral_mono' measurableSet_Ioi fun t _ =>
          lintegral_liminf_le fun n => (hFmeas n).of_uncurry_left
    _ ≤ liminf (fun n => ∫⁻ t in Ioi 0, ∫⁻ x, F n t x) atTop :=
        lintegral_liminf_le fun n => (hFmeas n).lintegral_prod_right'
    _ ≤ liminf (fun n : ℕ => ENNReal.ofReal C *
          (eLpNorm g 2 volume + ENNReal.ofReal (1 / ((n : ℝ) + 1))) ^ 2) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        calc ∫⁻ t in Ioi 0, ∫⁻ x, F n t x
            = ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ m) *
                ∫⁻ x, ENNReal.ofReal (heatGradSq (m + 1) t (ψ n) x) := by
              refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (ψ n x ^ 2) := hC (ψ n) (hψs n).1 (hψs n).2
          _ ≤ _ := by gcongr; exact hnorm n
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x ^ 2) := by
        rw [hlimR.liminf_eq, lintegral_ofReal_sq_eq_eLpNorm_sq hg.aestronglyMeasurable]

end QSH
