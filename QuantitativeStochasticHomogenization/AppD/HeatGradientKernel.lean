import QuantitativeStochasticHomogenization.AppD.HeatEnergyIdentity
import QuantitativeStochasticHomogenization.AppD.HeatSemigroupDerivatives
import QuantitativeStochasticHomogenization.AppD.LaplacianExpansion
import QuantitativeStochasticHomogenization.AppD.DerivativeCommutation

/-!
# Appendix D: the derivatives of order `k` of the heat flow of a test function

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, first paragraph of the proof of Lemma D.3: by the semigroup property and Young's
inequality,
`‖∇^k Φ(t, ·) ∗ ψ‖_{L²} = ‖∇^{k-1} Φ(t/2, ·) ∗ ∇ Φ(t/2, ·) ∗ ψ‖_{L²}
  ≤ C t^{-(k-1)/2} ‖∇ Φ(t/2, ·) ∗ ψ‖_{L²}`,
so that, with (D.6), `∫_0^∞ t^{k-1} ‖∇^k Φ(t, ·) ∗ ψ‖²_{L²} dt ≤ C ‖ψ‖²_{L²}` for a smooth compactly
supported `ψ` and `k ≥ 1` (`lintegral_heatGradSq_le_of_smooth`).

Here `heatKernelDeriv t l = ∂_{l₁} ⋯ ∂_{l_m} Φ(t, ·)` and `heatGradSq k t u x` is the squared
Euclidean norm `∑_{w} |(∂_{w₁} ⋯ ∂_{w_k} Φ(t, ·) ∗ u)(x)|²` of the tensor `(∇^k Φ(t, ·) ∗ u)(x)`.
-/

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The derivative `∂_{l₁} ⋯ ∂_{l_m} Φ(t, ·)` of the heat kernel along a list of coordinates. -/
def heatKernelDeriv (t : ℝ) (l : List (Fin d)) : Vec d → ℝ :=
  l.foldr coordinateDerivative (euclideanHeatKernel t)

/-- The squared Euclidean norm `|∇^k Φ(t, ·) ∗ u|²(x) = ∑_{w} |(∂_{w₁} ⋯ ∂_{w_k} Φ(t, ·) ∗ u)(x)|²`
of the tensor of the `k`-th derivatives of the heat kernel convolved with `u`. -/
def heatGradSq (k : ℕ) (t : ℝ) (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ w : Fin k → Fin d, kconv (heatKernelDeriv t (List.ofFn w)) u x ^ 2

theorem heatGradSq_nonneg (k : ℕ) (t : ℝ) (u : Vec d → ℝ) (x : Vec d) :
    0 ≤ heatGradSq k t u x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem ofReal_sq_eq_enorm_sq (a : ℝ) : ENNReal.ofReal (a ^ 2) = ‖a‖ₑ ^ 2 := by
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]

theorem ofReal_heatGradSq (k : ℕ) (t : ℝ) (u : Vec d → ℝ) (x : Vec d) :
    ENNReal.ofReal (heatGradSq k t u x) =
      ∑ w : Fin k → Fin d, ‖kconv (heatKernelDeriv t (List.ofFn w)) u x‖ₑ ^ 2 := by
  rw [heatGradSq, ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  simp_rw [ofReal_sq_eq_enorm_sq]

theorem contDiff_heatKernelDeriv (t : ℝ) (l : List (Fin d)) :
    ContDiff ℝ ∞ (heatKernelDeriv t l) :=
  foldr_coordinateDerivative_contDiff (contDiff_euclideanHeatKernel t) l

theorem continuous_heatKernelDeriv (t : ℝ) (l : List (Fin d)) :
    Continuous (heatKernelDeriv t l) :=
  (contDiff_heatKernelDeriv t l).continuous

theorem heatKernelDeriv_ofFn_eq {m : ℕ} (t : ℝ) (w : Fin m → Fin d) :
    heatKernelDeriv t (List.ofFn w) =
      multiIndexDerivative (countIndex w) (euclideanHeatKernel (d := d) t) :=
  foldr_coordinateDerivative_eq_multiIndexDerivative (contDiff_euclideanHeatKernel t)
    (countIndex w) (fun i => by simp [countIndex])

theorem integrable_heatKernelDeriv {t : ℝ} (ht : 0 < t) (l : List (Fin d)) :
    Integrable (heatKernelDeriv t l) := by
  rw [← List.ofFn_get l, heatKernelDeriv_ofFn_eq]
  exact integrable_multiIndexDerivative_euclideanHeatKernel ht _

/-- `‖∂_{w₁} ⋯ ∂_{w_m} Φ(t, ·)‖_{L¹} = C_w t^{-m/2}`. -/
theorem lintegral_enorm_heatKernelDeriv {m : ℕ} {t : ℝ} (ht : 0 < t) (w : Fin m → Fin d) :
    ∫⁻ z, ‖heatKernelDeriv t (List.ofFn w) z‖ₑ =
      ENNReal.ofReal ((∏ i, heatDerivConst (countIndex w i).val) * t ^ (-(m : ℝ) / 2)) := by
  rw [heatKernelDeriv_ofFn_eq, ← ofReal_integral_norm_eq_lintegral_enorm
    (integrable_multiIndexDerivative_euclideanHeatKernel ht _)]
  simp_rw [Real.norm_eq_abs]
  rw [integral_abs_multiIndexDerivative_euclideanHeatKernel_eq ht, sum_countIndex]

theorem continuous_kconv_of_hasCompactSupport {K ψ : Vec d → ℝ} (hK : Continuous K)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) : Continuous (kconv K ψ) :=
  hcψ.continuous_convolution_right _ hK.locallyIntegrable hψ

theorem lintegral_enorm_sq_eq_ofReal_integral {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (f x))]
  simp_rw [ofReal_sq_eq_enorm_sq]

/-- The change of variables `t = 2 s` on `(0, ∞)`. -/
theorem lintegral_Ioi_comp_half (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi 0, f (t / 2) = 2 * ∫⁻ s in Ioi 0, f s := by
  set g : ℝ → ℝ≥0∞ := (Ioi (0 : ℝ)).indicator f with hg
  have h1 : ∫⁻ t in Ioi 0, f (t / 2) = ∫⁻ t, g ((1 / 2) * t) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext t
    simp only [hg, indicator, mem_Ioi]
    by_cases ht : 0 < t
    · have h2 : 0 < 1 / 2 * t := by positivity
      simp only [ht, h2, ↓reduceIte]
      rw [div_eq_inv_mul, one_div]
    · have h2 : ¬ 0 < 1 / 2 * t := fun h => ht (by linarith)
      simp only [ht, h2, ↓reduceIte]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ (1 / 2 : ℝ) (by norm_num)).toMeasurableEquiv
  have he : ∀ t, e t = (1 / 2) * t := fun t => rfl
  have h2 : ∫⁻ t, g ((1 / 2) * t) = ∫⁻ s, g s ∂(Measure.map e volume) := by
    rw [lintegral_map_equiv]
    simp only [he]
  have hmap : Measure.map e volume = ENNReal.ofReal |(1 / 2 : ℝ)⁻¹| • volume := by
    rw [show (e : ℝ → ℝ) = fun t => (1 / 2) * t from funext he]
    exact Real.map_volume_mul_left (by norm_num)
  rw [h1, h2, hmap, lintegral_smul_measure, lintegral_indicator measurableSet_Ioi]
  norm_num

/-- The weights of the kernel step: `t^m (C (t/2)^{-m/2})² = 2^m C²`. -/
theorem pow_mul_sq_rpow_half {t : ℝ} (ht : 0 < t) (m : ℕ) (c : ℝ) :
    t ^ m * (c * (t / 2) ^ (-(m : ℝ) / 2)) ^ 2 = 2 ^ m * c ^ 2 := by
  have h2 : 0 < t / 2 := half_pos ht
  have hsq : ((t / 2) ^ (-(m : ℝ) / 2)) ^ 2 = ((t / 2) ^ m)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le, show -(m : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(m : ℝ)
      by push_cast; ring, Real.rpow_neg h2.le, Real.rpow_natCast]
  rw [mul_pow, hsq, div_pow]
  field_simp

/-- Splitting a word of length `m + 1` into its first letter and the rest. -/
theorem sum_fun_succ {m : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (m + 1) → Fin d) → M) :
    ∑ w, f w = ∑ j, ∑ w : Fin m → Fin d, f (Fin.cons j w) := by
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin d).sum_comp, Fintype.sum_prod_type]
  rfl

section TestFunction

variable {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)

include hψ hcψ

/-- **The semigroup property with one derivative on each factor**:
`∂_j ∂^l Φ(t) ∗ ψ = ∂^l Φ(t/2) ∗ (Φ(t/2) ∗ ∂_j ψ)`. -/
theorem kconv_heatKernelDeriv_cons {t : ℝ} (ht : 0 < t) (j : Fin d) (l : List (Fin d))
    (x : Vec d) :
    kconv (heatKernelDeriv t (j :: l)) ψ x =
      ∫ y, heatKernelDeriv (t / 2) l (x - y) * heatSmooth (t / 2) (coordinateDerivative j ψ) y := by
  have hχ : ContDiff ℝ ∞ (coordinateDerivative j ψ) := contDiff_coordinateDerivative hψ j
  have hcχ := hasCompactSupport_coordinateDerivative hcψ j
  have h1 : kconv (heatKernelDeriv t (j :: l)) ψ =
      kconv (heatKernelDeriv t l) (coordinateDerivative j ψ) := by
    have h := convolution_foldr_coordinateDerivative hψ hcψ [j] (contDiff_heatKernelDeriv t l)
    simp only [List.foldr_cons, List.foldr_nil, List.reverse_singleton] at h
    exact h.symm
  rw [h1, kconv_apply]
  have h2 : ∀ z, heatKernelDeriv t l (x - z) =
      ∫ y, heatKernelDeriv (t / 2) l (x - y) * euclideanHeatKernel (t / 2) (y - z) := fun z => by
    have h := foldr_euclideanHeatKernel_semigroup (half_pos ht) (half_pos ht) l x z
    rwa [add_halves] at h
  simp_rw [h2]
  obtain ⟨CA, -, hCA⟩ := abs_foldr_euclideanHeatKernel_le (d := d) (half_pos ht) l
  have hχi : Integrable (coordinateDerivative j ψ) :=
    hχ.continuous.integrable_of_hasCompactSupport hcχ
  have hΦi := integrable_euclideanHeatKernel (d := d) (half_pos ht)
  have hG : Integrable (fun p : Vec d × Vec d =>
      coordinateDerivative j ψ p.2 * euclideanHeatKernel (t / 2) (p.1 - p.2))
      (volume.prod volume) := by
    have h := hχi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hΦi
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
  have hF : Integrable (fun p : Vec d × Vec d => heatKernelDeriv (t / 2) l (x - p.1) *
      (coordinateDerivative j ψ p.2 * euclideanHeatKernel (t / 2) (p.1 - p.2)))
      (volume.prod volume) :=
    hG.bdd_mul ((continuous_heatKernelDeriv _ l).comp
      (continuous_const.sub continuous_fst)).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hCA _)
  have hrhs : ∀ y, heatSmooth (t / 2) (coordinateDerivative j ψ) y =
      ∫ z, coordinateDerivative j ψ z * euclideanHeatKernel (t / 2) (y - z) := fun y => by
    rw [heatSmooth_eq_kconv, kconv_apply]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  simp_rw [hrhs, ← integral_const_mul]
  rw [integral_integral_swap hF]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [← integral_mul_const]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- **Young's inequality for one derivative of the heat flow**. -/
theorem lintegral_enorm_kconv_heatKernelDeriv_cons_le {t : ℝ} (ht : 0 < t) (j : Fin d)
    (l : List (Fin d)) :
    ∫⁻ x, ‖kconv (heatKernelDeriv t (j :: l)) ψ x‖ₑ ^ 2 ≤
      (∫⁻ z, ‖heatKernelDeriv (t / 2) l z‖ₑ) ^ 2 *
        ∫⁻ x, ‖heatSmooth (t / 2) (coordinateDerivative j ψ) x‖ₑ ^ 2 := by
  have hχ : ContDiff ℝ ∞ (coordinateDerivative j ψ) := contDiff_coordinateDerivative hψ j
  have hcχ := hasCompactSupport_coordinateDerivative hcψ j
  have hmeas : Measurable (heatSmooth (t / 2) (coordinateDerivative j ψ)) :=
    (continuous_kconv_of_hasCompactSupport (continuous_euclideanHeatKernel _) hχ.continuous
      hcχ).measurable
  have hpt : ∀ x, ‖kconv (heatKernelDeriv t (j :: l)) ψ x‖ₑ ^ 2 ≤
      (∫⁻ y, ‖heatKernelDeriv (t / 2) l (x - y)‖ₑ *
        ‖heatSmooth (t / 2) (coordinateDerivative j ψ) y‖ₑ) ^ 2 := by
    intro x
    rw [kconv_heatKernelDeriv_cons hψ hcψ ht j l x]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
    simp_rw [enorm_mul]
  exact (lintegral_mono hpt).trans (lintegral_sq_kernel_le
    (continuous_heatKernelDeriv _ l).measurable.enorm hmeas.enorm)

end TestFunction

/-- **The `k`-th derivatives of the heat flow of a test function**, `k = m + 1 ≥ 1`:
`∫_0^∞ t^m ‖∇^{m+1} Φ(t, ·) ∗ ψ‖²_{L²} dt ≤ C ‖ψ‖²_{L²}`. -/
theorem lintegral_heatGradSq_le_of_smooth (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : Vec d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ m) * ∫⁻ x, ENNReal.ofReal (heatGradSq (m + 1) t ψ x) ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (ψ x ^ 2) := by
  set c : (Fin m → Fin d) → ℝ := fun w => ∏ i, heatDerivConst (countIndex w i).val with hc
  set C : ℝ := 2 ^ m * ∑ w, c w ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun ψ hψ hcψ => ?_⟩
  have hs : IsSmoothCompact ψ := ⟨hψ, hcψ⟩
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ m) * ∫⁻ x, ENNReal.ofReal (heatGradSq (m + 1) t ψ x) ≤
        ENNReal.ofReal C * ENNReal.ofReal (heatEnergy (t / 2) ψ) := by
    intro t ht
    have ht : 0 < t := ht
    have hmeas : ∀ w : Fin (m + 1) → Fin d,
        Measurable fun x => ‖kconv (heatKernelDeriv t (List.ofFn w)) ψ x‖ₑ ^ 2 := fun w =>
      ((continuous_kconv_of_hasCompactSupport (continuous_heatKernelDeriv t _) hψ.continuous
        hcψ).measurable.enorm).pow_const 2
    simp_rw [ofReal_heatGradSq]
    rw [lintegral_finsetSum _ fun w _ => hmeas w, sum_fun_succ]
    simp only [List.ofFn_cons]
    have hI : ∀ j, MemLp (heatSmooth (t / 2) (coordinateDerivative j ψ)) 2 volume := fun j =>
      memLp_kconv (measurable_euclideanHeatKernel _)
        (lintegral_enorm_euclideanHeatKernel_ne_top (half_pos ht)) (hs.coordinateDerivative j)
    have hE : ENNReal.ofReal (heatEnergy (t / 2) ψ) =
        ∑ j, ∫⁻ x, ‖heatSmooth (t / 2) (coordinateDerivative j ψ) x‖ₑ ^ 2 := by
      rw [heatEnergy, ENNReal.ofReal_sum_of_nonneg fun j _ => integral_nonneg fun x =>
        sq_nonneg _]
      exact Finset.sum_congr rfl fun j _ => (lintegral_enorm_sq_eq_ofReal_integral (hI j)).symm
    rw [hE, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    set I := ∫⁻ x, ‖heatSmooth (t / 2) (coordinateDerivative j ψ) x‖ₑ ^ 2 with hIdef
    have hCj : ENNReal.ofReal C * I =
        ∑ w : Fin m → Fin d, ENNReal.ofReal (2 ^ m * c w ^ 2) * I := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity), hC,
        Finset.mul_sum]
    rw [hCj, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have hY := lintegral_enorm_kconv_heatKernelDeriv_cons_le hψ hcψ ht j (List.ofFn w)
    rw [lintegral_enorm_heatKernelDeriv (half_pos ht)] at hY
    have hcw : 0 ≤ c w * (t / 2) ^ (-(m : ℝ) / 2) :=
      mul_nonneg (Finset.prod_nonneg fun i _ => heatDerivConst_nonneg _)
        (Real.rpow_nonneg (half_pos ht).le _)
    calc ENNReal.ofReal (t ^ m) * ∫⁻ x, ‖kconv (heatKernelDeriv t (j :: List.ofFn w)) ψ x‖ₑ ^ 2
        ≤ ENNReal.ofReal (t ^ m) * (ENNReal.ofReal (c w * (t / 2) ^ (-(m : ℝ) / 2)) ^ 2 * I) := by
          gcongr
      _ = ENNReal.ofReal (2 ^ m * c w ^ 2) * I := by
          rw [← mul_assoc, ← ENNReal.ofReal_pow hcw, ← ENNReal.ofReal_mul (by positivity),
            pow_mul_sq_rpow_half ht]
  calc ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ m) * ∫⁻ x, ENNReal.ofReal (heatGradSq (m + 1) t ψ x)
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal C * ENNReal.ofReal (heatEnergy (t / 2) ψ) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal C * (2 * ∫⁻ s in Ioi 0, ENNReal.ofReal (heatEnergy s ψ)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_Ioi_comp_half (fun s => ENNReal.ofReal (heatEnergy s ψ))]
    _ ≤ ENNReal.ofReal C * (2 * ENNReal.ofReal ((∫ x, ψ x ^ 2) / 2)) := by
        gcongr
        exact lintegral_heatEnergy_le hψ hcψ
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (ψ x ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hs.memLp.integrable_sq
          (Eventually.of_forall fun x => sq_nonneg (ψ x))]
        congr 1
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end QSH
