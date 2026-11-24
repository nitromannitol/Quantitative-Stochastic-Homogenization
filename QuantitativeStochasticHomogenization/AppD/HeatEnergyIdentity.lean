import QuantitativeStochasticHomogenization.AppD.HeatEquation
import QuantitativeStochasticHomogenization.AppD.HeatTaylorPairing
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianL2
import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity

/-!
# Appendix D: the energy identity of the heat flow

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, proof of Lemma D.3: for a smooth compactly supported `ψ` and `w(t) = Φ(t) ∗ ψ`,
`∫ w(a)² - ∫ w(b)² = 2 ∫_a^b ‖∇w(t)‖²_{L²} dt` for `0 < a ≤ b`
(`integral_heatSmooth_sq_sub_eq`), so that `∫_0^∞ ‖∇w(t)‖²_{L²} dt ≤ ½ ‖ψ‖²_{L²}`, which is (D.6)
for `ψ` (`lintegral_heatEnergy_le`).

The identity is obtained by integrating `∂ₜ (w²) = 2 w Δw` in time at every point
(`heatSmooth_sq_sub_eq_integral`), exchanging the time and space integrals by Fubini's theorem
(the heat kernels on the time window `[a, b]` are dominated by `(b/a)^{d/2} Φ(b)`), and integrating
`∫ w Δw = -‖∇w‖²` by parts (`integral_heatSmooth_mul_heatSmooth_coordLaplacian`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The energy `‖∇(Φ(t) ∗ ψ)‖²_{L²} = ∑ⱼ ‖Φ(t) ∗ ∂ⱼψ‖²_{L²}` of the heat flow at time `t`. -/
def heatEnergy (t : ℝ) (ψ : Vec d → ℝ) : ℝ :=
  ∑ j, ∫ x, heatSmooth t (coordinateDerivative j ψ) x ^ 2

theorem heatSmooth_eq_kconv (t : ℝ) (f : Vec d → ℝ) :
    heatSmooth t f = kconv (euclideanHeatKernel t) f := rfl

theorem lintegral_enorm_euclideanHeatKernel_ne_top {t : ℝ} (ht : 0 < t) :
    ∫⁻ z : Vec d, ‖euclideanHeatKernel t z‖ₑ ≠ ⊤ := by
  rw [lintegral_enorm_euclideanHeatKernel ht]
  exact ENNReal.one_ne_top

/-- The heat flow of a continuous compactly supported function is bounded by a bound of it. -/
theorem abs_heatSmooth_le_of_abs_le {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ} {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) (x : Vec d) : |heatSmooth t f x| ≤ M := by
  rw [heatSmooth_eq_integral]
  calc |∫ y, euclideanHeatKernel t y * f (x - y)|
      ≤ ∫ y, euclideanHeatKernel t y * M := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((integrable_euclideanHeatKernel ht).mul_const M)
          (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ht.le y)]
        exact mul_le_mul_of_nonneg_left (hM _) (euclideanHeatKernel_nonneg ht.le y)
    _ = M := by rw [integral_mul_const, integral_euclideanHeatKernel ht, one_mul]

/-- On the time window `[a, b]` the heat flow is dominated by `(b/a)^{d/2} Φ(b) ∗ |f|`. -/
theorem abs_heatSmooth_le_mul {a b t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a b) {f : Vec d → ℝ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (x : Vec d) :
    |heatSmooth t f x| ≤ (b / a) ^ ((d : ℝ) / 2) * heatSmooth b (fun y => |f y|) x := by
  have ht0 : 0 < t := ha.trans_le ht.1
  have hb : 0 < b := ht0.trans_le ht.2
  rw [heatSmooth_eq_integral, heatSmooth_eq_integral, ← integral_const_mul]
  have hcabs : HasCompactSupport fun y => |f y| := hcf.comp_left (g := abs) abs_zero
  have hint : Integrable (fun y => euclideanHeatKernel b y * |f (x - y)|) :=
    integrable_mul_comp_sub_of_compact (continuous_euclideanHeatKernel b) hf.abs hcabs x
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul _)
    (Eventually.of_forall fun y => ?_))
  dsimp only
  rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ht0.le y), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc euclideanHeatKernel t y ≤ (b / t) ^ ((d : ℝ) / 2) * euclideanHeatKernel b y :=
        euclideanHeatKernel_le_mul ht0 ht.2 y
    _ ≤ (b / a) ^ ((d : ℝ) / 2) * euclideanHeatKernel b y := by
        refine mul_le_mul_of_nonneg_right ?_ (euclideanHeatKernel_nonneg hb.le y)
        exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hb.le ha ht.1)
          (by positivity)

section TestFunction

variable {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)

include hψ hcψ

/-- **Integration by parts**: `∫ w Δw = -‖∇w‖²_{L²}` for `w = Φ(t) ∗ ψ`. -/
theorem integral_heatSmooth_mul_heatSmooth_coordLaplacian {t : ℝ} (ht : 0 < t) :
    ∫ x, heatSmooth t ψ x * heatSmooth t (coordLaplacian ψ) x = -heatEnergy t ψ := by
  have hs : IsSmoothCompact ψ := ⟨hψ, hcψ⟩
  have hκm := measurable_euclideanHeatKernel (d := d) t
  have hκ1 := lintegral_enorm_euclideanHeatKernel_ne_top (d := d) ht
  have hD : ∀ j, IsSmoothCompact (coordinateDerivative j (coordinateDerivative j ψ)) := fun j =>
    (hs.coordinateDerivative j).coordinateDerivative j
  have hsum : ∀ x, heatSmooth t (coordLaplacian ψ) x =
      ∑ j, heatSmooth t (coordinateDerivative j (coordinateDerivative j ψ)) x := fun x =>
    heatSmooth_finsetSum Finset.univ (fun j _ => ⟨(hD j).1.continuous, (hD j).2⟩) x
  have hint : ∀ j, Integrable (fun x => heatSmooth t ψ x *
      heatSmooth t (coordinateDerivative j (coordinateDerivative j ψ)) x) := fun j =>
    integrable_kconv_mul hκm hκ1 hs (hD j)
  simp_rw [hsum, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => hint j, heatEnergy,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := integral_kconv_mul_kconv_coordinateDerivative hκm hκ1 hs (hs.coordinateDerivative j) j
  simp_rw [sq]
  exact h

/-- **The heat equation integrated in time** at a point: `w(b)² - w(a)² = ∫_a^b 2 w Δw`. -/
theorem heatSmooth_sq_sub_eq_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : Vec d) :
    heatSmooth b ψ x ^ 2 - heatSmooth a ψ x ^ 2 =
      ∫ t in a..b, 2 * heatSmooth t ψ x * heatSmooth t (coordLaplacian ψ) x := by
  have hΔ := contDiff_coordLaplacian hψ
  have hcΔ := hasCompactSupport_coordLaplacian hcψ
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht => by
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun τ => heatSmooth τ ψ x ^ 2)
      (2 * heatSmooth t ψ x * heatSmooth t (coordLaplacian ψ) x) t := fun t ht => by
    refine ((hasDerivAt_heatSmooth (hpos t ht) hψ hcψ x).pow 2).congr_deriv ?_
    rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
    push_cast
    ring
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_).symm
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  exact (((hasDerivAt_heatSmooth (hpos t ht) hψ hcψ x).continuousAt.const_mul 2).mul
    (hasDerivAt_heatSmooth (hpos t ht) hΔ hcΔ x).continuousAt).continuousWithinAt

/-- The integrand `2 w Δw` of the energy identity is integrable on `(a, b] × ℝ^d`. -/
theorem integrable_heatSmooth_mul_coordLaplacian {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (Function.uncurry fun (t : ℝ) (x : Vec d) =>
      2 * heatSmooth t ψ x * heatSmooth t (coordLaplacian ψ) x)
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hb : 0 < b := ha.trans_le hab
  have hΔ := contDiff_coordLaplacian hψ
  have hcΔ := hasCompactSupport_coordLaplacian hcψ
  obtain ⟨M, hM⟩ := hψ.continuous.bounded_above_of_compact_support hcψ
  have hM' : ∀ y, |ψ y| ≤ M := fun y => by simpa [Real.norm_eq_abs] using hM y
  have hHi : Integrable (heatSmooth b (fun y => |coordLaplacian ψ y|)) :=
    (integrable_euclideanHeatKernel hb).integrable_convolution _
      ((hΔ.continuous.abs).integrable_of_hasCompactSupport (hcΔ.comp_left (g := abs) abs_zero))
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := by
    rw [isFiniteMeasure_restrict, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hdom : Integrable (fun p : ℝ × Vec d =>
      (2 * M * (b / a) ^ ((d : ℝ) / 2)) * heatSmooth b (fun y => |coordLaplacian ψ y|) p.2)
      ((volume.restrict (Ioc a b)).prod volume) :=
    (integrable_const _).mul_prod hHi
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (x : Vec d) =>
      2 * heatSmooth t ψ x * heatSmooth t (coordLaplacian ψ) x)
      ((volume.restrict (Ioc a b)).prod volume) := by
    have h1 := (stronglyMeasurable_heatSmooth_uncurry hψ.continuous.measurable).comp_measurable
      measurable_swap
    have h2 := (stronglyMeasurable_heatSmooth_uncurry hΔ.continuous.measurable).comp_measurable
      measurable_swap
    exact ((h1.const_mul 2).mul h2).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  have hprod : (volume.restrict (Ioc a b)).prod (volume : Measure (Vec d)) =
      ((volume : Measure ℝ).prod (volume : Measure (Vec d))).restrict (Ioc a b ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with p hp
  have ht : p.1 ∈ Icc a b := ⟨hp.1.1.le, hp.1.2⟩
  have ht0 : 0 < p.1 := ha.trans hp.1.1
  have h1 := abs_heatSmooth_le_of_abs_le ht0 hM' p.2
  have h2 := abs_heatSmooth_le_mul ha ht hΔ.continuous hcΔ p.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, abs_two]
  calc 2 * |heatSmooth p.1 ψ p.2| * |heatSmooth p.1 (coordLaplacian ψ) p.2|
      ≤ 2 * M * ((b / a) ^ ((d : ℝ) / 2) *
          heatSmooth b (fun y => |coordLaplacian ψ y|) p.2) := by gcongr
    _ = _ := by ring

/-- **The energy identity**: `∫ w(b)² - ∫ w(a)² = -2 ∫_a^b ‖∇w(t)‖²_{L²} dt` for `0 < a ≤ b`. -/
theorem integral_heatSmooth_sq_sub_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, heatSmooth b ψ x ^ 2) - ∫ x, heatSmooth a ψ x ^ 2 =
      -2 * ∫ t in a..b, heatEnergy t ψ := by
  have hs : IsSmoothCompact ψ := ⟨hψ, hcψ⟩
  have hsq : ∀ t, 0 < t → Integrable (fun x => heatSmooth t ψ x ^ 2) := fun t ht => by
    have hm : MemLp (heatSmooth t ψ) 2 volume := memLp_kconv (measurable_euclideanHeatKernel t)
      (lintegral_enorm_euclideanHeatKernel_ne_top ht) hs
    exact hm.integrable_sq
  rw [← integral_sub (hsq b (ha.trans_le hab)) (hsq a ha)]
  simp_rw [heatSmooth_sq_sub_eq_integral hψ hcψ ha hab, intervalIntegral.integral_of_le hab]
  rw [← integral_integral_swap (integrable_heatSmooth_mul_coordLaplacian hψ hcψ ha hab),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_heatSmooth_mul_heatSmooth_coordLaplacian hψ hcψ (ha.trans ht.1)]
  ring

/-- The heat flow is a contraction of `L²`. -/
theorem integral_heatSmooth_sq_le {t : ℝ} (ht : 0 < t) :
    ∫ x, heatSmooth t ψ x ^ 2 ≤ ∫ x, ψ x ^ 2 := by
  have hs : IsSmoothCompact ψ := ⟨hψ, hcψ⟩
  have hm : MemLp (heatSmooth t ψ) 2 volume := memLp_kconv (measurable_euclideanHeatKernel t)
    (lintegral_enorm_euclideanHeatKernel_ne_top ht) hs
  rw [← sq_toReal_eLpNorm_two hm, ← sq_toReal_eLpNorm_two hs.memLp]
  have hle : eLpNorm (heatSmooth t ψ) 2 volume ≤ eLpNorm ψ 2 volume := by
    have h := eLpNorm_heatConv_le ht hψ.continuous.measurable
    have heq : heatSmooth t ψ = fun x => ∫ y, euclideanHeatKernel t (x - y) * ψ y :=
      funext (kconv_apply _ _)
    rwa [heq]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hs.memLp.eLpNorm_ne_top hle) 2

theorem integral_heatEnergy_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, heatEnergy t ψ ≤ (∫ x, ψ x ^ 2) / 2 := by
  have h := integral_heatSmooth_sq_sub_eq hψ hcψ ha hab
  have hb0 : 0 ≤ ∫ x, heatSmooth b ψ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have ha1 := integral_heatSmooth_sq_le hψ hcψ ha
  linarith

theorem integrableOn_heatEnergy {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun t => heatEnergy t ψ) (Ioc a b) := by
  have h := ((integrable_heatSmooth_mul_coordLaplacian hψ hcψ ha hab).integral_prod_left).const_mul
    (-1 / 2)
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [Function.uncurry_apply_pair]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_heatSmooth_mul_heatSmooth_coordLaplacian hψ hcψ (ha.trans ht.1)]
  ring

/-- **(D.6) for test functions**: `∫_0^∞ ‖∇(Φ(t) ∗ ψ)‖²_{L²} dt ≤ ½ ‖ψ‖²_{L²}`. -/
theorem lintegral_heatEnergy_le :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (heatEnergy t ψ) ≤ ENNReal.ofReal ((∫ x, ψ x ^ 2) / 2) := by
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    ext t
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_gt (max t (1 / t))
      refine ⟨n, ?_, ?_⟩
      · have h1 : 1 / t < n + 1 := by linarith [le_max_right t (1 / t)]
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ ht] at h1
        linarith
      · linarith [le_max_left t (1 / t)]
    · rintro ⟨n, hn, -⟩
      exact lt_trans (by positivity) hn
  have hdir : Directed (· ⊆ ·) fun n : ℕ => Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    refine Monotone.directed_le fun m n hmn => Ioc_subset_Ioc ?_ ?_
    · have : (m : ℝ) + 1 ≤ n + 1 := by
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith
      exact one_div_le_one_div_of_le (by positivity) this
    · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
  rw [hU, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun n => ?_
  have ha : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hab : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_heatEnergy hψ hcψ ha hab)
    (Eventually.of_forall fun t => Finset.sum_nonneg fun j _ => integral_nonneg fun x =>
      sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← intervalIntegral.integral_of_le hab]
  exact integral_heatEnergy_le hψ hcψ ha hab

end TestFunction

end QSH
