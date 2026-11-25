import QuantitativeStochasticHomogenization.AppD.PropositionD2Fractional
import QuantitativeStochasticHomogenization.AppD.HeatTaylorPairing

/-!
# Appendix D: the heat flow on `L^p(ℝ^d)`

Tools for Proposition D.1 with `u ∈ L^p(ℝ^d)`:
* Young's inequality `‖K ∗ h‖_{L^q} ≤ ‖K‖_{L¹} ‖h‖_{L^q}` (`lintegral_conv_rpow_le`,
  `memLp_kconv_of_memLp`), proved by Jensen's inequality and Tonelli's theorem;
* the semigroup property `Φ(a + b) ∗ u = Φ(a) ∗ (Φ(b) ∗ u)` for `u ∈ L^p` (`heatSmooth_add_of_memLp`);
* the pairing `∫ F (Φ(s) ∗ χ) = ∫ (Φ(s) ∗ F) χ` (`integral_mul_heatSmooth_comm`) and its consequence
  `∫ u (Φ(t) ∗ χ) = ∫ (Φ(t/2) ∗ u) (Φ(t/2) ∗ χ)` (`integral_mul_heatSmooth_split`) for a continuous
  compactly supported `χ`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff Convolution Nat

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Young's inequality** for nonnegative functions:
`∫ (∫ K(x - y) f(y) dy)^q dx ≤ (∫ K)^q ∫ f^q`. -/
theorem lintegral_conv_rpow_le {q : ℝ} (hq : 1 < q) {K f : Vec d → ℝ≥0∞} (hK : Measurable K)
    (hf : Measurable f) :
    ∫⁻ x, (∫⁻ y, K (x - y) * f y) ^ q ≤ (∫⁻ z, K z) ^ q * ∫⁻ y, f y ^ q := by
  have hKx : ∀ x : Vec d, ∫⁻ y, K (x - y) = ∫⁻ z, K z := fun x => lintegral_sub_left_eq_self K x
  have hm : Measurable (Function.uncurry fun (x y : Vec d) => K (x - y) * f y ^ q) :=
    (hK.comp (measurable_fst.sub measurable_snd)).mul ((hf.comp measurable_snd).pow_const _)
  calc ∫⁻ x, (∫⁻ y, K (x - y) * f y) ^ q
      ≤ ∫⁻ x, (∫⁻ y, K (x - y)) ^ (q - 1) * ∫⁻ y, K (x - y) * f y ^ q :=
        lintegral_mono fun x => lintegral_mul_rpow_le hq
          (hK.comp (measurable_const.sub measurable_id)).aemeasurable hf.aemeasurable
    _ = (∫⁻ z, K z) ^ (q - 1) * ∫⁻ x, ∫⁻ y, K (x - y) * f y ^ q := by
        simp_rw [hKx]
        exact lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ z, K z) ^ (q - 1) * ((∫⁻ z, K z) * ∫⁻ y, f y ^ q) := by
        congr 1
        rw [lintegral_lintegral_swap hm.aemeasurable]
        have h : ∀ y, ∫⁻ x, K (x - y) * f y ^ q = (∫⁻ z, K z) * f y ^ q := fun y => by
          rw [lintegral_mul_const _ (show Measurable (fun x => K (x - y)) from
            hK.comp (measurable_id.sub_const y)),
            lintegral_sub_right_eq_self K y]
        simp_rw [h]
        exact lintegral_const_mul _ (hf.pow_const _)
    _ = (∫⁻ z, K z) ^ q * ∫⁻ y, f y ^ q := by
        rw [← mul_assoc]
        congr 1
        conv_rhs => rw [show q = (q - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]

theorem enorm_kconv_le (K h : Vec d → ℝ) (x : Vec d) :
    ‖kconv K h x‖ₑ ≤ ∫⁻ y, ‖K (x - y)‖ₑ * ‖h y‖ₑ := by
  rw [kconv_apply]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp_rw [enorm_mul]

/-- **Young's inequality** `‖K ∗ h‖_{L^q} ≤ ‖K‖_{L¹} ‖h‖_{L^q}`, with the measurability of `K ∗ h`. -/
theorem memLp_kconv_of_memLp {K h : Vec d → ℝ} {q : ℝ} (hq : 1 < q) (hK : Integrable K)
    (hKm : Measurable K) (hh : MemLp h (ENNReal.ofReal q) volume) :
    MemLp (kconv K h) (ENNReal.ofReal q) volume ∧
      eLpNorm (kconv K h) (ENNReal.ofReal q) volume ≤
        (∫⁻ z, ‖K z‖ₑ) * eLpNorm h (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  set h' := hh.aestronglyMeasurable.mk h with hh'
  have hh'm : Measurable h' := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hhh' : h =ᵐ[volume] h' := hh.aestronglyMeasurable.ae_eq_mk
  have hconv : kconv K h = kconv K h' := by
    funext x
    rw [kconv_apply, kconv_apply]
    refine integral_congr_ae ?_
    filter_upwards [hhh'] with y hy
    rw [hy]
  have hmeas : AEStronglyMeasurable (kconv K h) volume := by
    rw [hconv]
    have hs : StronglyMeasurable (fun p : Vec d × Vec d => K (p.1 - p.2) * h' p.2) :=
      ((hKm.comp (measurable_fst.sub measurable_snd)).mul (hh'm.comp measurable_snd)).stronglyMeasurable
    have := hs.integral_prod_right' (ν := volume)
    refine this.aestronglyMeasurable.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [kconv_apply]
  have hq' : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hp0 : ENNReal.ofReal q ≠ 0 := by simp; linarith
  have hY : ∫⁻ x, ‖kconv K h x‖ₑ ^ q ≤ (∫⁻ z, ‖K z‖ₑ) ^ q * ∫⁻ y, ‖h y‖ₑ ^ q := by
    calc ∫⁻ x, ‖kconv K h x‖ₑ ^ q ≤ ∫⁻ x, (∫⁻ y, ‖K (x - y)‖ₑ * ‖h' y‖ₑ) ^ q := by
          refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hq0.le
          rw [hconv]
          exact enorm_kconv_le K h' x
      _ ≤ (∫⁻ z, ‖K z‖ₑ) ^ q * ∫⁻ y, ‖h' y‖ₑ ^ q :=
          lintegral_conv_rpow_le hq hKm.enorm hh'm.enorm
      _ = (∫⁻ z, ‖K z‖ₑ) ^ q * ∫⁻ y, ‖h y‖ₑ ^ q := by
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [hhh'] with y hy
          rw [hy]
  have hbound : eLpNorm (kconv K h) (ENNReal.ofReal q) volume ≤
      (∫⁻ z, ‖K z‖ₑ) * eLpNorm h (ENNReal.ofReal q) volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hmeas,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hh.aestronglyMeasurable, hq']
    calc (∫⁻ x, ‖kconv K h x‖ₑ ^ q) ^ (1 / q)
        ≤ ((∫⁻ z, ‖K z‖ₑ) ^ q * ∫⁻ y, ‖h y‖ₑ ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hY (by positivity)
      _ = (∫⁻ z, ‖K z‖ₑ) * (∫⁻ y, ‖h y‖ₑ ^ q) ^ (1 / q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hK1 : ∫⁻ z, ‖K z‖ₑ < ⊤ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hK]
    exact ENNReal.ofReal_lt_top
  have hlt : eLpNorm (kconv K h) (ENNReal.ofReal q) volume < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top hK1 hh.eLpNorm_lt_top)
  exact ⟨hlt, hbound⟩

/-- An `L^p` function times a translate of the heat kernel is integrable. -/
theorem integrable_euclideanHeatKernel_mul_of_memLp {t : ℝ} (ht : 0 < t) {p : ℝ} (hp : 1 ≤ p)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) (x : Vec d) :
    Integrable (fun y => euclideanHeatKernel t (x - y) * u y) :=
  integrable_mul_of_bound_of_memLp (K := fun y => euclideanHeatKernel t (x - y)) hp
    ((integrable_euclideanHeatKernel ht).comp_sub_left x)
    ((continuous_euclideanHeatKernel t).comp (continuous_const.sub continuous_id))
    (fun z => by
      rw [abs_of_nonneg (euclideanHeatKernel_nonneg ht.le _)]
      exact euclideanHeatKernel_le_const ht _) hu

/-- **The semigroup property on `L^p`**: `Φ(a + b) ∗ u = Φ(a) ∗ (Φ(b) ∗ u)`. -/
theorem heatSmooth_add_of_memLp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {p : ℝ} (hp : 1 ≤ p)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) (x : Vec d) :
    heatSmooth (a + b) u x = heatSmooth a (heatSmooth b u) x := by
  have hsg : ∀ z, euclideanHeatKernel (d := d) (a + b) (x - z) =
      ∫ y, euclideanHeatKernel a (x - y) * euclideanHeatKernel b (y - z) := fun z => by
    have h := foldr_euclideanHeatKernel_semigroup (d := d) ha hb [] x z
    simpa using h
  have hum : AEStronglyMeasurable u volume := hu.aestronglyMeasurable
  set F : Vec d × Vec d → ℝ := fun q =>
    euclideanHeatKernel a (x - q.1) * (euclideanHeatKernel b (q.1 - q.2) * u q.2) with hF
  have hFi : Integrable F (volume.prod volume) := by
    have hm : AEStronglyMeasurable F (volume.prod volume) := by
      refine (((continuous_euclideanHeatKernel a).comp
        (continuous_const.sub continuous_fst)).aestronglyMeasurable).mul
        ((((continuous_euclideanHeatKernel b).comp
          (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul ?_)
      exact hum.comp_snd
    refine ⟨hm, ?_⟩
    have hint := integrable_euclideanHeatKernel_mul_of_memLp (add_pos ha hb) hp hu x
    rw [HasFiniteIntegral, lintegral_prod_symm _ hm.enorm]
    have hz : ∀ z, ∫⁻ y, ‖F (y, z)‖ₑ = ENNReal.ofReal (euclideanHeatKernel (a + b) (x - z)) *
        ‖u z‖ₑ := fun z => by
      simp only [hF, enorm_mul]
      have hnn : ∀ w, ‖euclideanHeatKernel (d := d) a w‖ₑ = ENNReal.ofReal (euclideanHeatKernel a w) :=
        fun w => Real.enorm_of_nonneg (euclideanHeatKernel_nonneg ha.le w)
      have hnn' : ∀ w, ‖euclideanHeatKernel (d := d) b w‖ₑ = ENNReal.ofReal (euclideanHeatKernel b w) :=
        fun w => Real.enorm_of_nonneg (euclideanHeatKernel_nonneg hb.le w)
      simp_rw [hnn, hnn', ← mul_assoc]
      rw [lintegral_mul_const' _ _ enorm_ne_top, hsg z]
      congr 1
      rw [ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul (euclideanHeatKernel_nonneg ha.le _)]
      · exact ((integrable_euclideanHeatKernel ha).comp_sub_left x).mul_of_top_left
          (memLp_top_of_bound ((continuous_euclideanHeatKernel b).comp
            (continuous_id.sub continuous_const)).aestronglyMeasurable
            ((4 * Real.pi * b) ^ (-(d : ℝ) / 2)) (Eventually.of_forall fun y => by
              rw [Real.norm_of_nonneg (euclideanHeatKernel_nonneg hb.le _)]
              exact euclideanHeatKernel_le_const hb _))
      · exact Eventually.of_forall fun y => mul_nonneg (euclideanHeatKernel_nonneg ha.le _)
          (euclideanHeatKernel_nonneg hb.le _)
    simp_rw [hz]
    have h2 := hint.hasFiniteIntegral
    rw [HasFiniteIntegral] at h2
    refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h2
    rw [enorm_mul, Real.enorm_of_nonneg (euclideanHeatKernel_nonneg (add_pos ha hb).le _)]
  rw [show heatSmooth (a + b) u x = kconv (euclideanHeatKernel (a + b)) u x from rfl,
    show heatSmooth a (heatSmooth b u) x = kconv (euclideanHeatKernel a) (heatSmooth b u) x from rfl,
    kconv_apply, kconv_apply]
  calc ∫ z, euclideanHeatKernel (a + b) (x - z) * u z
      = ∫ z, ∫ y, F (y, z) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hF]
        rw [hsg z, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
    _ = ∫ y, ∫ z, F (y, z) := (integral_integral_swap hFi).symm
    _ = ∫ y, euclideanHeatKernel a (x - y) * heatSmooth b u y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hF]
        rw [integral_const_mul, show heatSmooth b u y = kconv (euclideanHeatKernel b) u y from rfl,
          kconv_apply]

theorem integrable_mul_euclideanHeatKernel_of_memLp {t : ℝ} (ht : 0 < t) {p : ℝ} (hp : 1 ≤ p)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) :
    Integrable (fun x => u x * euclideanHeatKernel t x) := by
  refine (integrable_euclideanHeatKernel_mul_of_memLp ht hp hu 0).congr
    (Eventually.of_forall fun y => ?_)
  simp only [zero_sub, euclideanHeatKernel_neg, mul_comm]

/-- **Pairing with the heat flow**: `∫ F (Φ(s) ∗ χ) = ∫ (Φ(s) ∗ F) χ`. -/
theorem integral_mul_heatSmooth_comm {s : ℝ} (hs : 0 < s) {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * euclideanHeatKernel (4 * s) x)) {χ : Vec d → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
    ∫ x, F x * heatSmooth s χ x = ∫ y, heatSmooth s F y * χ y := by
  have h := integral_mul_convolution_eq hs [] hFm hF hχ hcχ
  simp only [List.foldr_nil] at h
  change ∫ x, F x * ((euclideanHeatKernel s) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) x = _
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [mul_comm, show heatSmooth s F y = kconv (euclideanHeatKernel s) F y from rfl, kconv_apply]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_comm, ← neg_sub y x, euclideanHeatKernel_neg]

/-- **Splitting the heat flow between the two factors**:
`∫ u (Φ(t) ∗ χ) = ∫ (Φ(t/2) ∗ u) (Φ(t/2) ∗ χ)` for `u ∈ L^p`. -/
theorem integral_mul_heatSmooth_split {t : ℝ} (ht : 0 < t) {p : ℝ} (hp : 1 < p) {u : Vec d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) {χ : Vec d → ℝ} (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) :
    ∫ x, u x * heatSmooth t χ x = ∫ x, heatSmooth (t / 2) u x * heatSmooth (t / 2) χ x := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hv := (memLp_kconv_of_memLp (K := euclideanHeatKernel (t / 2)) hp
    (integrable_euclideanHeatKernel ht2) (continuous_euclideanHeatKernel _).measurable hu).1
  change MemLp (heatSmooth (t / 2) u) (ENNReal.ofReal p) volume at hv
  rw [integral_mul_heatSmooth_comm ht hu.aestronglyMeasurable
    (integrable_mul_euclideanHeatKernel_of_memLp (by positivity) hp.le hu) hχ hcχ]
  have hsplit : ∀ y, heatSmooth t u y = heatSmooth (t / 2) (heatSmooth (t / 2) u) y := fun y => by
    rw [← heatSmooth_add_of_memLp ht2 ht2 hp.le hu y, add_halves]
  simp_rw [hsplit]
  rw [← integral_mul_heatSmooth_comm ht2 hv.aestronglyMeasurable
    (integrable_mul_euclideanHeatKernel_of_memLp (by positivity) hp.le hv) hχ hcχ]

end QSH
