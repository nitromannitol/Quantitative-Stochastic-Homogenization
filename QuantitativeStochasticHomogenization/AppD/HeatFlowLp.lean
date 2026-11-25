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
  compactly supported `χ`;
* the Taylor formula of the heat semigroup paired with a field `F` with `F exp(-‖x‖²/16)` integrable,
  for tests supported in a ball `B_R` (`integral_mul_heatTaylor_ball`), the version of
  `integral_mul_heatTaylor` for the ball `B_R` in place of the unit ball.
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

/-- `|K ∗ h (x)| ≤ ∫ |K(x - y)| |h(y)| dy`. -/
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

/-- An `L^p` function times the heat kernel is integrable. -/
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

/-! ## The Taylor formula paired with a field, for tests supported in a ball -/

/-- The positive part `(‖x‖ - R)₊`. -/
def distBall (R : ℝ) (x : Vec d) : ℝ := max (‖x‖ - R) 0

/-- `(‖x‖ - R)₊² ≥ ‖x‖²/2 - R²`. -/
theorem distBall_sq_ge {R : ℝ} (hR : 0 ≤ R) (x : Vec d) : ‖x‖ ^ 2 / 2 - R ^ 2 ≤ distBall R x ^ 2 := by
  unfold distBall
  rcases le_or_gt R ‖x‖ with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (‖x‖ - 2 * R)]
  · rw [max_eq_right (by linarith)]
    nlinarith [norm_nonneg x]

/-- `exp(-(‖x‖ - R)₊²/8) ≤ exp(R²/8) exp(-‖x‖²/16)`. -/
theorem exp_distBall_le {R : ℝ} (hR : 0 ≤ R) (x : Vec d) :
    Real.exp (-(distBall R x ^ 2) / 8) ≤ Real.exp (R ^ 2 / 8) * Real.exp (-(‖x‖ ^ 2) / 16) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := distBall_sq_ge hR x
  linarith

/-- **Uniform Gaussian decay of heat-smoothed functions supported in the ball `B_R`.** -/
theorem abs_heatSmooth_le_ball {R : ℝ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {f : Vec d → ℝ} {M : ℝ}
    (hM : ∀ z, |f z| ≤ M)
    (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) (x : Vec d) :
    |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distBall R x ^ 2) / 8) := by
  rw [heatSmooth_eq_integral]
  have hs2 : 0 < 2 * s := by positivity
  have hpt : ∀ y, ‖euclideanHeatKernel s y * f (x - y)‖ ≤
      M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distBall R x ^ 2) / 8) *
        euclideanHeatKernel (2 * s) y := fun y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg hs.le y)]
    by_cases hz : f (x - y) = 0
    · rw [hz, abs_zero, mul_zero]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      have := euclideanHeatKernel_nonneg hs2.le y
      positivity
    have hxy := hsupp _ hz
    have hy : distBall R x ≤ ‖y‖ := by
      unfold distBall
      refine max_le ?_ (norm_nonneg y)
      have h2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      linarith
    have hsq : distBall R x ^ 2 ≤ euclideanSq y := by
      have h0 : 0 ≤ distBall R x := le_max_right _ _
      calc distBall R x ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ h0 hy 2
        _ ≤ euclideanSq y := norm_sq_le_euclideanSq y
    have hexp : Real.exp (-(euclideanSq y) / (8 * s)) ≤ Real.exp (-(distBall R x ^ 2) / 8) := by
      refine Real.exp_le_exp.mpr ?_
      have h0 : 0 ≤ distBall R x ^ 2 := sq_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [euclideanHeatKernel_eq_mul hs y]
    have hK := euclideanHeatKernel_nonneg hs2.le y
    have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := by positivity
    calc 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
          Real.exp (-(euclideanSq y) / (8 * s)) * |f (x - y)|
        ≤ 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
          Real.exp (-(distBall R x ^ 2) / 8) * M := by
          gcongr
          exact hM _
      _ = _ := by ring
  calc |∫ y, euclideanHeatKernel s y * f (x - y)|
      ≤ ∫ y, M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distBall R x ^ 2) / 8) *
        euclideanHeatKernel (2 * s) y :=
        norm_integral_le_of_norm_le ((integrable_euclideanHeatKernel hs2).const_mul _)
          (Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul, integral_euclideanHeatKernel hs2, mul_one]

/-- The Gaussian bound of `abs_heatSmooth_le_ball` in the form `C exp(-‖x‖²/16)`. -/
theorem abs_heatSmooth_le_exp_ball {R : ℝ} (hR : 0 ≤ R) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {f : Vec d → ℝ} {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) (x : Vec d) :
    |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (R ^ 2 / 8) * Real.exp (-(‖x‖ ^ 2) / 16) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distBall R x ^ 2) / 8) :=
        abs_heatSmooth_le_ball hs hs1 hM hsupp x
    _ ≤ M * 2 ^ ((d : ℝ) / 2) * (Real.exp (R ^ 2 / 8) * Real.exp (-(‖x‖ ^ 2) / 16)) := by
        gcongr
        exact exp_distBall_le hR x
    _ = _ := by ring

/-- `F (Φ(s) ∗ f)` is integrable for `s ∈ (0, 1]` and a bounded `f` vanishing outside `B_R`, when
`F exp(-‖x‖²/16)` is integrable. -/
theorem integrable_mul_heatSmooth_ball {R : ℝ} (hR : 0 ≤ R) {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) : Integrable (fun x => F x * heatSmooth s f x) := by
  have hmeas : StronglyMeasurable (fun x : Vec d => heatSmooth s f x) :=
    (stronglyMeasurable_heatSmooth_uncurry hf).comp_measurable
      (measurable_id.prodMk measurable_const)
  refine (hF.norm.const_mul (M * 2 ^ ((d : ℝ) / 2) * Real.exp (R ^ 2 / 8))).mono'
    (hFm.mul hmeas.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos (-(‖x‖ ^ 2) / 16))]
  have h := abs_heatSmooth_le_exp_ball hR hs hs1 hM hsupp x
  calc |F x| * |heatSmooth s f x| ≤
      |F x| * (M * 2 ^ ((d : ℝ) / 2) * Real.exp (R ^ 2 / 8) * Real.exp (-(‖x‖ ^ 2) / 16)) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- **The Taylor formula of the heat semigroup paired with a field**: for `F` with
`F exp(-‖x‖²/16)` integrable and `χ` smooth with support in the ball `B_R`,
`∫ F χ = ∑_{k ≤ m} (-1)^k/k! ∫ F Φ(1) ∗ Δ^k χ - ∫₀¹ (-s)^m/m! ∫ F Φ(s) ∗ Δ^{m+1} χ ds`. -/
theorem integral_mul_heatTaylor_ball {R : ℝ} (hR : 0 ≤ R) {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsupp : ∀ z ∈ tsupport χ, ‖z‖ ≤ R)
    (m : ℕ) :
    ∫ x, F x * χ x = (∑ k ∈ Finset.range (m + 1), (-1) ^ k / (k ! : ℝ) *
        ∫ x, F x * heatSmooth 1 (iterLaplacian k χ) x) -
      ∫ s in (0 : ℝ)..1, (-s) ^ m / (m ! : ℝ) *
        ∫ x, F x * heatSmooth s (iterLaplacian (m + 1) χ) x := by
  have hsm := iterLaplacian_smooth hχ hcχ
  have hb : ∀ k, ∃ M, ∀ z, |iterLaplacian k χ z| ≤ M := fun k =>
    (hsm k).1.continuous.bounded_above_of_compact_support (hsm k).2
  have hsk : ∀ k, ∀ z, iterLaplacian k χ z ≠ 0 → ‖z‖ ≤ R := fun k z hz =>
    hsupp z (tsupport_iterLaplacian_subset χ k (subset_tsupport _ hz))
  have hmk : ∀ k, Measurable (iterLaplacian k χ) := fun k => (hsm k).1.continuous.measurable
  have hI : ∀ k, ∀ s : ℝ, 0 < s → s ≤ 1 →
      Integrable (fun x => F x * heatSmooth s (iterLaplacian k χ) x) := fun k s hs hs1 => by
    obtain ⟨M, hM⟩ := hb k
    exact integrable_mul_heatSmooth_ball hR hFm hF (hmk k) hM (hsk k) hs hs1
  set f := iterLaplacian (m + 1) χ with hfdef
  obtain ⟨M, hM⟩ := hb (m + 1)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set H : Vec d → ℝ → ℝ := fun x s => F x * ((-s) ^ m / (m ! : ℝ) * heatPath f x s) with hH
  have hint : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry H)
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
      show AEStronglyMeasurable
        (fun p : Vec d × ℝ => F p.1 * ((-p.2) ^ m / (m ! : ℝ) * heatPath f p.1 p.2)) _
      refine (hFm.comp_fst (ν := volume.restrict (Ioc (0 : ℝ) 1))).mul ?_
      refine AEStronglyMeasurable.mul ?_
        (stronglyMeasurable_heatPath_uncurry (hmk (m + 1))).aestronglyMeasurable
      exact (Measurable.aestronglyMeasurable (by fun_prop))
    have hbound : Integrable (fun p : Vec d × ℝ =>
        (M * 2 ^ ((d : ℝ) / 2) * Real.exp (R ^ 2 / 8) / (m ! : ℝ)) *
          (‖F p.1 * Real.exp (-(‖p.1‖ ^ 2) / 16)‖ * 1))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
      (hF.norm.mul_prod (integrable_const (1 : ℝ))).const_mul _
    refine hbound.mono' hmeas ?_
    have hae : ∀ᵐ p : Vec d × ℝ ∂(volume.prod (volume.restrict (Ioc (0 : ℝ) 1))),
        p.2 ∈ Ioc (0 : ℝ) 1 :=
      Measure.QuasiMeasurePreserving.ae (μa := volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))
        (p := fun s : ℝ => s ∈ Ioc (0 : ℝ) 1) Measure.quasiMeasurePreserving_snd
        (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with p hp
    obtain ⟨x, s⟩ := p
    simp only [Function.uncurry_apply_pair, hH]
    rw [heatPath_of_pos hp.1]
    have h := abs_heatSmooth_le_exp_ball hR hp.1 hp.2 hM (hsk (m + 1)) x
    have hpow : |(-s) ^ m| ≤ 1 := by
      rw [abs_pow, abs_neg, abs_of_pos hp.1]
      exact pow_le_one₀ hp.1.le hp.2
    have hfac : (0 : ℝ) < m ! := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div,
      abs_of_pos hfac, abs_of_pos (Real.exp_pos _)]
    have hA : 0 ≤ |heatSmooth s f x| := abs_nonneg _
    calc |F x| * (|(-s) ^ m| / (m ! : ℝ) * |heatSmooth s f x|)
        ≤ |F x| * (1 / (m ! : ℝ) *
          (M * 2 ^ ((d : ℝ) / 2) * Real.exp (R ^ 2 / 8) * Real.exp (-(‖x‖ ^ 2) / 16))) := by
          gcongr
      _ = _ := by ring
  have htaylor : ∀ x, F x * χ x = F x * heatTaylorSum (m + 1) χ x 1 -
      ∫ s in Ioc (0 : ℝ) 1, H x s := fun x => by
    rw [hH]
    simp only
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, ← mul_sub]
    congr 1
    exact heatTaylor hχ hcχ x m
  have hsum : ∀ x, F x * heatTaylorSum (m + 1) χ x 1 = ∑ k ∈ Finset.range (m + 1),
      (-1) ^ k / (k ! : ℝ) * (F x * heatSmooth 1 (iterLaplacian k χ) x) := fun x => by
    unfold heatTaylorSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [heatPath_of_pos one_pos]
    ring
  have hI1 : Integrable (fun x => F x * heatTaylorSum (m + 1) χ x 1) := by
    simp_rw [hsum]
    exact integrable_finsetSum _ fun k _ => (hI k 1 one_pos le_rfl).const_mul _
  have hI2 : Integrable (fun x => ∫ s in Ioc (0 : ℝ) 1, H x s) := hint.integral_prod_left
  have hA : ∫ x, F x * heatTaylorSum (m + 1) χ x 1 = ∑ k ∈ Finset.range (m + 1),
      (-1) ^ k / (k ! : ℝ) * ∫ x, F x * heatSmooth 1 (iterLaplacian k χ) x := by
    rw [integral_congr_ae (Eventually.of_forall hsum),
      integral_finsetSum _ fun k _ => (hI k 1 one_pos le_rfl).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hB : ∫ x, ∫ s in Ioc (0 : ℝ) 1, H x s = ∫ s in (0 : ℝ)..1, (-s) ^ m / (m ! : ℝ) *
      ∫ x, F x * heatSmooth s (iterLaplacian (m + 1) χ) x := by
    rw [integral_integral_swap hint, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [hH]
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [heatPath_of_pos hs.1]
    ring
  rw [integral_congr_ae (Eventually.of_forall htaylor), integral_sub hI1 hI2, hA, hB]

end QSH
