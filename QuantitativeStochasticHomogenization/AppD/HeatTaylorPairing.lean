import QuantitativeStochasticHomogenization.AppD.HeatPairing

/-!
# Appendix D: the Taylor formula of the heat semigroup paired with a field

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: for `0 < s ≤ 1` and `f` bounded by `M` and vanishing outside the unit ball,
`|Φ(s) ∗ f (x)| ≤ 2^{d/2} M exp(-(‖x‖ - 1)₊² / 8)` (`abs_heatSmooth_le`), uniformly in `s`.
Hence a field `F` with `F exp(-‖x‖²/16)` integrable can be paired with the Taylor formula of the
heat semigroup, the remainder being exchanged with the spatial integral by Fubini's theorem
(`integral_mul_heatTaylor`).
-/

open MeasureTheory Filter Set
open scoped ContDiff Topology Convolution Nat

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanHeatKernel_eq_mul {s : ℝ} (hs : 0 < s) (y : Vec d) :
    euclideanHeatKernel s y = 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
      Real.exp (-(euclideanSq y) / (8 * s)) := by
  unfold euclideanHeatKernel
  have h1 : (4 * Real.pi * (2 * s)) = 2 * (4 * Real.pi * s) := by ring
  rw [h1, Real.mul_rpow (x := 2) (y := 4 * Real.pi * s) (by norm_num) (by positivity)]
  have h2 : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp [neg_div]
  have h3 : Real.exp (-(euclideanSq y) / (4 * s)) = Real.exp (-(euclideanSq y) / (4 * (2 * s))) *
      Real.exp (-(euclideanSq y) / (8 * s)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h3]
  calc _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) * ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) *
        (Real.exp (-(euclideanSq y) / (4 * (2 * s))) * Real.exp (-(euclideanSq y) / (8 * s)))) := by
        rw [h2]; ring
    _ = _ := by ring

theorem heatSmooth_eq_integral (s : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    heatSmooth s f x = ∫ y, euclideanHeatKernel s y * f (x - y) := by
  simp [heatSmooth, convolution_def]

/-- The positive part `(‖x‖ - 1)₊`. -/
def distUnitBall (x : Vec d) : ℝ := max (‖x‖ - 1) 0

theorem distUnitBall_sq_ge (x : Vec d) : ‖x‖ ^ 2 / 2 - 1 ≤ distUnitBall x ^ 2 := by
  unfold distUnitBall
  rcases le_or_gt 1 ‖x‖ with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (‖x‖ - 2)]
  · rw [max_eq_right (by linarith)]
    nlinarith [norm_nonneg x]

theorem exp_distUnitBall_le (x : Vec d) :
    Real.exp (-(distUnitBall x ^ 2) / 8) ≤ Real.exp (1 / 8) * Real.exp (-(‖x‖ ^ 2) / 16) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := distUnitBall_sq_ge x
  linarith

/-- **Uniform Gaussian decay of heat-smoothed functions supported in the unit ball.** -/
theorem abs_heatSmooth_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {f : Vec d → ℝ} {M : ℝ}
    (hM : ∀ z, |f z| ≤ M)
    (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ 1) (x : Vec d) :
    |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) := by
  rw [heatSmooth_eq_integral]
  have hs2 : 0 < 2 * s := by positivity
  have hpt : ∀ y, ‖euclideanHeatKernel s y * f (x - y)‖ ≤
      M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) *
        euclideanHeatKernel (2 * s) y := fun y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg hs.le y)]
    by_cases hz : f (x - y) = 0
    · rw [hz, abs_zero, mul_zero]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      have := euclideanHeatKernel_nonneg hs2.le y
      positivity
    have hxy := hsupp _ hz
    have hy : distUnitBall x ≤ ‖y‖ := by
      unfold distUnitBall
      refine max_le ?_ (norm_nonneg y)
      have h2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      linarith
    have hsq : distUnitBall x ^ 2 ≤ euclideanSq y := by
      have h0 : 0 ≤ distUnitBall x := le_max_right _ _
      calc distUnitBall x ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ h0 hy 2
        _ ≤ euclideanSq y := norm_sq_le_euclideanSq y
    have hexp : Real.exp (-(euclideanSq y) / (8 * s)) ≤ Real.exp (-(distUnitBall x ^ 2) / 8) := by
      refine Real.exp_le_exp.mpr ?_
      have h0 : 0 ≤ distUnitBall x ^ 2 := sq_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [euclideanHeatKernel_eq_mul hs y]
    have hK := euclideanHeatKernel_nonneg hs2.le y
    have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := by positivity
    calc 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
          Real.exp (-(euclideanSq y) / (8 * s)) * |f (x - y)|
        ≤ 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * s) y *
          Real.exp (-(distUnitBall x ^ 2) / 8) * M := by
          gcongr
          exact hM _
      _ = _ := by ring
  calc |∫ y, euclideanHeatKernel s y * f (x - y)|
      ≤ ∫ y, M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) *
        euclideanHeatKernel (2 * s) y :=
        norm_integral_le_of_norm_le ((integrable_euclideanHeatKernel hs2).const_mul _)
          (Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul, integral_euclideanHeatKernel hs2, mul_one]

theorem measurable_euclideanHeatKernel_uncurry :
    Measurable (fun p : ℝ × Vec d => euclideanHeatKernel p.1 p.2) := by
  unfold euclideanHeatKernel euclideanSq dot
  fun_prop

theorem stronglyMeasurable_heatSmooth_uncurry {f : Vec d → ℝ} (hf : Measurable f) :
    StronglyMeasurable (fun p : Vec d × ℝ => heatSmooth p.2 f p.1) := by
  simp_rw [heatSmooth_eq_integral]
  refine StronglyMeasurable.integral_prod_right
    (f := fun (p : Vec d × ℝ) (y : Vec d) => euclideanHeatKernel p.2 y * f (p.1 - y)) ?_
  refine Measurable.stronglyMeasurable ?_
  exact (measurable_euclideanHeatKernel_uncurry.comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
    (hf.comp ((measurable_fst.comp measurable_fst).sub measurable_snd))

theorem stronglyMeasurable_heatPath_uncurry {f : Vec d → ℝ} (hf : Measurable f) :
    StronglyMeasurable (fun p : Vec d × ℝ => heatPath f p.1 p.2) := by
  unfold heatPath
  exact StronglyMeasurable.ite (measurableSet_le measurable_snd measurable_const)
    (hf.comp measurable_fst).stronglyMeasurable (stronglyMeasurable_heatSmooth_uncurry hf)

theorem tsupport_coordinateDerivative_subset (f : Vec d → ℝ) (j : Fin d) :
    tsupport (coordinateDerivative j f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (unitVector j)

theorem tsupport_iterLaplacian_subset (f : Vec d → ℝ) (k : ℕ) :
    tsupport (iterLaplacian k f) ⊆ tsupport f := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rw [iterLaplacian_succ]
    refine closure_minimal (fun z hz => ?_) (isClosed_tsupport _)
    by_contra hnot
    apply hz
    show ∑ j, coordinateDerivative j (coordinateDerivative j (iterLaplacian k f)) z = 0
    refine Finset.sum_eq_zero fun j _ => image_eq_zero_of_notMem_tsupport fun h => hnot (ih ?_)
    exact tsupport_coordinateDerivative_subset _ j (tsupport_coordinateDerivative_subset _ j h)

/-- The Gaussian bound of `abs_heatSmooth_le` in the form `C exp(-‖x‖²/16)`. -/
theorem abs_heatSmooth_le_exp {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {f : Vec d → ℝ} {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ 1) (x : Vec d) :
    |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (1 / 8) * Real.exp (-(‖x‖ ^ 2) / 16) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc |heatSmooth s f x| ≤ M * 2 ^ ((d : ℝ) / 2) * Real.exp (-(distUnitBall x ^ 2) / 8) :=
        abs_heatSmooth_le hs hs1 hM hsupp x
    _ ≤ M * 2 ^ ((d : ℝ) / 2) * (Real.exp (1 / 8) * Real.exp (-(‖x‖ ^ 2) / 16)) := by
        gcongr
        exact exp_distUnitBall_le x
    _ = _ := by ring

theorem integrable_mul_heatSmooth {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ 1) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) : Integrable (fun x => F x * heatSmooth s f x) := by
  have hmeas : StronglyMeasurable (fun x : Vec d => heatSmooth s f x) :=
    (stronglyMeasurable_heatSmooth_uncurry hf).comp_measurable
      (measurable_id.prodMk measurable_const)
  refine (hF.norm.const_mul (M * 2 ^ ((d : ℝ) / 2) * Real.exp (1 / 8))).mono'
    (hFm.mul hmeas.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos (-(‖x‖ ^ 2) / 16))]
  have h := abs_heatSmooth_le_exp hs hs1 hM hsupp x
  calc |F x| * |heatSmooth s f x| ≤
      |F x| * (M * 2 ^ ((d : ℝ) / 2) * Real.exp (1 / 8) * Real.exp (-(‖x‖ ^ 2) / 16)) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- **The Taylor formula of the heat semigroup paired with a field**: for `F` with
`F exp(-‖x‖²/16)` integrable and `χ` smooth with support in the unit ball,
`∫ F χ = ∑_{k ≤ m} (-1)^k/k! ∫ F Φ(1) ∗ Δ^k χ - ∫₀¹ (-s)^m/m! ∫ F Φ(s) ∗ Δ^{m+1} χ ds`. -/
theorem integral_mul_heatTaylor {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsupp : ∀ z ∈ tsupport χ, ‖z‖ ≤ 1)
    (m : ℕ) :
    ∫ x, F x * χ x = (∑ k ∈ Finset.range (m + 1), (-1) ^ k / (k ! : ℝ) *
        ∫ x, F x * heatSmooth 1 (iterLaplacian k χ) x) -
      ∫ s in (0 : ℝ)..1, (-s) ^ m / (m ! : ℝ) *
        ∫ x, F x * heatSmooth s (iterLaplacian (m + 1) χ) x := by
  have hsm := iterLaplacian_smooth hχ hcχ
  have hb : ∀ k, ∃ M, ∀ z, |iterLaplacian k χ z| ≤ M := fun k =>
    (hsm k).1.continuous.bounded_above_of_compact_support (hsm k).2
  have hsk : ∀ k, ∀ z, iterLaplacian k χ z ≠ 0 → ‖z‖ ≤ 1 := fun k z hz =>
    hsupp z (tsupport_iterLaplacian_subset χ k (subset_tsupport _ hz))
  have hmk : ∀ k, Measurable (iterLaplacian k χ) := fun k => (hsm k).1.continuous.measurable
  have hI : ∀ k, ∀ s : ℝ, 0 < s → s ≤ 1 →
      Integrable (fun x => F x * heatSmooth s (iterLaplacian k χ) x) := fun k s hs hs1 => by
    obtain ⟨M, hM⟩ := hb k
    exact integrable_mul_heatSmooth hFm hF (hmk k) hM (hsk k) hs hs1
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
        (M * 2 ^ ((d : ℝ) / 2) * Real.exp (1 / 8) / (m ! : ℝ)) *
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
    have h := abs_heatSmooth_le_exp hp.1 hp.2 hM (hsk (m + 1)) x
    have hpow : |(-s) ^ m| ≤ 1 := by
      rw [abs_pow, abs_neg, abs_of_pos hp.1]
      exact pow_le_one₀ hp.1.le hp.2
    have hfac : (0 : ℝ) < m ! := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div,
      abs_of_pos hfac, abs_of_pos (Real.exp_pos _)]
    have hA : 0 ≤ |heatSmooth s f x| := abs_nonneg _
    calc |F x| * (|(-s) ^ m| / (m ! : ℝ) * |heatSmooth s f x|)
        ≤ |F x| * (1 / (m ! : ℝ) *
          (M * 2 ^ ((d : ℝ) / 2) * Real.exp (1 / 8) * Real.exp (-(‖x‖ ^ 2) / 16))) := by
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
