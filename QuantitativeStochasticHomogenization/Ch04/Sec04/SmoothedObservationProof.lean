import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationScales

/-!
# The observation of the smoothed correctors from the linear estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (SCOTT-localization (5)). If the Gaussian averages of the corrected fields
satisfy the linear estimate `|∫ Φ_{z,r} (ξ + ∇φ_ξ) - ξ| ≤ O_s(C (1 + |ξ|) r^{-β})` for `r ≥ 1`
(`GaussianGradientAverageBound`, the linear estimate of the bootstrap), then the smoothed
correctors are observed at the exponent `β` (`SmoothedCorrectorObservation`), with constants
chosen before the law:

* `X` is the minimal scale of E8 at the exponent `sγ < d`, so `X^γ = O_s(C)`;
* `Y = (2d)^{1/2}/θ ∑ᵢ Qᵢ^{1/2} + τ_r`, with `Qᵢ` the segment average of the squared linear
  quantities over the segments from `z` to `B_{S/θ}(z)` and `τ_r` the Gaussian error terms;
* `Y = O_s(C S^{-β})` by Lemma A.4 below the exponent one, and `Y ≤ C r^{-μ}`, `μ = κ a₁/2`, on
  `{X ≤ r}` by the oscillation bound of E8 on `B_R(z)`, `R = S r^{ε'}`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The linear estimate at the exponent `β`**: the body of the linear estimate of the
bootstrap (`LinearAverageEstimateAt`). -/
def GaussianGradientAverageBound (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (s β C : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
    OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ)) s
      (C * (1 + euclideanNorm ξ) * r ^ (-β))

theorem obsError_nonneg (d : ℕ) {C₈ κ D σ θ a₁ ε' δ r : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hD : 0 ≤ D) (hr : 0 < r) : 0 ≤ obsError d C₈ κ D σ θ a₁ ε' δ r := by
  have hS : 0 < r ^ a₁ := Real.rpow_pos_of_pos hr _
  have hR : 0 < r ^ a₁ * r ^ ε' := mul_pos hS (Real.rpow_pos_of_pos hr _)
  have h1 := gaussTail'_nonneg d (r ^ a₁ * r ^ ε') (σ * r ^ a₁)
  have h2 := gaussTail_nonneg d (r ^ a₁ * r ^ ε') (mul_pos hσ hS)
  unfold obsError
  have hDR : 0 ≤ D / (r ^ a₁ * r ^ ε') := div_nonneg hD hR.le
  have hSθ : 0 ≤ r ^ a₁ / θ := (div_pos hS hθ).le
  exact add_nonneg (mul_nonneg hSθ (mul_nonneg (Nat.cast_nonneg d) (add_nonneg
    (mul_nonneg h1 (Real.sqrt_nonneg _)) (mul_nonneg (mul_nonneg hDR h2) (Real.sqrt_nonneg _)))))
    (mul_nonneg h2 (Real.sqrt_nonneg _))

theorem obsGradient_nonneg (d : ℕ) {C₈ κ D σ θ a₁ ε' r : ℝ} (hσ : 0 < σ) (hD : 0 ≤ D)
    (hr : 0 < r) : 0 ≤ obsGradient d C₈ κ D σ θ a₁ ε' r := by
  have hS : 0 < r ^ a₁ := Real.rpow_pos_of_pos hr _
  have hR : 0 < r ^ a₁ * r ^ ε' := mul_pos hS (Real.rpow_pos_of_pos hr _)
  have hρ : 0 < σ * r ^ a₁ := mul_pos hσ hS
  have h1 := gaussTail'_nonneg d (r ^ a₁ * r ^ ε') (σ * r ^ a₁)
  have hK : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / (σ * r ^ a₁)) *
      (4 * Real.pi * (2 * (σ * r ^ a₁) ^ 2)) ^ (-(d : ℝ) / 2) +
      D / (r ^ a₁ * r ^ ε') * heatKernelPeak d (σ * r ^ a₁) := by
    have h2 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / (σ * r ^ a₁)) :=
      mul_nonneg (by positivity) (div_nonneg (by norm_num) hρ.le)
    have h3 : 0 ≤ (4 * Real.pi * (2 * (σ * r ^ a₁) ^ 2)) ^ (-(d : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    exact add_nonneg (mul_nonneg h2 h3)
      (mul_nonneg (div_nonneg hD hR.le) (heatKernelPeak_pos hρ.ne').le)
  unfold obsGradient
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hK (Real.sqrt_nonneg _))
    (mul_nonneg h1 (Real.sqrt_nonneg _)))

theorem euclideanNorm_unitVector' (i : Fin d) : euclideanNorm (unitVector i : Vec d) = 1 := by
  rw [euclideanNorm, euclideanSq_unitVector, Real.sqrt_one]

section Good

variable {P : Measure (CoefficientField d Λ)}

theorem integrable_heatKernel_euclideanSq_grad (S : HomogenizationData P)
    (a : CoefficientField d Λ) (i : Fin d)
    (hgauss : ∀ (q : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel q r x * euclideanSq (correctorColumn S a i x)))
    (q : Vec d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => heatKernel q r x *
      euclideanSq ((S.corrector (unitVector i)).grad a x)) := by
  have hgm : Measurable ((S.corrector (unitVector i)).grad a) :=
    (S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left
  have h2 : Continuous fun v : Vec d => euclideanSq v := by
    unfold euclideanSq dot
    fun_prop
  refine (((hgauss q r hr).const_mul 2).add ((integrable_heatKernel_mask q hr.ne').const_mul 2)).mono'
    ((contDiff_heatKernel q r).continuous.aestronglyMeasurable.mul
      (h2.measurable.comp hgm).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_pos q hr x).le
    (zero_le_euclideanSq _))]
  have := euclideanSq_grad_le S a i x
  have h0 := (heatKernel_pos q hr x).le
  calc heatKernel q r x * euclideanSq ((S.corrector (unitVector i)).grad a x) ≤
        heatKernel q r x * (2 * euclideanSq (correctorColumn S a i x) + 2) :=
        mul_le_mul_of_nonneg_left this h0
    _ = 2 * (heatKernel q r x * euclideanSq (correctorColumn S a i x)) +
        2 * heatKernel q r x := by ring

/-- The linear quantity of the `i`-th corrector at the center `p` and the radius `ρ`. -/
def linearQuantity (S : HomogenizationData P) (ρ : ℝ) (i : Fin d) (p : Vec d)
    (a : CoefficientField d Λ) : ℝ :=
  euclideanNorm (gradientAverage S a p ρ (unitVector i) - unitVector i)

/-- **The smoothed observation of the correctors on the good event** `{X ≤ r}`. -/
theorem corrector_observation_good (S : HomogenizationData P) (a : CoefficientField d Λ)
    (z : Vec d) {C₈ κ D σ θ a₁ ε' δ r : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hD : 0 ≤ D)
    (hr : 2 ≤ r) (hRT : a₁ + ε' ≤ 1 + δ)
    (h4 : 4 * (r ^ a₁ / θ) ≤ r ^ a₁ * r ^ ε') (hρ1 : 1 ≤ σ * r ^ a₁)
    (ht₀R : r + d ≤ r ^ a₁ * r ^ ε')
    (hsmall : (2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (-((r ^ a₁ * r ^ ε' / 2) ^ 2) / (8 * (σ * r ^ a₁) ^ 2)) ≤ 1 / 2)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (r ^ a₁ * r ^ ε' / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z (r ^ a₁ * r ^ ε') → χ x = 0)
    (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / (r ^ a₁ * r ^ ε')) ^ 2) (i : Fin d)
    (hwg : HasWeakGradient Set.univ ((S.corrector (unitVector i)).potential a)
      ((S.corrector (unitVector i)).grad a))
    (hloc : ∀ R : ℝ, 0 < R →
      MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) ∧
      MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R)))
    (hgauss : ∀ (q : Vec d) (r' : ℝ), 0 < r' →
      Integrable (fun x => heatKernel q r' x * euclideanSq (correctorColumn S a i x)))
    (hE8 : ∀ t : ℝ, r + d ≤ t →
      (∃ c, ∫ x in ball z t, ((S.corrector (unitVector i)).potential a x - c) ^ 2 ≤
        2 ^ d * (C₈ * (2 * t) ^ (1 - κ)) ^ 2 * volume.real (ball z t)) ∧
      ∫ x in ball z t, euclideanSq (correctorColumn S a i x) ≤
        2 ^ (d + 1) * (1 + C₈ ^ 2) * volume.real (ball z t)) :
    (∃ c : ℝ, localizationObjective z (r ^ (1 + δ)) (r ^ a₁) σ θ
        (fun x => (S.corrector (unitVector i)).potential a x - c) ≤
      2 * (r ^ a₁ / θ) ^ 2 * d * segmentAverage (linearQuantity S (σ * r ^ a₁) i) z (r ^ a₁ / θ) a +
        2 * obsError d C₈ κ D σ θ a₁ ε' δ r ^ 2) ∧
    segmentAverage (linearQuantity S (σ * r ^ a₁) i) z (r ^ a₁ / θ) a ≤
      obsGradient d C₈ κ D σ θ a₁ ε' r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hS : 0 < r ^ a₁ := Real.rpow_pos_of_pos hr0 _
  have hR : 0 < r ^ a₁ * r ^ ε' := mul_pos hS (Real.rpow_pos_of_pos hr0 _)
  have hT : 0 < r ^ (1 + δ) := Real.rpow_pos_of_pos hr0 _
  have hρ : 0 < σ * r ^ a₁ := mul_pos hσ hS
  have hR₁ : 0 < r ^ a₁ / θ := div_pos hS hθ
  have hRTle : r ^ a₁ * r ^ ε' ≤ r ^ (1 + δ) := by
    rw [← Real.rpow_add hr0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hRT
  have hcs := corrector_smoothed_observation S a i hwg hloc hgauss (t₀ := r + d)
    (by have := Nat.cast_nonneg (α := ℝ) d; linarith) (fun t ht => (hE8 t ht).1)
    (fun t ht => (hE8 t ht).2) hS hσ hθ hρ1 h4 hRTle ht₀R hD hsmall hχ hχc hχ01 hχ1 hχR hχD
  dsimp only at hcs
  obtain ⟨hobj, hgrad⟩ := hcs
  rw [volume_real_ball_eq_mul z hR, volume_real_ball_eq_mul z hT, exp_ratio_eq hS hθ hσ] at hobj
  rw [volume_real_ball_eq_mul z hR, exp_ratio_eq hS hθ hσ] at hgrad
  have hgv : ∀ p : Vec d,
      Integrable (fun x => heatKernel p (σ * r ^ a₁) x • (S.corrector (unitVector i)).grad a x) :=
    fun p => integrable_heatKernel_smul_of_energy
      ((S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left).aestronglyMeasurable
      hρ (integrable_heatKernel_euclideanSq_grad S a i hgauss p hρ)
  have hN : ∀ p : Vec d, linearQuantity S (σ * r ^ a₁) i p a =
      euclideanNorm (∫ x, heatKernel p (σ * r ^ a₁) x • (S.corrector (unitVector i)).grad a x) :=
    fun p => by unfold linearQuantity; rw [gradientAverage_sub_unitVector S a i hρ (hgv p)]
  have hseg : segmentAverage (linearQuantity S (σ * r ^ a₁) i) z (r ^ a₁ / θ) a =
      ∫ w, (volume.real (ball z (r ^ a₁ / θ)))⁻¹ * euclideanNorm (∫ x, heatKernel
        (z + w.2 • (w.1 - z)) (σ * r ^ a₁) x • (S.corrector (unitVector i)).grad a x) ^ (2 : ℝ)
          ∂segmentMeasure z (r ^ a₁ / θ) := by
    unfold segmentAverage
    exact integral_congr_ae (Eventually.of_forall fun w => by simp only [hN])
  refine ⟨⟨_, hobj.trans (le_of_eq ?_)⟩, ?_⟩
  · rw [hseg]
    unfold obsError obsOscillation obsEnergy
    rfl
  · refine segmentAverage_le_sq hR₁ a (fun p => zero_le_euclideanNorm _) fun p hp => ?_
    rw [hN p]
    refine (hgrad p hp).trans (le_of_eq ?_)
    unfold obsGradient obsEnergy
    rfl

end Good

theorem measurable_linearQuantity_uncurry {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (ρ : ℝ) (i : Fin d) :
    Measurable (Function.uncurry (linearQuantity S ρ i)) := by
  have hg : Measurable fun w : Vec d × CoefficientField d Λ => ((w.1, ρ), w.2) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have h := (measurable_gradientAverage_uncurry S (unitVector i)).comp hg
  exact euclideanNorm_continuous.measurable.comp (h.sub measurable_const)

theorem sq_rpow_one_half {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

theorem sq_bound_of_parts (d : ℕ) {S A q τ Q E θ Y : ℝ} (hS : 0 < S) (hA0 : 0 ≤ A)
    (hq0 : 0 ≤ q) (hτ0 : 0 ≤ τ) (hq2 : q ^ 2 = Q) (hA2 : A ^ 2 = 2 * d / θ ^ 2)
    (hτ : S * τ = Real.sqrt 2 * E) (hY : A * q + τ ≤ Y) :
    2 * (S / θ) ^ 2 * d * Q + 2 * E ^ 2 ≤ (S * Y) ^ 2 := by
  have h1 : (S * A * q) ^ 2 = 2 * (S / θ) ^ 2 * d * Q := by
    rw [mul_pow, mul_pow, hA2, hq2, div_pow]
    ring
  have h2 : (S * τ) ^ 2 = 2 * E ^ 2 := by
    rw [hτ, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 : 0 ≤ (S * A * q) * (S * τ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hS.le hA0) hq0) (mul_nonneg hS.le hτ0)
  have h4 : (S * A * q) ^ 2 + (S * τ) ^ 2 ≤ (S * (A * q + τ)) ^ 2 := by nlinarith
  have h5 : (S * (A * q + τ)) ^ 2 ≤ (S * Y) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hS.le (add_nonneg (mul_nonneg hA0 hq0) hτ0))
      (mul_le_mul_of_nonneg_left hY hS.le) 2
  rw [← h1, ← h2]
  exact h4.trans h5

set_option maxHeartbeats 400000 in
/-- **The observation of the smoothed correctors from the linear estimate**, with constants
chosen before the law. -/
theorem smoothedCorrectorObservation_of_gaussianGradient (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {s δ γ α σ θ β C : ℝ} (hs1 : 1 < s) (hs2 : s < 2) (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) (hγ : 0 < γ) (hγs : s * γ < d) (hσ : 0 < σ)
    (hθ : 0 < θ) (hC : 0 < C) :
    ∃ μ C' : ℝ, 0 < μ ∧ 0 < C' ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ S : HomogenizationData P, GaussianGradientAverageBound P S s β C →
        SmoothedCorrectorObservation S s δ γ α σ θ β μ C' := by
  obtain ⟨κ₈, C₈, hκ₈, hC₈, hE8⟩ := exists_translated_corrector_bounds hd hΛ
  have hs0 : 0 < s := by linarith
  have hsγ : 0 < s * γ := mul_pos hs0 hγ
  obtain ⟨Cs, hCs, hP8⟩ := hE8 (s * γ) hsγ hγs
  obtain ⟨D, hD, hcut⟩ := exists_ball_cutoff d
  set ε := localizationEpsilon δ α γ with hεdef
  have hε : 0 < ε := localizationEpsilon_pos hδ hα hαγ
  have hεδ : ε ≤ δ / 2 := min_le_right _ _
  set a₁ := 1 + δ - ε with ha₁def
  have ha₁ : 1 < a₁ := by linarith
  set κ := κ₈ * ((d : ℝ) - s * γ) with hκdef
  have hκ : 0 < κ := mul_pos hκ₈ (by linarith)
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  set ε' := min ε (κ * a₁ / (2 * ((d : ℝ) + 1))) with hε'def
  have hε' : 0 < ε' := lt_min hε (div_pos (mul_pos hκ (by linarith)) (by positivity))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'κ : ε' * (d + 1) ≤ κ * a₁ / 2 := by
    have h := min_le_right ε (κ * a₁ / (2 * ((d : ℝ) + 1)))
    calc ε' * (d + 1) ≤ κ * a₁ / (2 * ((d : ℝ) + 1)) * (d + 1) :=
          mul_le_mul_of_nonneg_right h hd1.le
      _ = κ * a₁ / 2 := by field_simp
  set μ := κ * a₁ / 2 with hμdef
  have hμ : 0 < μ := div_pos (mul_pos hκ (by linarith)) two_pos
  obtain ⟨r₀, KG, hr₀, hKG, hscale⟩ :=
    smoothed_scales d (C₈ := C₈) (δ := δ) (β := β) hσ hθ ha₁ hε' hκ hD.le hε'κ
  have hKs := segmentConstant_pos hs0 hs2
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  set A := Real.sqrt (2 * d) / θ with hA
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hA0 : 0 < A := div_pos (Real.sqrt_pos.2 (by linarith)) hθ
  set CY := A * (d * (segmentConstant s ^ (1 / 2 : ℝ) * (C * 2 * σ ^ (-β)))) +
    1 / Real.log 2 ^ s⁻¹ with hCY
  have hCY0 : 0 < CY := by
    have h1 : 0 < segmentConstant s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hKs _
    have h2 : 0 < σ ^ (-β) := Real.rpow_pos_of_pos hσ _
    exact add_pos_of_nonneg_of_pos (mul_nonneg hA0.le (mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg h1.le (mul_nonneg (mul_nonneg hC.le (by norm_num)) h2.le))))
      (one_div_pos.2 hl2)
  set C' := max (max (Cs ^ γ) ((r₀ + 1) ^ γ / Real.log 2 ^ s⁻¹)) (max CY (A * d * KG + 1))
    with hC'
  have hC'1 : Cs ^ γ ≤ C' := le_max_of_le_left (le_max_left _ _)
  have hC'2 : (r₀ + 1) ^ γ / Real.log 2 ^ s⁻¹ ≤ C' := le_max_of_le_left (le_max_right _ _)
  have hC'3 : CY ≤ C' := le_max_of_le_right (le_max_left _ _)
  have hC'4 : A * d * KG + 1 ≤ C' := le_max_of_le_right (le_max_right _ _)
  have hC'0 : 0 < C' := hCY0.trans_le hC'3
  refine ⟨μ, C', hμ, hC'0, fun P hP S hlin => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  intro z r hr
  have hr0 : 0 < r := by linarith
  have hSr : localizationIntermediateRadius δ α γ r = r ^ a₁ := rfl
  have hTr : localizationOuterRadius δ r = r ^ (1 + δ) := rfl
  rw [hSr, hTr]
  have hS : 0 < r ^ a₁ := Real.rpow_pos_of_pos hr0 _
  by_cases hrr : r < r₀
  · -- small radii: the good event is empty
    refine ⟨fun _ => r₀ + 1, fun _ => 0, fun _ => by linarith, fun _ => le_rfl, ?_, ?_, ?_⟩
    · have hc : 0 < (r₀ + 1) ^ γ := Real.rpow_pos_of_pos (by linarith) _
      exact ((osBound_of_le_const measurable_const hs0 hc
        (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl).mono_scale hC'2
    · have hc : 0 < C' * (r ^ a₁) ^ (-β) * Real.log 2 ^ s⁻¹ :=
        mul_pos (mul_pos hC'0 (Real.rpow_pos_of_pos hS _)) hl2
      have h := (osBound_of_le_const (P := P) measurable_const hs0 hc
        (Eventually.of_forall fun _ => hc.le)).aeOsBound_of_ae_eq
          (EventuallyEq.rfl : (fun _ : CoefficientField d Λ => (0 : ℝ)) =ᵐ[P] fun _ => 0)
      rwa [mul_div_cancel_right₀ _ hl2.ne'] at h
    · exact Eventually.of_forall fun a ha => absurd ha (by linarith)
  · -- large radii
    have hrr' : r₀ ≤ r := not_lt.1 hrr
    obtain ⟨h4, hρ1, ht₀R, hsmall, hGr, hτμ, hτβ⟩ := hscale r hrr'
    have hR : 0 < r ^ a₁ * r ^ ε' := mul_pos hS (Real.rpow_pos_of_pos hr0 _)
    obtain ⟨χ, hχ, hχc, hχ01, hχ1, hχR, hχD⟩ := hcut z (r ^ a₁ * r ^ ε') hR
    obtain ⟨X, hXm, hXos, hX1, hXae⟩ := hP8 P hP S z
    set ρ := σ * r ^ a₁ with hρdef
    have hρ0 : 0 < ρ := mul_pos hσ hS
    set R₁ := r ^ a₁ / θ with hR₁def
    have hR₁ : 0 < R₁ := div_pos hS hθ
    set τ := Real.sqrt 2 * obsError d C₈ κ D σ θ a₁ ε' δ r / r ^ a₁ with hτdef
    have hτ0 : 0 ≤ τ := div_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (obsError_nonneg d hσ hθ hD.le hr0)) hS.le
    set Q : Fin d → CoefficientField d Λ → ℝ := fun i a =>
      segmentAverage (linearQuantity S ρ i) z R₁ a with hQdef
    have hQ0 : ∀ i a, 0 ≤ Q i a := fun i a => integral_nonneg fun w =>
      mul_nonneg (inv_nonneg.2 measureReal_nonneg) (Real.rpow_nonneg (zero_le_euclideanNorm _) _)
    set Y : CoefficientField d Λ → ℝ := fun a => A * ∑ i, Q i a ^ (1 / 2 : ℝ) + τ with hYdef
    have hY0 : ∀ a, 0 ≤ Y a := fun a => add_nonneg (mul_nonneg hA0.le (Finset.sum_nonneg
      fun i _ => Real.rpow_nonneg (hQ0 i a) _)) hτ0
    refine ⟨X, Y, fun a => zero_le_one.trans (hX1 a), hY0, ?_, ?_, ?_⟩
    · have h1 := hXos.rpow (fun a => zero_le_one.trans (hX1 a)) hγ
      rw [show s * γ / γ = s by field_simp] at h1
      exact (h1.aeOsBound_of_ae_eq EventuallyEq.rfl).mono_scale hC'1
    · -- the stochastic integrability of `Y`
      have hθ₀ : 0 < C * (1 + 1) * ρ ^ (-β) :=
        mul_pos (mul_pos hC (by norm_num)) (Real.rpow_pos_of_pos hρ0 _)
      have hQi : ∀ i : Fin d, OsBound P (fun a => Q i a ^ (1 / 2 : ℝ)) s
          (segmentConstant s ^ (1 / 2 : ℝ) * (C * (1 + 1) * ρ ^ (-β))) := fun i => by
        have hN : ∀ p, OsBound P (linearQuantity S ρ i p) s (C * (1 + 1) * ρ ^ (-β)) := fun p => by
          have h := hlin p ρ hρ1 (unitVector i)
          rw [euclideanNorm_unitVector'] at h
          exact h
        exact osBound_sqrt_segmentAverage (measurable_linearQuantity_uncurry S ρ i)
          (fun p a => zero_le_euclideanNorm _) hs0 hs2 hθ₀ hN z hR₁
      have hsum := osBound_finset_sum Finset.univ Finset.univ_nonempty hs1.le fun i _ => hQi i
      have hτc : OsBound P (fun _ => τ) s ((r ^ a₁) ^ (-β) / Real.log 2 ^ s⁻¹) :=
        osBound_of_le_const measurable_const hs0 (Real.rpow_pos_of_pos hS _)
          (Eventually.of_forall fun _ => hτβ)
      have hY := osBound_add (hsum.const_mul hA0) hτc hs1.le
      refine (hY.aeOsBound_of_ae_eq EventuallyEq.rfl).mono_scale ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hρdef,
        Real.mul_rpow hσ.le hS.le]
      have hSβ : 0 < (r ^ a₁) ^ (-β) := Real.rpow_pos_of_pos hS _
      have e : A * (d * (segmentConstant s ^ (1 / 2 : ℝ) * (C * (1 + 1) * (σ ^ (-β) *
          (r ^ a₁) ^ (-β))))) + (r ^ a₁) ^ (-β) / Real.log 2 ^ s⁻¹ = CY * (r ^ a₁) ^ (-β) := by
        rw [hCY]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hC'3 hSβ.le
    · -- the good event
      have hg1 := ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient
      have hg2 := ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable
      have hg3 := ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S
      filter_upwards [hg1, hg2, hg3, hXae] with a hwg hloc hgauss h8 hXr
      have hgood := fun i => corrector_observation_good S a z (C₈ := C₈) (κ := κ) (δ := δ)
        hσ hθ hD.le hr (by linarith) h4 hρ1 ht₀R hsmall hχ hχc hχ01 hχ1 hχR hχD i
        (hwg i) (hloc i) (hgauss i) fun t ht => h8 i t (by linarith)
      have hG0 : 0 ≤ obsGradient d C₈ κ D σ θ a₁ ε' r := obsGradient_nonneg d hσ hD.le hr0
      have hqG : ∀ i, Q i a ^ (1 / 2 : ℝ) ≤ obsGradient d C₈ κ D σ θ a₁ ε' r := fun i => by
        have h := Real.rpow_le_rpow (hQ0 i a) (hgood i).2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq hG0] at h
        rwa [← Real.sqrt_eq_rpow]
      refine ⟨?_, fun i => ?_⟩
      · have hsum : ∑ i, Q i a ^ (1 / 2 : ℝ) ≤ d * obsGradient d C₈ κ D σ θ a₁ ε' r := by
          calc ∑ i, Q i a ^ (1 / 2 : ℝ) ≤ ∑ _i : Fin d, obsGradient d C₈ κ D σ θ a₁ ε' r :=
                Finset.sum_le_sum fun i _ => hqG i
            _ = d * obsGradient d C₈ κ D σ θ a₁ ε' r := by simp
        have hrμ : 0 < r ^ (-μ) := Real.rpow_pos_of_pos hr0 _
        calc Y a = A * ∑ i, Q i a ^ (1 / 2 : ℝ) + τ := rfl
          _ ≤ A * (d * (KG * r ^ (-μ))) + r ^ (-μ) := by
              refine add_le_add (mul_le_mul_of_nonneg_left (hsum.trans ?_) hA0.le) hτμ
              exact mul_le_mul_of_nonneg_left hGr (Nat.cast_nonneg d)
          _ = (A * d * KG + 1) * r ^ (-μ) := by ring
          _ ≤ C' * r ^ (-μ) := mul_le_mul_of_nonneg_right hC'4 hrμ.le
      · obtain ⟨c, hc⟩ := (hgood i).1
        refine ⟨c, hc.trans ?_⟩
        set q := Q i a ^ (1 / 2 : ℝ) with hq
        have hq0 : 0 ≤ q := Real.rpow_nonneg (hQ0 i a) _
        have hq2 : q ^ 2 = Q i a := sq_rpow_one_half (hQ0 i a)
        have hYq : A * q + τ ≤ Y a := by
          have : q ≤ ∑ j, Q j a ^ (1 / 2 : ℝ) :=
            Finset.single_le_sum (f := fun j => Q j a ^ (1 / 2 : ℝ))
              (fun j _ => Real.rpow_nonneg (hQ0 j a) _) (Finset.mem_univ i)
          simp only [hYdef]
          linarith [mul_le_mul_of_nonneg_left this hA0.le]
        have hA2 : A ^ 2 = 2 * d / θ ^ 2 := by
          rw [hA, div_pow, Real.sq_sqrt (by positivity)]
        have hτS : r ^ a₁ * τ = Real.sqrt 2 * obsError d C₈ κ D σ θ a₁ ε' δ r := by
          have := hS.ne'
          rw [hτdef]; field_simp
        exact sq_bound_of_parts d hS hA0.le hq0 hτ0 hq2 hA2 hτS hYq

end QSH
