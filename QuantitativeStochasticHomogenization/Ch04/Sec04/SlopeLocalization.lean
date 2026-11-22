import QuantitativeStochasticHomogenization.Ch04.Sec04.TranslatedCorrectorBounds
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBallProof

/-!
# The localized energy estimate from the single-slope estimate of Lemma 4.21

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21 and (5.85). The oscillation, Gaussian energy and outer energy hypotheses of
`LocalizationCorrectorSlopeData` follow from the corrector bounds at the center `z`
(`exists_translated_corrector_bounds` with the exponent `sγ < d`) above a random radius whose
`γ`-th power is `O_s(C)`: the oscillation constant is `ε = 2 · 2^{d/2} C (2r)^{-β(d-sγ)}`, small
for large `r`, the energies on balls `B_t(z)`, `t ≥ r`, are at most `2^{d+1}(1 + C²) |B_t|`, and
the Gaussian energy at scale `√2 r` is at most `heatShellConstant d 0` times this constant.
What remains of Lemma 4.21 is the single-slope estimate `LocalizationSlopeEstimate` for the
selected coordinates below a fixed fraction of the intermediate scale.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Gaussian averages over the whole space from ball integrals with polynomial growth.** -/
theorem integral_heatKernel_mul_le_of_ball_growth_univ {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    {z : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hKf : Integrable (fun x => heatKernel z ρ x * f x))
    (hfi : ∀ R : ℝ, IntegrableOn f (ball z R)) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hgrowth : ∀ t : ℝ, ρ ≤ t → ∫ x in ball z t, f x ≤ A * (t / ρ) ^ k * volume.real (ball z t)) :
    ∫ x, heatKernel z ρ x * f x ≤ heatShellConstant d k * A := by
  have hn : ∀ n : ℕ, ∫ x in ball z n, heatKernel z ρ x * f x ≤ heatShellConstant d k * A :=
    fun n => integral_heatKernel_mul_le_of_ball_growth hf0 (hfi n) hρ hA k fun t ht =>
      (setIntegral_mono_set (hfi t) (Eventually.of_forall fun x => hf0 x)
        Set.inter_subset_right.eventuallyLE).trans (hgrowth t ht)
  have hmono : Monotone fun n : ℕ => ball z (n : ℝ) := fun n m hnm x hx =>
    (lt_of_lt_of_le hx (Nat.cast_le.mpr hnm) : euclideanNorm (x - z) < m)
  have hU : (⋃ n : ℕ, ball z (n : ℝ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm (x - z))
    exact ⟨n, hn⟩
  have ht := tendsto_setIntegral_of_monotone (μ := volume)
    (s := fun n : ℕ => ball z (n : ℝ)) (f := fun x => heatKernel z ρ x * f x)
    (fun n => measurableSet_ball z (n : ℝ)) hmono (by rw [hU]; exact hKf.integrableOn)
  rw [hU, Measure.restrict_univ] at ht
  exact le_of_tendsto' ht hn

theorem integrableOn_euclideanSq_unitVector_add {Λ : ℝ} {a : CoefficientField d Λ}
    (i : Fin d) {φ : Vec d → ℝ} {g : Vec d → Vec d} (hφg : HasWeakGradient Set.univ φ g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (harm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g x))
      (fun _ => 0)) (z : Vec d) (R : ℝ) :
    IntegrableOn (fun x => euclideanSq (unitVector i + g x)) (ball z R) :=
  (integrable_finsetSum Finset.univ fun k _ =>
    ((localCorrectedCoordinate a z R i 0 φ g hφg hloc harm).memLp_grad k).integrable_sq).congr
    (Eventually.of_forall fun x => by simp only [euclideanSq, dot, sq]; rfl)

theorem rpow_max_of_nonneg {x y γ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hγ : 0 ≤ γ) :
    max x y ^ γ = max (x ^ γ) (y ^ γ) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow hx h hγ)]
  · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hy h hγ)]

/-- **The single-slope estimate of Lemma 4.21 on a good event** (the remaining analytic input
of (5.85) in this form): there are `c ∈ (0, 1]`, `K₁ ≥ 0` and `C₁ > 0` such that for every law
there is a homogenization data `S` with the following property. For every localized family,
center and scale `r ≥ 2` there are nonnegative random variables `X` and `Y` with
`X^γ ≤ O_s(C₁)` and `Y ≤ O_s(C₁ r^{-γ})`, and almost surely, if `X ≤ r`, there are slopes `b`
with `∑ b_{ij}² ≤ 1/4` such that the selected coordinates `w_i` satisfy
`∫_{B_t(z)} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ K₁ Y² (t/r)² |B_t|` for `r ≤ t ≤ c S`,
`W_i = correctorColumn S a i`, `S = r^{1+δ-ε}`. -/
def LocalizationSlopeEstimate (d : ℕ) (Λ s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (c K₁ C₁ : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r → ∃ b : Fin d → Fin d → ℝ, ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4 ∧
            ∀ i, ∀ t : ℝ, r ≤ t → t ≤ c * localizationIntermediateRadius δ α γ r →
              ∫ x in ball z t, euclideanSq (((W a z r hr).coordinate i).grad x -
                (correctorColumn S a i x + ∑ j, b i j • correctorColumn S a j x)) ≤
                  K₁ * Y a ^ 2 * (t / r) ^ 2 * volume.real (ball z t)

/-- The oscillation constant at scale `r` is eventually small. -/
theorem eventually_oscillationConstant_small {β' C : ℝ} (hβ' : 0 < β') :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      (d : ℝ) * (2 * Real.sqrt (2 ^ d) * C * (2 * r) ^ (-β')) ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16 := by
  have h1 : Tendsto (fun r : ℝ => (2 * r) ^ (-β')) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hβ').comp (tendsto_id.const_mul_atTop' two_pos)
  have h2 : Tendsto (fun r : ℝ => (d : ℝ) * (2 * Real.sqrt (2 ^ d) * C * (2 * r) ^ (-β')) ^ 2)
      atTop (𝓝 0) := by
    have := ((h1.const_mul (2 * Real.sqrt (2 ^ d) * C)).pow 2).const_mul (d : ℝ)
    simpa using this
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ d / 16 := by positivity
  obtain ⟨R, hR⟩ := eventually_atTop.1 ((tendsto_order.1 h2).2 _ hpos)
  exact ⟨max R 1, le_max_right _ _, fun r hr => (hR r (le_trans (le_max_left _ _) hr)).le⟩

theorem sq_two_sqrt_mul_rpow_neg {C r β' : ℝ} (hr : 0 < r) :
    (2 * Real.sqrt (2 ^ d) * C * (2 * r) ^ (-β')) ^ 2 * r ^ 2 =
      2 ^ d * (C * (2 * r) ^ (1 - β')) ^ 2 := by
  have h2r : 0 < 2 * r := by positivity
  have hsplit : (2 * r) ^ (1 - β') = (2 * r) * (2 * r) ^ (-β') := by
    rw [sub_eq_add_neg, Real.rpow_add h2r, Real.rpow_one]
  rw [hsplit, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- **The corrector hypotheses of Lemma 4.21 from the single-slope estimate**: the oscillation
and energy bounds come from `exists_translated_corrector_bounds` at the exponent `sγ < d`. -/
theorem localizationCorrectorSlopeEstimate_of_slope (hd : 2 ≤ d) {Λ s δ γ α σ θ C₀ : ℝ}
    (hΛ : 1 < Λ) (hs : 1 ≤ s) (hδ : 0 < δ) (hγ : 0 < γ) (hγs : s * γ < d)
    (h : LocalizationSlopeEstimate d Λ s δ γ α σ θ C₀) :
    LocalizationCorrectorSlopeEstimate d Λ s δ γ α σ θ C₀ := by
  obtain ⟨β, C, hβ, hC, htr⟩ := exists_translated_corrector_bounds hd hΛ
  have hs0 : 0 < s := by linarith
  obtain ⟨Cs, hCs, htrP⟩ := htr (s * γ) (by positivity) hγs
  have hβ' : 0 < β * ((d : ℝ) - s * γ) := mul_pos hβ (by linarith)
  obtain ⟨R, hR1, hRε⟩ := eventually_oscillationConstant_small (d := d) (C := C) hβ'
  obtain ⟨c, K₁, C₁, hc, hc1, hK₁, hC₁, hmain⟩ := h
  set E₁ : ℝ := 2 ^ (d + 1) * (1 + C ^ 2) with hE₁_def
  have hE₁ : 0 ≤ E₁ := by positivity
  have hsc0 : 0 ≤ heatShellConstant d 0 := by
    unfold heatShellConstant heatShellSum
    exact mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg)
      (tsum_nonneg fun j => by positivity)
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have hRγ : 0 < R ^ γ := Real.rpow_pos_of_pos (by linarith) _
  have h1d : (0 : ℝ) < (1 + d) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  set C₁' := C₁ + (1 + d) ^ γ * Cs ^ γ + R ^ γ / Real.log 2 ^ s⁻¹ with hC₁'_def
  have hCsγ : 0 < Cs ^ γ := Real.rpow_pos_of_pos hCs _
  refine ⟨c, heatShellConstant d 0 * E₁, E₁, K₁, C₁', hc, hc1, mul_nonneg hsc0 hE₁, hE₁, hK₁,
    by positivity, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨S, hS⟩ := hmain P hP
  refine ⟨S, fun W z r hr => ?_⟩
  obtain ⟨X, Y, hX0, hY0, hXos, hYos, hae⟩ := hS W z r hr
  obtain ⟨Xz, hXzm, hXzos, hXz1, hXzae⟩ := htrP P hP S z
  have hr0 : 0 < r := by linarith
  have hrγ : 0 < r ^ (-γ) := Real.rpow_pos_of_pos hr0 _
  have hXz0 : ∀ a, 0 ≤ Xz a := fun a => zero_le_one.trans (hXz1 a)
  refine ⟨fun a => max (max (X a) ((1 + d) * Xz a)) R, Y,
    fun a => le_trans (hX0 a) ((le_max_left _ _).trans (le_max_left _ _)), hY0, ?_,
    hYos.mono_scale (mul_le_mul_of_nonneg_right (by
      have := mul_pos h1d hCsγ; have := div_pos hRγ hl2; linarith) hrγ.le), ?_⟩
  · -- the stochastic integrability of the combined radius
    have hpow : ∀ a, max (max (X a) ((1 + d) * Xz a)) R ^ γ =
        max (max (X a ^ γ) ((1 + d) ^ γ * Xz a ^ γ)) (R ^ γ) := fun a => by
      rw [rpow_max_of_nonneg (le_max_of_le_left (hX0 a)) (by linarith) hγ.le,
        rpow_max_of_nonneg (hX0 a) (by have := hXz0 a; positivity) hγ.le,
        Real.mul_rpow (by positivity) (hXz0 a)]
    have hXzγ : AEOsBound P (fun a => (1 + d) ^ γ * Xz a ^ γ) s ((1 + d) ^ γ * Cs ^ γ) := by
      have h1 := hXzos.rpow hXz0 hγ
      rw [show s * γ / γ = s by field_simp] at h1
      exact (h1.aeOsBound_of_ae_eq EventuallyEq.rfl).const_mul h1d
    have hconst : AEOsBound P (fun _ => R ^ γ) s (R ^ γ / Real.log 2 ^ s⁻¹) :=
      (osBound_of_le_const measurable_const hs0 hRγ
        (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl
    have hsum := (hXos.add hXzγ hs).add hconst hs
    refine hsum.of_le_ae ?_ (Eventually.of_forall fun a => ?_)
    · have hm : AEMeasurable (fun a => max (max (X a ^ γ) ((1 + d) ^ γ * Xz a ^ γ)) (R ^ γ)) P :=
        (hXos.1.max hXzγ.1).max aemeasurable_const
      exact hm.congr (Eventually.of_forall fun a => (hpow a).symm)
    · rw [hpow a]
      have h1 := Real.rpow_nonneg (hX0 a) γ
      have h2 : 0 ≤ (1 + d) ^ γ * Xz a ^ γ := mul_nonneg h1d.le (Real.rpow_nonneg (hXz0 a) γ)
      simp only [max_le_iff]
      refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · -- the pathwise hypotheses on the good event
    filter_upwards [hae, hXzae,
      ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable,
      ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).harmonic]
      with a ha hza hint hwg hloc harm hXr
    simp only [max_le_iff] at hXr
    obtain ⟨⟨hXar, hXzr⟩, hRr⟩ := hXr
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hXzd : Xz a + d ≤ r := by
      have := hXz1 a
      nlinarith
    obtain ⟨b, hb, hslope⟩ := ha hXar
    have hosc : ∀ i : Fin d, ∃ c : ℝ, ∫ x in ball z r,
        ((S.corrector (unitVector i)).potential a x - c) ^ 2 ≤
          2 ^ d * (C * (2 * r) ^ (1 - β * ((d : ℝ) - s * γ))) ^ 2 * volume.real (ball z r) :=
      fun i => (hza i r hXzd).1
    choose cc hcc using hosc
    have hT : r ≤ localizationOuterRadius δ r := by
      unfold localizationOuterRadius
      calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    refine ⟨⟨cc, 2 * Real.sqrt (2 ^ d) * C * (2 * r) ^ (-(β * ((d : ℝ) - s * γ))),
      hRε r hRr, fun i => ?_⟩, fun i => ?_, fun i => ?_, b, hb, fun i t hrt htS => ?_⟩
    · rw [sq_two_sqrt_mul_rpow_neg hr0]
      exact hcc i
    · refine integral_heatKernel_mul_le_of_ball_growth_univ (fun x => zero_le_euclideanSq _)
        (by positivity) (hint i z _ (by positivity))
        (integrableOn_euclideanSq_unitVector_add i (hwg i) (hloc i) (harm i) z) hE₁ 0
        fun t ht => ?_
      have hrt : r ≤ t := le_trans (le_mul_of_one_le_left hr0.le
        (by rw [Real.one_le_sqrt]; norm_num)) ht
      rw [pow_zero, mul_one]
      exact (hza i t (hXzd.trans hrt)).2
    · exact (hza i _ (hXzd.trans hT)).2
    · exact hslope i t hrt htS

/-- **(5.85) from the first-order Liouville theorem and the single-slope estimate of
Lemma 4.21.** For every window of exponents, a choice of the structural constants
`α, σ, θ, C₀` with `LocalizationSlopeEstimate` gives the frozen statement
`QSH.Frozen.localizedEnergy`. -/
theorem localizedEnergy_of_slope (hL : firstOrderLiouvilleStatement)
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ : ℝ, 0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
        0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationSlopeEstimate d Λ s δ γ α σ θ C₀) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_correctorSlope hL fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => by
    obtain ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀, hest⟩ :=
      h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
    have hγ0 : 0 < γ := lt_of_le_of_lt (by positivity) hγ1
    have hs0 : 0 < s := by linarith
    have hγs : s * γ < d := by
      have h1 : γ < (d : ℝ) / s := lt_of_lt_of_le hγ2 (min_le_left _ _)
      rw [lt_div_iff₀ hs0] at h1
      linarith
    exact ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀,
      localizationCorrectorSlopeEstimate_of_slope hd hΛ hs1.le hδ hγ0 hγs hest⟩

/-- **(5.85) from the harmonic approximation of Section 3.3 and the single-slope estimate of
Lemma 4.21**, through `firstOrderLiouville_of_harmonicApproximation_only`. -/
theorem localizedEnergy_of_harmonicApproximation_of_slope
    (h2 : harmonicApproximationStatement)
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ : ℝ, 0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
        0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationSlopeEstimate d Λ s δ γ α σ θ C₀) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_slope (firstOrderLiouville_of_harmonicApproximation_only h2) h

end QSH
