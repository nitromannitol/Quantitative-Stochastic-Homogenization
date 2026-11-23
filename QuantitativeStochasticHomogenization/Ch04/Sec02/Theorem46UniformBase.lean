import QuantitativeStochasticHomogenization.Ch04.Sec02.Theorem46Uniform

/-!
# The initial exponent of the bootstrap with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 4.3 and Step 2 of the proof of Theorem 4.6. Proposition 3.21 at the exponent `s ≥ 1`
with constant `C` and rate `μ` gives `Fluc(s, min μ 1)` with the constant
`baseFluctuationConstant Λ s C μ`, which depends only on `Λ, s, C, μ`
(`flucEstimateAt_of_gaussianCorrectorRate`, for every bounded jointly measurable version of `J₁`).
Hence Proposition 3.21 with constants chosen before the law gives `UniformBaseFluctuation`
(`uniformBaseFluctuation_of_rate`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The constant of `Fluc(s, min μ 1)` from Proposition 3.21 at the exponent `s` with constant
`C` and rate `μ`: `K C' + (28 C + 2 K C') / L` with `K = 2|Λ| + 3`, `L = (log 2)^{1/s}`,
`r₀ = max 1 ((5C)^{1/μ})` and `C' = 2^{1/s} max C (r₀/L)`. -/
def baseFluctuationConstant (Λ s C μ : ℝ) : ℝ :=
  (2 * |Λ| + 3) * ((2 : ℝ) ^ s⁻¹ * max C (max 1 ((5 * C) ^ μ⁻¹) / Real.log 2 ^ s⁻¹)) +
    (28 * C + 2 * (2 * |Λ| + 3) *
      ((2 : ℝ) ^ s⁻¹ * max C (max 1 ((5 * C) ^ μ⁻¹) / Real.log 2 ^ s⁻¹))) / Real.log 2 ^ s⁻¹

theorem baseFluctuationConstant_pos {s C : ℝ} (hC : 0 < C) (μ : ℝ) :
    0 < baseFluctuationConstant Λ s C μ := by
  have hL : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have hC' : 0 < (2 : ℝ) ^ s⁻¹ * max C (max 1 ((5 * C) ^ μ⁻¹) / Real.log 2 ^ s⁻¹) :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hC)
  unfold baseFluctuationConstant
  positivity

/-- **Proposition 4.3 with the constant chosen before the law**: for a bounded jointly measurable
version `J` of `J₁`, Proposition 3.21 at the exponent `s ≥ 1` with constant `C` and rate `μ`, the
structure (4.12) of `A₁` and the bounds on `ā` give `Fluc(s, min μ 1)` for `J` with the constant
`baseFluctuationConstant Λ s C μ`. -/
theorem flucEstimateAt_of_gaussianCorrectorRate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ} (hJ : IsBoundedJointVersion P J)
    {s C μ : ℝ} (hs : 1 ≤ s) (hC : 0 < C) (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S s C μ) :
    FlucEstimateAt P J s (min μ 1) (baseFluctuationConstant Λ s C μ) := by
  set L : ℝ := Real.log 2 ^ s⁻¹ with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  set r₀ : ℝ := max 1 ((5 * C) ^ μ⁻¹) with hr₀
  have hr₀1 : 1 ≤ r₀ := le_max_left _ _
  have hr₀0 : 0 < r₀ := zero_lt_one.trans_le hr₀1
  set C' : ℝ := (2 : ℝ) ^ s⁻¹ * max C (r₀ / L) with hC'
  have hC'0 : 0 < C' := mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hC)
  set K : ℝ := 2 * |Λ| + 3 with hK
  have hK0 : 0 < K := by positivity
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  obtain ⟨X₀, -, hX₀z⟩ := hrate
  have hconst : OsBound P (fun _ => r₀) s (r₀ / L) :=
    osBound_of_le_const measurable_const hs0 hr₀0 (Filter.Eventually.of_forall fun _ => le_rfl)
  intro z r hr p q hp hq
  obtain ⟨hX₀, hgood₀⟩ := hX₀z z
  set X : CoefficientField d Λ → ℝ := fun a => max (X₀ a z) r₀ with hXdef
  have hX1 : ∀ a, 1 ≤ X a := fun a => hr₀1.trans (le_max_right _ _)
  have hXos : OsBound P X s C' := osBound_max hX₀ hconst
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hp2 : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq2 : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  set c := homogenizedJ1 S.homogenized p q with hc
  have hcK := abs_homogenizedJ1_le hA hp.le hq.le
  have hJK : ∀ a : CoefficientField d Λ, |J a z r p q| ≤ |Λ| + 1 := fun a => hJ.2.1 a z r p q hp hq
  have hm : Measurable fun a : CoefficientField d Λ => J a z r p q :=
    (hJ.measurable_slice r p q).comp (measurable_id.prodMk measurable_const)
  have hJint : Integrable (fun a => J a z r p q) P :=
    Integrable.of_bound hm.aestronglyMeasurable (|Λ| + 1)
      (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hJK a)
  have hXint := hXos.integrable_and_integral_le hs fun a => zero_le_one.trans (hX1 a)
  set δ : ℝ := 14 * C * r ^ (-μ) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hZ : ∀ᵐ a ∂P, |J a z r p q - c| ≤ δ + K * (X a / r) := by
    filter_upwards [hgood₀, hspan, hJ.2.2] with a ha hsp hJa
    rw [hJa z r p q]
    by_cases hXr : X a ≤ r
    · have hr₀r : r₀ ≤ r := (le_max_right _ _).trans hXr
      have h5C : 5 * C ≤ r ^ μ := by
        have h1 : (5 * C) ^ μ⁻¹ ≤ r := (le_max_right _ _).trans hr₀r
        have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hμ.le
        rwa [Real.rpow_inv_rpow (by positivity) hμ.ne'] at h2
      have hε : C * r ^ (-μ) ≤ 1 / 5 := by
        rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hr0 _)]
        linarith
      have h1 := abs_J1Heat_sub_homogenizedJ1_le S a hA hsp z r
        (mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)) hε
        (ha r hr ((le_max_left _ _).trans hXr)) p q
      rw [← hc] at h1
      have h2 : euclideanNorm p ^ 2 + euclideanNorm q ^ 2 ≤ 2 := by
        rw [euclideanNorm_sq, euclideanNorm_sq]; linarith
      have h3 : 0 ≤ C * r ^ (-μ) := mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)
      have h4 : 0 ≤ K * (X a / r) :=
        mul_nonneg hK0.le (div_nonneg (zero_le_one.trans (hX1 a)) hr0.le)
      nlinarith
    · have h1 : 1 ≤ X a / r := by
        rw [le_div_iff₀ hr0]; linarith
      have h2 : |J1Heat a z r p q - c| ≤ K := by
        have := abs_sub (J1Heat a z r p q) c
        have h5 := hJK a
        rw [hJa z r p q] at h5
        linarith
      nlinarith
  have hE : |(∫ a, J a z r p q ∂P) - c| ≤ δ + K * (2 * C') / r := by
    have hsub : (∫ a, J a z r p q ∂P) - c = ∫ a, (J a z r p q - c) ∂P := by
      rw [integral_sub hJint (integrable_const c), integral_const, probReal_univ, one_smul]
    have hXr : Integrable (fun a => δ + K * (X a / r)) P :=
      (integrable_const δ).add ((hXint.1.div_const r).const_mul K)
    calc |(∫ a, J a z r p q ∂P) - c|
        = |∫ a, (J a z r p q - c) ∂P| := by rw [hsub]
      _ ≤ ∫ a, |J a z r p q - c| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ a, (δ + K * (X a / r)) ∂P :=
          integral_mono_ae (hJint.sub (integrable_const c)).abs hXr hZ
      _ = δ + K * (∫ a, X a ∂P) / r := by
          rw [integral_add (integrable_const δ) ((hXint.1.div_const r).const_mul K),
            integral_const, probReal_univ, one_smul, integral_const_mul, integral_div]
          ring
      _ ≤ δ + K * (2 * C') / r := by
          gcongr
          exact hXint.2
  set D : ℝ := 2 * δ + K * (2 * C') / r with hD
  have hD0 : 0 < D := by positivity
  have hbound : ∀ᵐ a ∂P, |J a z r p q - ∫ a', J a' z r p q ∂P| ≤ K / r * X a + D := by
    filter_upwards [hZ] with a ha
    have h1 := abs_sub_le (J a z r p q) c (∫ a', J a' z r p q ∂P)
    rw [abs_sub_comm c] at h1
    have h2 : K * (X a / r) = K / r * X a := by ring
    linarith
  have hos1 : OsBound P (fun a => K / r * X a) s (K / r * C') := hXos.const_mul (by positivity)
  have hos2 : OsBound P (fun _ => D) s (D / L) :=
    osBound_of_le_const measurable_const hs0 hD0 (Filter.Eventually.of_forall fun _ => le_rfl)
  have hos := (osBound_add hos1 hos2 hs).of_le_ae
    (continuous_abs.measurable.comp (hm.sub measurable_const)) hbound
  refine ⟨hJint, hos.mono_scale ?_⟩
  have hmin : r ^ (-μ) ≤ r ^ (-min μ 1) := rpow_neg_le_rpow_neg hr (min_le_left _ _)
  have hone : r⁻¹ ≤ r ^ (-min μ 1) := by
    have := rpow_neg_le_rpow_neg hr (min_le_right μ 1)
    rwa [Real.rpow_neg_one] at this
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr0
  have hρ0 : 0 ≤ r ^ (-μ) := Real.rpow_nonneg hr0.le _
  calc K / r * C' + D / L
      = K * C' * r⁻¹ + (28 * C * r ^ (-μ) + 2 * K * C' * r⁻¹) / L := by
        rw [hD, hδ]; ring
    _ ≤ K * C' * r ^ (-min μ 1) +
          (28 * C * r ^ (-min μ 1) + 2 * K * C' * r ^ (-min μ 1)) / L := by
        gcongr
    _ = baseFluctuationConstant Λ s C μ * r ^ (-min μ 1) := by
        rw [baseFluctuationConstant, ← hr₀, ← hL, ← hC', ← hK]
        ring

/-- **Proposition 4.3 with constants chosen before the law** from Proposition 3.21 with
constants chosen before the law at every exponent `u ∈ (1, 2)`: the structure (4.12) of `A₁`
follows from the first-order Liouville theorem and the bounds on `ā` from the measurability of
the Dirichlet energies. -/
theorem uniformBaseFluctuation_of_rate (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hrate : ∀ u : ℝ, 1 < u → u < 2 → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        GaussianCorrectorRate P S u C μ) :
    UniformBaseFluctuation d Λ := by
  intro u hu1 hu2
  obtain ⟨C, μ, hC, hμ, h⟩ := hrate u hu1 hu2
  refine ⟨min μ 1, baseFluctuationConstant Λ u C μ, lt_min hμ one_pos,
    baseFluctuationConstant_pos hC μ, fun P hP J hJ => ?_⟩
  haveI := hP.1
  obtain ⟨S, hS⟩ := h P hP
  exact flucEstimateAt_of_gaussianCorrectorRate S (S.homogenizedMatrixBounds (by linarith))
    (ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S) hJ hu1.le hC hμ hS

end QSH
