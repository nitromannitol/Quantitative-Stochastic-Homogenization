import QuantitativeStochasticHomogenization.Ch04.Sec03.Proposition410Uniform
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedEnergyJointMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerExistence

/-!
# Proposition 4.11 with constants chosen before the law from the localized energies

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, Proposition 4.11, at the exponents used by the bootstrap of Theorem 4.6.

The localized random variables of Proposition 4.11 are the localized energies `J₁^{(δ)}` of
Section 4.4 (`familyJ1` of a localized family `W`, which is chosen once, independently of the law).
`PilotLocalizationEstimates d Λ` states the estimate `|J₁ - J₁^{(δ)}| ≤ O_s(D r^{-γ})`,
`γ = (α(1+δ) + δ) ∧ d/s - η`, for every law and every localized family, under `Fluc(s, α)` with
constant `C` for a bounded jointly measurable version of `J₁`, with `D` and the structural
constants of the family chosen before the law. The localized energies are jointly local in the
coefficients and the center (`measurable_indicator_familyJ1`), so this gives
`UniformLocalizationEstimates d Λ` (`uniformLocalizationEstimates_of_pilot`): below `r = 2` the
localized energy is zero and `|J| ≤ |Λ| + 1`.

With Proposition 3.21 and the heat identity (H) with constants chosen before the law, this is the
last input of the bootstrap (`bootstrapInputs_of_rate_heat_pilot`); the frozen statements E1–E4,
E7, Theorem 4.6 (i), (iii) and (5.58) follow from these three inputs
(`negativeSobolevCorrector_of_rate_heat_pilot` and the theorems after it).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `AEOsBound` passes to an almost surely equal measurable random variable as `OsBound`. -/
theorem AEOsBound.osBound_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {s θ : ℝ} (h : AEOsBound P X s θ) (hY : Measurable Y) (hXY : X =ᵐ[P] Y) :
    OsBound P Y s θ := by
  obtain ⟨-, hs, hθ, hE⟩ := h
  refine ⟨hY, hs, hθ, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (Y ω) 0) ^ s)) ∂P
      = ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P :=
        lintegral_congr_ae (by
          filter_upwards [hXY] with ω h
          rw [h])
    _ ≤ 2 := hE

/-- **Proposition 4.11 at the exponents of the bootstrap, for the localized energies**: for
`s ∈ (1, 2)`, `α ∈ (0, d/2]`, `δ, η > 0` and every constant `C`, there are structural constants
`α_c, σ, θ, C₀` of a localized family and `D` such that, for every law satisfying the assumptions,
every bounded jointly measurable version `J` of `J₁` with `Fluc(s, α)` with constant `C`, and every
localized family `W`, `|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)| ≤ O_s(D r^{-γ})` for `r ≥ 2`,
`γ = (α(1+δ) + δ) ∧ d/s - η`. -/
def PilotLocalizationEstimates (d : ℕ) (Λ : ℝ) : Prop :=
  ∀ s α δ η C : ℝ, 1 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 → 0 < δ → 0 < η → 0 < C →
    ∃ αc σ θ C₀ D : ℝ, 0 < σ ∧ 0 < θ ∧ 0 < C₀ ∧ 0 < D ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s α C →
        ∀ W : LocalizedFamily d Λ δ (min (α * (1 + δ) + δ) ((d : ℝ) / s) - η) αc σ θ C₀,
        ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
          euclideanNorm p < 1 → euclideanNorm q < 1 →
          AEOsBound P (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) s
            (D * r ^ (-(min (α * (1 + δ) + δ) ((d : ℝ) / s) - η)))

/-- **The localized field of one localized family**: the estimate of the localized energies of a
localized family `W` for `r ≥ 2` gives `LocFieldEstimateAt` with the localized field `J₁^{(δ)}` of
`W`; below `r = 2` the localized energy is zero and `|J| ≤ |Λ| + 1`. -/
theorem locFieldEstimateAt_of_localizedFamily (hΛ0 : 0 ≤ Λ) {s δ γ αc σ θ C₀ D : ℝ}
    (hs0 : 0 < s) (hσ : 0 < σ) (hθ : 0 < θ) (hC₀ : 0 < C₀) (hD : 0 < D)
    {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ} (hJ : IsBoundedJointVersion P J)
    (W : LocalizedFamily d Λ δ γ αc σ θ C₀)
    (hloc : ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      AEOsBound P (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) s
        (D * r ^ (-γ))) :
    LocFieldEstimateAt P localSigma J s δ γ (max D ((|Λ| + 1) * 2 ^ |γ| / Real.log 2 ^ s⁻¹)) := by
  have hL : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have h2γ : (0 : ℝ) < 2 ^ |γ| := Real.rpow_pos_of_pos two_pos _
  intro r hr p q hp hq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hfm : Measurable fun w : CoefficientField d Λ × Vec d => familyJ1 W w.1 w.2 r p q := by
    have h := measurable_indicator_familyJ1 hΛ0 hσ hθ hC₀ W r p q MeasurableSet.univ
      (fun x _ => Set.subset_univ (ball x (localizationOuterRadius δ r)))
    simp only [Set.indicator_univ] at h
    exact measurable_prod_of_le (localSigma_le _) h
  refine ⟨fun a x => familyJ1 W a x r p q, fun U hU => ?_, fun z => ?_⟩
  · exact measurable_indicator_familyJ1 hΛ0 hσ hθ hC₀ W r p q hU fun x hx y hy => ⟨x, hx, hy⟩
  have hJz : Measurable fun a : CoefficientField d Λ => J a z r p q :=
    (hJ.measurable_slice r p q).comp (measurable_id.prodMk measurable_const)
  have hfz : Measurable fun a : CoefficientField d Λ => familyJ1 W a z r p q := by
    have h := hfm.comp (measurable_id.prodMk (measurable_const (a := z)))
    exact h
  have hm : Measurable fun a => |J a z r p q - familyJ1 W a z r p q| := (hJz.sub hfz).abs
  by_cases hr2 : 2 ≤ r
  · refine ((hloc z r hr2 p q hp hq).osBound_of_ae_eq hm ?_).mono_scale
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr0.le _))
    filter_upwards [hJ.2.2] with a ha
    show |J1Heat a z r p q - localizedJ1 (W a z r hr2) r p q| =
      |J a z r p q - familyJ1 W a z r p q|
    rw [ha z r p q]
    simp [familyJ1, hr2]
  · have h0 : ∀ a, familyJ1 W a z r p q = 0 := fun a => by simp [familyJ1, hr2]
    have hb : ∀ᵐ a ∂P, |J a z r p q - familyJ1 W a z r p q| ≤ |Λ| + 1 :=
      Eventually.of_forall fun a => by rw [h0, sub_zero]; exact hJ.2.1 a z r p q hp hq
    have hc := osBound_of_le_const hm hs0 (by positivity : (0 : ℝ) < |Λ| + 1) hb
    refine hc.mono_scale ?_
    have hr2' : r ≤ 2 := (not_le.mp hr2).le
    have h1 : r ^ (-|γ|) ≤ r ^ (-γ) :=
      Real.rpow_le_rpow_of_exponent_le hr (by linarith [le_abs_self γ])
    have h2 : (2 : ℝ) ^ (-|γ|) ≤ r ^ (-|γ|) :=
      Real.rpow_le_rpow_of_nonpos hr0 hr2' (by linarith [abs_nonneg γ])
    have he : (|Λ| + 1) / Real.log 2 ^ s⁻¹ =
        (|Λ| + 1) * 2 ^ |γ| / Real.log 2 ^ s⁻¹ * 2 ^ (-|γ|) := by
      rw [Real.rpow_neg two_pos.le]
      field_simp
    rw [he]
    exact mul_le_mul (le_max_right _ _) (h2.trans h1) (Real.rpow_nonneg two_pos.le _)
      (le_max_of_le_left hD.le)

/-- **Proposition 4.11 with constants chosen before the law** from the estimate of the localized
energies: the localized field is the localized energy of one localized family, jointly local by
`measurable_indicator_familyJ1`. -/
theorem uniformLocalizationEstimates_of_pilot (hΛ : 1 < Λ) (h : PilotLocalizationEstimates d Λ) :
    UniformLocalizationEstimates d Λ := by
  intro s α δ η C hs1 hs2 hα0 hα hδ hη hC
  obtain ⟨αc, σ, θ, C₀, D, hσ, hθ, hC₀, hD, hloc⟩ := h s α δ η C hs1 hs2 hα0 hα hδ hη hC
  obtain ⟨W⟩ := nonempty_localizedFamily d Λ δ (min (α * (1 + δ) + δ) ((d : ℝ) / s) - η) αc hσ hθ
    hC₀.le
  refine ⟨max D ((|Λ| + 1) * 2 ^ |min (α * (1 + δ) + δ) ((d : ℝ) / s) - η| /
    Real.log 2 ^ s⁻¹), lt_max_of_lt_left hD, fun P hP J hJ hF => ?_⟩
  have := hP.1
  exact locFieldEstimateAt_of_localizedFamily (by linarith) (by linarith) hσ hθ hC₀ hD hJ W
    (hloc P hP J hJ hF W)

/-- **The inputs of the bootstrap from Proposition 3.21, the heat identity (H) and the estimate
of the localized energies**, all with constants chosen before the law. -/
theorem bootstrapInputs_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ ∧
      UniformExpectationEstimates d Λ :=
  bootstrapInputs_of_rate_heat_localization hrate hH fun d hd Λ hΛ =>
    uniformLocalizationEstimates_of_pilot hΛ (hloc d hd Λ hΛ)

/-! ## The frozen statements from the three remaining inputs -/

/-- **Theorem 4.6 (i) with constants chosen before the law** from Proposition 3.21, the heat
identity (H) and the localized energy estimates, with constants chosen before the law. -/
theorem uniformAdditivityJ1_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    UniformAdditivityJ1 :=
  uniformAdditivityJ1_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The Gaussian gradient bound with constants chosen before the law** from Proposition 3.21,
the heat identity (H) and the localized energy estimates, with constants chosen before the law. -/
theorem uniformLinearAverageEstimate_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    UniformLinearAverageEstimate :=
  uniformLinearAverageEstimate_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`QSH.Frozen.negativeSobolevCorrector` (E7)** from Proposition 3.21, the heat identity (H) and
the localized energy estimates, with constants chosen before the law. -/
theorem negativeSobolevCorrector_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    QSH.Frozen.negativeSobolevCorrector :=
  negativeSobolevCorrector_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`QSH.Frozen.averagedCorrectorGradient` (E1)** from Proposition 3.21, the heat identity (H)
and the localized energy estimates, with constants chosen before the law. -/
theorem averagedCorrectorGradient_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    QSH.Frozen.averagedCorrectorGradient :=
  averagedCorrectorGradient_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`QSH.Frozen.blockCLT` (E4)** from Proposition 3.21, the heat identity (H) and the localized
energy estimates, with constants chosen before the law. -/
theorem blockCLT_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    QSH.Frozen.blockCLT :=
  blockCLT_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`QSH.Frozen.blockBoundary` (E2)** from Proposition 3.21, the heat identity (H) and the
localized energy estimates, with constants chosen before the law. -/
theorem blockBoundary_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    QSH.Frozen.blockBoundary :=
  blockBoundary_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`QSH.Frozen.blockChange` (E3)** from Proposition 3.21, the heat identity (H) and the
localized energy estimates, with constants chosen before the law. -/
theorem blockChange_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    QSH.Frozen.blockChange :=
  blockChange_of_uniform_inputs fun d hd Λ hΛ =>
    let h := bootstrapInputs_of_rate_heat_pilot hrate hH hloc d hd Λ hΛ
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **(5.58) with a constant chosen before the law** (the hypothesis `h558` of
`coarsenedCoefficientEstimates_of_energyEstimate_liouville`) from Proposition 3.21, the heat
identity (H) and the localized energy estimates, with constants chosen before the law. -/
theorem uniformEnergyEstimate_of_rate_heat_pilot
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀ :=
  uniformEnergyEstimate_of_uniform_inputs (bootstrapInputs_of_rate_heat_pilot hrate hH hloc)

end QSH
