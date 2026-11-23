import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationUniform
import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationEstimateReduction

/-!
# Proposition 4.11 at the exponents of the bootstrap from the single-slope estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, Proposition 4.11 with Lemmas 4.21 and 4.22, at the intermediate exponents of the
bootstrap of Theorem 4.6.

The reduction of (5.85) to the single-slope estimate of Lemma 4.21 (`LocalizationSlopeEstimate`,
through `LocalizationCorrectorSlopeEstimate`, `LocalizationInnerSlopeEstimate`,
`LocalizationBallGrowthEstimate` and `LocalizationApproximationUniform`) uses the law only through
the single-slope estimate itself. It holds for every class `L` of laws satisfying the assumptions
(`LocalizationSlopeEstimateOn L`, ...), with the constants chosen before the law
(`localizationEstimateOn_of_slopeOn`).

The bootstrap applies it to the class `FlucLaw s α C` of the laws for which a bounded jointly
measurable version of `J₁` satisfies `Fluc(s, α)` with constant `C`: the single-slope estimate on
these classes at `γ = (α(1+δ) + δ) ∧ d/s - η` gives `PilotLocalizationEstimates`
(`pilotLocalizationEstimates_of_slopeOn`; for `γ ≤ 0` the localization error is bounded by
`localizationCap d Λ`). Under the Gaussian inputs, `Fluc(s, α)` gives the linear estimate at
`(s, α)` with a constant chosen before the law (Lemma 4.13 and the heat identity,
`exists_uniform_commutator_linear`), so the single-slope estimate is needed only on the classes
`LinearLaw s α C` of the laws with the linear estimate at `(s, α)`
(`LinearSlopeEstimates`, `pilotLocalizationEstimates_of_gaussianInputs_slopeOn`).

With Proposition 3.21 and the heat identity (H) with constants chosen before the law, the
single-slope estimate on these classes gives the Gaussian gradient bound, hence every law is in a
class `LinearLaw s (d/2) C`, and (5.85) follows (`localizedEnergy_of_rate_heat_slope`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The single-slope estimate is monotone in the class of laws. -/
theorem LocalizationSlopeEstimateOn.mono {L L' : Measure (CoefficientField d Λ) → Prop}
    (hLL : ∀ P, L P → L' P) {s δ γ α σ θ C₀ : ℝ}
    (h : LocalizationSlopeEstimateOn L' s δ γ α σ θ C₀) :
    LocalizationSlopeEstimateOn L s δ γ α σ θ C₀ := by
  obtain ⟨c, K₁, C₁, hc, hc1, hK₁, hC₁, hmain⟩ := h
  exact ⟨c, K₁, C₁, hc, hc1, hK₁, hC₁, fun P hP => hmain P (hLL P hP)⟩

/-- The localization error is almost surely measurable for every law and localized family. -/
theorem aemeasurable_abs_J1Heat_sub_localizedJ1 (hΛ : 0 ≤ Λ) {δ γ α σ θ C₀ : ℝ} (hσ : 0 < σ)
    (hθ : 0 < θ) (hC₀ : 0 < C₀) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d) :
    AEMeasurable (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) P := by
  have h1 := aemeasurable_J1Heat_of_lawHypotheses d Λ P hP z r p q hr
  have h2 : Measurable fun a => localizedJ1 (W a z r hr) r p q :=
    (measurable_localizedJ1_of_localizedFamily hΛ hσ hθ hC₀ W z r hr p q).mono
      (localSigma_le_measurableSpace _) le_rfl
  exact (h1.sub h2.aemeasurable).abs

/-- **Lemmas 4.21 and 4.22 for a class of laws, with constants chosen before the law**: the
single-slope estimate on a class `L` of laws satisfying the assumptions gives
`|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)| ≤ O_s(C r^{-γ})` for every law of `L`, every localized
family and `r ≥ 2`, with one constant `C`. -/
theorem localizationEstimateOn_of_slopeOn (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {L : Measure (CoefficientField d Λ) → Prop} (hLP : ∀ P, L P → LawHypotheses P)
    {s δ γ α σ θ C₀ : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hα : 0 < α)
    (hαγ : γ < α * (1 + δ) + δ) (hγ : 0 < γ) (hγs : s * γ < d) (hσ : 0 < σ) (hθ : 0 < θ)
    (hC₀ : 0 < C₀) (h : LocalizationSlopeEstimateOn L s δ γ α σ θ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), L P →
      ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        AEOsBound P (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) s
          (C * r ^ (-γ)) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨C, hC, happ⟩ := localizationApproximationUniformOn_of_ballGrowthOn hLP (by omega) hΛ0
    hs hδ hγ.le (localizationBallGrowthEstimateOn_of_innerSlopeOn hδ hα hαγ
      (localizationInnerSlopeEstimateOn_of_correctorSlopeOn firstOrderLiouville hd hΛ hLP
        (localizationCorrectorSlopeEstimateOn_of_slopeOn hd hΛ hLP hs hδ hγ hγs h)))
  refine ⟨C, hC, fun P hLP' W z r hr p q hp hq => ?_⟩
  obtain ⟨Z, hZ, hae⟩ := happ P hLP' W z r hr p q hp hq
  refine AEOsBound.of_le (aemeasurable_abs_J1Heat_sub_localizedJ1 hΛ0 hσ hθ hC₀ (hLP P hLP') W
    z r hr p q) hZ ?_
  filter_upwards [hae] with a ha
  rcases ha with ⟨η, κ, ha⟩ | ha
  · exact abs_J1Heat_sub_localizedJ1_le_of_approximationAt hΛ0 _ (ha.toAt' hΛ0).toAt
  · exact ha

/-- For `γ ≤ 0` the localization error is bounded by `localizationCap d Λ`, so it is
`O_s(C r^{-γ})` with `C = localizationCap d Λ / (log 2)^{1/s}` for every law. -/
theorem localizationEstimate_of_nonpos (hΛ : 0 ≤ Λ) {s δ γ α σ θ C₀ : ℝ} (hs : 0 < s)
    (hγ : γ ≤ 0) (hσ : 0 < σ) (hθ : 0 < θ) (hC₀ : 0 < C₀) {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ)
    (hr : 2 ≤ r) (p q : Vec d) (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    AEOsBound P (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) s
      (localizationCap d Λ / Real.log 2 ^ s⁻¹ * r ^ (-γ)) := by
  have : IsProbabilityMeasure P := hP.1
  have hr0 : 0 < r := by linarith
  have hcap := localizationCap_pos (d := d) hΛ
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have hc : AEOsBound P (fun _ => localizationCap d Λ) s
      (localizationCap d Λ / Real.log 2 ^ s⁻¹) :=
    (osBound_of_le_const measurable_const hs hcap
      (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl
  refine (AEOsBound.of_le (aemeasurable_abs_J1Heat_sub_localizedJ1 hΛ hσ hθ hC₀ hP W z r hr p q)
    hc (Eventually.of_forall fun a =>
      abs_J1Heat_sub_localizedJ1_le_cap hΛ hr0 (W a z r hr) hp.le hq.le)).mono_scale ?_
  have h1 : 1 ≤ r ^ (-γ) := Real.one_le_rpow (by linarith) (by linarith)
  have h2 : 0 ≤ localizationCap d Λ / Real.log 2 ^ s⁻¹ := by positivity
  nlinarith

/-- The laws satisfying the assumptions for which a bounded jointly measurable version of `J₁`
satisfies `Fluc(s, α)` with constant `C`. -/
def FlucLaw (s α C : ℝ) (P : Measure (CoefficientField d Λ)) : Prop :=
  LawHypotheses P ∧ ∃ J, IsBoundedJointVersion P J ∧ FlucEstimateAt P J s α C

/-- The laws satisfying the assumptions with a homogenization data satisfying the linear
estimate at `(s, β)` with constant `C`. -/
def LinearLaw (s β C : ℝ) (P : Measure (CoefficientField d Λ)) : Prop :=
  LawHypotheses P ∧ ∃ S : HomogenizationData P, LinearAverageEstimateAt P S s β C

/-- The exponent of the bootstrap is below the two caps of Proposition 4.11. -/
theorem pilot_exponent_bounds {s α δ η : ℝ} (hs : 0 < s) (hη : 0 < η) :
    min (α * (1 + δ) + δ) ((d : ℝ) / s) - η < α * (1 + δ) + δ ∧
      s * (min (α * (1 + δ) + δ) ((d : ℝ) / s) - η) < d := by
  have h1 := min_le_left (α * (1 + δ) + δ) ((d : ℝ) / s)
  have h2 := min_le_right (α * (1 + δ) + δ) ((d : ℝ) / s)
  refine ⟨by linarith, ?_⟩
  have h3 : s * min (α * (1 + δ) + δ) ((d : ℝ) / s) ≤ d :=
    calc s * min (α * (1 + δ) + δ) ((d : ℝ) / s) ≤ s * ((d : ℝ) / s) :=
          mul_le_mul_of_nonneg_left h2 hs.le
      _ = d := by field_simp
  have h4 : 0 < s * η := mul_pos hs hη
  rw [mul_sub]
  linarith

/-- **Proposition 4.11 at the exponents of the bootstrap from the single-slope estimate** on the
classes `FlucLaw s α C`, with the structural constants and the constant of the estimate chosen
before the law. -/
theorem pilotLocalizationEstimates_of_slopeOn (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (h : ∀ s α δ γ C : ℝ, 1 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 → 0 < δ → 0 < γ →
      γ < α * (1 + δ) + δ → s * γ < d → 0 < C →
      ∃ σ θ C₀ : ℝ, 0 < σ ∧ 0 < θ ∧ 0 < C₀ ∧
        LocalizationSlopeEstimateOn (FlucLaw (d := d) (Λ := Λ) s α C) s δ γ α σ θ C₀) :
    PilotLocalizationEstimates d Λ := by
  intro s α δ η C hs1 hs2 hα0 hα hδ hη hC
  have hs0 : 0 < s := by linarith
  obtain ⟨hαγ, hγs⟩ := pilot_exponent_bounds (d := d) (α := α) (δ := δ) hs0 hη
  by_cases hγ : 0 < min (α * (1 + δ) + δ) ((d : ℝ) / s) - η
  · obtain ⟨σ, θ, C₀, hσ, hθ, hC₀, hslope⟩ := h s α δ _ C hs1 hs2 hα0 hα hδ hγ hαγ hγs hC
    obtain ⟨D, hD, hest⟩ := localizationEstimateOn_of_slopeOn hd hΛ (fun P hP => hP.1) hs1.le
      hδ hα0 hαγ hγ hγs hσ hθ hC₀ hslope
    exact ⟨α, σ, θ, C₀, D, hσ, hθ, hC₀, hD, fun P hP J hJ hF => hest P ⟨hP, J, hJ, hF⟩⟩
  · have hΛ0 : 0 ≤ Λ := by linarith
    have hcap := localizationCap_pos (d := d) hΛ0
    have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
    exact ⟨α, 1, 1, 1, localizationCap d Λ / Real.log 2 ^ s⁻¹, one_pos, one_pos, one_pos,
      by positivity, fun P hP _ _ _ W z r hr p q hp hq =>
        localizationEstimate_of_nonpos hΛ0 hs0 (not_lt.mp hγ) one_pos one_pos one_pos hP W z r
          hr p q hp hq⟩

/-- **The single-slope estimate of Lemma 4.21 on the classes of laws with the linear estimate**:
for `s ∈ (1, 2)`, `α ∈ (0, d/2]`, `δ > 0`, `0 < γ < α(1+δ) + δ` with `sγ < d` and `C > 0`, there are
structural constants `σ, θ ∈ (0, 1/2]`, `C₀ > 0` with the single-slope estimate on the class
`LinearLaw s α C`. -/
def LinearSlopeEstimates (d : ℕ) (Λ : ℝ) : Prop :=
  ∀ s α δ γ C : ℝ, 1 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 → 0 < δ → 0 < γ →
    γ < α * (1 + δ) + δ → s * γ < d → 0 < C →
    ∃ σ θ C₀ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
      LocalizationSlopeEstimateOn (LinearLaw (d := d) (Λ := Λ) s α C) s δ γ α σ θ C₀

/-- **Proposition 4.11 at the exponents of the bootstrap from the Gaussian inputs and the
single-slope estimate** on the classes `LinearLaw s α C`: under the Gaussian inputs, `Fluc(s, α)`
for a bounded jointly measurable version of `J₁` gives the linear estimate at `(s, α)` with a
constant chosen before the law (`exists_uniform_commutator_linear`, at `τ = (s d/2 + d)/2`). -/
theorem pilotLocalizationEstimates_of_gaussianInputs_slopeOn (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hG : UniformGaussianInputs d Λ) (h : LinearSlopeEstimates d Λ) :
    PilotLocalizationEstimates d Λ := by
  obtain ⟨Cr, μ, CE, Ck, hCE, hCμ, hG⟩ := hG
  refine pilotLocalizationEstimates_of_slopeOn hd hΛ
    fun s α δ γ C hs1 hs2 hα0 hα hδ hγ hαγ hγs hC => ?_
  have hs0 : 0 < s := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb2 : 0 < (d : ℝ) / 2 := by linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (s * ((d : ℝ) / 2) + d) / 2 := ⟨_, rfl⟩
  have hτ1 : s * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s ≤ τ / ((d : ℝ) / 2) := by rw [le_div_iff₀ hb2]; exact hτ1
  obtain ⟨hCτ, hμτ⟩ := hCμ τ hτ0 hτ2
  obtain ⟨_, Cl, _, hCl, hlin⟩ := exists_uniform_commutator_linear (Ck := Ck) hd hΛ
    hs0 hα0 hα hC hτ0 hCτ hμτ hCE hτs
  obtain ⟨σ, θ, C₀, hσ, -, hθ, -, hC₀, hslope⟩ := h s α δ γ Cl hs1 hs2 hα0 hα hδ hγ hαγ hγs hCl
  refine ⟨σ, θ, C₀, hσ, hθ, hC₀, hslope.mono fun P hP => ⟨hP.1, ?_⟩⟩
  obtain ⟨hPl, J, hJ, hF⟩ := hP
  obtain ⟨S, hH, hE, hr⟩ := hG P hPl
  exact ⟨S, (hlin P hPl S J hJ.measurable_slice hJ.2.2 hF (hr τ hτ0 hτ2)
    (hE.mono hCE.le (by linarith)) hH).2⟩

/-! ## The frozen statements from Proposition 3.21, the heat identity and the single-slope
estimate -/

/-- **Proposition 4.11 at the exponents of the bootstrap** from Proposition 3.21, the heat
identity (H) and the single-slope estimate on the classes `LinearLaw`, all with constants chosen
before the law. -/
theorem pilotLocalizationEstimates_of_rate_heat_slope
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hS : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → LinearSlopeEstimates d Λ) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ := fun d hd Λ hΛ =>
  pilotLocalizationEstimates_of_gaussianInputs_slopeOn hd hΛ
    (uniformGaussianInputs_of_rate_heat hd hΛ (hrate d hd Λ hΛ) (hH d hd Λ hΛ)) (hS d hd Λ hΛ)

/-- **`QSH.Frozen.localizedEnergy` (E6)** from Proposition 3.21, the heat identity (H) and the
single-slope estimate on the classes `LinearLaw`, all with constants chosen before the law: the
bootstrap gives the Gaussian gradient bound, i.e. every law satisfying the assumptions is in a class
`LinearLaw s (d/2) C` with `C` chosen before the law, and the single-slope estimate at `α = d/2`
on this class is `LocalizationSlopeEstimate` (`localizedEnergy_of_slope`). -/
theorem localizedEnergy_of_rate_heat_slope
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (hS : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → LinearSlopeEstimates d Λ) :
    QSH.Frozen.localizedEnergy := by
  have hG := uniformLinearAverageEstimate_of_rate_heat_pilot hrate hH
    (pilotLocalizationEstimates_of_rate_heat_slope hrate hH hS)
  refine localizedEnergy_of_slope firstOrderLiouville
    fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => ?_
  have hs0 : 0 < s := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb2 : 0 < (d : ℝ) / 2 := by linarith
  have hγ0 : 0 < γ := lt_of_le_of_lt (by positivity) hγ1
  have hαγ : γ < (d : ℝ) / 2 * (1 + δ) + δ := lt_of_lt_of_le hγ2 (min_le_right _ _)
  have hγs : s * γ < d := by
    have h1 : γ < (d : ℝ) / s := lt_of_lt_of_le hγ2 (min_le_left _ _)
    rw [lt_div_iff₀ hs0] at h1
    linarith
  obtain ⟨Cl, hCl, hlin⟩ := hG d hd Λ s hΛ hs0 hs2
  obtain ⟨σ, θ, C₀, hσ, hσ2, hθ, hθ2, hC₀, hslope⟩ :=
    hS d hd Λ hΛ s ((d : ℝ) / 2) δ γ Cl hs1 hs2 hb2 le_rfl hδ hγ0 hαγ hγs hCl
  exact ⟨(d : ℝ) / 2, σ, θ, C₀, hb2, le_rfl, hαγ, hσ, hσ2, hθ, hθ2, hC₀,
    hslope.mono (L := LawHypotheses) fun P hP => ⟨hP, hlin P hP⟩⟩

end QSH
