import QuantitativeStochasticHomogenization.Ch04.Sec03.HomogenizedBoundsFromAverages

/-!
# The linear estimate and Lemma 4.13 at the optimal exponent `d/2`

Under the inputs of `estimate558_of_heatBound_and_rate`, Theorem 4.6 (i) gives `Fluc(s, d/2)` for
every `s ∈ (0, 2)` (`flucJ1_half_dim_of_heat`), and then Lemma 4.13 and the linear estimate of
Step 1 hold at the exponent `d/2`: `|∫ Φ_{z,r} (a - ā)(eⱼ + ∇φ_{eⱼ})| ≤ O_s(C r^{-d/2})` and
`|∫ Φ_{z,r} G ξ - ξ| ≤ O_s(C (1 + |ξ|) r^{-d/2})` (`linearAverageEstimate_half_dim`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Optimal

variable {P : Measure (CoefficientField d Λ)}

/-- The consequences of Proposition 3.21 and of the expectations (1) used below: the bounds on
`ā`, the energy bound below the scale at every exponent, and the integrability of the averages
and of the trial. -/
theorem inputs_of_rate_and_expectations [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β) :
    HomogenizedMatrixBounds S.homogenized Λ ∧
      (∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN) ∧
      AveragesIntegrable P S ∧ TrialIntegrable P S := by
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdr : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK⟩ := exists_dot_mulVec_le S.homogenized
  obtain ⟨C1, μ1, -, hμ1, hr1⟩ := hrate 1 one_pos hdr
  obtain ⟨CN1, -, hN1⟩ := gaussianEnergyBound_of_rate S hK one_pos hμ1.le hr1
  have hint := averagesIntegrable_of_energyBound S hΛ.le hN1
  have hA := homogenizedMatrixBounds_of_expectedAverages S hΛ.le hint one_pos (hexp 1 one_pos hd1')
  refine ⟨hA, fun τ hτ0 hτd => ?_, hint, trialIntegrable_of_energyBound S hΛ.le hN1⟩
  obtain ⟨C, μ, -, hμ', hr⟩ := hrate τ hτ0 hτd
  exact gaussianEnergyBound_of_rate S (fun ξ => (hA ξ).2) hτ0 hμ'.le hr

/-- **Lemma 4.13 and the linear estimate under `Fluc(s, α)`** from the inputs of
`estimate558_of_heatBound_and_rate`. -/
theorem linearAverageEstimate_of_flucJ1_heat [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck) {s α : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (hα0 : 0 < α) (hα : α ≤ (d : ℝ) / 2) (hF : FlucJ1 P s α) :
    CommutatorEstimate P S s α ∧ LinearAverageEstimate P S s α := by
  have hd1 : 1 ≤ d := by omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨hA, hN, hint, -⟩ := inputs_of_rate_and_expectations hd S hΛ hrate hexp
  have hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d),
      Measurable (fun a => gradientAverage S a z r ξ) ∧
        Measurable (fun a => fluxAverage S a z r ξ) := fun z r ξ =>
    ⟨measurable_gradientAverage S z r ξ, measurable_fluxAverage_of S hmeasF z r ξ⟩
  have hC := commutatorEstimate_of_flucJ1 hd1 S hΛ hA hspan hmeasJ hrate hN hexp hint hmeasA hs0
    hs2 hα0 hα hF
  set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s ≤ τ / ((d : ℝ) / 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hτ1
  obtain ⟨CN, -, hNτ⟩ := hN τ hτ0 hτ2
  exact ⟨hC, linearAverageEstimate_of_heat hd1 S hΛ.le hs0 hα0 hC hheat
    (measurable_commutatorNorm S hmeasF) (fun z r ξ => (hmeasA z r ξ).1) hNτ hτs hint⟩

/-- **Theorem 4.6 (i), `Fluc(s, d/2)`**, from the inputs of `estimate558_of_heatBound_and_rate`. -/
theorem flucJ1_half_dim_of_heat [IsProbabilityMeasure P] (hd : 2 ≤ d) (S : HomogenizationData P)
    (hΛ : 0 < Λ) (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (hmeasF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    FlucJ1 P s ((d : ℝ) / 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hA, hN, hint, htrial⟩ := inputs_of_rate_and_expectations hd S hΛ hrate hexp
  obtain ⟨h410, -⟩ := proposition410_of_linearAverages hd1 S hΛ.le hA hspan hrate hN htrial hmeasJ
    hmeasL (fun s' α hs0' hs2' hα0 hα hF => (linearAverageEstimate_of_flucJ1_heat hd S hΛ hspan
      hrate hexp hmeasJ hmeasF hheat hs0' hs2' hα0 hα hF).2)
    (fun β hβ hβd => trialObjectiveExpectation_of_expectedAverages S hint (hexp β hβ hβd))
  have hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d),
      Measurable fun a : CoefficientField d Λ => J1Heat a z r p q := fun z r p q =>
    (hmeasJ r p q).comp (measurable_id.prodMk measurable_const)
  have hrate' : ∀ s : ℝ, 1 < s → s < 2 → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S s C μ := fun s hs1 hs2 =>
    hrate s (by linarith) (by linarith)
  exact (additiveStructure_of_bootstrap hd1 h410 h411 h412 (flucJ1_base S hA hspan hrate' hmeas)
    hs0 hs2).1

/-- **Lemma 4.13 and the linear estimate at the exponent `d/2`** from the inputs of
`estimate558_of_heatBound_and_rate`. -/
theorem linearAverageEstimate_half_dim [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 < Λ) (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (hmeasF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    CommutatorEstimate P S s ((d : ℝ) / 2) ∧ LinearAverageEstimate P S s ((d : ℝ) / 2) := by
  have hd0 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact linearAverageEstimate_of_flucJ1_heat hd S hΛ hspan hrate hexp hmeasJ hmeasF hheat hs0 hs2
    hd0 le_rfl (flucJ1_half_dim_of_heat hd S hΛ hspan hrate hexp hmeasJ hmeasL hmeasF hheat h411
      h412 hs0 hs2)

end Optimal

end QSH
