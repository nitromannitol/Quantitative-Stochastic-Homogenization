import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapEstimate

/-!
# Proposition 4.10 from the linear estimate of Step 1

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10 and Remark 4.18, and Section 5.3, (5.58).

`proposition410_of_linearAverages`: the conclusion of Proposition 4.10 and (4.70) from

* the linear estimate of Step 1 under `Fluc(s, α)` (`LinearAverageEstimate`);
* the expectation of the trial at deterministic slopes (`TrialObjectiveExpectation`);
* the energy of the corrected fields below the scale (`GaussianEnergyBound`) and Proposition 3.21
  (`GaussianCorrectorRate`), at every exponent `τ ∈ (0, d)`;
* the structure (4.12) of `A₁`, the bounds on `ā`, the almost sure integrability of the trial and
  the measurability of `J₁` and of the trial.

`estimate558_of_linearAverages`: (5.58) and Theorem 4.6 (ii) from the same inputs and the
conclusions of Propositions 4.11 and 4.12.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Linear

variable {P : Measure (CoefficientField d Λ)}

/-- The expectation of the trial at deterministic slopes gives the expectation of the trial at the
homogenized slope, with the constant `5 C`. -/
theorem trialExpectationEstimateAt_of_objective (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) {β C : ℝ} (hC : 0 < C)
    (hE : TrialObjectiveExpectationAt P S β C) : TrialExpectationEstimateAt P S β (5 * C) := by
  have hdet : IsUnit S.homogenized.det := isUnit_det_of_coercive fun ξ => (hA ξ).1
  intro z r hr p q hp hq
  obtain ⟨hi, hb⟩ := hE z r hr p q hp hq (homogenizedSlope S.homogenized p q)
  have hhc : homogenizedJ1Objective S.homogenized p q (homogenizedSlope S.homogenized p q) =
      homogenizedJ1 S.homogenized p q := by
    rw [homogenizedJ1Objective_eq S.symmetric hdet]
    simp [homogenizedSlope, dot]
  have hc4 := euclideanSq_homogenizedSlope_le (fun ξ => (hA ξ).1) hp.le hq.le
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hρ : 0 ≤ r ^ (-β) := Real.rpow_nonneg hr0.le _
  refine ⟨hi, ?_⟩
  rw [← hhc]
  refine hb.trans ?_
  have : C * (1 + euclideanSq (homogenizedSlope S.homogenized p q)) ≤ 5 * C := by nlinarith
  exact mul_le_mul_of_nonneg_right this hρ

/-- The expectation of the trial at deterministic slopes gives the expectation of the trial at the
homogenized slope. -/
theorem trialExpectationEstimate_of_objective (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) {β : ℝ}
    (hE : TrialObjectiveExpectation P S β) : TrialExpectationEstimate P S β := by
  obtain ⟨C, hC, hE⟩ := hE
  exact ⟨5 * C, by positivity, trialExpectationEstimateAt_of_objective S hA hC hE⟩

/-- **Proposition 4.10** (with (4.70)) from the linear estimate of Step 1 and the inputs listed in
the module docstring. -/
theorem proposition410_of_linearAverages [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN)
    (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (h4 : ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
      FlucJ1 P s α → LinearAverageEstimate P S s α)
    (hE : ∀ β : ℝ, 0 < β → β ≤ d → TrialObjectiveExpectation P S β) :
    ImprovementOfAdditivity P J1Heat ∧ ExpectationEstimates P S.homogenized := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine proposition410 hd S hA hspan hrate htrial hmeasJ ?_ fun β hβ hβd =>
    trialExpectationEstimate_of_objective S hA (hE β hβ hβd)
  intro s α hs0 hs2 hα0 hα hF
  set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s * ((d : ℝ) / 2) < τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ1
  obtain ⟨C, μ, hC, hμ, hr⟩ := hrate τ hτ0 hτ2
  obtain ⟨CN, hCN, hNτ⟩ := hN τ hτ0 hτ2
  exact trialGapEstimate_of_linearAverages S hΛ hA hspan hmeasJ hmeasL hd hs0 hα hτ1 hC hμ hCN
    hr hNτ hF (h4 s α hs0 hs2 hα0 hα hF) (hE (2 * α) (by positivity) (by linarith))

/-- **(5.58) and Theorem 4.6 (ii)** from the linear estimate of Step 1, the inputs of
`proposition410_of_linearAverages` and the conclusions of Propositions 4.11 and 4.12. -/
theorem estimate558_of_linearAverages [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN)
    (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (h4 : ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
      FlucJ1 P s α → LinearAverageEstimate P S s α)
    (hE : ∀ β : ℝ, 0 < β → β ≤ d → TrialObjectiveExpectation P S β)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨h410, hbias⟩ := proposition410_of_linearAverages hd1 S hΛ hA hspan hrate hN htrial
    hmeasJ hmeasL h4 hE
  have hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d),
      Measurable fun a : CoefficientField d Λ => J1Heat a z r p q := fun z r p q =>
    (hmeasJ r p q).comp (measurable_id.prodMk measurable_const)
  have hrate' : ∀ s : ℝ, 1 < s → s < 2 → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S s C μ := fun s hs1 hs2 =>
    hrate s (by linarith) (by linarith)
  exact estimate558 hd1 S hA hspan hrate' hmeas h410 hbias h411 h412 hs0 hs2

end Linear

end QSH
