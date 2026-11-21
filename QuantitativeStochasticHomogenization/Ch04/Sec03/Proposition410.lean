import QuantitativeStochasticHomogenization.Ch04.Sec03.ImprovedAdditivity

/-!
# Proposition 4.10 from the quadratic response at the deterministic slope

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10 and Remark 4.18, and Section 5.3, (5.58).

`proposition410`: the conclusion `ImprovementOfAdditivity` of Proposition 4.10 for `J₁` and the
expectation estimate (4.70), from

* the quadratic response at the deterministic slope: `Fluc(s, α)` implies the trial gap estimate
  `O_{s/2}(C r^{-2α})` (`TrialGapEstimate`), for `s ∈ (0, 2)` and `α ∈ (0, d/2]`;
* the expectation of the trial: `TrialExpectationEstimate` at every rate `β ∈ (0, d]`;
* the inputs of Proposition 4.3 (the structure (4.12) of `A₁`, the bounds on `ā`, Proposition 3.21
  at every exponent `τ ∈ (0, d)`), the almost sure integrability of the trial and the joint
  measurability of `J₁`.

The exponent is `η = min(μ/2, τ/s - d/2)` with `τ` the midpoint of `(s d/2, d)` and `μ` the rate of
Proposition 3.21 at `τ`.

`estimate558_of_trialGap`: (5.58) and Theorem 4.6 (ii) from the same inputs and the conclusions of
Propositions 4.11 and 4.12.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

section Proposition410

variable {P : Measure (CoefficientField d Λ)}

/-- **Proposition 4.10** (with the expectation estimate (4.70) of Remark 4.18) from the quadratic
response at the deterministic slope, the expectation of the trial and the inputs of
Proposition 4.3. -/
theorem proposition410 [IsProbabilityMeasure P] (hd : 1 ≤ d) (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hcore : ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
      FlucJ1 P s α → TrialGapEstimate P S (s / 2) (2 * α))
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → TrialExpectationEstimate P S β) :
    ImprovementOfAdditivity P J1Heat ∧ ExpectationEstimates P S.homogenized := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨fun s hs0 hs2 => ?_, fun s α hs0 hs2 hα0 hα hF => ?_⟩
  · set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
    have hτ1 : s * ((d : ℝ) / 2) < τ := by rw [hτ]; nlinarith
    have hτ2 : τ < d := by rw [hτ]; nlinarith
    have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ1
    obtain ⟨C, μ, hC, hμ, hr⟩ := hrate τ hτ0 hτ2
    have hκ : (d : ℝ) / 2 < τ / s := by rw [lt_div_iff₀ hs0]; linarith
    refine ⟨min (μ / 2) (τ / s - (d : ℝ) / 2), lt_min (by positivity) (by linarith),
      fun α hα0 hα hF => ⟨?_, ?_⟩⟩
    · exact addJ1_improved_of_trialGap S hA hspan htrial hmeasJ hs0 hα hτ1 hC hμ hr
        (hcore s α hs0 hs2 hα0 hα hF)
    · exact addJ1_of_trialGapEstimate S hspan htrial hmeasJ (hcore s α hs0 hs2 hα0 hα hF)
  · exact expectationJ1Estimate_of_trialGap S hspan (hcore s α hs0 hs2 hα0 hα hF)
      (hexp (2 * α) (by positivity) (by linarith))

/-- **(5.58) and Theorem 4.6 (ii)** from the inputs of `proposition410` and the conclusions of
Propositions 4.11 and 4.12: for every `s ∈ (0, 2)`,
`|E[J₁(Φ_{z,r}, p, q)] - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ C r^{-d}` and
`J₁(Φ_{z,r}, p, q) = ½ p·āp + ½ q·ā⁻¹q - p·q + O_s(C r^{-d/2})`. -/
theorem estimate558_of_trialGap [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hcore : ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
      FlucJ1 P s α → TrialGapEstimate P S (s / 2) (2 * α))
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → TrialExpectationEstimate P S β)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨h410, hbias⟩ := proposition410 hd1 S hA hspan hrate htrial hmeasJ hcore hexp
  have hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d),
      Measurable fun a : CoefficientField d Λ => J1Heat a z r p q := fun z r p q =>
    (hmeasJ r p q).comp (measurable_id.prodMk measurable_const)
  have hrate' : ∀ s : ℝ, 1 < s → s < 2 → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S s C μ := fun s hs1 hs2 =>
    hrate s (by linarith) (by linarith)
  exact estimate558 hd1 S hA hspan hrate' hmeas h410 hbias h411 h412 hs0 hs2

end Proposition410

end QSH
