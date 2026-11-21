import QuantitativeStochasticHomogenization.Ch04.Sec03.Lemma413Statement
import QuantitativeStochasticHomogenization.Ch04.Sec03.Estimate558

/-!
# (5.58) with Lemma 4.13 in place

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13 and Proposition 4.10, and Section 5.3, (5.58).

`commutatorEstimate_of_flucJ1`: under `Fluc(s, α)` with `0 < s < 2` and `0 < α ≤ d/2`, the
inputs of `estimate558_of_inputs` and the measurability of the gradient and flux averages give the
commutator estimate of Lemma 4.13 (Proposition 3.21 and the energy bound are used at the exponent
`τ = (s d/2 + d)/2`).

`estimate558_of_commutator`: (5.58) and Theorem 4.6 (ii) from the inputs of
`estimate558_of_inputs`, where the linear estimate of Step 1 is now needed only from `Fluc(s, α)`
together with the conclusion of Lemma 4.13 (the remaining step is the heat identity (H) of the
route used here).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **Lemma 4.13 under `Fluc(s, α)`** from Proposition 3.21 and the energy bound at every exponent
`τ ∈ (0, d)` and the expectations of the averages at every rate `β ∈ (0, d]`. -/
theorem commutatorEstimate_of_flucJ1 {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hint : AveragesIntegrable P S)
    (hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d), Measurable (fun a => gradientAverage S a z r ξ) ∧
      Measurable (fun a => fluxAverage S a z r ξ))
    {s α : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hα0 : 0 < α) (hα : α ≤ (d : ℝ) / 2)
    (hF : FlucJ1 P s α) : CommutatorEstimate P S s α := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s ≤ τ / ((d : ℝ) / 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hτ1
  obtain ⟨C, μ, -, hμ, hr⟩ := hrate τ hτ0 hτ2
  obtain ⟨CN, -, hNτ⟩ := hN τ hτ0 hτ2
  obtain ⟨CF, hCF, hF⟩ := hF
  exact lemma413 hd S hΛ hA hspan hmeasJ hs0 hα0.le hα hCF hF hμ hr hNτ hτs hint
    (hexp α hα0 (by linarith)) hmeasA

/-- **(5.58) and Theorem 4.6 (ii)** from the inputs of `estimate558_of_inputs`, with the linear
estimate of Step 1 needed only under `Fluc(s, α)` and the conclusion of Lemma 4.13. -/
theorem estimate558_of_commutator {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hμ : ∀ (n : ℕ) (ξ : Vec d),
      AEStronglyMeasurable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (havg : AveragesIntegrable P S) (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d), Measurable (fun a => gradientAverage S a z r ξ) ∧
      Measurable (fun a => fluxAverage S a z r ξ))
    (hH : ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
      FlucJ1 P s α → CommutatorEstimate P S s α → LinearAverageEstimate P S s α)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hA := homogenizedMatrixBounds_of_aestronglyMeasurable S hΛ.le hμ
  exact estimate558_of_inputs hd S hΛ.le hμ hspan hrate hN hexp havg htrial hmeasJ hmeasL
    (fun s' α hs0' hs2' hα0 hα hF => hH s' α hs0' hs2' hα0 hα hF
      (commutatorEstimate_of_flucJ1 hd1 S hΛ hA hspan hmeasJ hrate hN hexp havg hmeasA hs0' hs2'
        hα0 hα hF)) h411 h412 hs0 hs2

end QSH
