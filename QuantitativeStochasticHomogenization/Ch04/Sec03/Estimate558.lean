import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAverages
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedBounds

/-!
# (5.58) from the remaining inputs

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(5.58) and Theorem 4.6 (ii), with the inputs of the route of Propositions 4.3 and 4.10 used here
reduced to:

* the structure (4.12) of `A₁` (`GradientsOfA1AreCorrected`);
* the almost sure measurability of the Dirichlet energies on the triadic cubes (for `I ≤ ā ≤ Λ I`);
* Proposition 3.21 (`GaussianCorrectorRate`) and the energy bound below the scale
  (`GaussianEnergyBound`), at every exponent `τ ∈ (0, d)`;
* the expectations of the Gaussian averages (`ExpectedAveragesEstimate`) with their almost sure
  integrability (`AveragesIntegrable`), and the almost sure integrability of the trial;
* the linear estimate of Step 1 under `Fluc(s, α)` (`LinearAverageEstimate`);
* the measurability of `J₁` and of the trial;
* the conclusions of Propositions 4.11 and 4.12.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **(5.58) and Theorem 4.6 (ii)** from the inputs listed in the module docstring. -/
theorem estimate558_of_inputs {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 ≤ Λ)
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
    (h4 : ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
      FlucJ1 P s α → LinearAverageEstimate P S s α)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) :=
  estimate558_of_linearAverages hd S hΛ (homogenizedMatrixBounds_of_aestronglyMeasurable S hΛ hμ)
    hspan hrate hN htrial hmeasJ hmeasL h4
    (fun β hβ hβd => trialObjectiveExpectation_of_expectedAverages S havg (hexp β hβ hβd))
    h411 h412 hs0 hs2

end QSH
