import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof
import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeLocalization
import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimatesLiouville

/-!
# The frozen statements E5 and E6 with the first-order Liouville theorem discharged

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*.
The first-order Liouville theorem `QSH.firstOrderLiouville` (Theorem 3.8 with `k = 1`) and the
harmonic approximation `QSH.harmonicApproximation` are proved, so the localized energy bound
(Lemma 4.21) needs only the single-slope estimate, and the coarsened coefficient estimates
(Lemma 5.24) need only the energy estimate (5.58).
-/

open MeasureTheory

namespace QSH

/-- The frozen localized-energy statement from the single-slope estimate alone. -/
theorem localizedEnergy_of_slope_only
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ : ℝ, 0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
        0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationSlopeEstimate d Λ s δ γ α σ θ C₀) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_harmonicApproximation_of_slope harmonicApproximation h

/-- The frozen coarsened coefficient estimates from the energy estimate (5.58) alone. -/
theorem coarsenedCoefficientEstimates_of_energyEstimate
    (h558 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀) :
    QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_energyEstimate_liouville h558 firstOrderLiouville

end QSH
