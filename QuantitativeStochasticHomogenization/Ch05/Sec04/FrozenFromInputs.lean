import QuantitativeStochasticHomogenization.Ch04.Sec04.PilotLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatPathwiseBoundProof
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec04.LiouvilleCorollaries

/-!
# The frozen statements from Proposition 3.21 and the single-slope estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.1, (4.126), (5.58), Lemma 5.24, Lemma 5.29 and (5.85).

The seven frozen statements E1–E7 follow from two inputs, both with constants chosen before the
law:

* `UniformGaussianCorrectorRate`: Proposition 3.21, the bounds of the Gaussian averages of the
  corrector gradients, fluxes and energies at every exponent `τ < d`;
* `UniformLinearSlopeEstimates`: the single-slope estimate of Lemma 4.21 on the classes
  `LinearLaw s β C` of the laws with the linear estimate at `(s, β)`, for localized families of a
  construction exponent `α < β` (`LinearSlopeEstimates`).

The heat identity (H) is `exists_heatPathwiseKernel`, with a kernel of mass `(d + 1)/u`, and the
existence of homogenization data is `homogenizationDataExists`. With them, the bootstrap of
Theorem 4.6 gives Theorem 4.6 (i) and (iii) and the Gaussian gradient bound with constants chosen
before the law, hence E1 (Theorem 4.1), E2–E4 (Lemma 5.29), E5 (Lemma 5.24 through (5.58)), E6
((5.85)) and E7 ((4.126)).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **Proposition 3.21 with constants chosen before the law**: for `d ≥ 2` and `Λ > 1` there are
constants `C τ, μ τ > 0` for `τ ∈ (0, d)` such that every law satisfying the assumptions has a
homogenization data with `GaussianCorrectorRate` at every `τ ∈ (0, d)` with these constants. -/
def UniformGaussianCorrectorRate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
    (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ)

/-- **The single-slope estimate of Lemma 4.21 on the classes of laws with the linear estimate**,
for every `d ≥ 2` and `Λ > 1`. -/
def UniformLinearSlopeEstimates : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → LinearSlopeEstimates d Λ

/-- **The heat identity (H) with a kernel of mass `C_k/u`, `C_k = d + 1` chosen before the law.** -/
theorem uniformHeatPathwiseKernel :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k :=
  fun d hd Λ hΛ => ⟨(d : ℝ) + 1, exists_heatPathwiseKernel d hd Λ hΛ⟩

/-- **Proposition 4.11 at the exponents of the bootstrap** from Proposition 3.21 and the
single-slope estimate, with constants chosen before the law. -/
theorem pilotLocalizationEstimates_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → PilotLocalizationEstimates d Λ :=
  pilotLocalizationEstimates_of_rate_heat_slope hR uniformHeatPathwiseKernel hS

/-- **Theorem 4.6 (i) with constants chosen before the law** (`UniformAdditivityJ1`) from
Proposition 3.21 and the single-slope estimate. -/
theorem uniformAdditivityJ1_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : UniformAdditivityJ1 :=
  uniformAdditivityJ1_of_rate_heat_pilot hR uniformHeatPathwiseKernel
    (pilotLocalizationEstimates_of_rate_slope hR hS)

/-- **E1, Theorem 4.1** (`QSH.Frozen.averagedCorrectorGradient`) from Proposition 3.21 and the
single-slope estimate, with constants chosen before the law. -/
theorem averagedCorrectorGradient_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.averagedCorrectorGradient :=
  averagedCorrectorGradient_of_rate_heat_pilot hR uniformHeatPathwiseKernel
    (pilotLocalizationEstimates_of_rate_slope hR hS)

/-- **E2, Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`) from Proposition 3.21 and the
single-slope estimate, with constants chosen before the law. -/
theorem blockBoundary_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.blockBoundary :=
  blockBoundary_of_uniformAdditivityJ1 (uniformAdditivityJ1_of_rate_slope hR hS)
    homogenizationDataExists

/-- **E3, Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`) from Proposition 3.21 and the
single-slope estimate, with constants chosen before the law. -/
theorem blockChange_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.blockChange :=
  blockChange_of_uniformAdditivityJ1 (uniformAdditivityJ1_of_rate_slope hR hS)
    homogenizationDataExists

/-- **E4, Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`) from Proposition 3.21 and the single-slope
estimate, with constants chosen before the law. -/
theorem blockCLT_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.blockCLT :=
  blockCLT_of_uniformAdditivityJ1 (uniformAdditivityJ1_of_rate_slope hR hS)
    homogenizationDataExists

/-- **(5.58) with a constant chosen before the law** from Proposition 3.21 and the single-slope
estimate. -/
theorem uniformEnergyEstimate_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀ :=
  uniformEnergyEstimate_of_rate_heat_pilot hR uniformHeatPathwiseKernel
    (pilotLocalizationEstimates_of_rate_slope hR hS)

/-- **E5, Lemma 5.24** (`QSH.Frozen.coarsenedCoefficientEstimates`) from Proposition 3.21 and the
single-slope estimate, through (5.58) with a constant chosen before the law. -/
theorem coarsenedCoefficientEstimates_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_energyEstimate (uniformEnergyEstimate_of_rate_slope hR hS)

/-- **E6, (5.85)** (`QSH.Frozen.localizedEnergy`) from Proposition 3.21 and the single-slope
estimate, with constants chosen before the law. -/
theorem localizedEnergy_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_rate_heat_slope hR uniformHeatPathwiseKernel hS

/-- **E7, (4.126)** (`QSH.Frozen.negativeSobolevCorrector`) from Proposition 3.21 and the
single-slope estimate, with constants chosen before the law. -/
theorem negativeSobolevCorrector_of_rate_slope (hR : UniformGaussianCorrectorRate)
    (hS : UniformLinearSlopeEstimates) : QSH.Frozen.negativeSobolevCorrector :=
  negativeSobolevCorrector_of_rate_heat_pilot hR uniformHeatPathwiseKernel
    (pilotLocalizationEstimates_of_rate_slope hR hS)

end QSH
