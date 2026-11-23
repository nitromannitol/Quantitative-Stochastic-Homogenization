import QuantitativeStochasticHomogenization.Ch05.Sec04.FrozenFromSlope
import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeEstimatesFromLinear
import QuantitativeStochasticHomogenization.Ch04.Sec04.FiniteBallObservationAbsorption

/-!
# The frozen statements from the estimate with compact tests

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21 and its consequences: Proposition 4.11, Theorem 4.6, Theorem 4.1, (4.126), (5.58),
Lemma 5.24, Lemma 5.29 and (5.85).

The single input is `UniformCompactTestFiniteBall`: for every `d ≥ 2`, `Λ > 1` and `k > 0`, the
estimate with compact tests `CompactTestFiniteBall d Λ k`, a deterministic finite-ball estimate
for `a`-harmonic functions above a random radius at every center, with tests chosen for each law
(in place of AKM Lemma 4.20, which uses Theorem 3.8 at a high order). It gives the finite-ball
observation (`finiteBallObservation_of_compactTests`), and with the observation of the smoothed
correctors (`smoothedCorrectorObservation_of_gaussianGradient`) and the excess decay of one slope
(`ballExcessDecay`) the single-slope estimate on the classes of laws with the linear estimate
(`slopeEstimateOnClass_of_linear_finiteBall`). The class of the laws
with the linear estimate there is `LinearLaw` and its single-slope estimate is
`LocalizationSlopeEstimateOn`, by definition (`linearSlopeEstimates_of_finiteBall`). Proposition 3.21
(`uniformGaussianCorrectorRate`), the heat identity (H) (`exists_heatPathwiseKernel`) and the
existence of homogenization data (`homogenizationDataExists`) are proved, so the frozen statements
E1–E7 follow from `UniformCompactTestFiniteBall` alone. For (5.85) the linear estimate at the
exponent `d/2` with one constant for all laws comes from the same chain
(`uniformLinearAverageEstimate_of_compactTests`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The estimate with compact tests** for every `d ≥ 2`, `Λ > 1` and `k > 0`. -/
def UniformCompactTestFiniteBall : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ k : ℝ, 0 < k → CompactTestFiniteBall d Λ k

/-- **The finite-ball observation at every order** from the estimate with compact tests, in the
form of the hypothesis of `slopeEstimateOnClass_of_linear_finiteBall`. -/
theorem finiteBallObservation_of_uniformCompactTests (hT : UniformCompactTestFiniteBall)
    (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∀ k : ℝ, 0 < k → ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      FiniteBallObservation d Λ σ θ k :=
  fun k hk => finiteBallObservation_of_compactTests hk.le (hT d hd Λ hΛ k hk)

/-- **The single-slope estimate on the classes `LinearLaw`** from the finite-ball observation at
every order: the class of `slopeEstimateOnClass_of_linear_finiteBall` is `LinearLaw s β C` and its
single-slope estimate is `LocalizationSlopeEstimateOn`, by definition. -/
theorem linearSlopeEstimates_of_finiteBall (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hD : ∀ k : ℝ, 0 < k → ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      FiniteBallObservation d Λ σ θ k) :
    LinearSlopeEstimates d Λ := by
  intro s β α δ γ C hs1 hs2 hα hαβ _ hδ hγ hαγ hγs hC
  obtain ⟨σ, θ, C₀, hσ, hσ2, hθ, hθ2, hC₀, h⟩ :=
    slopeEstimateOnClass_of_linear_finiteBall hd hΛ hD hs1 hs2 hα hαβ hδ hγ hαγ hγs hC
  exact ⟨σ, θ, C₀, hσ, hσ2, hθ, hθ2, hC₀, h⟩

/-- **The single-slope estimate on the classes `LinearLaw`** from the estimate with compact
tests. -/
theorem uniformLinearSlopeEstimates_of_compactTests (hT : UniformCompactTestFiniteBall) :
    UniformLinearSlopeEstimates := fun _ hd _ hΛ =>
  linearSlopeEstimates_of_finiteBall hd hΛ (finiteBallObservation_of_uniformCompactTests hT hd hΛ)

/-- **The Gaussian gradient bound at the exponent `d/2` with one constant for all laws** from the
estimate with compact tests: the bootstrap of Theorem 4.6 with Proposition 4.11 from the
single-slope estimate. -/
theorem uniformLinearAverageEstimate_of_compactTests (hT : UniformCompactTestFiniteBall) :
    UniformLinearAverageEstimate :=
  uniformLinearAverageEstimate_of_rate_heat_pilot uniformGaussianCorrectorRate_holds
    uniformHeatPathwiseKernel
    (pilotLocalizationEstimates_of_rate_slope uniformGaussianCorrectorRate_holds
      (uniformLinearSlopeEstimates_of_compactTests hT))

/-- **Theorem 4.6 (i) with constants chosen before the law** from the estimate with compact
tests. -/
theorem uniformAdditivityJ1_of_compactTests (hT : UniformCompactTestFiniteBall) :
    UniformAdditivityJ1 :=
  uniformAdditivityJ1_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **Theorem 4.6 (iii) with constants chosen before the law** from the estimate with compact
tests. -/
theorem uniformFluctuationJ1_of_compactTests (hT : UniformCompactTestFiniteBall) :
    UniformFluctuationJ1 :=
  uniformFluctuationJ1_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **E1, Theorem 4.1** (`QSH.Frozen.averagedCorrectorGradient`) from the estimate with compact
tests. -/
theorem averagedCorrectorGradient_of_compactTests (hT : UniformCompactTestFiniteBall) :
    QSH.Frozen.averagedCorrectorGradient :=
  averagedCorrectorGradient_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **E2, Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`) from the estimate with compact tests. -/
theorem blockBoundary_of_compactTests (hT : UniformCompactTestFiniteBall) :
    QSH.Frozen.blockBoundary :=
  blockBoundary_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **E3, Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`) from the estimate with compact tests. -/
theorem blockChange_of_compactTests (hT : UniformCompactTestFiniteBall) :
    QSH.Frozen.blockChange :=
  blockChange_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **E4, Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`) from the estimate with compact tests. -/
theorem blockCLT_of_compactTests (hT : UniformCompactTestFiniteBall) : QSH.Frozen.blockCLT :=
  blockCLT_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **(5.58) with a constant chosen before the law** from the estimate with compact tests. -/
theorem uniformEnergyEstimate_of_compactTests (hT : UniformCompactTestFiniteBall) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀ :=
  uniformEnergyEstimate_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **E5, Lemma 5.24** (`QSH.Frozen.coarsenedCoefficientEstimates`) from the estimate with
compact tests, through (5.58). -/
theorem coarsenedCoefficientEstimates_of_compactTests (hT : UniformCompactTestFiniteBall) :
    QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

/-- **E6, (5.85)** (`QSH.Frozen.localizedEnergy`) from the estimate with compact tests: the
finite-ball observation at every order and the linear estimate at the exponent `d/2` with one
constant for all laws (`localizedEnergy_of_finiteBall_linear`). -/
theorem localizedEnergy_of_compactTests (hT : UniformCompactTestFiniteBall) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_finiteBall_linear
    (fun _ hd _ hΛ => finiteBallObservation_of_uniformCompactTests hT hd hΛ)
    (fun d hd Λ s hΛ hs1 hs2 =>
      uniformLinearAverageEstimate_of_compactTests hT d hd Λ s hΛ (by linarith) hs2)

/-- **E7, (4.126)** (`QSH.Frozen.negativeSobolevCorrector`) from the estimate with compact
tests. -/
theorem negativeSobolevCorrector_of_compactTests (hT : UniformCompactTestFiniteBall) :
    QSH.Frozen.negativeSobolevCorrector :=
  negativeSobolevCorrector_of_linearSlope (uniformLinearSlopeEstimates_of_compactTests hT)

end QSH
