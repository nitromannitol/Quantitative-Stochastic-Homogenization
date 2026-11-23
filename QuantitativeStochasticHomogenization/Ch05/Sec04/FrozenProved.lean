import QuantitativeStochasticHomogenization.Ch05.Sec04.FrozenFromCompactTests
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestFiniteBallProof

/-!
# The frozen statements E1–E7

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.1, (4.126), Lemma 5.24, Lemma 5.29 and (5.85), with constants chosen before the law.

The estimate with compact tests holds for every `d ≥ 2`, `Λ > 1` and `k > 0`
(`compactTestFiniteBall`), so `UniformCompactTestFiniteBall` holds and the theorems of
`FrozenFromCompactTests` have no hypothesis: the finite-ball observation at every order, the
single-slope estimate on the classes `LinearLaw`, Proposition 4.11 at the exponents of the
bootstrap, the Gaussian gradient bound at the exponent `d/2`, Theorem 4.6 (i) and (iii), (5.58),
and the frozen statements E1–E7.

The proofs of E1–E7 are stated here and not after the markers of the files under `Frozen/`: each
of these files is imported by the modules of its proof, whose last steps have the frozen
proposition as their type (for E1, `Frozen.AveragedCorrectorGradient` is imported by
`Ch04.Opening.Theorem41`, which `FrozenFromCompactTests` imports), so a proof in the file itself
would close an import cycle.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **The estimate with compact tests** for every `d ≥ 2`, `Λ > 1` and `k > 0`. -/
theorem uniformCompactTestFiniteBall : UniformCompactTestFiniteBall :=
  fun _ hd _ hΛ _ hk => compactTestFiniteBall hd hΛ hk

/-- **The finite-ball observation of the proof of Lemma 4.21** at every order `k > 0`. -/
theorem finiteBallObservation_holds {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) :
    ∀ k : ℝ, 0 < k → ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      FiniteBallObservation d Λ σ θ k :=
  finiteBallObservation_of_uniformCompactTests uniformCompactTestFiniteBall hd hΛ

/-- **The single-slope estimate on the classes `LinearLaw`**. -/
theorem uniformLinearSlopeEstimates_holds : UniformLinearSlopeEstimates :=
  uniformLinearSlopeEstimates_of_compactTests uniformCompactTestFiniteBall

/-- **Proposition 4.11 at the exponents of the bootstrap, with constants chosen before the law**. -/
theorem uniformLocalizationEstimates_holds {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) :
    UniformLocalizationEstimates d Λ :=
  uniformLocalizationEstimates_of_linearSlope uniformLinearSlopeEstimates_holds hd hΛ

/-- **The Gaussian gradient bound at the exponent `d/2` with one constant for all laws**. -/
theorem uniformLinearAverageEstimate_holds : UniformLinearAverageEstimate :=
  uniformLinearAverageEstimate_of_compactTests uniformCompactTestFiniteBall

/-- **Theorem 4.6 (i) with constants chosen before the law**. -/
theorem uniformAdditivityJ1_holds : UniformAdditivityJ1 :=
  uniformAdditivityJ1_of_compactTests uniformCompactTestFiniteBall

/-- **Theorem 4.6 (iii) with constants chosen before the law**. -/
theorem uniformFluctuationJ1_holds : UniformFluctuationJ1 :=
  uniformFluctuationJ1_of_compactTests uniformCompactTestFiniteBall

/-- **(5.58) with a constant chosen before the law**. -/
theorem uniformEnergyEstimate_holds :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀ :=
  uniformEnergyEstimate_of_compactTests uniformCompactTestFiniteBall

/-- **E1, Theorem 4.1** (`QSH.Frozen.averagedCorrectorGradient`). -/
theorem averagedCorrectorGradient_holds : QSH.Frozen.averagedCorrectorGradient :=
  averagedCorrectorGradient_of_compactTests uniformCompactTestFiniteBall

/-- **E2, Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`). -/
theorem blockBoundary_holds : QSH.Frozen.blockBoundary :=
  blockBoundary_of_compactTests uniformCompactTestFiniteBall

/-- **E3, Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`). -/
theorem blockChange_holds : QSH.Frozen.blockChange :=
  blockChange_of_compactTests uniformCompactTestFiniteBall

/-- **E4, Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`). -/
theorem blockCLT_holds : QSH.Frozen.blockCLT :=
  blockCLT_of_compactTests uniformCompactTestFiniteBall

/-- **E5, Lemma 5.24** (`QSH.Frozen.coarsenedCoefficientEstimates`). -/
theorem coarsenedCoefficientEstimates_holds : QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_compactTests uniformCompactTestFiniteBall

/-- **E6, (5.85)** (`QSH.Frozen.localizedEnergy`). -/
theorem localizedEnergy_holds : QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_compactTests uniformCompactTestFiniteBall

/-- **E7, (4.126)** (`QSH.Frozen.negativeSobolevCorrector`). -/
theorem negativeSobolevCorrector_holds : QSH.Frozen.negativeSobolevCorrector :=
  negativeSobolevCorrector_of_compactTests uniformCompactTestFiniteBall

end QSH
