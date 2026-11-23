import QuantitativeStochasticHomogenization.Ch05.Sec04.FrozenFromInputs
import QuantitativeStochasticHomogenization.Ch04.Sec01.UniformGaussianRate

/-!
# The frozen statements from the single-slope estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 3.21, Propositions 4.3, 4.10, 4.11, Lemma 4.13, Theorem 4.6, Theorem 4.1, (4.126),
(5.58), Lemma 5.24, Lemma 5.29 and (5.85).

Proposition 3.21 with constants chosen before the law is `uniformGaussianCorrectorRate`, which is
the statement `UniformGaussianCorrectorRate`. With the heat identity (H)
(`exists_heatPathwiseKernel`), the Gaussian inputs of the bootstrap hold for every `d ≥ 2` and
`Λ > 1` (`uniformGaussianInputs_holds`), hence, with constants chosen before the law and for the
bounded jointly measurable versions of `J₁`:

* Proposition 4.3 (`uniformBaseFluctuation_holds`);
* Proposition 4.10 (`uniformImprovementOfAdditivity_holds`) and (4.70)
  (`uniformExpectationEstimates_holds`);
* Lemma 4.13 with the linear estimate (`exists_uniform_commutator_linear_of_fluctuations`).

Proposition 4.11 at the exponents of the bootstrap needs in addition the single-slope estimate of
Lemma 4.21 on the classes of laws with the linear estimate (`UniformLinearSlopeEstimates`,
`uniformLocalizationEstimates_of_linearSlope`), and so do Theorem 4.6 (i) and (iii)
(`uniformAdditivityJ1_of_linearSlope`, `uniformFluctuationJ1_of_linearSlope`) and the frozen
statements E1–E7 (`averagedCorrectorGradient_of_linearSlope` and the theorems after it), which
follow from this single input.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **Proposition 3.21 with constants chosen before the law**, in the form of the input
`UniformGaussianCorrectorRate` of the frozen statements. -/
theorem uniformGaussianCorrectorRate_holds : UniformGaussianCorrectorRate :=
  uniformGaussianCorrectorRate

/-- **The Gaussian inputs of the bootstrap** hold: Proposition 3.21 and the heat identity (H),
with constants chosen before the law. -/
theorem uniformGaussianInputs_holds (hd : 2 ≤ d) (hΛ : 1 < Λ) : UniformGaussianInputs d Λ :=
  uniformGaussianInputs_of_rate_heat hd hΛ (uniformGaussianCorrectorRate d hd Λ hΛ)
    (uniformHeatPathwiseKernel d hd Λ hΛ)

/-- **Proposition 4.3 with constants chosen before the law** for the bounded jointly measurable
versions of `J₁`. -/
theorem uniformBaseFluctuation_holds (hd : 2 ≤ d) (hΛ : 1 < Λ) : UniformBaseFluctuation d Λ :=
  (uniformGaussianInputs_holds hd hΛ).uniformBaseFluctuation hd hΛ

/-- **Proposition 4.10 with constants chosen before the law** for the bounded jointly measurable
versions of `J₁`. -/
theorem uniformImprovementOfAdditivity_holds (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    UniformImprovementOfAdditivity d Λ :=
  uniformImprovementOfAdditivity_of_gaussianInputs hd hΛ (uniformGaussianInputs_holds hd hΛ)

/-- **(4.70) with constants chosen before the law** for the bounded jointly measurable versions of
`J₁`. -/
theorem uniformExpectationEstimates_holds (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    UniformExpectationEstimates d Λ :=
  uniformExpectationEstimates_of_gaussianInputs hd hΛ (uniformGaussianInputs_holds hd hΛ)

/-- **Lemma 4.13 and the linear estimate with constants chosen before the law**: for
`s ∈ (0, 2)`, `α ∈ (0, d/2]` and `C_F > 0` there are `C_c, C_l > 0` such that every law has
homogenization data `S` for which `Fluc(s, α)` with constant `C_F` for a bounded jointly
measurable version of `J₁` gives the commutator estimate and the linear estimate at `(s, α)`. -/
theorem exists_uniform_commutator_linear_of_fluctuations (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {s α CF : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hα0 : 0 < α) (hα : α ≤ (d : ℝ) / 2)
    (hCF : 0 < CF) :
    ∃ Cc Cl : ℝ, 0 < Cc ∧ 0 < Cl ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ S : HomogenizationData P, ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s α CF →
        CommutatorEstimateAt P S s α Cc ∧ LinearAverageEstimateAt P S s α Cl := by
  obtain ⟨C, μ, CE, Ck, hCE, hCμ, hG⟩ := uniformGaussianInputs_holds hd hΛ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb2 : 0 < (d : ℝ) / 2 := by linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (s * ((d : ℝ) / 2) + d) / 2 := ⟨_, rfl⟩
  have hτ1 : s * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s ≤ τ / ((d : ℝ) / 2) := by rw [le_div_iff₀ hb2]; exact hτ1
  obtain ⟨hCτ, hμτ⟩ := hCμ τ hτ0 hτ2
  obtain ⟨Cc, Cl, hCc, hCl, h⟩ := exists_uniform_commutator_linear (Ck := Ck) hd hΛ
    hs0 hα0 hα hCF hτ0 hCτ hμτ hCE hτs
  refine ⟨Cc, Cl, hCc, hCl, fun P hP => ?_⟩
  obtain ⟨S, hH, hE, hr⟩ := hG P hP
  exact ⟨S, fun J hJ hF => h P hP S J hJ.measurable_slice hJ.2.2 hF (hr τ hτ0 hτ2)
    (hE.mono hCE.le (by linarith)) hH⟩

/-- **Proposition 4.11 at the exponents of the bootstrap with constants chosen before the law**
from the single-slope estimate on the classes of laws with the linear estimate. -/
theorem uniformLocalizationEstimates_of_linearSlope (hS : UniformLinearSlopeEstimates)
    (hd : 2 ≤ d) (hΛ : 1 < Λ) : UniformLocalizationEstimates d Λ :=
  uniformLocalizationEstimates_of_pilot hΛ
    (pilotLocalizationEstimates_of_gaussianInputs_slopeOn hd hΛ (uniformGaussianInputs_holds hd hΛ)
      (hS d hd Λ hΛ))

/-- **Theorem 4.6 (i) with constants chosen before the law** from the single-slope estimate. -/
theorem uniformAdditivityJ1_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    UniformAdditivityJ1 :=
  uniformAdditivityJ1_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **Theorem 4.6 (iii) with constants chosen before the law** from the single-slope estimate. -/
theorem uniformFluctuationJ1_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    UniformFluctuationJ1 :=
  uniformFluctuationJ1_of_uniform_inputs fun _ hd _ hΛ =>
    ⟨uniformGaussianInputs_holds hd hΛ, uniformImprovementOfAdditivity_holds hd hΛ,
      uniformLocalizationEstimates_of_linearSlope hS hd hΛ⟩

/-- **E1, Theorem 4.1** (`QSH.Frozen.averagedCorrectorGradient`) from the single-slope estimate. -/
theorem averagedCorrectorGradient_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    QSH.Frozen.averagedCorrectorGradient :=
  averagedCorrectorGradient_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **E2, Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`) from the single-slope estimate. -/
theorem blockBoundary_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    QSH.Frozen.blockBoundary :=
  blockBoundary_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **E3, Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`) from the single-slope estimate. -/
theorem blockChange_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    QSH.Frozen.blockChange :=
  blockChange_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **E4, Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`) from the single-slope estimate. -/
theorem blockCLT_of_linearSlope (hS : UniformLinearSlopeEstimates) : QSH.Frozen.blockCLT :=
  blockCLT_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **(5.58) with a constant chosen before the law** from the single-slope estimate. -/
theorem uniformEnergyEstimate_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀ :=
  uniformEnergyEstimate_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **E5, Lemma 5.24** (`QSH.Frozen.coarsenedCoefficientEstimates`) from the single-slope
estimate, through (5.58). -/
theorem coarsenedCoefficientEstimates_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **E6, (5.85)** (`QSH.Frozen.localizedEnergy`) from the single-slope estimate. -/
theorem localizedEnergy_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_rate_slope uniformGaussianCorrectorRate_holds hS

/-- **E7, (4.126)** (`QSH.Frozen.negativeSobolevCorrector`) from the single-slope estimate. -/
theorem negativeSobolevCorrector_of_linearSlope (hS : UniformLinearSlopeEstimates) :
    QSH.Frozen.negativeSobolevCorrector :=
  negativeSobolevCorrector_of_rate_slope uniformGaussianCorrectorRate_holds hS

end QSH
