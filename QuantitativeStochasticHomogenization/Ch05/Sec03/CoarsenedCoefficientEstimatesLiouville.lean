import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarseFluxDefectMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatGram
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatMeasurability
import QuantitativeStochasticHomogenization.Ch03.Sec03.DimensionA1
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBallProof

/-!
# Section 5.3: (5.63) from (5.58) and the first-order Liouville theorem

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, (5.63)–(5.64). Of the inputs of `coarsenedCoefficientEstimates_of_corrected_energy`,

* the almost sure measurability of `J₁(Φ_{z,r}, p, q)` holds for every finite law
  (`aestronglyMeasurable_J1Heat`);
* the finite Gaussian energy of the corrected coordinates follows from the sublinearity of the
  correctors (`ae_integrable_heatKernel_mul_euclideanSq_correctorColumn`), giving
  `hasGaussianCorrectorEnergy_of_lawHypotheses`;
* the identification (4.12) of the gradients of `A₁` with the corrected fields follows from
  Theorem 3.8 for `k = 1` (`ae_gradients_harmonicA1`), giving
  `ae_gradientsOfA1AreCorrected_of_liouville`.

Hence the frozen statement holds under (5.58) with constants uniform over the laws and the
first-order Liouville theorem (`coarsenedCoefficientEstimates_of_energyEstimate_liouville`), and
under (5.58) and the harmonic approximation of Theorem 3.8
(`coarsenedCoefficientEstimates_of_energyEstimate_harmonicApproximation`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `p + ∑ᵢ pᵢ ∇φ_{eᵢ} = G p`. -/
theorem correctedAffineGrad_eq_correctedField {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (p x : Vec d) :
    correctedAffineGrad S a p x = correctedField S a p x := by
  rw [correctedAffineGrad, correctedField]
  simp only [correctedCoordinate, smul_add, Finset.sum_add_distrib, sum_smul_unitVector_eq]

/-- **(4.12) from Theorem 3.8 for `k = 1`.** -/
theorem ae_gradientsOfA1AreCorrected_of_liouville (hL : firstOrderLiouvilleStatement)
    (hd : 2 ≤ d) (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a := by
  filter_upwards [ae_gradients_harmonicA1 hL hd hΛ hP S] with a ha
  refine ⟨fun w => ?_, fun ξ => ?_⟩
  · obtain ⟨c, hc, -⟩ := ha.1 w
    refine ⟨c, ?_⟩
    filter_upwards [hc] with x hx
    rw [hx, correctedAffineGrad_eq_correctedField]
  · obtain ⟨w, -, hw⟩ := ha.2 ξ
    refine ⟨w, Eventually.of_forall fun x => ?_⟩
    rw [hw, correctedAffineGrad_eq_correctedField]

/-- **The corrected coordinates have finite Gaussian energy**, from the sublinearity of the
correctors. -/
theorem hasGaussianCorrectorEnergy_of_lawHypotheses (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (S : HomogenizationData P) :
    HasGaussianCorrectorEnergy S :=
  ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S

/-- **(5.63) from (5.58) and the first-order Liouville theorem.** -/
theorem coarsenedCoefficientEstimates_of_energyEstimate_liouville
    (h558 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀)
    (hL : firstOrderLiouvilleStatement) :
    QSH.Frozen.coarsenedCoefficientEstimates := by
  refine coarsenedCoefficientEstimates_of_corrected_energy h558 ?_ ?_ ?_
  · intro d hd Λ hΛ P hP z r hr p q
    have := hP.1
    exact (aestronglyMeasurable_J1Heat (by linarith) P z r (by linarith) p q).aemeasurable
  · exact fun d hd Λ hΛ P hP S => ae_gradientsOfA1AreCorrected_of_liouville hL hd hΛ hP S
  · exact fun d hd Λ hΛ P hP S => hasGaussianCorrectorEnergy_of_lawHypotheses hd hΛ hP S

/-- **(5.63) from (5.58) and the harmonic approximation** of the proof of Theorem 3.8. -/
theorem coarsenedCoefficientEstimates_of_energyEstimate_harmonicApproximation
    (h558 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀)
    (h2 : harmonicApproximationStatement) :
    QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_energyEstimate_liouville h558
    (firstOrderLiouville_of_harmonicApproximation_only h2)

end QSH
