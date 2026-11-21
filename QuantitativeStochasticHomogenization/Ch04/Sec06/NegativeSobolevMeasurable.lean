import QuantitativeStochasticHomogenization.Ch04.Sec06.CorrectorGaussianEnergy
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedBounds

/-!
# Section 4.6: (4.126) with the bounds of the homogenized matrix

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126). The bounds `1 ≤ ā ≤ Λ` used in `negativeSobolevCorrector_of_corrector_energy_bounds`
follow from the almost sure strong measurability of the Dirichlet energies on the triadic cubes
(`homogenizedMatrixBounds_of_aestronglyMeasurable`), which gives
`negativeSobolevCorrector_of_corrector_energy_measurable`.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

/-- **(4.126) from (4.2), (4.3), the measurability of the Dirichlet energies and the Gaussian energy
estimate of the corrected field** `e + ∇φ_e(·/ε)` at the unit scale. -/
theorem negativeSobolevCorrector_of_corrector_energy_measurable
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C C₁ : ℝ, 0 < C ∧ 0 < C₁ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        (∀ (n : ℕ) (ξ : Vec d), AEStronglyMeasurable
          (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P) ∧
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y)) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y))
              1 (C * r ^ (-(d : ℝ) / 2))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y •
              ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e))) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y •
              ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e))) 1
                (C * r ^ (-(d : ℝ) / 2))) ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ R : CoefficientField d Λ → ℝ, OsBound P R 1 C₁ ∧
            ∀ᵐ a ∂P, vectorGaussianEnergy (fun x => e + (S.corrector e).grad a (ε⁻¹ • x)) ^
              (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_corrector_energy_bounds fun d hd Λ hΛ => ?_
  obtain ⟨C, C₁, hC, hC₁, hP⟩ := h d hd Λ hΛ
  refine ⟨C, C₁, hC, hC₁, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨hmeas, S, hS⟩ := hP P hPl
  exact ⟨S, homogenizedMatrixBounds_of_aestronglyMeasurable S (by linarith) hmeas, hS⟩

end QSH
