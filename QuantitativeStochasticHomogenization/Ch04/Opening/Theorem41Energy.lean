import QuantitativeStochasticHomogenization.Ch04.Opening.Theorem41
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatGram

/-!
# Theorem 4.1, (4.2), from the linear estimate alone

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.1, (4.2). The corrected coordinates `eᵢ + ∇φ_{eᵢ}` have finite energy against every
Gaussian mask, almost surely, by the sublinearity of the correctors
(`ae_integrable_heatKernel_mul_euclideanSq_correctorColumn`), for all homogenization data of a law
satisfying the assumptions (`hasGaussianCorrectorEnergy_of_lawHypotheses`). Hence the frozen
statement follows from the linear estimate `|∫ Φ_{z,r} G ξ - ξ| ≤ O_s(C (1 + |ξ|) r^{-d/2})` with
constants uniform over the laws (`averagedCorrectorGradient_of_linearAverage_uniform`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The corrected coordinates have finite Gaussian energy**, from the sublinearity of the
correctors. -/
theorem hasGaussianCorrectorEnergy_of_lawHypotheses (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (S : HomogenizationData P) :
    HasGaussianCorrectorEnergy S :=
  ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S

/-- **`QSH.Frozen.averagedCorrectorGradient`** from the linear estimate
`|∫ Φ_{z,r} G ξ - ξ| ≤ O_s(C (1 + |ξ|) r^{-d/2})` with `s` and `C` uniform over the laws. -/
theorem averagedCorrectorGradient_of_linearAverage_uniform
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ s C : ℝ, 1 ≤ s ∧ 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
          OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ))
            s (C * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2)))) :
    QSH.Frozen.averagedCorrectorGradient := by
  refine averagedCorrectorGradient_of_linearAverage fun d hd Λ hΛ => ?_
  obtain ⟨s, C, hs, hC, hP⟩ := h d hd Λ hΛ
  refine ⟨s, C, hs, hC, fun P hPl => ?_⟩
  obtain ⟨S, hS⟩ := hP P hPl
  exact ⟨S, hasGaussianCorrectorEnergy_of_lawHypotheses hd hΛ hPl S, hS⟩

end QSH
