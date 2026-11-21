import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Frozen statement: Theorem 4.1, (4.2)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.1, (4.2), in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM Theorem 4.1, (4.2), with `s = 1`** (einstein input E1): for `d ≥ 2` and `Λ > 1` there is
`C` such that every law satisfying (P1)-(P2) has correctors and a homogenized matrix with
`|∫ Φ_{z,r} ∇φ_e| ≤ O_1(C r^{-d/2})` for `|e| < 1`, `z ∈ ℝ^d`, `r ≥ 1`. -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.averagedCorrectorGradient : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
      ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
        (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y) volume) ∧
        OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y))
          1 (C * r ^ (-(d : ℝ) / 2))
-- FROZEN-STATEMENT-END
