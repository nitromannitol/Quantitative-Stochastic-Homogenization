import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.Ch05.Sec03HeuristicScalingLimit
import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Frozen statement: Lemma 5.24, (5.63)-(5.64)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 5.24, (5.63)-(5.64), in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM Lemma 5.24, (5.63)-(5.64), with `s = 1`**: `|b_r(z)| ≤ O_1(C r^{-d/2})` and the flux
defect over `A₁` normalized in `L²(Φ_{z,r})` is `O_{1/2}(C r^{-d})`, for every choice of correctors
and `ā`. Both random variables are built from `A₁`, which is identified with its
finite-dimensional form (4.12) only almost surely, so they are almost surely measurable
(Remark 5.17). -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.coarsenedCoefficientEstimates : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ S : HomogenizationData P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      AEOsBound P (fun a => matrixSize (coarsenedCoefficient a S.homogenized z r)) 1
        (C * r ^ (-(d : ℝ) / 2)) ∧
      AEOsBound P (fun a => coarseFluxDefect a S.homogenized z r) (1 / 2) (C * r ^ (-(d : ℝ)))
-- FROZEN-STATEMENT-END
