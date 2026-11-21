import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Frozen statement: (4.126), Theorem 4.24

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126), Theorem 4.24, in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM (4.126)** after Theorem 4.24, `p = 2`, integer `m > d/2`, `s = 1`:
the `H^{-m}(B_1)` norms of `∇φ_e(·/ε)` and `a(·/ε)(e + ∇φ_e(·/ε)) - ā e` are bounded by a
measurable `Z ≤ O_1(C ε^{d/2})`, for `0 < ε < 1/2`. -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.negativeSobolevCorrector : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ m : ℕ, (d : ℝ) / 2 < m →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ Z : CoefficientField d Λ → ℝ, Measurable Z ∧ OsBound P Z 1 (C * ε ^ ((d : ℝ) / 2)) ∧
          ∀ᵐ a ∂P,
            vectorNegativeIntegerSobolevNorm m (originBall d 1)
              (fun x => (S.corrector e).grad a (ε⁻¹ • x)) +
            vectorNegativeIntegerSobolevNorm m (originBall d 1)
              (fun x => (a (ε⁻¹ • x)).mulVec (e + (S.corrector e).grad a (ε⁻¹ • x)) -
                S.homogenized.mulVec e) ≤
            ENNReal.ofReal (Z a)
-- FROZEN-STATEMENT-END
