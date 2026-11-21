import QuantitativeStochasticHomogenization.Ch04.Sec01EnergyQuantityJ1

/-!
# Section 5.3: Heuristic Derivation of the Scaling Limit

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 5 (Scaling Limits of First-Order Correctors), Section 5.3. Numbered results of this section:
Lemma 5.24; Definition 5.23.

Defined here: the coarsened coefficients `b_r(z)` (Definition 5.23) and the flux defect of (5.64).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **The coarsened coefficients `b_r(z)`**, Definition 5.23, (5.62), with `ā = A`. -/
def coarsenedCoefficient {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (A : Mat d) (z : Vec d)
    (r : ℝ) : Mat d := fun j k =>
  (J1Heat a z r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
    J1Heat a z r (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2

/-- A Euclidean (Frobenius) matrix norm, for `|b_r(z)|` in (5.63). -/
def matrixSize {d : ℕ} (M : Mat d) : ℝ := Real.sqrt (∑ j : Fin d, ∑ k : Fin d, (M j k) ^ 2)

/-- The supremum in (5.64) over `u ∈ A₁` normalized in `L²(Φ_{z,r})`. -/
def coarseFluxDefect {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (A : Mat d) (z : Vec d)
    (r : ℝ) : ℝ :=
  sSup {e : ℝ | ∃ w : HarmonicA1 a,
    Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ∧
    Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ≤ 1 ∧
    e = euclideanNorm
      ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec (∫ x, heatKernel z r x • w.grad x))}

end QSH
