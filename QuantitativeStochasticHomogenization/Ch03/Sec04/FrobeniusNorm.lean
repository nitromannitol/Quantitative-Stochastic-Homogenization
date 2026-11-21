import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Euclidean norm of the flux-corrector tensor

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Environment/MatrixNorm.lean`.

Matrix-valued corrector estimates use the Frobenius norm. The operator norm
in the coefficient Lipschitz assumption remains a separate condition.
-/

open scoped BigOperators

namespace QSH

/-- Sum of squares of every matrix entry. -/
def frobeniusSq {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, A i j * A i j

/-- Euclidean (Frobenius) norm of a matrix, with no new matrix norm instance. -/
noncomputable def frobeniusNorm {d : ℕ} (A : Mat d) : ℝ := Real.sqrt (frobeniusSq A)

theorem frobeniusSq_nonneg {d : ℕ} (A : Mat d) : 0 ≤ frobeniusSq A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg (A i j)))

end QSH
