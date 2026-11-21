import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Nonnegativity of the squared Euclidean norm

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Sharpness/Energy.lean`.

The squared Euclidean norm `euclideanSq` is a sum of squares, hence nonnegative.
-/

namespace QSH

/-- The Euclidean squared norm is nonnegative. -/
theorem euclideanSq_nonneg {d : ℕ} (g : Vec d) : 0 ≤ euclideanSq g :=
  show 0 ≤ ∑ i, g i * g i from
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (g i))

end QSH
