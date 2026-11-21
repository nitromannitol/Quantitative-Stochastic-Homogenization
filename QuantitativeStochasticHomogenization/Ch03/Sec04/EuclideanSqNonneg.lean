import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import Mathlib.Tactic.ByContra

/-!
# The positive energy in the sharpness coefficient

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Sharpness/Energy.lean`.

the application, `eq.sharp-constant`, lines 1261–1265. These pointwise facts use
the Euclidean sum of squares. The event that the actual constructed gradient is
nonzero with positive probability is a separate obligation.
-/

namespace QSH

/-- The Euclidean squared norm is nonnegative. -/
theorem euclideanSq_nonneg {d : ℕ} (g : Vec d) : 0 ≤ euclideanSq g :=
  show 0 ≤ ∑ i, g i * g i from
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (g i))

end QSH
