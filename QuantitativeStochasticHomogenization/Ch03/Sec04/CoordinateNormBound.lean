import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Coordinates and the Euclidean norm

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Regeneration/HalfSpaces.lean`.

Each coordinate of a vector is bounded in absolute value by its Euclidean norm.
-/

open scoped BigOperators

namespace QSH


/-- Scalar prerequisite: each coordinate of a vector is bounded by its Euclidean
norm. -/
theorem coordinate_abs_le_euclideanNorm {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  have hsq : x i * x i ≤ ∑ j, x j * x j :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

end QSH
