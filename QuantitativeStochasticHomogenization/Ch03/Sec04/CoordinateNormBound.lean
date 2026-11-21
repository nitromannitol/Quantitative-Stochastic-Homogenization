import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Coordinate Norm Bound

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Regeneration/HalfSpaces.lean`.
-/

open scoped BigOperators

namespace QSH

/-!
Scalar half-space prerequisites for the regeneration step, from the application
lines 331--340 (`regen.future`, the half-space `R₊ = {e₁·x ≥ -2R}`) and lines
377--403 (the corrected past and future half-spaces, separated by `2R`).

Every declaration here is a coordinate fact about the explicit Euclidean norm
`euclideanNorm`. None of them is the paper's regeneration lemma, the factorization
at `τ₁`, the finite-range argument, or any other probabilistic claim of the paper.
-/

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
