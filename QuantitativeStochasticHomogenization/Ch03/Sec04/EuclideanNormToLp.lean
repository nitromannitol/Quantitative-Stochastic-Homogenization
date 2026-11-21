import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# The Euclidean norm through `EuclideanSpace`

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/TimeChange/EuclideanTransport.lean`.

The norm `euclideanNorm` is the norm of `EuclideanSpace ℝ (Fin d)` transported along `WithLp.toLp`; this gives the triangle inequality and homogeneity without changing the default norm on `Vec d`.
-/

open WithLp

namespace QSH

/-- The manuscript norm agrees with the Hilbert space norm after transport. -/
theorem euclideanNorm_eq_norm_toLp {d : ℕ} (x : Vec d) :
    euclideanNorm x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change x i * x i = ‖x i‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs, pow_two]

/-- The triangle inequality for `euclideanNorm`. -/
theorem euclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_toLp, euclideanNorm_eq_norm_toLp,
    euclideanNorm_eq_norm_toLp]
  exact norm_add_le (toLp 2 x) (toLp 2 y)

/-- Absolute homogeneity of `euclideanNorm`. -/
theorem euclideanNorm_smul_abs {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [euclideanNorm_eq_norm_toLp, euclideanNorm_eq_norm_toLp]
  exact norm_smul c (toLp 2 x : EuclideanSpace ℝ (Fin d))

end QSH
