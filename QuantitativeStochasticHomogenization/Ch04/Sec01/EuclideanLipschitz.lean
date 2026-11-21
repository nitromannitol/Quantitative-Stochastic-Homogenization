import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# The Euclidean norm and the sup norm

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Environment/EuclideanLipschitz.lean`.

The Euclidean norm on `Vec d` is at most `√d` times the sup norm.
-/

open MeasureTheory

open scoped NNReal ENNReal

noncomputable section

namespace QSH

/-- Explicit comparison with the ambient coordinate norm, leaving the norm intact. -/
theorem euclideanNorm_le_dimension_mul_norm {d : ℕ} (x : Vec d) :
    euclideanNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := by
  unfold euclideanNorm euclideanSq dot
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hi (i : Fin d) : x i * x i ≤ ‖x‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg (x i)) (norm_nonneg x)).mpr (norm_le_pi_norm x i)
    rw [Real.norm_eq_abs, sq_abs] at hs
    simpa only [pow_two] using hs
  have hd : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) d]
  calc
    (∑ i, x i * x i) ≤ ∑ _ : Fin d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = (d : ℝ) * ‖x‖ ^ 2 := by simp
    _ ≤ ((d : ℝ) + 1) ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    _ = (((d : ℝ) + 1) * ‖x‖) ^ 2 := by ring

end QSH
