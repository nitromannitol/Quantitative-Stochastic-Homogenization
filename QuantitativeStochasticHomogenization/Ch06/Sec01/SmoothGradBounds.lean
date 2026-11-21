import QuantitativeStochasticHomogenization.Front.Notation
import HCPoly.Setup.AnalyticCarriers

/-!
# Gradients of smooth functions

Moved from einstein-relation-lean c97689e `EinsteinFull/Homogenization/SmoothGradBounds.lean`.

The coordinates of the gradient of a differentiable function are bounded by the operator norm
of its derivative, so the squared Euclidean length of the gradient is at most the dimension
times the squared operator norm.
-/

namespace QSH

open _root_.Homogenization _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem abs_fderiv_apply_basisVec_le (η : _root_.Homogenization.Vec d → ℝ) (x : _root_.Homogenization.Vec d) (i : Fin d) :
    |fderiv ℝ η x (basisVec i)| ≤ ‖fderiv ℝ η x‖ := by
  have h := (fderiv ℝ η x).le_opNorm (basisVec i)
  have hb : ‖(basisVec i : _root_.Homogenization.Vec d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hji : j = i <;> simp [basisVec, hji]
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ η x (basisVec i)‖ ≤ ‖fderiv ℝ η x‖ * ‖(basisVec i : _root_.Homogenization.Vec d)‖ := h
    _ ≤ ‖fderiv ℝ η x‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖fderiv ℝ η x‖ := mul_one _

theorem vecNormSq_smoothGrad_le (η : _root_.Homogenization.Vec d → ℝ) (x : _root_.Homogenization.Vec d) :
    vecNormSq (smoothGrad η x) ≤ d * ‖fderiv ℝ η x‖ ^ 2 := by
  change ∑ i, smoothGrad η x i * smoothGrad η x i ≤ _
  calc ∑ i, smoothGrad η x i * smoothGrad η x i ≤ ∑ _i : Fin d, ‖fderiv ℝ η x‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := abs_fderiv_apply_basisVec_le η x i
        have h2 : |smoothGrad η x i| ≤ ‖fderiv ℝ η x‖ := h
        nlinarith [abs_nonneg (smoothGrad η x i), sq_abs (smoothGrad η x i)]
    _ = d * ‖fderiv ℝ η x‖ ^ 2 := by simp

end QSH
