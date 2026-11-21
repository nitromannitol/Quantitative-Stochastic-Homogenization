import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakDivergenceZero
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanNormToLp
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallPoincareEstimate
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialBallVolume

/-!
# Scaling positive Euclidean ball mean squares

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/BallMeanSquareScaling.lean`.

The exact volume factor relates
normalized spatial squares to a monotone, unnormalized energy integral.
-/

open MeasureTheory

open scoped Pointwise

namespace QSH

/-- Positive-radius Euclidean ball volumes have their exact dilation factor. -/
theorem volume_real_euclideanBall {d : ℕ} (R : ℝ) (hR : 0 < R) :
    volume.real (ball (0 : Vec d) R) = R^d * volume.real (ball (0 : Vec d) 1) := by
  have hs : R • ball (0 : Vec d) 1 = ball (0 : Vec d) R := by
    rw [← Set.preimage_smul_inv₀ hR.ne']
    ext x
    simp only [Set.mem_preimage, ball, Set.mem_ofPred_eq, sub_zero,
      euclideanNorm_smul _ (inv_nonneg.mpr hR.le)]
    rw [inv_mul_lt_iff₀ hR, mul_one]
  change (volume (ball (0 : Vec d) R)).toReal = _
  rw [← hs, Measure.addHaar_smul_of_nonneg volume hR.le,
    Module.finrank_fin_fun, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
  rfl

/-- Squared spatial energy increases with the positive radius. -/
theorem monotoneOn_integral_sq_euclideanBall {d : ℕ} (u : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) :
    MonotoneOn (fun R => ∫ x in ball 0 R, u x^2) (Set.Ioi 0) := by
  intro R hR S hS hRS
  apply setIntegral_mono_set (hu S hS).integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  exact Filter.Eventually.of_forall fun x hx => lt_of_lt_of_le hx hRS

end QSH
