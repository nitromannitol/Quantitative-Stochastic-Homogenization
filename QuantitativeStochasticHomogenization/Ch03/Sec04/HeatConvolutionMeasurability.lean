import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Joint measurability of the heat kernel

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatConvolutionMeasurability.lean`.

The Euclidean heat kernel is jointly measurable in time and space.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Joint measurability of the explicit Gaussian kernel. -/
theorem measurable_euclideanHeatKernel_joint :
    Measurable (fun q : ℝ × Vec d => euclideanHeatKernel q.1 q.2) := by
  have hsq : Measurable (fun q : ℝ × Vec d => euclideanSq q.2) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).mul
        ((measurable_pi_apply i).comp measurable_snd)
  unfold euclideanHeatKernel
  exact ((measurable_const.mul measurable_fst).pow_const _).mul
    (Real.continuous_exp.measurable.comp (hsq.neg.div (measurable_const.mul measurable_fst)))

end QSH
