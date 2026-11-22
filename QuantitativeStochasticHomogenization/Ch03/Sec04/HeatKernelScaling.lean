import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.HeatTransferIdentity
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Scaling and initial values of heat-kernel convolutions

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatKernelScaling.lean`.

A compact continuous spatial kernel
convolved with the Euclidean heat kernel tends to its initial value as time
decreases to zero. The proof uses Gaussian scaling and dominated convergence.
-/

open MeasureTheory Filter

open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Spatial smoothness of the Gaussian. -/
theorem contDiff_euclideanHeatKernel_top (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanHeatKernel (d := d) t) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanSq x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∑ i, x i * x i)
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  exact contDiff_const.mul ((hsq.neg.div_const (4 * t)).exp)

end QSH
