import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.HeatTransferIdentity
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaling and initial values of heat-kernel convolutions

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatKernelScaling.lean`.

Source: the application–1022`. A compact continuous spatial kernel
convolved with the Euclidean heat kernel tends to its initial value as time
decreases to zero. The proof uses Gaussian scaling and dominated convergence.
-/

open MeasureTheory Filter

open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Spatial smoothness of the Gaussian. -/
theorem contDiff_euclideanHeatKernel (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanHeatKernel (d := d) t) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanSq x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∑ i, x i * x i)
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  exact contDiff_const.mul ((hsq.neg.div_const (4 * t)).exp)

end QSH
