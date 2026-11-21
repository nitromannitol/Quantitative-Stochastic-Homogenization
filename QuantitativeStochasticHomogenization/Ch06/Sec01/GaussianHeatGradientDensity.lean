import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# The heat formula for the flux corrector

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatSelectedSkewMeaningSupport.lean`.

The Euclidean heat formula (6.7) for the gradient of a skew flux-corrector column: the density `heatGradientDensity`, its spatial integral, and the iterated local `L²` selection predicate.
-/

open MeasureTheory

namespace QSH

noncomputable def gaussianHeatKernel {d : ℕ} (t : ℝ) (_ht : 0 < t)
    (z : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
    Real.exp (-euclideanSq z / (4 * t))

noncomputable def centeredGaussianHeatKernel {d : ℕ} (t : ℝ) (ht : 0 < t)
    (y x : Vec d) : ℝ :=
  gaussianHeatKernel t ht (y - x)

noncomputable def centeredGaussianHeatKernelSecondDerivative {d : ℕ}
    (t : ℝ) (ht : 0 < t) (y x : Vec d) (i k : Fin d) : ℝ :=
  coordinateDerivative k
    (fun z => coordinateDerivative i
      (fun w => centeredGaussianHeatKernel t ht y w) z) x

/-- The `k` component of the row/column ordered AKM (6.7) integrand. -/
noncomputable def heatGradientDensity {d : ℕ} (g : Vec d → Vec d)
    (t : ℝ) (row col k : Fin d) (x y : Vec d) : ℝ :=
  if ht : 0 < t then
    g y col * centeredGaussianHeatKernelSecondDerivative t ht y x row k -
      g y row * centeredGaussianHeatKernelSecondDerivative t ht y x col k
  else 0

/-- The full-space spatial integral in AKM (6.7), before the positive-time
integration is performed. -/
noncomputable def heatGradientSpaceIntegral {d : ℕ}
    (g : Vec d → Vec d) (t : ℝ) (row col k : Fin d) (x : Vec d) : ℝ :=
  ∫ y : Vec d, heatGradientDensity g t row col k x y

def iteratedHeatTimeWindow (m n : ℕ) : Set ℝ :=
  Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)

/-- The AKM (6.7) heat-gradient formula in its printed order: the full-space
integral in `y` is evaluated at each time before integration in positive time.
The independent cutoffs approximate the two time endpoints without truncating
the spatial integral. -/
noncomputable def iteratedHeatGradientTruncation {d : ℕ}
    (g : Vec d → Vec d) (m n : ℕ) (row col k : Fin d) (x : Vec d) : ℝ :=
  ∫ t in iteratedHeatTimeWindow m n,
    heatGradientSpaceIntegral g t row col k x

end QSH
