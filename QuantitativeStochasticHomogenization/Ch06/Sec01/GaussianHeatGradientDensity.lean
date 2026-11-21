import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Heat-selected skew corrector meaning

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatSelectedSkewMeaningSupport.lean`.

This module records the Euclidean heat formula, its iterated local `L²`
selection predicate, and the source identities for a skew flux-corrector
column. The source conventions are anchored at the application,
lines 688–702, 732–735, 748, and 754–758. The heat formula follows AKM,
equation (6.7); local `L²` convergence is recorded by the selection
predicate below.
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

/-- The AKM (6.7) heat-gradient formula in its source order: the full-space
integral in `y` is evaluated at each time before integration in positive time.
The independent cutoffs approximate the two time endpoints without truncating
the spatial integral. -/
noncomputable def iteratedHeatGradientTruncation {d : ℕ}
    (g : Vec d → Vec d) (m n : ℕ) (row col k : Fin d) (x : Vec d) : ℝ :=
  ∫ t in iteratedHeatTimeWindow m n,
    heatGradientSpaceIntegral g t row col k x

end QSH
