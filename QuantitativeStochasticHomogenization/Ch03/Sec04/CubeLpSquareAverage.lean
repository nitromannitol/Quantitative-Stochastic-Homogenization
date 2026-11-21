import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MultiscalePoincareVector
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientEllipticity
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.MultiscaleVectorAverages
import Homogenization.HighContrast.Coupled.WeakForm
import Homogenization.Sobolev.H1.OriginCubeSymmetry
import Homogenization.Sobolev.Foundations.DifferenceQuotient
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.L2Space
import Homogenization.Sobolev.H1.Definitions
import Homogenization.Sobolev.H1.BasicLemmas
import Homogenization.Sobolev.PotentialSolenoidalL2
import Homogenization.CoarseGraining.BlockFormalism
import Mathlib.Topology.Order.MonotoneConvergence
import Homogenization.CoarseGraining.Definitions
import Homogenization.CoarseGraining.CoarseBounds.AeBridge
import Homogenization.CoarseGraining.MuOperator.AEEOperator.CoeffOperatorData
import Homogenization.CoarseGraining.OriginCubeOpenBridge
import Homogenization.Book.Ch02.Theorems.DeterministicIdentities
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import Homogenization.Book.Ch02.Theorems.Quadraticity
import Homogenization.CoarseGraining.Translation
import Homogenization.Geometry.TriadicCubeTranslation
import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
import Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Homogenization.CoarseGraining.CoarseBounds.Sandwich
import Homogenization.Internal.Ch02.Representatives
import Homogenization.Book.Ch02.Theorems.MatrixPositivity
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Homogenization.PDE.DirichletRHS
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.EnergyDensities
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.ParentRestriction
import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.EnergyDefect
import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
import Homogenization.Book.Ch04.Theorems.CanonicalSolutions.Measurability
import Homogenization.Probability.RegCoeffField.EllipticSupport
import Homogenization.Book.Ch04.Theorems.Expectations
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CoarseAverages
import Mathlib.Algebra.Order.Chebyshev
import Homogenization.Geometry.TriadicPartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
import Homogenization.Probability.EfronStein.TwoPoint
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities
import Homogenization.Book.Ch02.Theorems.GradientUniqueness
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube

/-!
# Normalized square averages

Moved from einstein-relation-lean c97689e `EinsteinFull/Homogenization/CubeLpSquareAverage.lean`.

For a square-integrable function, the square of the normalized cube `L²` norm
is the normalized spatial average of its square. This identifies the norm in
the optimizer flatness estimate of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, (2.47).
-/

open scoped ENNReal

open MeasureTheory

open _root_.Homogenization

namespace QSH

/-- The normalized cube `L²` norm squared equals the integrable spatial
average of the square. -/
theorem integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq {d : ℕ} (Q : TriadicCube d)
    (f : _root_.Homogenization.Vec d → ℝ) (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => (f x) ^ 2) (normalizedCubeMeasure Q) ∧
      (cubeLpNorm Q 2 f) ^ 2 = cubeAverage Q (fun x => (f x) ^ 2) := by
  refine ⟨hf.integrable_sq, ?_⟩
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact toReal_eLpNorm_two_sq_eq_integral_sq hf

end QSH
