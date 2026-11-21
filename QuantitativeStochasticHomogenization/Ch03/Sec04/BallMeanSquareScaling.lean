import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanNormToLp
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallPoincareEstimate
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialBallVolume
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.List
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Abel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Topology.Continuous
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Scaling positive Euclidean ball mean squares

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/BallMeanSquareScaling.lean`.

Source: the application. The exact volume factor relates
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
    simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, sub_zero,
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
