import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Metrizable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Joint measurability for heat transfer

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatConvolutionMeasurability.lean`.

Source: the application–1031`. The time-dependent convolutions in the
heat-transfer identity are measurable jointly in time and environment.
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
