import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatKernelMixedHessian
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

/-!
# The source heat-gradient density as a stationary convolution

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatGradientConvolution.lean`.

Source: the application. The two derivatives of the centered
Gaussian are the ordinary mixed Hessian at the relative spatial argument.
-/

open MeasureTheory

namespace QSH

private theorem euclideanHeatKernel_sub_comm {d : ℕ} (t : ℝ) (x y : Vec d) :
    euclideanHeatKernel t (y - x) = euclideanHeatKernel t (x - y) := by
  have hs : euclideanSq (y - x) = euclideanSq (x - y) := by
    unfold euclideanSq dot
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  simp only [euclideanHeatKernel, hs]

/-- Twice differentiating the centered Gaussian gives its ordinary Hessian. -/
theorem centeredHeatKernel_secondDerivative {d : ℕ} (t : ℝ)
    (i j : Fin d) (x y : Vec d) :
    coordinateDerivative j (coordinateDerivative i
      (fun w => euclideanHeatKernel t (y - w))) x =
      coordinateDerivative j (coordinateDerivative i
        (euclideanHeatKernel (d := d) t)) (x - y) := by
  have heq : (fun w => euclideanHeatKernel t (y - w)) =
      (fun w => euclideanHeatKernel t (w - y)) :=
    funext fun w => euclideanHeatKernel_sub_comm t w y
  rw [heq]
  have hfirst : coordinateDerivative i (fun w => euclideanHeatKernel t (w - y)) =
      fun w => coordinateDerivative i (euclideanHeatKernel t) (w - y) := by
    funext w
    unfold coordinateDerivative
    rw [fderiv_comp_sub]
  rw [hfirst]
  exact congrArg (fun A : Vec d →L[ℝ] ℝ => A (unitVector j))
    (fderiv_comp_sub (𝕜 := ℝ) (f := coordinateDerivative i
      (euclideanHeatKernel (d := d) t)) (x := x) y)

/-- The literal source density is a difference of two mixed-Hessian
convolution integrands, with exactly its original row and column signs. -/
theorem heatGradientDensity_eq_mixedHessian {d : ℕ} (g : Vec d → Vec d)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d) (x y : Vec d) :
    heatGradientDensity g t j k l x y =
      g y k * coordinateDerivative l (coordinateDerivative j
        (euclideanHeatKernel (d := d) t)) (x - y) -
      g y j * coordinateDerivative l (coordinateDerivative k
        (euclideanHeatKernel (d := d) t)) (x - y) := by
  unfold heatGradientDensity
  rw [dif_pos ht]
  change g y k * coordinateDerivative l (coordinateDerivative j
      (fun w => euclideanHeatKernel t (y - w))) x -
    g y j * coordinateDerivative l (coordinateDerivative k
      (fun w => euclideanHeatKernel t (y - w))) x = _
  rw [centeredHeatKernel_secondDerivative, centeredHeatKernel_secondDerivative]

end QSH
