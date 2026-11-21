import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatKernelMixedHessian
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# The heat-gradient density as a stationary convolution

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatGradientConvolution.lean`.

The two derivatives of the centered
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

/-- The density is a difference of two mixed-Hessian
convolution integrands, with exactly its original row and column signs. -/
theorem heatGradientDensity_eq_mixedHessian {d : ℕ} (g : Vec d → Vec d)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d) (x y : Vec d) :
    heatGradientDensity g t j k l x y =
      g y k * coordinateDerivative l (coordinateDerivative j
        (euclideanHeatKernel (d := d) t)) (x - y) -
      g y j * coordinateDerivative l (coordinateDerivative k
        (euclideanHeatKernel (d := d) t)) (x - y) := by
  unfold heatGradientDensity
  rw [dite_eq_left ht]
  change g y k * coordinateDerivative l (coordinateDerivative j
      (fun w => euclideanHeatKernel t (y - w))) x -
    g y j * coordinateDerivative l (coordinateDerivative k
      (fun w => euclideanHeatKernel t (y - w))) x = _
  rw [centeredHeatKernel_secondDerivative, centeredHeatKernel_secondDerivative]

end QSH
