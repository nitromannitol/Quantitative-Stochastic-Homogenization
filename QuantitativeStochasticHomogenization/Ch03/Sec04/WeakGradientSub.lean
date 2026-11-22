import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakDivergenceZero
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanNormToLp

/-!
# The equation for two locally agreeing coefficient fields

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/PairedParabolicEquation.lean`.

If two coefficient fields agree on the
spatial domain, subtracting their actual parabolic solutions gives a
homogeneous parabolic equation with their gradient difference. Every test
integral is integrable; subtraction does not use the total-integral zero
convention. This is the PDE entering the paired weighted energy argument.
-/

open MeasureTheory Filter

open scoped Topology

namespace QSH

/-- Subtracting two actual weak partial derivatives preserves the weak
equation and local integrability.
-/
theorem hasWeakPartialDerivative_sub {d : ℕ} {U : Set (Vec d)} {j : Fin d}
    {f₁ f₂ g₁ g₂ : Vec d → ℝ}
    (h₁ : HasWeakPartialDerivative U j f₁ g₁)
    (h₂ : HasWeakPartialDerivative U j f₂ g₂) :
    HasWeakPartialDerivative U j (fun x => f₁ x - f₂ x) (fun x => g₁ x - g₂ x) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, ?_⟩
  intro ψ hψ
  have hdψ : IsSpatialTest U (coordinateDerivative j ψ) := by
    refine ⟨(contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const,
      hψ.2.1.fderiv_apply ℝ (unitVector j), ?_⟩
    apply Set.Subset.trans ?_ hψ.2.2
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    by_contra hxs
    exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs])
  simp only [sub_mul]
  rw [integral_sub (integrableOn_mul_spatialTest h₁.1 hdψ)
      (integrableOn_mul_spatialTest h₂.1 hdψ),
    integral_sub (integrableOn_mul_spatialTest h₁.2.1 hψ)
      (integrableOn_mul_spatialTest h₂.2.1 hψ), h₁.2.2 ψ hψ, h₂.2.2 ψ hψ]
  ring

/-- The actual gradient of the difference is the difference of gradients.
-/
theorem hasWeakGradient_sub {d : ℕ} {U : Set (Vec d)}
    {f₁ f₂ : Vec d → ℝ} {G₁ G₂ : Vec d → Vec d}
    (h₁ : HasWeakGradient U f₁ G₁) (h₂ : HasWeakGradient U f₂ G₂) :
    HasWeakGradient U (fun x => f₁ x - f₂ x) (fun x => G₁ x - G₂ x) := by
  intro j
  exact hasWeakPartialDerivative_sub (h₁ j) (h₂ j)

end QSH
