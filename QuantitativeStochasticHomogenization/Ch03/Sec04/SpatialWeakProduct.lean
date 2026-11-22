import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakDivergenceZero
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Product rules for spatial weak equations

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/SpatialWeakProduct.lean`.

Multiplying a weak gradient or row
divergence by a smooth spatial weight produces the terms called `H_R`
and `K_R` in the center average. All equations below use actual compactly
supported tests and retain local integrability of every field.
-/

open MeasureTheory

namespace QSH

/-- Local integrability suffices for the pairing with a smooth test
supported inside the domain.
-/
theorem integrableOn_mul_spatialTest {d : ℕ} {U : Set (Vec d)}
    {f ψ : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hψ : IsSpatialTest U ψ) : IntegrableOn (fun x => f x * ψ x) U volume := by
  have hfK := hf.integrableOn_compact_subset hψ.2.2 hψ.2.1
  have hint := hfK.mul_continuousOn hψ.1.continuous.continuousOn hψ.2.1
  have hs : Function.support (fun x => f x * ψ x) ⊆ tsupport ψ := by
    intro x hx
    apply subset_tsupport ψ
    exact (mul_ne_zero_iff.mp hx).2
  exact ((integrableOn_iff_integrable_of_support_subset hs).mp hint).integrableOn

end QSH
