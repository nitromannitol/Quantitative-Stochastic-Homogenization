import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Changing spatial weak representatives

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/SpatialWeakCongruence.lean`.

Conditional and center averages agree
only almost everywhere. Spatial weak equations are invariant under these
changes of representative, with local integrability retained on the domain.
-/

open MeasureTheory

namespace QSH

/-- An almost-everywhere equality on an open domain preserves local
integrability there.
-/
theorem locallyIntegrableOn_congr_ae {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hfg : f =ᵐ[volume.restrict U] g) : LocallyIntegrableOn g U volume := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  exact (hf.integrableOn_compact_subset hKU hK).congr
    (hfg.filter_mono (ae_mono (Measure.restrict_mono hKU le_rfl)))

/-- Both representatives in a weak partial derivative may be replaced
on a spatial null set.
-/
theorem hasWeakPartialDerivative_congr_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {j : Fin d} {f g f' g' : Vec d → ℝ}
    (h : HasWeakPartialDerivative U j f g)
    (hf : f =ᵐ[volume.restrict U] f') (hg : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDerivative U j f' g' := by
  refine ⟨locallyIntegrableOn_congr_ae hU h.1 hf,
    locallyIntegrableOn_congr_ae hU h.2.1 hg, ?_⟩
  intro ψ hψ
  calc
    (∫ x in U, f' x * coordinateDerivative j ψ x) =
        ∫ x in U, f x * coordinateDerivative j ψ x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -(∫ x in U, g x * ψ x) := h.2.2 ψ hψ
    _ = -(∫ x in U, g' x * ψ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

/-- A weak gradient uses one spatial almost-everywhere vector equality.
-/
theorem hasWeakGradient_congr_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {f f' : Vec d → ℝ} {G G' : Vec d → Vec d}
    (h : HasWeakGradient U f G)
    (hf : f =ᵐ[volume.restrict U] f') (hG : G =ᵐ[volume.restrict U] G') :
    HasWeakGradient U f' G' := by
  intro j
  exact hasWeakPartialDerivative_congr_ae hU (h j) hf
    (hG.mono fun _ hx => congrFun hx j)

end QSH
