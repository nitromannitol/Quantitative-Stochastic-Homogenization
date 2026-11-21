import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Spatial weak equations

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Calculus/Weak.lean`.

All equations are tested against actual smooth functions with compact support.
The reference measure is coordinate Lebesgue measure on `Fin d → ℝ`; geometric
balls are expressed using the Euclidean norm defined in the environment module.
-/

open MeasureTheory

namespace QSH

theorem hasWeakDivergence_zero {d : ℕ} (U : Set (Vec d)) :
    HasWeakDivergence U (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun _ => ?_, ?_, ?_⟩
  · exact locallyIntegrableOn_zero
  · exact locallyIntegrableOn_zero
  · intro φ _
    simp [dot]

end QSH
