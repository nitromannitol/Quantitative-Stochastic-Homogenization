import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# The Poincaré inequality on balls

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/External/GilbargTrudinger.lean`.

The statement `BallPoincareEstimate`: the Poincaré inequality on Euclidean balls with a constant depending only on the dimension, as in Gilbarg and Trudinger, *Elliptic Partial Differential Equations of Second Order*, (7.45). It is proved in `BallPoincareFromPDE` from the convex domain inequality of `PDEFoundation`.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- Ball specialization, with `p = 2` and `S = Ω`, of GT (7.45),
p. 164 (Lemmas 7.12 and 7.16). Both norms are unnormalized Euclidean
Lebesgue norms. The ball is convex; no boundary condition is imposed.
The statement includes every radius and center, and its constant depends
only on the dimension. -/
def BallPoincareEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (y : Vec d) (R : ℝ), 0 < R →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        MemLp u 2 (volume.restrict (ball y R)) →
        MemLp g 2 (volume.restrict (ball y R)) → HasWeakGradient (ball y R) u g →
        Real.sqrt (∫ x in ball y R,
          |u x - ⨍ z in ball y R, u z ∂volume| ^ 2 ∂volume) ≤
          C * R * Real.sqrt (∫ x in ball y R, euclideanSq (g x) ∂volume)

end QSH
