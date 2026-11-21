import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
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

/-!
# Deterministic interior estimates used for Lemma 5.1

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/External/GilbargTrudinger.lean`.

Proposed unfrozen contracts from Gilbarg--Trudinger, *Elliptic Partial
Differential Equations of Second Order*, 2001 reprint of the revised second
edition: Theorem 8.17, (8.46), p. 194, and Theorem 8.32, (8.86), p. 210.
Application: the application.

These are explicitly the homogeneous divergence-form specializations needed
here: `b = c = d = f = g = 0`. In 8.17 this sets `ν = k(R) = 0`, and one may
choose any `q > n`; `p > 1` is retained. The measurable coefficient hypotheses
(8.5)--(8.6), including the entrywise square-sum bound, are retained.
The conclusion is almost everywhere, rather than a statement about arbitrary
representatives of Sobolev classes.

In 8.32 the domain is a ball and the interior domain is its concentric half
ball. Coefficients satisfy (8.5) and the full bounded Hölder condition (8.85).
The solution is already `C^{1,α}`, as required by the printed theorem. This
contract does not assert existence of such a representative from an H¹ class.
The conclusion records the gradient part of (8.86), with zero right-hand side.
All lengths, Hölder distances and gradient norms are Euclidean. Scalar Lᵖ
norms are unnormalized, as in the book. No deterministic result is asserted
as a Lean theorem in this file.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- Ball specialization, with `p = 2` and `S = Ω`, of GT (7.45),
p. 164 (Lemmas 7.12 and 7.16). Both norms are unnormalized Euclidean
Lebesgue norms. The ball is convex; no boundary condition is imposed.
This proposed additional literature contract includes every radius and
center, and its constant depends only on the dimension.
Application: the Poincaré step in the application. -/
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
