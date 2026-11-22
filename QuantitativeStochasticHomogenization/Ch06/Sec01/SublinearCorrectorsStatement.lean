import QuantitativeStochasticHomogenization.AppA.OsNotation
import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrector

/-!
# Sublinearity of the first-order and flux correctors

Moved from einstein-relation-lean c97689e `EinsteinFull/External/Draft/AKMSublinearCorrectorsV2.lean`.
-/

open MeasureTheory

namespace QSH

/-- **Lemma 3.17, (3.85)–(3.86), Lemma 6.1 and Proposition 6.2, (6.13).** For `d ≥ 2` and
`Λ > 1` there are `β, C > 0` such that for every `s ∈ (0, d)` there is `C_s` with: for every law
satisfying (P1)–(P2), every unit slope `e` and every corrector `φ_e`, a flux corrector exists
(Lemma 6.1, selected by (6.7)), and for every flux corrector `S` there is a random scale
`X ≥ 1` with `X ≤ O_s(C_s)` above which the normalized `L²(B_r)` oscillations of `φ_e` and `S`
are at most `C r^{1 - β(d - s)}` and the normalized gradient energy of `φ_e` is at most `C`. Only
the oscillation part of (3.85) is stated. -/
def sublinearCorrectorsStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 1 < K →
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
    ∀ s : ℝ, 0 < s → s < d → ∃ Cs : ℝ, 0 < Cs ∧
    ∀ (P : Measure (CoefficientField d K)), LawHypotheses P →
    ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : Corrector P e,
      Nonempty (FluxCorrector φ) ∧
      ∀ S : FluxCorrector φ, ∃ X : CoefficientField d K → ℝ,
        Measurable X ∧ OsBound P X s Cs ∧
        ∀ᵐ a ∂P, 1 ≤ X a ∧ ∀ r : ℝ, X a ≤ r →
          Real.sqrt (⨍ x in ball 0 r,
            |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) +
          Real.sqrt (⨍ x in ball 0 r,
            frobeniusNorm (S.potential a x -
              (Matrix.of fun i j => ⨍ y in ball 0 r, S.potential a y i j)) ^ 2) ≤
                C * r ^ (1 - β * ((d : ℝ) - s)) ∧
          Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ C

end QSH
