import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine

/-!
# The first-order Liouville theorem

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 3.8 for `k = 1`, (3.39): almost surely every element of `A₁` is a corrected affine
function `c + p·x + ∑ᵢ pᵢ φ_{eᵢ}`. Together with `ae_exists_harmonicA1_correctedAffine` this
identifies `A₁` with the space of corrected affine functions, of dimension `d + 1`.

The statement is recorded here as `firstOrderLiouvilleStatement`; it is proved by the first-order
route (the sublinearity of the first-order and flux correctors, a comparison with a harmonic
function of the homogenized matrix on nearly full ellipsoids, and a quadratic decay iteration),
without the higher-order regularity theory of Theorem 3.8.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **Theorem 3.8 for `k = 1`.** For `d ≥ 2`, `Λ > 1` and every law satisfying (P1)–(P2) with
correctors `S`, almost surely every `w ∈ A₁` equals `c + p·x + ∑ᵢ pᵢ φ_{eᵢ}` for some `c` and
`p`, with gradient `p + ∑ᵢ pᵢ ∇φ_{eᵢ}`, almost everywhere. -/
def firstOrderLiouvilleStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ S : HomogenizationData P, ∀ᵐ a ∂P, ∀ w : HarmonicA1 a, ∃ (c : ℝ) (p : Vec d),
      (∀ᵐ x ∂(volume : Measure (Vec d)), w.potential x = c + correctedAffine S a p x) ∧
      (∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a p x)

end QSH
