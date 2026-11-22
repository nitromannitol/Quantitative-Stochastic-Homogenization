import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrector

/-!
# The divergence of the flux corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1, (6.6): the rows of the flux corrector `S_e` have divergence `a(e + ∇φ_e) - D e`, where
`D e` is the large-scale average of the flux `a(e + ∇φ_e)`.

The statement is recorded here as `fluxCorrectorDivergenceStatement`. For the heat-selected flux
corrector, the row divergence of the truncation `∫_b^T` of the heat formula (6.7) is
`H_b q - H_T q` for the centered flux `q`, since `q` is divergence free; `H_b q → q` as `b → 0`,
and `H_T q` converges to a constant as `T → ∞` by the scale pairing bounds of the flux defect
`a(e + ∇φ_e) - ā e` (`exists_uniform_flux_pairing`).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **Lemma 6.1, (6.6).** For every flux corrector `S` of a corrector `φ_e` of a law satisfying
(P1)–(P2), there is a deterministic vector `D` such that, almost surely, the `j`-th row of `S` has
weak divergence `(a(e + ∇φ_e))_j - D_j` on `ℝ^d`. -/
def fluxCorrectorDivergenceStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : Corrector P e, ∀ S : FluxCorrector φ,
      ∃ D : Vec d, ∀ᵐ a ∂P, ∀ j : Fin d,
        HasWeakDivergence Set.univ (fun x k => S.potential a x j k)
          (fun x => ((a x).mulVec (e + φ.grad a x)) j - D j)

end QSH
