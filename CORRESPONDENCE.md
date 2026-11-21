# Correspondence with the book

This file records where the Lean development departs from the book (Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Springer, 2019): a result
proved by a route different from the proof in the book, a hypothesis that the book leaves implicit
and the statement makes explicit, a measurability, integrability or summability fact that the
book takes for granted, and any other difference between a statement of the book and its Lean
form. Each entry names the numbered result of the book and the Lean declaration.

No result of the book is formalized in this repository yet, so there is no entry yet.

## Section 4.4: the localization of pp. 155-156

- **Existence of the coordinate minimizers and of the minimizer of smallest `L²` norm** (p. 155-156,
  "the existence of a minimizer follows"; "select the one with the smallest `L²(B_T)`-norm").
  `QSH.exists_isLeastNormCoordinateMinimizer`. The book uses weak continuity of `I` on `K` in
  `H¹(B_T)`. The Lean proof works in the Hilbert space of pairs (potential, gradient) in
  `L²(B_T)`, where `K` is closed and convex, and replaces weak compactness by the fact that a
  decreasing sequence of nonempty closed convex sets with bounded norms has a nonempty
  intersection (`QSH.nonempty_iInter_of_isQuadraticGauge`); this gives the minimizer and the
  minimizer of least norm in one step (`QSH.exists_lexicographic_minimizer`). Boundedness of the
  sublevel sets uses the Poincaré inequality on balls of the elliptic regularity library and a
  lower bound for the Gaussian observation of constants.
- **Uniqueness.** The book does not need uniqueness of the minimizer. The minimizer of least norm
  is unique up to null sets, with its gradient (`QSH.IsLeastNormCoordinateMinimizer.toPair_eq`),
  so `J₁^{(δ)}` does not depend on the selected basis (`QSH.localizedJ1_eq_of_basis`).
- **Measurability of `J₁^{(δ)}(z, r, p, q)` for `F(B_T(z))`** (p. 156, "It is clear that each of the
  functions `wᵢ` is `F(B_T)`-measurable"). `QSH.measurable_localizedJ1_of_basis`. The Lean proof:
  (i) a representative of the coefficients on `B_T(z)` jointly measurable for
  `Borel ⊗ F(B_T(z))`, from smooth averages (`QSH.localRepresentative`), so that integrals of the
  coefficients against integrable functions are `F(B_T(z))`-measurable; (ii) the `a`-harmonic
  extension of a gradient pair, through the energy projection onto the closed span of mean-zero
  test pairs, which is measurable in `a` because it is the unique minimizer of an energy that is
  measurable in `a` along a fixed dense sequence (`QSH.measurable_energyProj`); (iii) a measurable
  dense sequence in `K` made of rescaled harmonic extensions
  (`QSH.exists_measurable_dense_admissible`); (iv) measurable selection of the minimizer of least
  norm from such a sequence (`QSH.measurable_lexicographic_minimizer_param`); (v) `J₁^{(δ)}` as a
  supremum over a countable dense set of coefficient vectors of a polynomial whose coefficients
  are weighted pairings, measurable in `a` and continuous in the gradients.
- **Joint measurability in the coefficients and the center** (used in the proof of Proposition
  4.12, Section 4.5, where `x ↦ J₁^{(δ)}(x, r, p, q)` is integrated over boxes; the book does not
  discuss it). `QSH.measurable_indicator_localizedJ1`, from the translation covariance of the
  construction (`QSH.localizedJ1_eq_translate`) and the measurability of the translation of the
  coefficients for the local σ-algebra of a neighbourhood of the centers.
- **Lemma 4.22** is formalized in deterministic form (`QSH.abs_J1Heat_sub_localizedJ1_le`): the
  hypotheses are the approximation property of Lemma 4.21, stated for the gradients rescaled by
  `Φ_{z,r}^{1/2}` on `B_{r^{1+δ}}(z)` and restricted to gradients of bounded weighted norm, and the
  bound (4.104) on the energies outside the ball; the conclusion is a bound on
  `|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)|`. The book's proof uses maximizers; the Lean proof
  uses near maximizers, whose weighted norm is bounded by the concavity of the energy
  (`QSH.IsConcaveEnergy.abs_sSup_sub_sSup_le`), so it needs neither the existence of maximizers nor
  the finite dimension of `A₁`.
- **(4.104), the energies outside the ball** (p. 162). `QSH.outer_le_of_gaussianGram`: outside
  `B_T(z)` the mask of scale `r` is at most `2^{d/2} exp(-T²/(8r²))` times the mask of scale
  `√2 r`, so the outer energy of a combination of spanning fields `W_i` is at most that factor
  times `d E / m` times its inner energy, where `E` bounds the Gaussian energies of the `W_i` at
  scale `√2 r` and `m` is a lower bound for their Gaussian Gram matrix inside the ball. The lower
  bound (`QSH.heatGram_lower_bound`, constant `QSH.heatGramConstant d`) comes from the Poincaré
  inequality applied to `∑ ξ_i u_i`, where the `u_i` are functions with weak gradients `W_i` that
  are close to the coordinates in `L²(B_r(z))` (the corrected coordinates above the minimal
  scale): a linear function `ξ·(x - z)` oscillates by `|ξ| r/2` on one of two balls of radius
  `r/4` (`QSH.integral_dot_sub_sq_ge`).
- **(4.91) from matched columns.** `QSH.localizationDistances_of_matched`: if the rescaled
  gradients of `A₁` on `B_T(z)` are exactly the combinations of tuples `G_i` with
  `μ ∑ |c_i| ≤ ‖∑ c_i G_i‖`, and the `i`-th localized coordinate is within `ρ ≤ μ/2` of `G_i`, then
  both directed distances at norm `L` are at most `2 L ρ / μ`.
- **(5.85)** is reduced to the stochastic estimate for the localized families
  (`QSH.localizedEnergy_of_localizationEstimate`, `QSH.localizedEnergy_of_uniformApproximation`),
  and the almost sure hypotheses of Lemma 4.22 are reduced
  (`QSH.LocalizationApproximationAtUniform.of_matched`) to properties of the corrected
  coordinates (sublinearity on `B_r(z)`, Gaussian energies at scale `√2 r`, the first-order
  Liouville representation of `A₁`) and to fields `V_i` matched with the localized coordinates in
  `L²(Φ_{z,r}, B_T(z))`. The construction of the matched fields (the proof of Lemma 4.21 proper)
  and the stochastic bounds are not formalized yet.
