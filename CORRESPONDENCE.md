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
- **(5.85)** is reduced to the stochastic estimate for the localized families
  (`QSH.localizedEnergy_of_localizationEstimate`); the estimate itself (Proposition 4.11 with
  Lemmas 4.19-4.22) is not formalized yet.
