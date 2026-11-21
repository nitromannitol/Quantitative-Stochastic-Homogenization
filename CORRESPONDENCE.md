# Correspondence with the book

This file records where the Lean development departs from the book (Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Springer, 2019): a result
proved by a route different from the proof in the book, a hypothesis that the book leaves implicit
and the statement makes explicit, a measurability, integrability or summability fact that the
book takes for granted, and any other difference between a statement of the book and its Lean
form. Each entry names the numbered result of the book and the Lean declaration.

## Section 4.5: Proposition 4.12

Lean: `QSH.fluctuationEstimatesFor_locFieldEstimate`
(`QuantitativeStochasticHomogenization/Ch04/Sec05/Proposition412.lean`), with (4.117) as
`QSH.exists_blockBound` and (4.115) as `QSH.exists_centeredOsBound_field`.

- **Localization by a measurable family.** The proof integrates the localized quantities
  `x ↦ J₁^{(δ)}(x, r)` over cubes and uses that the integrals over cubes at distance larger than
  one are independent. Definition 4.9 provides one `F(B_{r^{1+δ}}(z))`-measurable random variable
  for each center `z`; the proof needs a family that is jointly measurable in the coefficients and
  the center, with the restriction to a set of centers measurable for the coefficients in its
  neighbourhood. The proposition is stated with this localization (`LocFieldEstimate`, Section
  4.2), which implies Definition 4.9 (`LocFieldEstimate.locEstimate`). Integrals over the `2^d`
  large cubes, at mutual distance larger than one after thickening, are independent; the cells of
  the frame are handled by the colouring of Lemma A.12, as in the book.
- **The inner scale of Step 1.** The book takes `r₁ = R^{η₁}/2` in (4.120). The induction hypothesis
  at the side `R/2` only covers scales `r ≥ (R/2)^{η₁}`, and `R^{η₁}/2 < (R/2)^{η₁}` since `η₁ < 1`.
  The Lean proof takes `r₁ = (R/2)^{η₁}`; the constraints of Step 2 (`r₁ ∈ [R'^{η₁}, R'^{η₂}]` for
  the cells of side `R' = R^{1-2ε}`, the separation `R' - 2 r₁^{1+δ} > 1`, and `r₁^{-α} ≤ C R^{-β-ε}`)
  hold for `R` large with this choice.
- **The decomposition in Step 2.** The book partitions the cube of side `R + R^{1-2ε}` minus the
  `2^d` cubes of side `R/2` into cubes of side `R^{1-2ε}`. The Lean proof uses the lattice cells
  of side `R' = R^{1-2ε}` around the center, restricts the weight to the cells that meet the
  complement of the large cubes (the frame cells, at most `5 d (2N+1)^{d-1}` of them for
  `N = ⌊R/(2R')⌋ + 2`), and bounds the rest of space by the Gaussian tail; the exponents are those
  of the book.
- **Hypotheses made explicit.** The field `J` is jointly measurable and bounded on the unit balls of
  `p, q`, the local σ-algebras have a unit range of dependence, are monotone and are contained in
  the σ-algebra of the coefficients; the book uses `0 ≤ J₁ ≤ C` and the corresponding facts for
  `J₁`.
- **Constants.** Lemma A.11 is used with equal scales and constant one
  (`centeredOsBound_sum_of_eq_scale`), which is the form needed at `β = d/2`.
