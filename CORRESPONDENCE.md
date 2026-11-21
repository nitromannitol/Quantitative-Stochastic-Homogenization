# Correspondence with the book

This file records where the Lean development departs from the book (Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Springer, 2019): a result
proved by a route different from the proof in the book, a hypothesis that the book leaves implicit
and the statement makes explicit, a measurability, integrability or summability fact that the
book takes for granted, and any other difference between a statement of the book and its Lean
form. Each entry names the numbered result of the book and the Lean declaration.

The material of Appendix A, of the opening of Chapter 4 and of Section 4.2 listed below was moved
from [einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean); the header
of each module names the source files and commits.

## Appendix A: The O_s Notation (`AppA/OsNotation.lean`)

- **(A.1), `OsBound P X s θ`.** The measurability of `X` and the positivity of `s` and `θ` are part
  of the definition, `X₊ = max X 0`, and the expectation is the lower Lebesgue integral of
  `exp((θ⁻¹ X₊)^s)`, so that no integrability condition is needed.
- **The notation `X = O_s(θ)` (after (A.2)).** Several statements (Definitions 4.7–4.9, Lemma A.9)
  bound `|X| ≤ O_s(θ)` instead of the pair `X ≤ O_s(θ)`, `-X ≤ O_s(θ)`. The two are equivalent up
  to the factor `2^{1/s}`: `OsBound.of_abs` and `OsBound.abs_of_neg`.
- **Lemma A.1.** `OsBound.measureReal_ge_le` and `osBound_of_measureReal_ge_le`, as in the book,
  for a probability measure and a measurable `X`; both are proved through the corresponding
  statements of subdiffusive-process (`osBound_iff_ogammaLE` identifies the two notions).
- **Remark A.2.** In place of (A.3), `osBound_of_tail` assumes `P[X ≥ t A] ≤ exp(-t^q)` for
  `t ≥ 1` and some `q ≥ s`, and concludes `X ≤ O_s(8^{1/s} A)`.
- **Lemma A.3.** (i) `OsBound.of_mem_Icc` and (ii) `OsBound.mul`, as in the book. A rule that is
  not in the book, `OsBound.mono_exponent`, passes to a smaller exponent on a probability space:
  `X ≤ O_s(θ)` and `0 < s' ≤ s` give `X ≤ O_{s'}((2e - 1)^{1/s'} θ)`.
- **Lemma A.4.** The case `s ≥ 1` with `C_s = 1` is `osBound_integral`, for an s-finite measure
  `μ`, a positive measurable and integrable scale `θ` with `∫ θ dμ > 0`, and a jointly measurable
  family; it also states that `x ↦ X(x)` is almost surely `μ`-integrable, so that `∫ X dμ` is a
  Bochner integral. The proof is Jensen's inequality for the probability measure
  `θ dμ / ∫ θ dμ`, as in the book. For finite sums there is also `osBound_finset_sum`. The case
  `s ∈ (0, 1)` is `osBound_integral_of_lt_one`, on a probability space, with the explicit constant
  `C_s = (1 + (1 - s)/(s log 2))^{1/s}`; the proof is the one of the book (the convex function
  `y ↦ exp((y + t_s)^s)` is `convexOn_exp_add_rpow`), and the final choice of `σ` is made by
  Hölder's inequality.
- **(A.12), `CenteredOsBound P X s θ`.** The condition `log E[exp(λ θ⁻¹ X)] ≤ λ² ∨ |λ|^{s/(s-1)}` is
  stated as `E[exp(λ θ⁻¹ X)] ≤ exp(λ² ∨ |λ|^{s/(s-1)})` together with the integrability of
  `exp(λ θ⁻¹ X)` for every real `λ`; the measurability of `X`, `s ∈ (1, 2]` and `θ > 0` are part
  of the definition.
- **Lemma A.9.** First implication: `CenteredOsBound.osBound_abs` (`|X| ≤ O_s(4 · 8^{1/s} θ)`) and
  `CenteredOsBound.osBound_and_neg` (the form of the book, `C = 4 · 8^{1/s}`); the proof is the
  Chernoff bound and `osBound_of_tail`, not Lemma A.5. Second implication:
  `exists_centeredOsBound_of_osBound` (the form of the book) and
  `exists_centeredOsBound_of_osBound_abs` (from `|X| ≤ O_s(θ)`); the proof uses the one-variable
  bounds of the moment generating function of the library CoarseGraining (quadratic for small
  parameters and mean zero, and the large-parameter regime) in place of Lemmas A.5 and A.8. The
  constant is chosen before the probability space, which ranges over a fixed universe.
- **Lemma A.10.** `centeredOsBound_integral_of_scale`, with `C = 1`, for an s-finite measure `μ`,
  a positive measurable and integrable scale `θ` with `∫ θ dμ > 0`, and a jointly measurable
  family; it also states that `x ↦ X(x)` is almost surely `μ`-integrable. The proof is Jensen's
  inequality for `exp` and the probability measure `θ dμ / ∫ θ dμ`, not Lemmas A.4 and A.9.
  `centeredOsBound_integral` is the case of a constant scale on a finite measure, and
  `exists_centeredOsBound_integral_sub` combines it with Lemma A.9 for the centered average of a
  bounded family with `|V(x)| ≤ O_s(θ)`.
- **Lemma A.11.** `centeredOsBound_sum`, with `C = √2`, and `centeredOsBound_sum_of_eq_scale`, with
  `C = 1` for equal scales, for a family indexed by a finite type and independent in the sense of
  `iIndepFun`. The scales are positive (the book allows `θᵢ ≥ 0`).
- **Lemma A.12.** `centeredOsBound_sum_of_localSigma_cube` (coefficient fields under (P1)–(P2)) and
  `centeredOsBound_sum_of_measurable_cube` (an abstract monotone family `F` of σ-algebras with a
  unit range of dependence, `HasUnitRange`): the set `Z ⊆ R ℤ^d` is `R I` for a finite nonempty
  set `I` of lattice indices, `□_{2R}(R k)` is the open cube `cube (R • k) (2R)`, and
  `C = (2 · 4^d)^{1/2}` depends on `d` (as the proof of the book does, through its `3^d`
  classes). The partition is by the residues of `k` modulo `4` instead of the translates of
  `(3R ℤ)^d`. The general forms are `centeredOsBound_lattice_sum` (measurable sets inside the
  cubes) and `centeredOsBound_sum_of_colouring` (any colouring with separated classes, with
  `C = (2N)^{1/2}` for `N` colours).
- **Lemma A.5.** (A.4) is `exists_log_integral_exp_le_of_osBound`, with the integrability of
  `exp(λ X)` stated, and is proved from the large-parameter bound of the moment generating
  function of the library CoarseGraining applied to `X₊`, not by the computation of the book.
  (A.5) is `osBound_of_log_integral_exp_le`, with `C = 2 · 8^{1/s}`; it assumes the integrability
  of `exp(λ X)` for `λ ≥ 1` and follows the book (the Chernoff bound at `λ = (x/2)^{s-1}`), with
  `osBound_of_tail` in place of Lemma A.1 and Remark A.2.
- **Lemma A.8.** `exists_abs_log_integral_exp_sub_le`: the bound is
  `|log E[exp(λ X)] - E[X²] λ²/2| ≤ C |λ|³` (the book writes `C λ³`), with the integrability of
  `exp(2|X|)`, `X²` and `exp(λ X)` stated. The proof is the second-order Taylor bound of `exp`
  (`abs_exp_sub_quadratic_le`), `E[exp(λ X)] ≥ 1`, and `u - u² ≤ log(1 + u) ≤ u` for `u ≥ 0`,
  instead of the derivatives of `λ ↦ log E[exp(λ X)]`.
- **Lemma A.7.** `osBound_triadicCube_sub_two_integral`: the random map `ρ` is a function of
  sets, and the hypotheses are assumed for the open cubes only: (A.6) for an abstract monotone
  family `F` of sub-σ-algebras with a unit range of dependence (`HasUnitRange`), (A.7) as
  `0 ≤ ρ ≤ K` with `K > 0`, the stationarity as the identical distribution of `ρ(U)` and
  `ρ(z + U)` for `z ∈ ℤ^d`, and (A.8) only for the subdivision of a cube of side `3^{N+k}` into
  its `3^{kd}` subcubes of side `3^N` (`triadicOffset`), which is the case of (A.8) used in the
  proof. The conclusion (A.9) holds with `C = 1`: the last step uses
  `exp(y₊) ≤ exp(y) + 1` instead of the Chebyshev inequality and Lemma A.1. The subcubes are
  grouped by the residues of their indices modulo `3`, as in the book.

## Chapter 4, opening (`Ch04/Opening.lean`)

- The semigroup property of the heat kernel, used without a number in the book:
  `integral_euclideanHeatKernel_mul` (`Φ(t) ∗ Φ(s) = Φ(t + s)`) and
  `integral_heatKernel_mul_heatKernel` (`∫ Φ_{z,ρ}(y) Φ_{y,r}(w) dy = Φ_{z,√(ρ² + r²)}(w)`), for
  `t, s, ρ, r > 0`.

## Section 4.2 (`Ch04/Sec02AdditiveStructureOfJ1.lean`)

- **Definitions 4.7–4.9.** `AddEstimate`, `FlucEstimate` and `LocEstimate` are stated for an
  arbitrary random field `J(a, z, r, p, q)` and an arbitrary family `F` of local σ-algebras; for
  `J₁(Φ_{z,r}, p, q)` and the σ-algebras `F(U)` of (0.9) they are `AddJ1`, `FlucJ1` and `LocJ1`.
  The equalities `X = Y + O_s(C r^{-α})` are stated as `|X - Y| ≤ O_s(C r^{-α})` (see Appendix A),
  `B₁` is the open unit ball, and the constant `C > 0` is existential. Definition 4.7 is stated
  for `1 ≤ r < R` (the book writes `1 ≤ r ≤ R`; the mask `Φ_{z,0}` is not defined), with the
  almost sure integrability of `x ↦ Φ_{z,√(R²-r²)}(x) J(x, r, p, q)`; Definition 4.8 includes the
  integrability of `J(z, r, p, q)`.
- **Propositions 4.10–4.12** are not proved. Their conclusions are the definitions
  `ImprovementOfAdditivity`, `LocalizationEstimates` and `FluctuationEstimates` (and
  `LocalizationEstimatesFor`, `FluctuationEstimatesFor` for any localization statement monotone in
  its exponent).
- **Theorem 4.6 (i), (iii), (iv).** `additiveStructure_J1` (and `additiveStructure_of_bootstrap`,
  `additiveStructure_of_bootstrapFor` for an abstract field) assume `d ≥ 1`, a probability
  measure, the conclusions of Propositions 4.10–4.12, and, for each `s ∈ (1, 2)`, an exponent
  `α₀ > 0` with `Fluc(s, α₀)` (supplied in the book by Proposition 4.3). The proof follows the
  book with two changes: Proposition 4.12 is stated for `s ∈ (1, 2]`, so Steps 1 and 2 are run for
  `s ∈ (1, 2)` and the exponents `s ≤ 1` are reached by `OsBound.mono_exponent`; in Step 3 the
  auxiliary exponent is `α = d/2 - δ/(2(1+δ))`, for which `α(1+δ) + δ = d/2 (1+δ) + δ/2 >
  d/2 (1+δ)`. Part (ii) is not formalized.
- **`LocFieldEstimate`.** The proof of Proposition 4.12 integrates the localized variables
  `x ↦ J₁^{(δ)}(x, r, p, q)` over boxes and uses the independence of integrals over boxes at
  distance larger than one, which needs a family that is jointly measurable in the coefficients
  and the center. `LocFieldEstimate` states localization by such a family and implies
  `LocEstimate` (`LocFieldEstimate.locEstimate`).

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

## Section 5.4: Lemma 5.29

Lean: (i) `QSH.exists_blockBound_all_scales`
(`QuantitativeStochasticHomogenization/Ch05/Sec04/Lemma529Clt.lean`), (ii)
`QSH.exists_blockBound_layer` (`Lemma529Boundary.lean`), (iii) `QSH.exists_blockBound_change`
(`Lemma529Change.lean`), for centered local additive fields; for the localized energy
`QSH.blockCLT_of_inputs`, `QSH.blockBoundary_of_inputs` and `QSH.blockChange_of_inputs`
(`BlockEstimates.lean`, `BlockEstimatesBoundary.lean`).

- **Hypotheses made explicit.** The three parts are proved for any family with the properties used
  in the proof of Proposition 4.12 (`CenteredLocalFields`): boundedness, joint locality, centering
  and the additivity (5.88). For the localized energy these properties are the two explicit
  hypotheses `LocalizedFieldInput` (boundedness and joint locality of `J₁^{(δ)}`) and
  `LocalizedAdditivityInput` ((5.88) with the exponent `γ`).
- **Part (i).** (5.89) at `β = d/2` is (4.117) for these fields; the statement at every scale
  `r ∈ [R^{η₁}, R]` follows by the decomposition of Step 2 of Proposition 4.12 at the scale of the
  block, with the Gaussian tail of the heat kernel summed over the lattice.
- **Part (ii).** The boundary layer is covered by the cells of side `R^β` around the center that
  meet it, at most `8 d (2N+1)^{d-1}` of them for `N = ⌈R/(2R^β)⌉ + 1`; the cells are coloured by
  their residues modulo `8` (`8^d` colours) for Lemma A.12.
- **Part (iii).** The book takes the layers of width `R^{(1+β)/2}`. Part (ii) at the scale `R^{η₁}`
  needs `R^{η₁(1+δ)}` at most the width of the layer, that is `η₁(1+δ) ≤ (1+β)/2`, which holds
  for every `β ≥ η₁` only when `η₁(1+2δ) ≤ 1`; the Lean proof takes the width `R^b` with
  `b = max((1+β)/2, (1+η₁(1+δ))/2)` and the gain `ε = min(η₁ α - d/2, (1-b)/2)`
  (`changeGain`). The difference `g - 1_{□_R}` is split into the inner cube `□_{R-R^b}` (where it
  is bounded by a Gaussian tail), the layers inside and outside `□_R` (part (ii) at the sides `R`
  and `R + R^b`), and the outside of `□_{R+R^b}` (the far block of Proposition 4.12).
