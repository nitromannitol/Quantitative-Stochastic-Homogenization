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

## Section 5.3 (`Ch05/Sec03/`) and the Gram space of Section 4.1 (`Ch04/Sec01/GramSpace.lean`)

- **Lemma 5.24, (5.63)–(5.64), with `s = 1`** (`coarsenedCoefficientEstimates_of`,
  `coarsenedCoefficient_aeOsBound`). The proof departs from the book, which deduces (5.64) from
  (5.62) and Lemma 4.25. When the gradients of `A₁` are, up to null sets, the fields `G ξ` of a
  linear family ((4.12)), the form `⟨ξ, η⟩ = ∫ Φ_{z,r} G ξ · a G η` makes the separation quotient
  `H` of `ℝ^d` a real inner product space of dimension at most `d`; with `U ξ = ∫ Φ_{z,r} G ξ` and
  `V ξ = ∫ Φ_{z,r} a G ξ`, completing the square in (4.8) gives
  `J₁(Φ_{z,r}, p, q) = ½ ‖U^* q - V^* p‖²` (`GramFamily.J1_eq_gramEnergy`), and `b_r(z)` is the
  matrix of `b = V V^* - ā U V^*` (`toEuclideanCLM_coarsenedCoefficient`). The entries of `b` and
  of `U V^* - I` are combinations of the errors of (5.58) at finitely many loads rescaled into the
  unit ball (homogeneity of both sides). If `‖U V^* - I‖ ≤ 1/2`, then `V^*` is onto and
  `(V - (ā + b) U) V^* = b (I - U V^*)`, which gives
  `‖V - (ā + b) U‖ ≤ C (‖b‖ + ‖U V^* - I‖)²`; the flux defect is at most `√Λ ‖V - (ā + b) U‖`.
- The statement assumes (5.58) with a constant `C₀(d, Λ)` (`EnergyEstimate`), the structure (4.12)
  of `A₁` against every mask `Φ_{z,r}`, almost surely, with `∫ Φ_{z,r} |G ξ|² < ∞`
  (`LinearA1Gradients`), and the almost sure measurability of `J₁(Φ_{z,r}, p, q)` and of the flux
  defect, which the book does not discuss. The bound `|ā| ≤ 2Λd²` used for the rescaling is
  deduced from (5.58) and `0 ≤ J₁(Φ, p, 0) ≤ Λ|p|²` (`norm_toEuclideanCLM_le_of_energyEstimate`).
- **Measurability of the flux defect of (5.64)** (`aemeasurable_coarseFluxDefect`), which the book
  does not discuss. On the event of (4.12) by the corrected fields `G ξ = ∑ᵢ ξᵢ Wᵢ` with finite
  Gaussian energy, the supremum in (5.64) is the supremum over the ellipsoid
  `{∑ ξᵢξⱼ ∫ Φ Wᵢ·Wⱼ ≤ 1}` of `|∑ ξᵢ ∫ Φ a Wᵢ - (ā + b) ∑ ξᵢ ∫ Φ Wᵢ|`; the flux averages are
  computed with a jointly measurable version of the coefficient field (the `liminf` of its
  mollifications, `coefficientVersion`, `Front/Assumptions/MeasurableVersion.lean`), and by
  continuity the supremum equals a supremum over a dense sequence. With it, Lemma 5.24 follows from
  (5.58), the measurability of `J₁`, (4.12) and the Gaussian energy of the corrected coordinates
  (`coarsenedCoefficientEstimates_of_corrected_energy`).
- Appendix A for almost surely measurable random variables (`AppA/AlmostSureOsBound.lean`):
  `AEOsBound P X s θ` holds if and only if `X` agrees almost surely with a measurable `Y ≤ O_s(θ)`.

## Chapter 4, opening: Theorem 4.1 (`Ch04/Opening/Theorem41.lean`)

- **Theorem 4.1, (4.2), with `s = 1`** (`averagedCorrectorGradient_of`). The book derives (4.2)
  from Theorem 4.6. Here (4.2) is deduced from the estimate `|∫ Φ_{z,r} ∇φ_{eᵢ}| ≤ O_s(C r^{-d/2})`
  in the coordinate directions for one exponent `s ≥ 1` (`CoordinateGradientEstimate`), which is
  the linear estimate obtained in the proof of the improvement of additivity once the exponent
  `d/2` is reached, from the linearity of the corrector gradients in the direction
  (`HasLinearCorrectorGradients`, a property of the construction of Lemma 3.16 by projection), and
  from the finite energy of the corrected coordinates against the masks
  (`HasGaussianCorrectorEnergy`, from Lemma 3.17). The exponent is lowered to `1` by
  `OsBound.mono_exponent`, with the constant `(2e - 1) d C`. For arbitrary homogenization data the
  linearity is obtained by replacing the correctors by the combinations `∑ᵢ eᵢ φ_{eᵢ}` of the
  coordinate correctors (`HomogenizationData.linearize`, `Corrector.linearCombination`, which
  proves that a finite linear combination of correctors is a corrector, including the sublinearity
  of Definition 3.15); this gives `averagedCorrectorGradient_of_coordinate`.

## Section 4.6: (4.126) and Appendix D (`Ch04/Sec06/`, `AppD/`)

- **(4.126), `p = 2`, integer `m > d/2`, `s = 1`** (`negativeSobolevCorrector_of_corrector_energy_bounds`).
  The book bounds negative Sobolev norms through the fractional heat-flow characterization of
  Appendix D and the full family of norms of Theorem 4.24. Here only integer orders on the unit
  ball are needed, and the argument has three steps.
  1. *Pathwise bound.* For a test `ψ` of the unit ball of `H^{n+1}(B_1)` the Taylor formula of the
     heat semigroup `ψ = ∑_{k ≤ n} (-1)^k/k! Φ(1) ∗ Δ^k ψ - ∫₀¹ (-s)^n/n! Φ(s) ∗ Δ^{n+1} ψ ds`
     (`heatTaylor`) is paired with the field (`integral_mul_heatTaylor`, Fubini's theorem with the
     uniform Gaussian bound `abs_heatSmooth_le`), half of the derivatives of `Δ^k = ∑_w ∂_w²` are
     moved onto the kernel (`heatSmooth_iterLaplacian`, `integral_mul_heatSmooth_iterLaplacian_eq`),
     and Cauchy–Schwarz on `B_1` gives `‖F‖_{H^{-(n+1)}(B_1)} ≤ C heatBracket n F`
     (`negativeIntegerSobolevNorm_le_heatBracket`), where the heat bracket collects the `L²(B_1)`
     norms of `Y_{β,s} = ∫ F(x) ∂^β Φ(s)(x - ·) dx` for `|β| ≤ n` at `s = 1` and for `|β| = n + 1`
     integrated against `s^n ds` on `(0, 1]`.
  2. *Summation of the scales.* Per-scale majorants `O_1(c s^{-|β|/2 - d/4} ε^{d/2})` of these norms
     (`HeatScaleEstimate`) are summed by the averaging property of `O_1`; the weight `s^n` makes
     `s^{n - (n+1)/2 - d/4}` integrable exactly when `n + 1 > d/2` (`HeatScaleEstimate.osBound_heatBracket`,
     `negativeSobolevCorrector_of_heatScale`).
  3. *Per-scale estimates.* For `s ≤ 2ε²`, Young's inequality with a Gaussian weight
     (`eLpNorm_heatDerivativeAverage_le`) bounds `Y_{β,s}` by the Gaussian `L²` norm of the field,
     which is `O_1(C₁)`; for `s > 2ε²`, the heat time is split, `Y_{β,s}(F) = Y_{β,s/2}(A_{s/2} F)`
     (`heatDerivativeAverage_add`), and the Gaussian averages `A_t F(u)` are `O_1(C ε^{d/2} t^{-d/4})`
     at every center by (4.2) (respectively (4.3)) at the center `u/ε` and the radius `√t/ε ≥ 1`
     (`osBound_abs_heatAverage_rescaled`), their Gaussian square average being `O_1` by
     `osBound_rpow_integral_sq` (`heatScaleEstimate_of_gaussian`).
  The frozen statement is thus deduced from (4.2) for the correctors in the form of the frozen
  statement of Theorem 4.1, (4.3) in the same form for the flux (made jointly measurable through
  `coefficientVersion`), the bounds `1 ≤ ā ≤ Λ`, and the Gaussian energy estimate of the corrected
  field `e + ∇φ_e(·/ε)` at the unit scale, which dominates the components of both fields
  (`gaussianEnergyEstimate_of_vector`) and gives their Gaussian moments (`GaussianMoments`).
- **The inputs of (4.126)** (`Ch04/Sec06/NegativeSobolevLinearEstimates.lean`). The correctors are
  taken in the linear form `φ_e = ∑ᵢ eᵢ φ_{eᵢ}` (`HomogenizationData.linearize`), so that
  `e + ∇φ_e = G e`. Then (4.2) is the linear estimate `|∫ Φ_{z,r} G e - e| ≤ O_1(C r^{-d/2})`, and
  (4.3) follows from it and the commutator estimate (4.34) through
  `∫ Φ (a G e - ā e) = ∑ⱼ eⱼ (∫ Φ a G eⱼ - ā ∫ Φ G eⱼ) + ā (∫ Φ G e - e)` and `|ā v| ≤ Λ |v|`. The
  Gaussian energy of `e + ∇φ_e(·/ε)` at the unit scale is bounded by a change of variables by the
  mask of radius `ε⁻¹ √(8d) ≥ 1`, where the energy bound below the scale at the exponent `d/2`
  gives `C (1 + X^d)` with `X = O_{d/2}(C)`; its square root is `O_1` by the power rule.
- **The bounds `1 ≤ ā ≤ Λ`** (`HomogenizationData.homogenizedMatrixBounds`) use the measurability of
  `a ↦ μ(U, e)`, which the book takes for granted. It is proved in
  `Ch01/Sec02/DirichletEnergyMeasurability.lean`: the infimum (1.7) over the gradients of `H¹₀(U)`
  equals the infimum over a countable subset dense among them in the separable space `L²(U)`,
  since `(G + W)·a(G + W) ≤ (1 + t) G·aG + (1 + t⁻¹) W·aW`, and the energy of each element of the
  subset is measurable once `a` is replaced by its jointly measurable version.

## Proposition 4.3, Proposition 4.10 and Theorem 4.6 (ii) (`Ch04/Sec01/`, `Ch04/Sec02/`, `Ch04/Sec03/`)

- **The bounds `½|e|² ≤ μ(U, e) ≤ ½Λ|e|²`** (`le_dirichletEnergy`, `dirichletEnergy_le`, in
  `Ch01/Sec02/DirichletEnergyBounds.lean`), for a measurable set of finite positive volume: the
  lower bound uses `∫_U g = 0` for `g` the gradient of a function of `H¹₀(U)`
  (`setIntegral_eq_zero_of_H01`, by the approximation in the definition of `H¹₀(U)` and
  `∫ ∂ᵢφ = 0`) and Jensen's inequality (`sq_setAverage_le`). Consequently
  `homogenizedMatrixBounds_of_aestronglyMeasurable`: `I ≤ ā ≤ Λ I` for a homogenization datum, given
  the almost sure measurability of `a ↦ μ(□ₙ, ξ)`, which the limit (1.22) (a Bochner integral)
  needs.
- **Lemma 4.13 (deterministic step).** `corrected_averages_eq_sum`: at a good scale the averaged
  gradient and flux of `eⱼ + ∇φ_{eⱼ}` are combinations, with coefficients bounded by
  `2 √d (Λ + 1)`, of the averaged gradients and fluxes of the maximizers at the loads `(0, eᵢ/2)`,
  which are polarization vectors of `J₁` (`integral_maximizer_eq_polarizationVector`,
  `integral_flux_maximizer_eq_fluxPolarizationVector`).
- **Lemma 4.13.** `lemma413` (`Ch04/Sec03/Lemma413Statement.lean`) proves (4.34) for the corrected
  coordinates with the Gaussian masks, `|∫ Φ_{z,r} (a - ā)(eⱼ + ∇φ_{eⱼ})| ≤ O_s(C r^{-α})`
  (`CommutatorEstimate`), under `Fluc(s, α)` with `α ≤ d/2`, from Proposition 3.21 and the energy
  bound below the scale at one exponent `τ ≥ s d/2`, the expectations of the averages at the rate
  `r^{-α}` (`ExpectedAveragesEstimate`) and the measurability of the averages, which are
  hypotheses. The proof is not the book's: the polarization vectors `Bᵢ = 2 m(0, eᵢ/2)` and
  `Cᵢ = 2 f(0, eᵢ/2)` fluctuate by `O_s(C r^{-α})` (`polarization_pair_fluctuation`); the mean of
  `Bᵢ` is close to `ā⁻¹eᵢ` at large scales (`mean_polarization_near_inverse`), so the matrix `D₀`
  with `D₀ E[Bᵢ] = E[Cᵢ]` exists and is bounded (`exists_matching_matrix`); the commutator against
  `D₀` is bounded pointwise by the fluctuations and, at bad scales, by the energy
  (`commutator_matching_le`); the expectations of the averages give `|D₀ - ā| ≤ C r^{-α}`
  (`matching_matrix_near`, `commutator_assembly`); below the threshold the energy bound suffices
  (`commutator_small`). `commutatorEstimate_of_flucJ1` and `estimate558_of_commutator` insert it in
  the proof of (5.58).
- **The linear estimate (Step 1 of the route of Proposition 4.10).** `HeatIdentityBound` records,
  as a hypothesis, the bound that the heat identity (H) of the route gives for `r ≥ 2`:
  `|∫ Φ_{z,r} (eᵢ + ∇φ_{eᵢ}) - eᵢ| ≤ ∫_{u > r²/2} ∫ k_r(u, x) |commutator at (z - x, √u)| dx du`
  almost surely, for a positive kernel with `∫ k_r(u, ·) ≤ C_k/u`. From it and Lemma 4.13,
  Lemma A.4 on the product of the time and space measures gives
  `|∫ Φ_{z,r} (eᵢ + ∇φ_{eᵢ}) - eᵢ| ≤ O_s(C r^{-α})` (`gradient_sub_osBound_of_heat`,
  `gradient_sub_osBound`), and linearity in the slope gives `LinearAverageEstimate`
  (`linearAverageEstimate_of_heat`). `estimate558_of_heatIdentity` proves (5.58) with this
  hypothesis in place of the linear estimate. The identity (H) itself (anisotropic Gaussians,
  integration by parts against the corrector, the limit `T → ∞`) is not formalized.
- **Integrability and measurability of the averages.** The gradient averages are jointly
  measurable in the center, the radius and the coefficient field (`measurable_gradientAverage_uncurry`,
  from the joint measurability of the corrector gradients); the flux averages involve `a(x)`, and
  their joint measurability is a hypothesis. The averages and the trial are integrable at the
  scales `r ≥ 1` under the energy bound (`averagesIntegrable_of_energyBound`,
  `trialIntegrable_of_energyBound`). The energy bound below the scale follows from Proposition 3.21
  and the bounds on `ā` (`gaussianEnergyBound_of_rate`), by `Φ_{z,r} ≤ (R/r)^d Φ_{z,R}` for `r ≤ R`
  (`heatKernel_le_mul`); `estimate558_of_heatIdentityBound` is (5.58) without these hypotheses.
- **The bounds `I ≤ ā ≤ Λ I` from the expectations (1).** Jensen's inequality for the heat kernel
  average and for the expectation (`euclideanSq_integral_le`), with `|av|² ≤ Λ v·av`
  (`euclideanSq_coefficient_mulVec_le`), gives `|E P ξ|² ≤ E[E ξ]` and `|E F ξ|² ≤ Λ E[E ξ]`; the
  limit `r → ∞` in (1) gives `|ξ|² ≤ ξ·āξ` and `|āξ|² ≤ Λ ξ·āξ`
  (`homogenizedMatrixBounds_of_expectedAverages`). `estimate558_of_heatBound_and_rate` is (5.58)
  from the structure (4.12) of `A₁`, Proposition 3.21 at every exponent `τ ∈ (0, d)`, the
  expectations (1) of the averages, the measurability of `J₁`, of the trial and of the flux
  averages, `HeatIdentityBound`, and the conclusions of Propositions 4.11 and 4.12. From the same
  inputs, Theorem 4.6 (i) gives `Fluc(s, d/2)` (`flucJ1_half_dim_of_heat`), and Lemma 4.13 and
  the linear estimate hold at the exponent `d/2` (`linearAverageEstimate_half_dim`).
- **(4.15), (4.22).** `J1_nonneg` and `J1_le`: `0 ≤ J₁(Ψ, p, q) ≤ Λ|p|² + |q|²` for every
  coefficient field and every nonnegative integrable mask of mass at most one, with the explicit
  constant and without Theorem 3.8 (the zero element of `A₁` and the Cauchy–Schwarz inequality
  for the form of `a`).
- **Proposition 4.3.** The deterministic part is `abs_J1_sub_homogenizedJ1_le`: if the gradients of
  `A₁` are exactly the fields `G ξ` of a family ((4.12)) and the functional of (4.8) at `G ξ` is
  within `ε (|ξ|² + |ξ| (|p| + |q|))` of `-½ ξ·āξ - p·āξ + q·ξ` ((4.11)) with `ε ≤ 1/5`, then (4.10)
  holds with the constant `7ε`; the proof is the two-sided argument of the book with the explicit
  threshold `1/5` in place of nondegeneracy. (4.11) follows from the bounds on the three averages
  (`abs_j1Functional_sub_le_of_averages`). `proposition43` is the random statement at every center,
  with a jointly measurable family of scales; its inputs are explicit hypotheses: the structure
  (4.12) of `A₁` (`GradientsOfA1AreCorrected`, from Theorem 3.8), the bounds `I ≤ ā ≤ Λ I`
  (`HomogenizedMatrixBounds`), and Proposition 3.21 at every center for the corrected fields
  `∑ ξᵢ (eᵢ + ∇φ_{eᵢ})`, including the cross terms of the energy matrix (`GaussianCorrectorRate`).
  The book takes the scale of Proposition 3.21 at the origin and translates it (Definition 4.5).
- **Step 2 of the proof of Theorem 4.6.** `flucJ1_of_gaussianCorrectorRate` gives
  `Fluc(s, min(μ, 1))` for `s ≥ 1` from Proposition 4.3 and the bound (4.24), and `flucJ1_base` is
  the initial exponent required by `additiveStructure_J1`. The measurability of
  `a ↦ J₁(Φ_{z,r}, p, q)` is a hypothesis.
- **Proposition 4.10.** The proof follows a route different from Lemmas 4.13–4.18: the trial at the
  deterministic slope `c* = -p + ā⁻¹q` (`homogenizedSlope`). The functional of (4.8) at a fixed
  field is averaged by the heat semigroup (`j1Functional_heatKernel_eq_integral`), and
  `J₁(Φ_{z,R}) ≤ ∫ Φ_{z,√(R²-r²)} J₁(Φ_{·,r})` (`J1Heat_le_integral_heatKernel_mul`), so the
  additivity defect lies between `0` and the average of the trial gap
  (`additivityDefect_le_trialGap`). A bound `O_t(C r^{-β})` on the trial gap at every center
  (`TrialGapEstimate`) gives `Add(t, β)` by Lemma A.4 (`addJ1_of_trialGapEstimate`), and with
  Proposition 4.3 at an exponent `τ > s d/2` it gives `Add(s, α + η)` with
  `η = min(μ/2, τ/s - d/2)` (`addJ1_improved_of_trialGap`, from `Δ ≤ √(2δ) √G + B`).
  `proposition410` proves the conclusion `ImprovementOfAdditivity` and (4.70) from the trial gap
  estimate `O_{s/2}(C r^{-2α})` under `Fluc(s, α)` and the expectation of the trial
  (`TrialExpectationEstimate`), which are hypotheses, together with the inputs of Proposition 4.3,
  the almost sure integrability of the trial (`TrialIntegrable`) and the joint measurability of
  `(a, x) ↦ J₁(Φ_{x,r}, p, q)`.
- **The trial gap estimate (Step 2 of the route of Proposition 4.10).** On a linear family of
  gradients spanning `A₁`, the functional of (4.8) is `-½ ξ·Aξ + l·ξ` (`j1Functional_fieldOf`),
  `J₁ = ½ l·A⁻¹l` and the gap to the trial at a slope `k` is `½ (k - c)·A(k - c)`
  (`J1_sub_j1Functional_fieldOf`); the averaged gradient `m` of the maximizer is the polarization
  vector of `J₁` ((4.16), `integral_maximizer_eq_polarizationVector`), whose fluctuations are
  bounded by `Fluc(s, α)` (`polarizationVector_fluctuation`). The comparison of the expectations of
  the gaps at the deterministic slopes `E[m]` and `c*` gives `|E[m] - c*| ≤ C r^{-α}`, and
  `trialGapEstimate_of_linearAverages` gives the trial gap estimate `O_{s/2}(C r^{-2α})` from the
  linear estimate of the gradient averages (`LinearAverageEstimate`, the output of Step 1, through
  the heat identity, in the route), the expectation of the trial at deterministic slopes
  (`TrialObjectiveExpectation`, from the cell averages of the stationary fields), the energy of
  the corrected fields below the scale (`GaussianEnergyBound`) and Proposition 3.21; these are
  hypotheses. `proposition410_of_linearAverages` and `estimate558_of_linearAverages` state
  Proposition 4.10 and (5.58) from them. The finite sums, squares and means of `O_s` variables at
  every exponent used here are `osBound_finset_sum_of_pos`, `OsBound.sq`, `OsBound.integral_sq_le`
  and `OsBound.integral_le_factorial_mul`.
- **Remark 4.18, (4.70), and Theorem 4.6 (ii).** `ExpectationEstimates` states (4.70);
  `expectationJ1Estimate_of_trialGap` proves it from the trial, with the mean bound
  `OsBound.integral_le_factorial_mul` for `O_t` variables with `t < 1`.
- **(5.58).** `theorem46_expectation_and_558`, `estimate558` and `estimate558_of_trialGap`:
  `|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ O_s(C r^{-d/2})` for every `s ∈ (0, 2)`, with
  Theorem 4.6 (ii), from Theorem 4.6 (iii) (`additiveStructure_J1`) and (4.70); for `s < 1` the
  triangle inequality is replaced by `X + Y ≤ 2 max(X, Y)`.

## Lemma 3.17, Lemma 6.1 and Proposition 6.2: sublinearity of the correctors

- Lean: `QSH.sublinearCorrectors : QSH.sublinearCorrectorsStatement`
  (`Ch06/Sec01/CorrectorSublinear.lean`), flux corrector `QSH.FluxCorrector` (`Ch06/Sec01/FluxCorrector.lean`).
- Route. The book proves Lemma 3.17 from the regularity theory of Chapter 3 and Proposition 6.2
  from the estimates of Chapter 4. Here both come from the homogenization theorem at a polynomial
  scale of Armstrong, Kuusi and Loher (*Homogenization at a polynomial scale in high contrast*,
  formalized in HighContrastHomogenization, `HCPoly.uniform_homogenization`), applied to the law of
  the dilated coefficient field `a(2·)`: above a multiple of its homogenization scale `X`, the
  corrector has bounded energy and oscillation `r^(1-θ) X^θ`, and the flux corrector, selected by
  the heat formula (6.7), has oscillation `r (r/X)^(-ϑ)`. The random radius is `(B X)^p` with
  `p = 2d/(d+s)`; its tail gives the stretched-exponential bound of order `s ∈ (0, d)`.
- Statement. Only the oscillation part of (3.85) is stated, with the exponent `1 - β(d - s)` in
  place of the exponents of the book, and the slope is a unit vector. The flux corrector is the
  selection (6.7) of Lemma 6.1, with its local Sobolev regularity and measurability explicit.
- The modules of `Ch03/Sec04/` and `Ch06/Sec01/` other than the section files were moved from
  einstein-relation-lean, commit `c97689e`; each names its source file.

## Section 3.3, (3.38)–(3.39), and Section 4.1, (4.8): the class A₁ and the energy J₁

- Lean: `ae_exists_harmonicA1_correctedAffine` (corrected affine functions belong to `A₁`),
  `ae_eq_zero_of_correctedAffineGrad_ae_eq_zero` (their gradients are linearly independent),
  `ae_gradients_harmonicA1` (`dim A₁ = d + 1`), `ae_J1Heat_eq_half_dot_inv` (`J₁ = ½ b·M⁻¹ b`),
  `J1Heat_bounds`, `aestronglyMeasurable_J1Heat`; `Ch03/Sec03/`, `Ch04/Sec01/`.
- The classification of `A₁` (Theorem 3.8 for `k = 1`) is the hypothesis
  `firstOrderLiouvilleStatement` of the results that use it. It is derived by the first-order
  route instead of the higher-order regularity theory of the book:
  `firstOrderLiouville_of_harmonicApproximation` proves it from two deterministic estimates on the
  ellipsoids `E_R = M B_R`, `M Mᵀ = ½(ā + āᵀ)`, with `ā` the homogenized matrix of the
  high-contrast theorem: the harmonic approximation on nearly full ellipsoids
  (`harmonicApproximationStatement`) and the decay `(t/b)²` of the part of degree at least two of
  harmonic functions (`harmonicExpansionStatement`). These give one step of the excess decay with
  the sharp factor `¼ (1 + C R^{-ν})` (`quarterExcessStepStatement`), and the iteration of this step
  classifies the subquadratic solutions. By the change of variables `x = M y` the second estimate
  reduces to square-integrable weakly harmonic functions on balls
  (`harmonicExpansionBallStatement`), proved as `harmonicExpansionBall` with the elliptic regularity
  library: Weyl's lemma, the Almgren frequency of the first-order Taylor remainder is at least two,
  so its sphere and ball means decay like `(t/r)⁴`, and it is orthogonal on balls to affine
  functions. Hence `firstOrderLiouville_of_harmonicApproximation_only` derives the classification
  from the approximation (2), which is stated and not yet proved here.
- `J₁ = ½‖-V*p + U*q‖²` is stated in coordinates: `M` is the Gram matrix of the corrector columns
  `eᵢ + ∇φ_{eᵢ}` for the inner product `∫ Φ_{z,r} v·a w` and `b` the load `∫ Φ_{z,r}(-p·a Wᵢ + q·Wᵢ)`.
- The bound `0 ≤ J₁ ≤ Λ|p|² + |q|²` holds for every coefficient field, and so does the sharper
  `J₁ ≤ ½(√Λ |p| + |q|)²` (`J1Heat_le_half_sq`). The measurability of
  `a ↦ J₁(Φ_{z,r}, p, q)` is almost everywhere strong measurability for every finite law, proved
  through analytic sets: the strict upper level sets of `J₁` are projections of Borel sets.
- Lemma 6.1, (6.5)–(6.6): `FluxCorrector.ae_add_transpose_eq_const` gives skew symmetry up to a
  constant matrix and `fluxCorrectorDivergence` the divergence identity (6.6), with the constant
  identified as `ā e` for the homogenized matrix of the high-contrast theorem
  (`FluxCorrector.ae_hasWeakDivergence_of_package`), without an ergodic theorem: the large-time
  heat averages of the flux converge by the scale pairing bounds of that theorem. The skew part
  `(S - Sᵀ)/2` satisfies the same identity (`FluxCorrector.ae_skew_divergence_of_package`).
