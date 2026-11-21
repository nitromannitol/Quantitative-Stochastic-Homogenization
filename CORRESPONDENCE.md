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
