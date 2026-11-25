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
- **Propositions 4.10–4.12** are proved, in the forms stated in ROADMAP.md. Their conclusions are the definitions
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
  d/2 (1+δ)`. Part (ii) is formalized only conditionally, together with (5.58), in the forms listed
  in the entry for Proposition 4.3, Proposition 4.10 and Theorem 4.6 (ii) below
  (`theorem46_expectation_and_558`, `estimate558_of_law`); (5.58) at `s = 1` with a constant chosen before
  the law is proved (`uniformEnergyEstimate_holds`). Part (i) with its constant `C(s, d, Λ)` chosen
  before the law is the statement `QSH.UniformAdditivityJ1` (`Ch04/Sec02/UniformAdditivity.lean`),
  proved with no hypothesis (`QSH.uniformAdditivityJ1_holds`, `Ch05/Sec04/FrozenProved.lean`); it is
  the hypothesis of the Section 5.4 block estimates for the localized energy.
- **`LocFieldEstimate`.** The proof of Proposition 4.12 integrates the localized variables
  `x ↦ J₁^{(δ)}(x, r, p, q)` over boxes and uses the independence of integrals over boxes at
  distance larger than one, which needs a family that is jointly measurable in the coefficients
  and the center. `LocFieldEstimate` states localization by such a family and implies
  `LocEstimate` (`LocFieldEstimate.locEstimate`).


## Theorem 4.6 with constants chosen before the law (`Ch04/Sec02/UniformBootstrap.lean`, `Ch04/Sec02/Theorem46Uniform.lean`, `Ch04/Sec02/Theorem46UniformBase.lean`, `Ch04/Sec03/Proposition410Uniform.lean`, `Ch04/Sec04/LocalizationUniform.lean`, `Ch04/Sec06/UniformCorrectorEstimates.lean`, `Ch05/Sec03/UniformEnergyEstimate.lean`, `Ch04/Sec04/PilotLocalization.lean`, `Ch05/Sec04/FrozenFromInputs.lean`, `Ch05/Sec04/FrozenFromSlope.lean`, `Ch05/Sec04/FrozenFromCompactTests.lean`)

- **The quantifier order.** The book's constants depend only on `(s, d, Λ)`. In the bootstrap this
  is the statement that each of Propositions 4.3, 4.10, 4.11 and 4.12 turns a constant of its
  input into a constant of its output that does not depend on the law. The statements
  `FlucEstimateAt`, `AddEstimateAt`, `LocFieldEstimateAt` are Definitions 4.7–4.9 with the constant
  as an argument, and `uniform_flucEstimate_half_dim` runs the induction for a family of laws with
  these implications; composing the per-law statements of Section 4.2 would not give this.
  Proposition 4.12 with its constant chosen before the law is `exists_flucEstimateAt_of_add_local`;
  Lemma 4.13, the linear estimate and the energy bound below the scale are
  `exists_uniform_commutator_of_fluctuations`, `exists_uniform_linear_of_heat` and
  `gaussianEnergyBound_of_rate_at`; Proposition 4.3 is `flucEstimateAt_of_gaussianCorrectorRate`.
- **The exponents.** One localization parameter `δ = min(ν, d/u - d/2)/(1 + d/2)` and one loss `δ/4`
  serve every step, with increments `δ/(2(1+δ))` clipped at `d/2` (this replaces Steps 1–3 of the
  book; at the last step the book's `α = (d - δ)/(2(1+δ))` does not satisfy `α(1+δ) + δ > d/2 (1+δ)`).
  The bootstrap is run at `u = 1 + s/2 ∈ (1, 2)` and lowered to `s` with the multiplier
  `(log 2)^{1/u - 1/s}` (`OsBound.mono_exponent_sharp`, optimal for constant random variables).
- **Versions of `J₁`.** `a ↦ J₁(Φ_{z,r}, p, q)` is identified with (4.12) only almost surely and is
  not known to be measurable, so the bootstrap is run for a bounded jointly measurable version
  (`IsBoundedJointVersion`: equal to `J₁` at all parameters almost surely, bounded by `|Λ| + 1`,
  from `HasJointHeatVersion`), and the results for `J₁` are stated with `AEOsBound`. In Lemma 4.13
  the polarization vectors are formed with the version (`polarizationVectorOf`); the book does not
  discuss this measurability.
- **Proposition 4.10 and (4.70)** with constants chosen before the law follow from the Gaussian
  inputs (`Ch04/Sec03/Proposition410Uniform.lean`): the trial gap, the improved additivity and the
  expectation of `J₁` are proved for the versions with explicit constants
  (`exists_trialGapEstimateAt_of_linearAverages`, `exists_addEstimateAt_improved_of_trialGap`,
  `addEstimateAt_of_trialGapEstimateAt`, `abs_integral_J1Heat_sub_le_of_trialGap`), with the trial
  gap formed with the version (`trialGapOf`). The expectations (1) have a constant chosen before
  the law (`expectedAveragesEstimateAt_of_energy_and_rate`: the moment `E[X(0)^d]` of the scale of
  the energy bound is bounded by `momentConstant (τ/d) C_N^d`). The homogenized matrix does not
  depend on the homogenization data (`HomogenizationData.homogenized_eq`).
- **Proposition 4.11** is used only at the stochastic exponents `s ∈ (1, 2)` and the spatial
  exponents `α ∈ (0, d/2]` of the bootstrap, with the localized energies of one localized family of
  Section 4.4 as the localized fields (`uniformLocalizationEstimates_of_pilot`,
  `Ch04/Sec04/LocalizationUniform.lean`); the family is chosen independently of the law.
- **Lemmas 4.21–4.22 for a class of laws.** The reduction of (5.85) to the single-slope estimate of
  Lemma 4.21 uses the law only through that estimate, so it is stated for every class `L` of laws
  (`LocalizationSlopeEstimateOn L`, `localizationEstimateOn_of_slopeOn`). Proposition 4.11 at the
  exponents of the bootstrap follows from the single-slope estimate on the classes `LinearLaw s β C`
  of the laws with the linear estimate at `(s, β)`, for localized families of a construction exponent
  `α < β` with `γ < α(1+δ) + δ` (`LinearSlopeEstimates`, `exists_construction_exponent`): under the
  Gaussian inputs, `Fluc(s, β)` gives this linear estimate with a constant chosen before the law
  (`pilotLocalizationEstimates_of_gaussianInputs_slopeOn`); for `γ ≤ 0` the localization error is
  bounded. The book proves Proposition 4.11 at every `α` with `Fluc(s, α)` as the input and the
  construction at the same exponent; here the input is the linear estimate it implies, and the
  construction exponent is taken below it, which the slack `η` allows. The single-slope estimate on
  `LinearLaw` departs from the book's proof of Lemma 4.21, which uses `Fluc(s, α)` beyond the linear
  estimate: Step 2 goes through Lemma 4.17 and the fluctuation bound (4.63). It follows from the
  book's argument with the corrected coordinate `ℓ_j + φ_{e_j}` as the competitor in place of `v_j`;
  Steps 3–6 use only (3.86), (3.101), (4.25), Theorem 3.8 and Lemma 4.20.
- Theorem 4.6 (i), (iii), (5.58), (5.85), (4.126), Theorem 4.1 and Lemma 5.29 are
  deduced from Proposition 3.21 with constants chosen before the law, the heat identity (H) with a
  kernel of mass `C_k/u`, and the single-slope estimate on the classes `LinearLaw`
  (`LinearSlopeEstimates`) (`bootstrapInputs_of_rate_heat_pilot`,
  `pilotLocalizationEstimates_of_rate_heat_slope`, `localizedEnergy_of_rate_heat_slope`). With the
  heat identity `exists_heatPathwiseKernel` and the homogenization data `homogenizationDataExists`,
  the frozen statements E1–E7 follow from `UniformGaussianCorrectorRate` (Proposition 3.21) and
  `UniformLinearSlopeEstimates` (`Ch05/Sec04/FrozenFromInputs.lean`, E5 through (5.58)).
  Proposition 3.21 is proved (`uniformGaussianCorrectorRate`), so Propositions 4.3 and 4.10, (4.70)
  and Lemma 4.13 with constants chosen before the law hold for the bounded jointly measurable
  versions of `J₁` (`uniformBaseFluctuation_holds`, `uniformImprovementOfAdditivity_holds`,
  `uniformExpectationEstimates_holds`, `exists_uniform_commutator_linear_of_fluctuations`), and
  E1–E7 follow from `UniformLinearSlopeEstimates` alone (`Ch05/Sec04/FrozenFromSlope.lean`). With
  the single-slope estimate from the finite-ball observation (next section), E1–E7 follow from the
  estimate with compact tests `CompactTestFiniteBall d Λ k`, `k > 0` (a deterministic finite-ball
  estimate above a random radius, with tests chosen for each law), alone (`Ch05/Sec04/FrozenFromCompactTests.lean`); for (5.85) the linear estimate at `d/2` with one
  constant for all laws comes from the same chain (`uniformLinearAverageEstimate_of_compactTests`).
  The estimate with compact tests is proved for every `d ≥ 2`, `Λ > 1` and `k > 0`
  (`compactTestFiniteBall`, Section 4.4 below), so E1–E7 hold with no hypothesis
  (`Ch05/Sec04/FrozenProved.lean`).

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
  `L²(Φ_{z,r}, B_T(z))`; these fields are the corrected gradients of slopes close to the unit
  vectors (`Ch04/Sec04/SlopeMatchedColumns.lean`), whose closeness to the localized coordinates is
  the single-slope estimate of the next entries.
- **Lemma 4.21 with one slope** (`QSH.localizedEnergy_of_slope`). (5.85) is reduced to the
  first-order Liouville theorem and the single-slope estimate `QSH.LocalizationSlopeEstimate`:
  above a random radius `X` with `X^γ ≤ O_s(C)`, the gradient of each selected coordinate is within
  `√K₁ Y (t/r)` of one corrected gradient `W_i + ∑_j b_{ij} W_j` in `L̲²(B_t(z))` for
  `r ≤ t ≤ c r^{1+δ-ε}`, with `Y ≤ O_s(C r^{-γ})`. The book's proof (pp. 156-162) approximates
  the selected coordinates by heterogeneous polynomials of high degree at the intermediate scale and
  uses the case `k = 1` of Theorem 3.8 at the scale `r`; the single-slope step is the hypothesis
  `QSH.LocalizationSlopeEstimate` (the book's (4.101)) of these reductions, which are stated for it
  (it is proved on the classes of laws with the linear estimate in the next entries), and Theorem C
  of Armstrong, Kuusi and Loher is its source (`QSH.exists_highContrastExcessPackage`, used in
  `QSH.ballExcessDecay`; the Caccioppoli inequality on balls `QSH.caccioppoli_ball` is also proved). The decay `(t/S)^ϑ` of Theorem C with `ϑ < 1` cannot meet the book's exact budget
  `(r/S)² S^{-2α} = r^{-2γ}` at `α = d/2`; it can only work with a fluctuation bound at an exponent above the chosen `α < d/2`
  (`Fluc(s, d/2)` being the natural one).
  Above the slope scale the Lean route uses the total energy bound on `B_{r^{1+δ}}(z)`, summed over Gaussian shells
  (`QSH.LocalizationInnerSlopeData.toBallGrowthData`). Off the event `{X ≤ r}` both energies are
  bounded deterministically (`QSH.abs_J1Heat_sub_localizedJ1_le_cap`) and `1_{X > r} ≤ r^{-γ} X^γ`
  (`QSH.localizationApproximationUniform_of_ballGrowth`). The oscillation and energy bounds of the
  correctors at the center `z` come from Lemma 3.17 at the origin for the coefficients translated
  by a lattice point near `z` (`QSH.exists_translated_corrector_bounds`).
  `QSH.localizedEnergy_of_slope_only` gives the frozen localized-energy statement from `QSH.LocalizationSlopeEstimate` alone, with `QSH.firstOrderLiouville` and `QSH.harmonicApproximation` discharged.

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
(`BlockEstimates.lean`, `BlockEstimatesBoundary.lean`), and from the law-uniform Theorem 4.6 (i)
`QSH.blockCLT_of_uniformAdditivityJ1`, `QSH.blockBoundary_of_uniformAdditivityJ1` and
`QSH.blockChange_of_uniformAdditivityJ1` (`LocalizedAdditivityProof.lean`).

- **Hypotheses made explicit.** The three parts are proved for any family with the properties used
  in the proof of Proposition 4.12 (`CenteredLocalFields`): boundedness, joint locality, centering
  and the additivity (5.88). For the localized energy these properties are
  `LocalizedFieldInput` (boundedness and joint locality of `J₁^{(δ)}`, proved) and
  `LocalizedAdditivityInput` ((5.88) with the exponent `γ`, deduced from the law-uniform
  Theorem 4.6 (i)); see the bullet on the two inputs below.
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
- **The two inputs.** `LocalizedFieldInput` holds for every localized family
  (`QSH.localizedFieldInput`, `LocalizedFieldInputProof.lean`), with the bound `(d²Λ + d)²/2`
  (`abs_familyJ1_le`; the book uses the boundedness at (4.103) without a constant) and the joint measurability of the construction of Section 4.4. `LocalizedAdditivityInput`
  is deduced as in the book from Theorem 4.6 (i), Lemma A.3 (i) (for values in `[0, B]`,
  `QSH.osBound_increase_exponent_of_bounded`) and (5.85) (`QSH.localizedAdditivityInput_of_uniform`,
  `LocalizedAdditivityProof.lean`). Theorem 4.6 (i) is
  used at the stochastic exponent `t = sγ/d`, with its constant `C(2t, d, Λ)` (in the book's parametrization, where the exponent `s` of
  Theorem 4.6 (i) gives `O_{s/2}`) chosen before the law
  (`QSH.UniformAdditivityJ1`, `Ch04/Sec02/UniformAdditivity.lean`, a hypothesis of
  `QSH.localizedAdditivityInput_of_uniform`, proved by `QSH.uniformAdditivityJ1_holds`); since
  the defect lies in `[0, Λ + 1]`, it is `O_s(C r^{-γ})`. Integrating the localization error over
  the inner centers needs a version of `J₁(Φ_{x,r}, p, q)` jointly measurable in the coefficients
  and `x`, which the book does not discuss: where (4.12) holds and the corrected coordinates have
  finite Gaussian energy, `J₁` is the supremum of the trial functionals at `G ξ` over a dense
  sequence of slopes (`QSH.hasJointHeatVersion_of_lawHypotheses`, `JointHeatVersion.lean`), given
  homogenization data for the law. Hence `QSH.blockCLT_of_uniformAdditivityJ1`,
  `QSH.blockBoundary_of_uniformAdditivityJ1` and `QSH.blockChange_of_uniformAdditivityJ1` give the
  three frozen statements from `UniformAdditivityJ1` and the existence of homogenization data for
  every law satisfying the assumptions. That existence is also part of the conclusion of the
  frozen statement E1 (`QSH.Frozen.averagedCorrectorGradient`), so E2-E4 follow from E1 and
  `UniformAdditivityJ1`.

## Section 5.3 (`Ch05/Sec03/`) and the Gram space of Section 4.1 (`Ch04/Sec01/GramSpace.lean`)

- **Definition 5.23** (`coarsenedCoefficient`, `Ch05/Sec03HeuristicScalingLimit.lean`). The matrix
  is defined by its entries, `b_r(z)_{jk} = ½ (J₁(Φ_{z,r}, e_j + e_k, ā e_j) - J₁(Φ_{z,r}, e_j - e_k, ā e_j))`,
  which is (5.62) at `p = e_j`, `p' = e_k`. The identity (5.62) for all `p, p'` uses that
  `(p, q) ↦ J₁(Φ_{z,r}, p, q)` is a quadratic form; it is `dot_coarsenedCoefficient_mulVec` when the
  gradients of `A₁` have the structure (4.12) (`LinearA1Gradients`), which holds almost surely.

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
  `QSH.coarsenedCoefficientEstimates_of_energyEstimate` gives the frozen coarsened coefficient estimates from (5.58) alone, with `QSH.firstOrderLiouville` discharged.
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
  Since the energy of the corrected coordinates now follows from Lemma 3.17 (`sublinearCorrectors`),
  `averagedCorrectorGradient_of_linearAverage_uniform` derives (4.2) from the linear estimate alone, for one
  exponent `s ≥ 1` and a constant chosen before the law.

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
  mask of radius `ε⁻¹ √(8d) ≥ 1`. There `|G e|² ≤ ∑ᵢ |eᵢ + ∇φ_{eᵢ}|²`, and the energy bound of
  Lemma 3.17 on the balls `B_R`, `R ≥ Xᵢ`, with `Xᵢ = O_{d/2}(C)`, gives `C Xᵢ^d` for the Gaussian
  average of each term at every radius `≥ 1` (shells of the heat kernel above `Xᵢ`, the comparison
  `Φ_{0,ρ} ≤ (Xᵢ/ρ)^d Φ_{0,Xᵢ}` below it); the square root is at most `B ∑ᵢ Xᵢ^{d/2} = O_1`
  (`Ch04/Sec06/NegativeSobolevSublinear.lean`). Thus (4.126) rests on the commutator estimate and
  the linear estimate at `s = 1` and the exponent `d/2`, with constants chosen before the law
  (`negativeSobolevCorrector_of_commutator_linear`). The repository proves both estimates with
  constants chosen before the law for every `s ∈ (0, 2)` (`exists_uniform_commutator_linear_half_dim`,
  from the Gaussian inputs and Propositions 4.10 and 4.11 with constants chosen before the law,
  which are proved by `uniformGaussianInputs_holds`, `uniformImprovementOfAdditivity_holds` and
  `uniformLocalizationEstimates_holds`; `negativeSobolevCorrector_of_uniform_inputs`), and for a
  single law with a constant that depends on the law (`commutator_linearAverage_half_dim`).
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
  hypothesis in place of the linear estimate. The identity (H) itself is formalized below
  (**The heat identity (H)**).
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
- **The expectations (1) (in the book, Lemma 3.23 and (3.92)–(3.93)).**
  `expectedAveragesEstimate_of_rate` (`Ch04/Sec03/ExpectedAveragesFromRate.lean`) proves
  `ExpectedAveragesEstimate P S β` for every `β > 0`, for a law satisfying (0.10)–(0.11), from
  Proposition 3.21 at one exponent with a positive rate. The proof is not the book's (which uses
  the Poincaré inequality on the torus): the densities `G ξ`, `a G ξ`, `G ξ · a G ξ`, formed with
  the jointly measurable version of the coefficients, are stationary, so their expectations are
  lattice periodic; by Poisson summation for the heat kernel (`Complex.tsum_exp_neg_quadratic`) the
  periodized mask `∑_{n ∈ ℤ^d} Φ_{z,r}(· + n)` is within `(1 + ∑_{k ≠ 0} e^{-4π²r²k²})^d - 1` of `1`
  (`abs_tsum_heatKernel_add_latticeShift_sub_one_le`), so every Gaussian average of a periodic
  function is within that error, times its cell integral of absolute values, of its cell mean
  (`norm_integral_heatKernel_smul_sub_cell_le`); the cell means are `ξ`, `āξ`, `ξ·āξ` because the
  averages at the origin converge almost surely to these values by Proposition 3.21, with the
  envelopes `|ξ|(1 + C(1 + X^d))/2`, `Λ|ξ|(1 + C(1 + X^d))/2`, `C(1 + X^d)|ξ|²` of the energy
  bound below the scale (dominated convergence, `norm_expectation_average_sub_le`). The error is
  `O(e^{-4π²r²})`, hence `O(r^{-β})` for every `β`. `estimate558_of_heatBound_and_law` is (5.58)
  without the expectations (1) as a hypothesis.
- **The heat identity: absolute convergence of the time integral.** `HeatPathwiseBound` is the
  bound of `HeatIdentityBound` with lower integrals, which is what (H) and the triangle inequality
  give; `heatIdentityBound_of_pathwise_of_rate` derives `HeatIdentityBound` from it and
  Proposition 3.21: the expected commutator at scale `ρ` is `O(ρ^{-μ})` uniformly in the center
  (`expectedCommutatorDecay_of_rate`, using that a nonnegative `O_s(θ)` variable has mean at most
  `θ(1 + 2⌈1/s⌉!)`), so by Tonelli the first moment of the time integral is finite and the lower
  integral is almost surely the Bochner integral. `estimate558_of_pathwise_and_law` is (5.58) with
  `HeatPathwiseBound` in place of `HeatIdentityBound`.
- **The heat identity (H).** Not the book's argument for the linear estimate (the book uses the
  multiscale estimates of Lemmas 4.14–4.16): `heatIdentity_bound`
  (`Ch04/Sec03/HeatIdentityDeterministic.lean`) proves (H) and the resulting bound for a fixed
  coefficient field from the weak gradient of the corrector, the divergence-free flux, their
  integrability against heat kernels and the sublinearity of the corrector. The homogenized matrix
  is diagonalized in an orthonormal frame (`exists_eigenframe`), in which the Gaussians of
  covariance `2B(u)`, `B(u) = r²I + 2(u - r²/2)ā`, are products of one-dimensional heat kernels
  (`anisoKernel`). The time derivative of their average of `∇φ_{eᵢ}` follows from the heat equation
  in each coordinate; the identities of the weak gradient and of the corrector equation extend from
  compactly supported tests to these Gaussian tests by cutoffs
  (`integral_mul_add_dot_gradient_eq_zero`), which turns `ā : ∇²` into the divergence of
  `(a - ā)(eᵢ + ∇φ_{eᵢ})`; the splitting `G_{B(u)} = G_{B(u) - uI} ∗ Φ_u` and Fubini's theorem
  give the Hessian of `G_{B(u) - uI}` against the commutator at scale `√u`. The terminal value at
  time `T` is at most `C T^{-1/2} ∫ Φ_{4ΛT}(z - y)|φ_{eᵢ}(y)| dy`, which tends to `0` because the
  Gaussian averages of `φ²_{eᵢ}` are `o(T)` by the sublinearity
  (`exists_integral_heatKernel_mul_abs_le_of_sublinear`, shells of radius `(k + 3)√T`). The
  Hessian is bounded by the isotropic kernel `(8Λ + 1)u⁻¹(4πu)^{-d/2}e^{-|x|²/(16Λu)}` of mass
  `(8Λ + 1)(4Λ)^{d/2}/u`, independent of the law (`heatPathwiseBound_of_lawHypotheses`), or by the
  sharp kernel `u⁻¹(1 + ½ x·E⁻¹x)G_E(x)`, `E = B(u) - uI`, of mass `(d + 1)/u`
  (`exists_heatPathwiseKernel`). For every law satisfying the assumptions and all homogenization
  data the almost sure inputs are the fields of `Corrector`, the finite Gaussian energy of the
  corrected coordinates (Lemma 3.17) and the bounds `1 ≤ ā ≤ Λ`. `estimate558_of_law` is (5.58)
  without the heat bound as a hypothesis.
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
- Statement. The exponent `1 - β(d - s)` is that of (3.85) and (6.13). The departures are that the
  random scale `X` depends on the slope `e`, on the corrector `φ` and on the flux corrector `S`,
  where the book uses one scale `X_s` for every slope in `∂B₁` (the supremum over `e` in (6.13)),
  that `X` is any measurable scale with `X ≤ O_s(C_s)` rather than the scale `X_s` of Theorem 3.8,
  and that (3.86), the bound on the gradient energy, is stated as well as the oscillation part of
  (3.85). The slope is a unit vector. The flux corrector is the
  selection (6.7) of Lemma 6.1, with its local Sobolev regularity and measurability explicit.
- The modules of `Ch03/Sec04/` and `Ch06/Sec01/` other than the section files were moved from
  einstein-relation-lean, commit `c97689e`; each names its source file.

## Section 3.3, (3.38)–(3.39), and Section 4.1, (4.8): the class A₁ and the energy J₁

- Lean: `ae_exists_harmonicA1_correctedAffine` (corrected affine functions belong to `A₁`),
  `ae_eq_zero_of_correctedAffineGrad_ae_eq_zero` (their gradients are linearly independent),
  `ae_gradients_harmonicA1` (`dim A₁ = d + 1`), `ae_J1Heat_eq_half_dot_inv` (`J₁ = ½ b·M⁻¹ b`),
  `J1Heat_bounds`, `aestronglyMeasurable_J1Heat`; `Ch03/Sec03/`, `Ch04/Sec01/`.
- The classification of `A₁` (Theorem 3.8 for `k = 1`) is `firstOrderLiouvilleStatement`, proved
  as `firstOrderLiouville`; the results that use it take it as the hypothesis `hL`. It is derived
  by the first-order route instead of the higher-order regularity theory of the book:
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
  from the approximation (2).
- The approximation (2) is proved as `harmonicApproximation`, with `ν = μ/(d + 2)`, by a route
  different from the comparison with a Dirichlet problem in the book. In the coordinates
  `y = M⁻¹x`, with `η = R^{-ν}`, the residual `u = v ∘ M` satisfies `|∫ u Δχ| ≤ ε ‖Δχ‖_{L²}` for
  tests `χ` in `B_{(1-2η)R}` (`exists_harmonic_ball_sq_le`). The test is smoothed with a round
  kernel at scale `ℓ = η²R`. The smoothed test `ψ` is paired with `v` by the tensor identity
  `∫ v ∑ᵢⱼ (ā eᵢ)ⱼ ∂ⱼ∂ᵢψ = ∑ᵢⱼₖ ∫ σᵢⱼₖ ∂ₖv ∂ⱼ∂ᵢψ + ∑ᵢⱼ ∫ φᵢ (a∇v)ⱼ ∂ⱼ∂ᵢψ`
  (`integral_mul_secondOrder_eq_tensor`), for the correctors recentred at their means on
  `B_{LR} ⊇ E_R`, together with the Caccioppoli inequality. The remainder is bounded by the
  mollification estimate `‖f - ρ_ℓ * f‖_{L²} ≤ ℓ ‖∇f‖_{L²}` and `‖∇²χ‖_{L²} = ‖Δχ‖_{L²}`. The orthogonal
  projection of `u` onto the closure of `{Δχ}` in `L²(B_{(1-2η)R})` has norm at most `ε`. The
  remainder is very weakly harmonic, and Weyl's lemma for very weak harmonic functions (the
  argument of the elliptic regularity library with locally integrable data) gives the smooth
  harmonic approximant (`exists_harmonic_sub_sq_le_of_laplacian_pairing`). The skew symmetry of
  `σᵢ` removes the third derivatives of the test.
- `J₁ = ½‖-V*p + U*q‖²` is stated in coordinates: `M` is the Gram matrix of the corrector columns
  `eᵢ + ∇φ_{eᵢ}` for the inner product `∫ Φ_{z,r} v·a w` and `b` the load `∫ Φ_{z,r}(-p·a Wᵢ + q·Wᵢ)`.
- The bound `0 ≤ J₁ ≤ Λ|p|² + |q|²` holds for every coefficient field, and so does the sharper
  `J₁ ≤ ½(√Λ |p| + |q|)²` (`J1Heat_le_half_sq`). The measurability of
  `a ↦ J₁(Φ_{z,r}, p, q)` is almost everywhere strong measurability for every finite law, proved
  through analytic sets: the strict upper level sets of `J₁` are projections of Borel sets.
- Lemma 6.1, (6.5)–(6.6): `FluxCorrector.ae_add_transpose_eq_const` gives skew symmetry up to a
  constant matrix and `fluxCorrectorDivergence` the divergence identity (6.6). The statement
  `fluxCorrectorDivergenceStatement` asserts only that there is a deterministic vector `D` with
  weak divergence `(a(e + ∇φ_e))_j - D_j`. In the proof `D` is identified as `ā e` for the
  homogenized matrix `ā` of the high-contrast theorem rather than the homogenized matrix of
  `HomogenizationData` (`FluxCorrector.ae_hasWeakDivergence_of_package`), without an ergodic theorem: the large-time
  heat averages of the flux converge by the scale pairing bounds of that theorem. The skew part
  `(S - Sᵀ)/2` satisfies the same identity (`FluxCorrector.ae_skew_divergence_of_package`).

## Lemma 1.1: basic properties of μ (`Ch01/Sec02/Lemma11.lean`, `Ch01/Sec02/DirichletMinimizer.lean`, `Ch01/Sec02/TestPoincare.lean`)

- Lean: `QSH.lemma_1_1`, with `coarseMatrix` (the matrix `a(U)` of (1.10)),
  `exists_isDirichletMinimizer`, `IsDirichletMinimizer.ae_eq`,
  `isDirichletMinimizer_iff_solvesDirichletProblem`, `IsDirichletMinimizer.integral_dot_eq_zero`
  and `IsDirichletMinimizer.quadraticResponse`.
- Domain. The book fixes a bounded Lipschitz domain; the Lean statement holds for every bounded set
  `U` of positive measure in dimension `d ≥ 1`, and the subadditivity (1.11) for partitions of `U`,
  up to a null set, by pairwise disjoint open sets.
- The minimizer (1.8) is the pair `(u, g)` of a function of `H¹₀(U)` and its weak gradient, with
  `v(·, U, p) = ℓ_p + u`; it is unique up to null sets of `U`. Existence: the book refers to the
  weak lower semicontinuity of the energy. Here a minimizing sequence of smooth tests is Cauchy in
  `L²(U)`: by the parallelogram identity and `ξ·aξ ≥ |ξ|²`,
  `⨍_U |∇vₙ - ∇vₘ|² ≤ 8(½ E(vₙ) + ½ E(vₘ) - μ(U, p))`, and the tests themselves by the Poincaré
  inequality for the tests of a cube containing `U` (from the zero-trace Poincaré inequality on axis
  cubes of the coarse-graining library, `Homogenization.scaled_dirichlet_poincare`). The limit lies
  in `H¹₀(U)` and has energy `μ(U, p)`.
- (1.9)–(1.10): `a(U)_{ij} = 2B(e_i, e_j)` for the polarization `B` of `p ↦ μ(U, p)`, which is a
  quadratic form by the parallelogram identity (see Section 1.3 below), in place of the linearity
  (1.15) of the minimizer.
- First variation: the minimizers are exactly the solutions of (1.12) in the weak sense, the test
  functions ranging over `H¹₀(U)`; the proof expands `t ↦ E(g + t h)` and uses that a quadratic
  polynomial `A t² + B t ≥ 0` has `B = 0`. Quadratic response: the exact identity
  `⨍_U ½(p + h)·a(p + h) - μ(U, p) = ⨍_U ½(h - g)·a(h - g)` (`IsDirichletMinimizer.trialEnergy_sub_eq`).

## Section 1.3: Propositions 1.7 and 1.8 (`Ch01/Sec03/Proposition17.lean`, `Ch01/Sec03/Proposition18.lean`, `Ch01/Sec03/MinimizerOscillation.lean`, `Ch01/Sec03/LocalMeasurability.lean`, `Ch01/Sec03/TriadicPartition.lean`)

- Lean: `QSH.proposition_1_7`, `QSH.proposition_1_8`, with `homogenizedMatrix` (the matrix `ā` of
  Definition 1.2, the polarization matrix of the limit (1.22)), `omegaModulus` (the modulus `ω` of
  (1.27), a supremum over the open ball `B₁`, with its bound `bddAbove_omegaModulus`) and
  `measurable_dirichletEnergy_localSigma` ((1.29) for open sets of finite measure with nonempty
  complement: the coefficients have a representative on `U`, the upper limit of gated averages
  against smooth bumps, jointly measurable for `Borel ⊗ F(U)`, as in
  `Ch04/Sec04/LocalCoefficientRepresentative.lean` for balls).
- Both constants depend only on `d` and `Λ` and are chosen before the law; `⌈m/2⌉` is written
  `(m + 1)/2`.
- Proposition 1.7. The matrix norm is the Frobenius norm (the book leaves it unspecified; all norms
  are equivalent with constants depending on `d`), and the entries of `a(□_m) - ā` are recovered
  from the deviations `μ(□_m, q) - μ̄(q)` at the points `q = ¼(eᵢ ± eⱼ)` of `B₁`. The assumption
  (0.11) is stated with a strict separation (`t > 1`), so two subcubes `z + □_n` are counted as
  independent when their indices differ by at least `3` in one coordinate (distance at least `2`),
  and each subcube has at most `5^d` other ones (`card_near_le`). Step 2 uses
  `E|μ(□_m, p) - μ̄(p)| ≤ 2 E[(μ(□_m, p) - E μ(□_n, p))₊] + 2ω(n)`, from the same facts as the
  book's `… + ω(m) + 2ω(n)`.
- Proposition 1.8. The minimizer is `v(·, □_m, p) = ℓ_p + u a` for any family of minimizers
  `a ↦ (u a, g a)` (unique up to null sets by Lemma 1.1). The book does not discuss the
  measurability of `a ↦ ⨍_{□_m} |v - ℓ_p|²`; it is proved (`measurable_setIntegral_sq_minimizer`):
  along tests of a countable family dense in `H¹₀`, selected measurably with energies within
  `1/(k+1)` of `μ(□_m, p)`, the mean squares converge to that of the minimizer by the quadratic
  response and the Poincaré inequality. In (1.35) the minimizers of the subcubes are replaced by
  tests with energies within `δ` of `μ(z + □_n, p)`, glued into a test of `□_m`, and `δ → 0`.
  In Step 2, `E[3^{-dr} Σ_z μ(z + □_n, p) - μ(□_m, p)] = E μ(□_n, p) - E μ(□_m, p) ≤ ω(n)` gives
  the bound `C 3^{-m} + C ω(⌈m/2⌉)`, which implies (1.33); the intermediate term `C 3^{-dm/8}` of
  the book is not needed.

## Section 1.4: Proposition 1.11 (`Ch01/Sec04/Proposition111.lean`)

- Lean: `QSH.proposition_1_11`, `QSH.proposition_1_11_of_ne_four`,
  `QSH.tendsto_integral_coarseDeviation`, with `coarseDeviation` (the random variable `E(m)` of
  (1.39), for the Frobenius norm), `coarseDeviation_le` ((1.52), with the constant `3/2`) and
  `tendsto_omegaModulus` (the limit in (1.28)). The constants depend only on `d` and `Λ`.
- (1.41). The proof gives `E[E(m)] ≤ C Σ_{n=0}^m 3^{n-m}(3^{-dn/4} + ω(⌈n/2⌉))`
  (`proposition_1_11`), and the book then bounds `Σ_{n=0}^m 3^{n-m} 3^{-dn/4}` by
  `C 3^{-(d/4 ∧ 1)m}`. This holds for `d ≠ 4` (`proposition_1_11_of_ne_four`); for `d = 4` the sum
  is `(m + 1) 3^{-m}`, which is not bounded by `C 3^{-m}`, so (1.41) is not proved here for `d = 4`;
  the limit `E[E(m)] → 0` is proved for every `d`.
- `E[E(m)] → 0`: the book uses the monotonicity of `ω`; here the weighted sums of the null
  sequence `3^{-dn/4} + ω(⌈n/2⌉)` against the weights `3^{n-m}` tend to zero by dominated
  convergence for series, and `ω(n) → 0` because `ω(n)` is at most half the sum of the absolute
  values of the entries of the matrix of `p ↦ E μ(□_n, p) - μ̄(p)`.

## Section 1.4: Propositions 1.10 and 1.12, Lemma 1.13, Corollary 1.14 (`Ch01/Sec04/Proposition112.lean`, `Ch01/Sec04/Proposition110.lean`, `Ch01/Sec04/Lemma113.lean`, `Ch01/Sec04/Corollary114.lean` and their proof modules)

- Lean: `QSH.proposition_1_12`, `QSH.proposition_1_10`, `QSH.lemma_1_13`, `QSH.corollary_1_14`,
  with `H1`, `h1Norm`, `hatNegativeSobolevNorm` and `vectorHatNegativeSobolevNorm`
  (`Ch01/Sec04/HatNegativeSobolev.lean`). The constants depend only on `d` (and on `Λ` for
  Proposition 1.10, chosen before the law).
- The norms. `‖f‖_{Ĥ̲⁻¹(U)}` of (0.31) is the supremum of `|⨍_U f v|` over `v ∈ H¹(U)` with weak
  gradient `g` and `|U|^{-1/d} ‖v‖_{L̲²(U)} + ‖g‖_{L̲²(U)} ≤ 1` (the normalized norm of (0.26), with
  the Euclidean norm of the gradient), valued in `[0, ∞]`. For a vector field the norm is the sum of
  the norms of its components, as for (0.29) in `Front/Notation.lean`; the book does not specify
  it, and the choices differ by factors depending on `d`. Proposition 1.10 and Lemma 1.13 are read
  with `Ĥ⁻¹`: their proofs pair with functions of `H¹` that do not vanish on the boundary (the test `g` of Proposition 1.12, `∇w` in (1.44), the
  fields `(e·x)e_i` in (1.45)).
- Proposition 1.12. `Z_n = 3^n ℤ^d ∩ □_m` is indexed by `k ∈ {0, …, 3^{m-n} - 1}^d`
  (`partitionCube n (m - n) k`) and `|Z_n| = 3^{d(m-n)}`. The book normalizes the tests by
  `3^{-2m}|(g)_{□_m}|² + ‖∇g‖²_{L̲²} ≤ 1`, here by the norm (0.26); the two are equivalent by the
  Poincaré inequality. The proof is the book's: the iteration over the scales with the Poincaré
  inequality (1.43) on the subcubes, proved from the mean-zero Poincaré inequality on axis cubes of
  the coarse-graining library (`Homogenization.scaled_meanZero_poincare`).
- Proposition 1.10. The statement is for every minimizer `(u, g)` of `μ(□_m, p)` (the minimizer is
  unique up to null sets), with the squared norms in `[0, ∞]`. (1.49) is proved by comparing
  `μ(U, p + tq)` with the energy of the trial gradient `g` of the minimizer for `p`, instead of the
  polarization of `⨍ ∇v(·, U, q)·a∇v(·, U, p)`. In Step 2 the glued minimizers `v_n` are replaced by
  tests of the subcubes close in `L²` to the gradients of the minimizers of the subcubes, glued into
  a test of `□_m`, and `δ → 0` (`subcube_averages_le`); the bound of the averages by
  `|Z_n|⁻¹ Σ_z |a(z + □_n) - ā| + |a(□_m) - ā|` and the bound
  `Σ_{n<m} 3^{n-m}(...)^{1/2} ≤ (5/2) E(m)^{1/2}` follow the book.
- Lemma 1.13. The Neumann solution of (1.47) and the estimate (1.48) (Lemma B.19 in the book) are
  those of the coarse-graining library on the cubes `originCube d m`, whose open realization is
  `□_m` (`Homogenization.meanZeroNeumannPoissonSolutionOfCoerciveEstimate`,
  `Homogenization.originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply`). The average of
  `∂_i w` is bounded by testing (1.47) with `x ↦ x_i`, as with `x ↦ p·x` in the book. For (1.45),
  `(v)_{□_m} = -⨍ x_1 ∂_1 v` for `v ∈ H¹₀(□_m)` (the field `(e·x)e` of the book with `e = e_1`).
- Corollary 1.14. The sum runs over `n = 0, …, m`, with the Euclidean norm of the vector averages
  `(∇u)_{y+□_n}` (`vectorAverage`), as in (1.46). The same estimate in the conventions of the
  coarse-graining library is `QSH.exists_originCube_multiscalePoincare`
  (`Ch03/Sec04/MultiscalePoincareVector.lean`).

## Section 1.3 and Lemma 3.16: the homogenized matrix and the first-order correctors

- Lean: `QSH.exists_homogenizedMatrix` (`Ch01/Sec03/SubadditiveLimit.lean`),
  `QSH.homogenizationDataExists_of_measurable` (`Ch03/Sec04/HomogenizationDataExistence.lean`) and
  `QSH.homogenizationDataExists` (`Ch03/Sec04/CorrectorMeasurability.lean`).
- Section 1.3, (1.21)–(1.22) and Definition 1.2. Route. The book obtains the quadratic form (1.10)
  from the existence and the linearity (1.15) of the minimizer (1.8). Here `μ(U, e)` is the infimum
  of the energies of the smooth compactly supported tests of `U` (by the approximation in the
  definition of `H¹₀(U)` and the continuity of the energy in `L²`), the tests form a vector space,
  and the parallelogram identity of the energy density gives
  `μ(U, e + f) + μ(U, e - f) = 2μ(U, e) + 2μ(U, f)` (`dirichletEnergy_parallelogram`). The
  expectations and the limit (1.22) inherit it, and a function with the parallelogram identity and
  the bound `|μ̄(e)| ≤ ½Λ|e|²` is a quadratic form `½ e·āe` with `ā` symmetric (the argument of
  Jordan and von Neumann, `exists_symmetric_of_parallelogram`). The subadditivity (1.11) is proved
  for partitions by disjoint open sets up to a null set, by gluing tests, and used for the
  partition of `□_{n+1}` into the `3^d` translates of `□_n`; stationarity enters through
  `μ(z + U, e)(a) = μ(U, e)(T_z a)` (`dirichletEnergy_preimage_sub`).
- Lemma 3.16. Route. The correctors are those of the homogenization theorem of Armstrong, Kuusi and
  Loher (Theorem C, `HCPoly.uniform_homogenization`) for the law of `a(2·)`, undilated:
  `φ_e(x) = 2 Φ_e(x/2)` (`UndilatedCorrector.lean`). Their sublinearity comes from the oscillation
  bounds of that theorem above its homogenization scale, as for Lemma 3.17 above. The stationarity
  of `∇φ_e` is the uniqueness argument of the proof of Lemma 3.16: `x ↦ φ_e(a)(x + z)` is a
  sublinear corrector of `T_z a`, and the Liouville classification of the high-contrast theorem on
  its event of full probability for `T_z a` (in place of Theorem 3.8) identifies its gradient with
  `∇φ_e(T_z a)` (`undilatedGradient_translate_ae_eq`). The homogenized matrix of
  `HomogenizationData` is the matrix of Definition 1.2 given by (1.22).
- Measurability. Definition 3.14 asks the stationary field to be measurable for `B × F`; the
  proof of Lemma 3.16 does not address the measurability of `(x, a) ↦ ∇φ_e(x, a)`, and the
  high-contrast theorem exports none for its corrector gradients. It is proved in
  `Ch03/Sec04/CorrectorMeasurability.lean` (`highContrastCorrectorMeasurable`) by the argument
  used for the measurability of `J₁` (`Ch04/Sec01/J1HeatMeasurability.lean`): the coefficient field
  is encoded in the Polish space `∏ₙ L²(B̄ₙ)`, the pairs of a coefficient field and an element of
  `A₁` whose potential minus `e·x` is sublinear on the closed balls `B̄ₙ` form a Borel set, and on
  the event of full probability its fibers have the single gradient `e + ∇φ_e` (the uniqueness of
  correctors). The events defined by the gradient are therefore preimages of analytic sets,
  universally measurable, and a jointly measurable representative of a measurable modification
  is the version of Definition 3.14. Hence `homogenizationDataExists`: every law satisfying
  (0.10)–(0.11) has homogenization data, and `blockCLT_of_uniformAdditivity` and its two
  companions (`Ch05/Sec04/BlockEstimatesFromCorrectors.lean`) give Lemma 5.29 (i)–(iii) from
  Theorem 4.6 (i) with constants uniform over the laws.

## Proposition 3.21 with constants chosen before the law (`Ch04/Sec01/UniformGaussianRate.lean`)

- Lean: `QSH.uniformGaussianCorrectorRate` (for `d ≥ 2`, `Λ > 1`: `C(τ), μ(τ) > 0` for
  `0 < τ < d`, and for every law homogenization data `S` with `GaussianCorrectorRate P S τ C(τ) μ(τ)`).
- Route. The book proves (3.101)–(3.103) from the quantitative convergence of the subadditive
  quantities of Chapter 2. Here the correctors are those of the homogenization theorem of
  Armstrong, Kuusi and Loher, and the bounds are proved at a realization, above `Y = B X` (`X` the
  homogenization scale of that theorem, `B` dimensional), at every mask `Φ_{x₀,r}` with `|x₀| ≤ r`
  (`gaussianBasisBounds_of_realization`, `exists_ae_gaussianBasisBounds`):
  `∫ Φ ∂ₖφ = -∫ (φ - c) ∂ₖΦ` and the dyadic telescoping of the oscillation bound of Lemma 3.17 give
  `|∫ Φ ∇φ| ≤ C (Y/r)^θ` (`Ch03/Sec04/GaussianSublinearity.lean`, `GaussianCorrectorBounds.lean`);
  the flux follows from the pairing bound of the fluxes (`exists_uniform_flux_pairing`) and
  `exists_heatConv_le`; the energy from `∫ Φ ∇φₗ · a Gᵢ = -∫ (φₗ - c) a Gᵢ · ∇Φ`, the test identity
  for `η (φ - c) ∈ H¹₀` (`CutoffTestIdentity.lean`, `GaussianTestExtension.lean`). The matrix of
  these bounds is the high-contrast homogenized matrix `ā`.
- Departure: the identification `S.homogenized = ā` (`homogenized_eq_of_basisBounds`,
  `Ch04/Sec01/HomogenizedFluxIdentification.lean`) is not in the book, whose matrix is defined by
  (1.22) and whose correctors are built from it. Lower bound: `μ(□ₙ, e) ≥ ⨍ (e·aG − ½ G·aG)` (the
  dual bound, `Ch01/Sec03/DirichletEnergyCorrectorBounds.lean`), whose expectation is the cell mean
  `½ e·āe` of a stationary density (`StationaryCubeAverages.lean`, `HomogenizedGaussianLimits.lean`).
  Upper bound: the trial function `η (φ_e − c)` with the inner cutoff of relative width `τ`, the
  error `4dτ|e|² + K E ψₙ(Y) → 4dτ|e|²` by the sublinearity of the correctors and dominated
  convergence.
- Centers: for a center `z` the bounds are transported from the nearest lattice point by
  stationarity, with the scale `X(a, z) = max(Y(T_k a), √d)^p`, `p = 2d/(d+τ)`, `O_τ(C)` by the
  tail `exp(-t^d)` of the high-contrast scale; the rate is `μ = θ (d − τ)/(2d)`.

## Section 4.4: Lemma 4.21 from the high-contrast excess decay (`Ch04/Sec04/`)

- **The zoom of Lemma 4.21** (pp. 157-158). The book zooms from the intermediate radius `S` to
  `r` with the `k = 1` regularity of Theorem 3.8. The Lean proof uses instead the excess-decay
  clause of the high-contrast homogenization theorem at an exponent `ϑ < 1`, transported from
  ellipsoids to balls (`QSH.ballExcessDecay`). The decay `(r/S)^ϑ` then closes the exponent budget
  `(r/S)^ϑ S^{-β} ≤ r^{-γ}` only when the fluctuation exponent `β` of the class of laws is larger
  than the construction exponent `α` (`QSH.exists_slope_budget`), so the single-slope estimate is
  proved on the classes of laws with the linear estimate at an exponent `β > α`
  (`QSH.slopeEstimateOnClass_of_linear_finiteBall`), and (5.85) uses the construction exponent
  `d/2 - h` (`QSH.localizedEnergy_of_observation`, `QSH.localizedEnergy_of_finiteBall_linear`).
- **The observation step** is split into a deterministic finite-ball observation for
  `a`-harmonic functions (`QSH.FiniteBallObservation`, a hypothesis of these theorems) and the
  observation of the smoothed correctors (`QSH.smoothedCorrectorObservation_of_gaussianGradient`).
  For the latter, the truncated Gaussian observation of `φ - c` at `y ∈ B_{S/θ}(z)`, with `c` the
  cut-off Gaussian mean, is bounded along the segment from `z` to `y` by the Gaussian averages of
  `∇φ` (`QSH.abs_truncated_observation_le`), and the squares of these averages are averaged over
  the segments, which is `O_{s/2}` by Lemma A.4 below the exponent one
  (`QSH.osBound_sqrt_segmentAverage`). The cutoff is taken at `R = S r^{ε'}`; its error terms are
  Gaussian tails, and the smallness on the event `{X ≤ r}` comes from the oscillation bound of the
  correctors on `B_R(z)` above the minimal scale.
- **The finite-ball observation** (Lemma 4.20 and its transfer, pp. 152-155). The book proves the
  observation (4.73) for the elements of `A_k` with Theorem 3.8 at the order `k` and transfers it to
  general solutions by approximation. The library has Theorem 3.8 only at `k = 1`. Here the
  finite-ball observation follows (`QSH.finiteBallObservation_of_compactTests`) from a deterministic
  finite-ball estimate with compact tests above a random radius (`QSH.CompactTestFiniteBall`), in
  which the tests may depend on the law through its homogenized matrix: the growth of `∫_{B_t(z)} u²`, `S ≤ t ≤ T`, is controlled by the
  pairings of `u` with finitely many tests supported in `B_S(z)` and the outer term. Each pairing
  differs from the pairing of the Gaussian average of `1_{B_T} u` by at most a Gaussian moment of
  the shifts times `σ` and the growth constant, which is absorbed for small `σ`
  (`QSH.integral_sq_ball_le_of_compactTests`); the observation ball is `B_{2S}(z)`, `θ = 1/2`.
  The estimate with compact tests is proved (`QSH.compactTestFiniteBall`, next section).

## Lemma 4.21: the estimate with compact tests and the frozen statements (`Ch04/Sec04/CompactTest*.lean`, `Ch05/Sec04/FrozenProved.lean`)

- **Lemma 4.20 is replaced.** The proof of Lemma 4.20 in the book controls a solution on the
  intermediate ball by its truncated Gaussian observation through the higher-order Liouville theorem
  (Theorem 3.8 at order `k`), which is not formalized. The Lean proof uses instead the estimate with
  compact tests `QSH.CompactTestFiniteBall d Λ k`, proved for every `d ≥ 2`, `Λ > 1` and `k > 0`
  from the first-order and flux correctors only (`QSH.compactTestFiniteBall`):
  `∫_{B_t(z)} u² ≤ C (∑ₗ Oₗ² + (S/T)^{2k} ⨍_{B_T(z)} u²) (t/S)^{2k} |B_t|` for `S ≤ t ≤ T` above a
  random radius at every center, where `Oₗ` are the pairings of `u` with finitely many rescaled
  compact tests at the scale `S`. The absorption of the tests into the truncated Gaussian
  observation gives the finite-ball observation (`QSH.finiteBallObservation_of_compactTests`).
- **Flux correctors and the tensor identity.** For the symmetric part `Dₛ` of the homogenized
  matrix, the profile `ρ` and the partner `χ` with `Dₛ∇χ = yρ` (`QSH.adaptedRho`, `QSH.adaptedChi`)
  give `∂_b ρ_b = b L χ_b`, `L = -∇·Dₛ∇`. The pairing of a solution with `L χ_b` is computed with
  the tensor identity of Section 3.3, that is with the first-order correctors and the skew flux
  correctors of Lemma 3.17, Lemma 6.1 and Proposition 6.2 above their random scale
  (`QSH.exists_ae_sublinearCorrectorFamily`), in place of a weak flux pairing. So the averages
  `U_t = ρ_{λt} * u` change in the scale at the rate `t^{-|α|-1-μ}` in their derivatives of order
  `|α|`, and `u - U_t` is small by the translation estimate and the Caccioppoli inequality.
  Integrating the derivatives of order `< ⌈k⌉` outwards and those of order `⌈k⌉` inwards and
  absorbing gives the estimate (`QSH.compactTest_core`).
- **Tests depending on the law.** The tests are the rescaled derivatives of `ρ` of order `< ⌈k⌉`,
  so they depend on the law through `Dₛ`; `CompactTestFiniteBall` chooses them after the law, while
  their number, their bounds and the constants are chosen before it. The absorption uses only
  these.
- **Random radius.** The correctors above the random scale at the nearest lattice point are
  translated to the center (`QSH.SublinearCorrectorFamily.translate`), so the radius has the
  stochastic integrability of that scale at every center.
- **The frozen statements.** `QSH.uniformCompactTestFiniteBall` gives the theorems of
  `Ch05/Sec04/FrozenFromCompactTests.lean` with no hypothesis: E1–E7
  (`QSH.averagedCorrectorGradient_holds`, `QSH.blockBoundary_holds`, `QSH.blockChange_holds`,
  `QSH.blockCLT_holds`, `QSH.coarsenedCoefficientEstimates_holds`, `QSH.localizedEnergy_holds`,
  `QSH.negativeSobolevCorrector_holds`), the single-slope estimate on the classes `LinearLaw`,
  Proposition 4.11 at the exponents of the bootstrap, Theorem 4.6 (i) and (iii) and (5.58) with
  constants chosen before the law. They are stated in `Ch05/Sec04/FrozenProved.lean` and not after
  the markers of the frozen files, since each frozen file is imported by the modules of its proof.

## Appendix D: Propositions D.1 and D.2, Lemmas D.3 and D.4 (`AppD/`)

- **Lemma D.4** (`lemmaD4`). The maximal function `maximalFunction f` is the centered maximal
  function over the open Euclidean balls, with values in `[0, ∞]`; it is lower semicontinuous
  (`lowerSemicontinuous_maximalFunction`), so its `L^p` norm is that of a measurable function. For
  `p < ∞` the bound is deduced from the strong estimate of the elliptic regularity library for the
  uncentered maximal function, `PDE.eLpNorm_uncenteredBallMaximal_le`, with the constant
  `2 (3^d p/(p - 1))^{1/p}` (a covering argument with the factor `3` in place of the factor `5` of
  the Vitali covering Lemma C.5), which is at most the constant `2 (5^d p/(p - 1))^{1/p}` of (D.16).
  For `p = ∞` the constant of (D.16) is read as its limit `2` (`maximalConstant`).
- **Lemma D.3** (`lemmaD3`). `u ∈ H^α(ℝ^d)` is given with its weak derivatives `g l = ∂_{l₁} ⋯ ∂_{l_m} u`
  for the lists of coordinates `l` of length `m ≤ α`, each in `L²(ℝ^d)`, `g (i :: l)` being the weak
  `i`-th derivative of `g l` (`IsSobolevFamily`); `[u]²_{H^α} = ∫ ∑_{|l| = α} |g l|²` is the square of
  the `L²` norm of the tensor `∇^α u`, and `|∇^k Φ(t, ·) ∗ u|²` (`heatGradSq`) is the sum of the squares
  of the convolutions of `u` with the `k`-th derivatives `∂_{w₁} ⋯ ∂_{w_k} Φ(t, ·)` of the heat kernel.
  The integrals are lower Lebesgue integrals, and the time integral is over `(0, ∞)`. The proof is
  the book's: (D.6) is proved for smooth compactly supported functions from the energy identity
  `∫ w(a)² - ∫ w(b)² = 2 ∫_a^b ‖∇w‖²` (`integral_heatSmooth_sq_sub_eq`), integrated in time at every
  point and exchanged with the space integral by Fubini's theorem; the reduction to `k = 1` uses the
  semigroup property and Young's inequality (`lintegral_heatGradSq_le_of_smooth`); the case `α = 0`
  for `u ∈ L²` follows by density and Fatou's lemma (`lintegral_heatGradSq_le`); for `α ≥ 1` the
  `α` derivatives are moved from the heat kernel onto the weak derivatives of `u`
  (`kconv_heatKernelDeriv_append_eq`), the weak derivative identity being extended from compactly
  supported tests to the derivatives of the heat kernel by the dilated cutoffs of the elliptic
  regularity library (`integral_mul_coordinateDerivative_of_hasWeakPartialDerivative`). The book
  reduces to `α = 0` by considering `∇^α u` in place of `u`, which is this step.
- **Proposition D.2** (`propositionD2_two`) is proved in the case `q = 2`, `α ∈ ℕ` of (D.3), in which,
  as the book remarks, its left-hand side is that of (D.5) by Tonelli's theorem. The cases `q ≠ 2`
  of (D.3) (Stein's argument with the maximal function and the Marcinkiewicz interpolation theorem)
  and (D.4) (fractional `α`, with the Gagliardo seminorm) are not formalized.
- **Proposition D.1.** Only the local variant of its first inequality used for (4.126) is
  formalized (see Section 4.6 above); the spaces `W^{-α,p}(ℝ^d)` and Remark B.6 on `ℝ^d` are not
  (Remark B.6 on balls is `remark_B_6`, see the Appendix B section).

## Appendix B: Definition B.4 for `α = 1` and Remark B.6 on balls (`AppB/DivergenceRepresentation.lean`)

- **Definition B.4** is formalized for `α = 1` and `p ∈ (1, ∞)` only, by the normalized norm
  `negativeSobolevOneNorm p U f F` of a distribution `h = f + ∇·F` (see the Appendix C section);
  the spaces `W^{-α,p}(U)` for `α ≠ 1`, and `W^{-1,1}`, `W^{-1,∞}`, are not formalized (for
  `p = 1` the test exponent `p/(p-1)` is `0` in Lean).
- **Remark B.6** (`remark_B_6`) is formalized on balls `B_r(z)`, for `d ≥ 1`, `p ∈ (1, ∞)` and
  `h = f + ∇·F` with `f, F ∈ L¹(B_r(z))`, with the normalized norms: there is `H ∈ L^p(B_r(z); ℝ^d)`
  with `∫ h ψ = -∫ H · ∇ψ` for every `ψ ∈ C_c^∞(B_r(z))` (the book's (B.5) is stated with the
  opposite sign convention `∫ w h = ∫ F · ∇w`, i.e. `F = -H`, and for `w ∈ W_0^{1,p'}(U)`; the
  pairing of a distribution with `W_0^{1,p'}` is its extension from `C_c^∞` by density) and
  `‖h‖_{W̲^{-1,p}(B_r(z))} ≤ ‖H‖_{L̲^p(B_r(z))} ≤ C(d) ‖h‖_{W̲^{-1,p}(B_r(z))}`, where
  `C(d) = 2 (2^d + 1) |B_1|^{-1/d} + d` (`divergenceRepresentationConstant`). The endpoint `p = ∞`
  and domains other than balls are not formalized. The proof is the book's: on the tests the
  gradient map into `L^{p'}(B_r(z); ℝ^d)` is injective, the test norm `‖ψ‖_{W̲^{1,p'}}` is at most
  `C(d) ‖∇ψ‖_{L̲^{p'}}` by the Poincaré inequality for tests of the elliptic regularity library
  (`PDE.eLpNormOn_testFunction_le_two_pow_add_one_mul_diameter_grad`, constant `(2^d + 1)·2r`), and the
  functional `ψ ↦ ⨍ h ψ` is represented through the Hahn–Banach theorem and the duality
  `(L^{p'})^* = L^p` (`PDE.exists_nativeLp_density_through_injective`). The lower bound is Hölder's
  inequality (`negativeSobolevOneNorm_zero_le`). For `d = 0` the statement fails (the ball is a
  point and `h = f` is not a divergence).

## Appendix C: Theorem C.1, Lemmas C.2 and C.4–C.6, Corollary C.3 (`AppC/`)

- **Norms and right-hand sides.** The normalized norms `‖·‖_{L̲^s(U)}` are `PDE.eLpMeanNormOn U s`
  of the elliptic regularity library, and `‖∇u‖_{L̲²(B)}`, `‖u - (u)_B‖_{L̲²(B)}` are `vectorRms` and
  `scalarRms`. A right-hand side `h ∈ H^{-1}(U)` is written `h = f + ∇·F` with `f ∈ L²(U)` and
  `F ∈ L²(U; ℝ^d)` (every element of `H^{-1}(U)` has this form), the equation `-∇·(a∇u) = h` is
  `HasWeakDivergence U (a∇u + F) (-f)`, and the normalized `W^{-1,p}(U)` norm of Definition B.4 and
  (0.29) is `negativeSobolevOneNorm p U f F`, the supremum of `|⨍_U (fψ - F·∇ψ)|` over
  `ψ ∈ C_c^∞(U)` with `‖ψ‖_{W̲^{1,p/(p-1)}(U)} ≤ 1`, the test norm being (B.1) normalized with `k = 1`
  (`sobolevOneTestNorm`). For `p = 2` and `F = 0` it has the same tests and the same pairing as
  `negativeIntegerSobolevNorm 1 U f` of `Front/Notation.lean`, and on tests the two test norms agree
  term by term (`PDE.eLpMeanNormOn U 2` in place of `scalarRms`); the equality of the two norms is
  not stated in Lean. The bound `|⨍_U h v| ≤ ‖h‖_{H̲^{-1}(U)} ‖v‖_{H̲¹(U)}` is extended from smooth
  tests to `v ∈ H¹₀(U)` through the smooth approximants of `PDE.H10Function`
  (`abs_integral_pairing_le_of_h10`).
- **Lemma C.2** (`lemma_C_2`; `interiorCaccioppoli` on balls with any center). The book's proof, with
  the test function `φ (φ (u - (u)_{B_r})) ∈ H¹₀(B_r)` built by the product lemmas of the elliptic
  regularity library and a cutoff with `|∇φ| ≤ 64/r`.
- **Corollary C.3** (`corollary_C_3`) is stated for `d ≥ 2`, the book's standing assumption: the exponent `2_* = 2d/(d+2)` is at
  least `1` only then, and the Sobolev–Poincaré inequality used, the convex-domain inequality
  `PDE.exists_convexSobolevPoincare_constant` with `p = 2_*`, is for `p ∈ [1, d)`.
- **Lemma C.4** (`lemma_C_4`). The book's proof, with these changes. The stopping radius of (C.8) is
  taken among the dyadic radii `(t - s)R/(10 · 2^k)`, and `λ₀` is `(160/(t - s))^{d/2}` (instead of
  `(20/(t - s))^{d/2}`) times `‖f‖_{L̲²(B_R)} + ‖g‖_{L̲²(B_R)}`; this gives
  `∫_{B_{5 r_z}(z)} f² ≤ 8^d λ² |B_{r_z}|` in place of the bound with `5^d`, whose proof in the book
  needs `10 r_z ≤ (t - s)R/10` (in the other case it follows from the choice of `λ₀`). The truncated quantity of the absorption is `∫_{B_{sR}} f² (|f| ∧ m)^ε`
  rather than `‖f_m‖^{2+ε}_{L^{2+ε}(B_{sR})}`: the first identity of the integration after (C.10)
  is an inequality, and the integral of `λ^{1+ε-q} μ_f({|f| ≥ λ})` is bounded by the truncated
  weighted quantity through `|f|^q ((8K|f|) ∧ m)^{2+ε-q} ≤ (8K)^{2+ε-q} f² (|f| ∧ m)^ε`
  (`rpow_mul_min_rpow_le`), not by `‖f_m‖^{2+ε}`. The level sets are `{|f| > λ}`. The Lebesgue
  points are those of the Lebesgue differentiation theorem on Euclidean balls, deduced from
  Mathlib's theorem on cubes (`ae_tendsto_ballAverage_abs_sub`), and `f, g` are replaced by
  measurable representatives. The exponent is `δ = (1/2) ∧ (2 - q)/(2 · 8^d (8K)^3)`, and Lemma C.6
  is used with a constant uniform in `dε/2 ∈ [0, d/2]` (`lemma_C_6_uniform`), since `ε = δ ∧ (p - 2)`
  depends on `p`.
- **Lemma C.5** (`lemma_C_5`). The family is indexed by a type, the subfamily is a countable set of
  indices on which the balls are pairwise disjoint; the proof is Mathlib's Vitali selection
  `Vitali.exists_disjoint_subfamily_covering_enlargement` with factor `2`.
- **Lemma C.6** (`lemma_C_6`) holds for every real `ξ`; the ratio is `θ = (2/3)^{1/max(ξ,1)}` in
  place of the book's `(2/3)^{1/ξ}`, which also covers `ξ = 0`.
- **Theorem C.1.** For `d ≥ 2`, `theorem_C_1_divergence` is the case `h = ∇·H`, `H ∈ L^p`, of the
  book's proof, with `‖H‖_{L̲^{(2+δ)∧p}(B_r)}` on the right-hand side, from Corollary C.3 on every
  ball `B_ρ(z) ⊆ B_r`, the bound `‖∇·H‖_{H̲^{-1}} ≤ ‖H‖_{L̲²}` and Lemma C.4. The book applies Lemma C.4
  with `q = 2_*`, which is `1` for `d = 2`, outside the range `(1, 2)` of the lemma; the proof uses
  `q = max(2_*, 3/2)`. The general case is reduced to this one in the book by Proposition B.16
  (the Dirichlet problem `-Δw = h` in `W^{1,s}_0(B_r)`, `H = -∇w`); the Lean proof uses instead the
  representation of Remark B.6 on balls (`remark_B_6`, see the Appendix B section): every
  `h ∈ W^{-1,s}(B_r)` is `∇·H` with `‖H‖_{L̲^s(B_r)} ≤ C(d) ‖h‖_{W̲^{-1,s}(B_r)}`, which is what the
  reduction uses. `theorem_C_1_of_divergenceRepresentation` is the reduction under this
  representation as a hypothesis (`DivergenceRepresentation d C`), `exists_divergenceRepresentation`
  discharges it, and `theorem_C_1` is the statement of the book, for `d ≥ 2` and
  `h = f + ∇·F` with `f ∈ L²(B_r)`, `F ∈ L²(B_r; ℝ^d)`.
  The elliptic regularity library proves a Meyers estimate on the unit ball for divergence-form
  right-hand sides with exponents up to `2 + c/√Λ` (`PDE.MeyersProof.result`, via a
  Gehring lemma on cubes with the lower exponent `2d/(d+1)`); the proof here follows the book through
  Lemma C.4, which holds for every `q ∈ (1, 2)`.

## Section 2.1: Lemmas 2.1, 2.2 and 2.7 (`Ch02/Sec01/DualEnergy.lean`, `Ch02/Sec01/DualMaximizer.lean`, `Ch02/Sec01/Lemma21.lean`, `Ch02/Sec01/DefectMaximizer.lean`, `Ch02/Sec01/Lemma22.lean`, `Ch02/Sec01/Lemma27.lean`)

- Lean: `QSH.lemma_2_1`, `QSH.lemma_2_2`, `QSH.lemma_2_7`, with `dualEnergy` (`μ*(U, q)` of (2.1)),
  `dualityDefect` (`J(U, p, q)` of (2.6)), `defectTrialEnergy` (the functional of (2.9)),
  `IsAHarmonic` (`A(U)` of (0.38) intersected with `H¹(U)`), `IsDualMaximizer`, `IsDefectMaximizer`
  (the maximizer `v(·, U, p, q)`), `coarseDualInvMatrix` (`a*⁻¹(U)`) and `coarseDualMatrix`
  (`a*(U)`), and the inequality (2.4) `dot_le_dirichletEnergy_add_dualEnergy`.
- Domain. The book fixes a bounded Lipschitz domain; the Lean statements are for bounded open convex
  nonempty sets, which include the cubes of Sections 2.2 and 2.3. The existence of the maximizer of
  (2.1), which the book calls routine, uses the Poincaré inequality on `U`; here it is the Neumann
  maximizer of the coarse-graining library on convex domains
  (`Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory`, field
  `neumann_meanZero_maximizer_exists`), whose `H¹` functions and functional are those of (2.1)
  (`dualTrialEnergy_eq_symmetricNeumannEnergyValue`). The inequality (2.4), the bound `≤` in (2.9)
  and (2.13) hold for every bounded open set; the pieces `U₁, …, U_N` of the partition in (2.15) are
  open sets, not necessarily convex.
- `A(U)`. The suprema (2.3) and (2.9) are over `u ∈ H¹(U)` with `a∇u` weakly divergence-free in `U`
  (tested against smooth compactly supported functions), where the integrals are defined; for such
  `u`, `∫_U ∇w·a∇u = 0` for every `w ∈ H¹₀(U)` by density (`IsAHarmonic.setIntegral_dot_eq_zero`).
- Lemma 2.1 and its maximizer: the maximizer is stated for every maximizer `(u_*, g_*)` of (2.1) and
  every minimizer `ℓ_p + u` of (1.7), as the pair `(u_* - ℓ_p - u, g_* - (p + g))`; the gradient of
  the maximizer of (2.9) is unique up to null sets (the book: unique up to additive constants).
- Lemma 2.2. The quadratic form (2.20) of `μ*(U, ·) = J(U, 0, ·)` is obtained from its parallelogram
  identity, which follows from the linearity (2.18) and the identity (2.19), and `a*⁻¹(U)` is its
  polarization matrix, as for `a(U)` in Lemma 1.1. The first variation (2.16) and the quadratic
  response (2.17) are stated with averages over `U`, the test functions ranging over
  `A(U) ∩ H¹(U)`; (2.13) and (2.14) are stated for every maximizer, componentwise.
- Lemma 2.7: for the Frobenius norm, with the supremum over the open ball `B₁` of
  `J(U, p, āp)^{1/2}` (a set bounded above, which the statement includes) and `C = 3d²(32Λ)^{1/2}`.
  The proof uses the completed square `J = ½ p·(a(U) - a*(U))p + ½ (q - a*(U)p)·a*⁻¹(U)(q - a*(U)p)`
  at the points `¼eₖ` and, for `a(U)`, the bound of the entries of the nonnegative matrix
  `a(U) - a*(U)` by the Cauchy–Schwarz inequality and `a(U) - a*(U) ≤ Λ`, in place of the book's
  minimization in `p`.

## Section 2.2: Lemma 2.12 and Definition 2.14, and the measurability of μ* (`Ch02/Sec02/Lemma212.lean`, `Ch02/Sec02/Definition214.lean`, `Ch02/Sec01/DualEnergyMeasurability.lean`)

- Lean: `QSH.lemma_2_12`, `QSH.averagedDualMatrix` (`ā_U` of (2.41)) with `expectedDualInvMatrix`,
  `QSH.averagedDualMatrix_bounds` ((2.42)) and `QSH.measurable_dualEnergy`.
- Lemma 2.12: for a bounded open set `U`, a partition of `U`, up to a null set, by pairwise disjoint
  open sets, and given maximizers of (2.9) on `U` and on the pieces (they exist on convex sets); the
  norm `½‖a^{1/2}X‖²_{L̲²(Uⱼ)}` is `⨍_{Uⱼ} ½ X·aX`. The proof is the book's, with the additivity of the
  functional of (2.9) over the partition (`defectTrialEnergy_eq_sum_of_partition`).
- Definition 2.14: the expectation of the matrix `a*⁻¹(U)` is taken entrywise. Its entries are
  measurable (`measurable_coarseDualInvMatrix_apply`): `μ*(U, q)` is the supremum of the functional
  of (2.1) over a countable dense set of gradients of `H¹(U)` in `L²(U)`, independent of the
  coefficient field (`exists_countable_dualEnergy_eq_iSup`), as for the Dirichlet energy (`measurable_dirichletEnergy`), for the
  σ-algebra F of (0.8); the F(U)-measurability, the analogue of (1.29), is not proved here.
  (2.42) comes from `Λ⁻¹ Id ≤ a*⁻¹(U) ≤ Id` and the bounds of the inverse of a symmetric positive
  definite matrix (`inv_mulVec_bounds`).

## Section 2.1: Theorem 2.4, and Section 2.2: Proposition 2.11 (`Ch02/Sec01/CubeCorrectorDefect.lean`, `Ch02/Sec01/Theorem24.lean`, `Ch02/Sec02/Proposition211.lean`)

- Lean: `QSH.theorem_2_4` and `QSH.proposition_2_11`, for `d ≥ 2` and `Λ > 1` (the book: `Λ ≥ 1`;
  `Λ > 1` as in the frozen statements), with the Frobenius norm of matrices as in Lemma 2.7.
- Theorem 2.4, (2.21): `∃ α ∈ (0, ½], ∀ s ∈ (0, d), ∃ C > 0`, for every law satisfying (0.10)–(0.11)
  and every `n`, `OsBound P (X - C 3^{-nα(d-s)}) 1 (C 3^{-ns})` with
  `X = |a(□_n) - ā| + |a*(□_n) - ā|`: the inequality `X ≤ A + O₁(θ)` of (0.42) is `X - A ≤ O₁(θ)`.
  The constants are chosen before the law; `α` does not depend on `s`. `ā` is the matrix of
  Definition 1.2 (`homogenizedMatrix`) and `a*(□_n)` the matrix of Lemma 2.2 (`coarseDualMatrix`),
  whose entries are measurable (`measurable_coarseDualMatrix_apply`).
- Proof of Theorem 2.4: not the book's, which goes through Proposition 2.11 (Section 2.2) and the
  independence of the subcubes. Here: (i) the first-order correctors and the skew parts of the flux
  correctors of Lemma 3.17, Lemma 6.1 and Proposition 6.2 form, almost surely, a family with a
  matrix `D` whose oscillations on `B_r` are at most `C r^{1 - μ}` for `r ≥ R`, with `R ≤ O_s(C_s)`
  and `μ = β(d - s)` (`exists_ae_sublinearCorrectorFamily`, at the exponent `s`); (ii) on
  `{R ≤ √d 3ⁿ}` the trials `p + ∇(η(φ - m))` and `Dp + div(η(σ - c))`, with `η` the inner cutoff of
  `□_n` of relative width `3^{-2μn/3}/4`, give `J(□_n, p, Dp) ≤ K |p|² 3^{-2μn/3}`
  (`dualityDefect_triadicCube_le_of_family`), and the bound of the proof of Lemma 2.7, which holds
  for any matrix (`frobeniusNorm_sub_add_le_of_dualityDefect_le`), gives
  `|a(□_n) - D| + |a*(□_n) - D| ≤ C 3^{-μn/3}`; (iii) with Proposition 1.7 and `ω(n) → 0`, this
  gives `D = ā` (`eq_homogenizedMatrix_of_ae_family`); (iv) on `{R ≥ 3ⁿ}`, `X` is bounded by a
  constant `C(d, Λ)` (`frobeniusNorm_sub_homogenizedMatrix_add_le`) and
  `1{R ≥ 3ⁿ} ≤ (R/3ⁿ)^s = O₁((C_s/3ⁿ)^s)` (`OsBound.indicator_le_of`). The exponent is
  `α = min(β/3, ½)`.
- Proposition 2.11, (2.29): `∃ α ∈ (0, ½], C ≥ 0`, for every law and every `n`, the expectations
  `E[J(□_n, p, ā p)]`, `p ∈ B₁`, are of integrable variables, their set is bounded above and its
  supremum is at most `C 3^{-nα}`. Proof: from Theorem 2.4 at `s = d/2` (the book's order is the
  reverse): by the completed square (2.12), `0 ≤ J(□_n, p, ā p) ≤ ½(1 + C)X` for `p ∈ B₁`
  (`dualityDefect_homogenizedMatrix_le`), and `X ≤ A + O₁(θ)` gives `E[X] ≤ A + 2θ`
  (`OsBound.integral_le_add_two_mul`).

## Section 2.2: Lemma 2.13 (`Ch02/Sec02/AdditivityDefect.lean`, `Ch02/Sec02/MaximizerAverage.lean`, `Ch02/Sec02/DualEnergyLocal.lean`, `Ch02/Sec02/DualEnergyTranslation.lean`, `Ch02/Sec02/SubcubeMeanGradient.lean`, `Ch02/Sec02/SubcubeVariance.lean`, `Ch02/Sec02/Lemma213.lean`)

- Lean: `QSH.lemma_2_13`: `∃ κ > 0, C ≥ 0` (depending only on `d`; the book: `C(d, Λ)`), for every
  `Λ`, every law satisfying (0.10)–(0.11), `p, q ∈ B₁`, `m ∈ ℕ` and every choice of maximizers
  `v(·, □_m, p, q)` of (2.9), the averages `⨍_{□_m} ∇v` are integrable and
  `var[⨍_{□_m} ∇v(·, □_m, p, q)] ≤ C 3^{-mκ} + C Σ_{n=0}^m 3^{-κ(m-n)} τ_n`, with
  `var[X] = E|X - E[X]|²` (`vecVariance`, the expectation taken componentwise) and
  `τ_n = sup_{p, q ∈ B₁} (E[J(□_n, p, q)] - E[J(□_{n+1}, p, q)])` (`additivityDefect`, the supremum
  of a set bounded above; `τ_n ≥ 0`).
- Ingredients: (2.43) for every maximizer, `⨍_U ∇v(·, U, p, q) = a*⁻¹(U) q - p`
  (`IsDefectMaximizer.setAverage_grad_eq`); the `F(U)`-measurability of `μ*(U, q)` and `a*⁻¹(U)`
  (`measurable_dualEnergy_localSigma`), the analogue of (1.29); the translation covariance of
  `μ*`, `J` and `a*⁻¹(U)` (`dualEnergy_preimage_sub`), which gives the stationarity used in Steps 1
  and 2.
- Proof: the book's three steps, at one scale (`m = n + 1` in (2.36), which is what Step 3 uses).
  Step 1: `E|M_{n+1} - 3^{-d} Σ_z M(z + □_n)|² ≤ 2 τ_n` by Jensen's inequality and Lemma 2.12
  (`integral_euclideanSq_meanGradient_succ_sub_le`). Step 2: the covariances of the subcube averages
  are expanded as in the book; each is at most `var[M_n]`, and the two opposite corner subcubes
  give independent averages (`indepFun_meanGradient_corner`). Two departures: (i) `LawHypotheses`
  asks for a separation larger than `1` (the frozen form of (0.11)), and the corner subcubes of `□_1`
  are at distance exactly `1`, so the contraction is used for `n ≥ 1`, with `var[M_1] ≤ 4` as the
  starting point; (ii) the recursion is written for `σ²_n` with
  `var[X + Y] ≤ (1 + t) var[Y] + (1 + t⁻¹) var[X]`, `t = 9^{-d}`
  (`vecVariance_add_le`), in place of the triangle inequality for `σ_n`:
  `σ²_{n+1} ≤ (1 - 9^{-d}) σ²_n + 2(1 + 9^d) τ_n` (`vecVariance_meanGradient_succ_le`), and
  `3^{-κ} = 1 - 9^{-d}`.

## Section 2.2: Lemmas 2.15 and 2.16, and (2.44) (`Ch02/Sec02/MaximizerMeasurability.lean`, `Ch02/Sec02/PartitionMeanGradient.lean`, `Ch02/Sec02/SubcubeDeviation.lean`, `Ch02/Sec02/Lemma215.lean`, `Ch02/Sec02/CubeCaccioppoli.lean`, `Ch02/Sec02/Lemma216.lean`)

- (2.44): `QSH.euclideanSq_inv_averagedDualMatrix_sub_le`, `|ā_{m+r}⁻¹ q - ā_m⁻¹ q|² ≤ 2 Σ_{k=m}^{m+r-1} τ_k`
  for `q ∈ B₁` (the book: `C Σ τ_k`), with `ā_U⁻¹ = E[a*⁻¹(U)]` (`inv_averagedDualMatrix`). The proof is
  the book's, on the partition of `□_{m+r}` into `3^{dr}` translates of `□_m`.
- Lemma 2.15: `QSH.lemma_2_15`: `∃ κ > 0` (depending only on `d`), `∀ Λ, ∃ C ≥ 0`, for every law, `n`,
  `p, q ∈ B₁` and every choice of maximizers `v(·, □_{n+1}, p, q)`, with `ℓ(x) = (ā_n⁻¹ q - p)·x`,
  the centered mean square `⨍_{□_{n+1}} |v - ℓ - (v - ℓ)_{□_{n+1}}|²` (`centeredMeanSq`) is integrable
  and its expectation is at most `C 3^{2n} (3^{-κn} + Σ_{m=0}^n 3^{-κ(n-m)} τ_m)`. The maximizer is
  defined up to a constant, which the book's (2.47) leaves implicit; the centered form is the
  statement for the maximizer with `⨍ (v - ℓ) = 0`. The measurability of this quantity, which the book
  does not discuss, is `measurable_centeredMeanSq_defectMaximizer`: the maximizer is approximated in
  `H¹` by functions chosen measurably from countable families, through Lemma 2.1 (a maximizer of
  `μ*` minus a minimizer of `μ`) and the quadratic responses of `μ*` and `μ`, as in Proposition 1.8.
- Proof of Lemma 2.15: the book's three steps. Corollary 1.14 in Lean also has the scale `n + 1`;
  its term is bounded through `var[M_{n+1}] ≤ 2 var[M_n] + 4 τ_n` (`vecVariance_meanGradient_succ_le_two`)
  and (2.44). Step 2 uses the triangle inequality for squares with the factor `3` and is applied to
  measurable majorants (`scaleMajorant`), so that only the left side of (2.47) needs a measurability
  argument. Step 3 uses `κ = min(κ_{2.13}, ½)` and geometric sums.
- Lemma 2.16: `QSH.lemma_2_16`: `∃ κ > 0` (depending only on `d`), `∀ Λ, ∃ C ≥ 0`, for every law, `n`
  and `p ∈ B₁`, `J(□_n, p, ā_n p)` is integrable and `E[J(□_n, p, ā_n p)] ≤ C (3^{-κn} + Σ τ_m ...)`.
  The proof is the book's, with three changes: since `|ā_n p| ≤ Λ` lies outside `B₁` in general,
  Lemma 2.15 and the definition of `τ_n` are used at `(p/Λ, ā_n p/Λ)` and scaled (`J` and `v` are
  homogeneous, `dualityDefect_smul_smul`, `IsDefectMaximizer.const_mul`); the Caccioppoli inequality is
  proved on the triadic cubes `□_n ⊆ □_{n+1}` (`caccioppoli_triadicCube`, from the Caccioppoli
  inequality of the elliptic regularity library for a quantitative cutoff, with the inner cube cutoff
  of `□_{n+1}`); and (2.55) is proved pointwise with Young's inequality, in place of Hölder's
  inequality in expectation, and with the centre term of Lemma 2.12 on the `3^d` subcubes of
  `□_{n+1}` for `∇v - ∇w` (`dualityDefect_triadicCube_le_center`).

## Section 4.1: Definition 4.2 and Lemma 4.4 (`Ch04/Sec01/Lemma44.lean`)

- Definition 4.2: `QSH.J1Nondegenerate S a Ψ`: `J₁(Ψ, p, 0) ≥ ¼ p·āp` and `J₁(Ψ, 0, q) ≥ ¼ q·ā⁻¹q`
  for all `p, q`, with `ā = S.homogenized`, the homogenized matrix of the homogenization data used in
  Chapter 4.
- Masks: `QSH.J1Mask S a Ψ`: `Ψ ≥ 0`, `Ψ ∈ L¹`, `∫ Ψ = 1`, the corrector columns `Wᵢ = eᵢ + ∇φ_{eᵢ}`
  belong to `L²(Ψ)` and their Gram matrix `M_{ij} = ∫ Ψ Wᵢ·a Wⱼ` is invertible. Given the first-order
  Liouville theorem, this says that `∇A₁` is a `d`-dimensional subspace of `L²(Ψ)`, which is the
  property the book uses for the existence of the maximizer (after (4.9)) and leaves implicit for a
  general mask. It holds almost surely for every heat kernel mask `Φ_{z,r}`
  (`QSH.ae_j1Mask_heatKernel`, from `ae_integrable_heatKernel_mul_euclideanSq_correctorColumn` and
  `ae_J1Heat_eq_half_dot_inv`).
- Lemma 4.4: `QSH.lemma_4_4`: almost surely, for every mask: existence of a maximizer
  (`IsJ1Maximizer`, the objective of (4.8) at `∇v` equals `J₁`), the first variation (4.13) as a
  characterization, uniqueness of `∇v` up to a null set, (4.14), (4.15), (4.16), (4.19), (4.20) and
  (4.21) at every maximizer, linearity of `(p, q) ↦ ∇v` (`IsJ1Maximizer.grad_add`, `grad_smul`),
  `J₁(Ψ, tp, tq) = t² J₁(Ψ, p, q)`, and, when `J₁` is nondegenerate at `Ψ`, (4.17) and (4.18) with
  `C = 16` and `C = 16 Λ`. Every integral in the statement comes with the integrability of its
  integrand. The derivatives are Fréchet derivatives (`HasFDerivAt`) represented by the vectors
  `-∫ Ψ a∇v` and `∫ Ψ ∇v`, taken componentwise.
- Proof: almost surely `A₁` consists of the corrected affine functions (`QSH.ae_j1Structure`, from
  `firstOrderLiouville` and `ae_exists_harmonicA1_correctedAffine`), and the objective at slope `c`
  is `b·c - ½ c·Mc` with the load `bᵢ = ∫ Ψ (-p·a Wᵢ + q·Wᵢ)`. The maximizers are the elements of
  slope `M⁻¹ b` (`J1Structure.isJ1Maximizer_iff`), `J₁ = ½ b·M⁻¹b`, and each item of the lemma is an
  identity for this quadratic, with `b` linear in `(p, q)` (`J1Mask.J1Load_add_smul`). The book's
  proof of (4.13) by the variation `v + tu` is replaced by this computation; (4.17)–(4.18) follow from
  the midpoint identity `½ J₁(p₁, q₁) + ½ J₁(p₂, q₂) - J₁(½(p₁ + p₂), ½(q₁ + q₂)) = ¼ J₁(p₁ - p₂, q₁ - q₂)`
  (`J1Structure.J1_midpoint`), (4.9), `ā ≥ 1` and `|q|² ≤ Λ q·ā⁻¹q`.
- Misprint in (4.15): the book's left inequality `‖∇v‖²_{L²(Ψ)} ≤ J₁(Ψ, p, q)` holds with the factor
  `½`: `½ ‖∇v‖²_{L²(Ψ)} ≤ J₁(Ψ, p, q)`, from (4.14) and `a ≥ 1`. For `a = 1` the elements of `A₁` are
  the affine functions, `J₁(Ψ, p, q) = ½ |q - p|²` and `∇v = q - p`, so the book's form fails for
  `p ≠ q`. The right inequality holds with `C = Λ`: `J₁(Ψ, p, q) ≤ Λ |p|² + |q|²` (`J1_le`).
- Definition 4.5 is not formalized: `𝒴ₛ` is the maximum of the minimal scales of Theorem 3.8 (all
  `k`), Proposition 3.21 and Proposition 4.3, and Theorem 3.8 is proved only for `k = 1`.

## Section 3.2: Lemmas 3.4 and 3.6 (`Ch03/Sec02/Lemma34.lean`)

- Setting: the balls are Euclidean balls centered at the origin, `‖·‖_{L̲²(U)}` is `scalarRms volume U`,
  `(u)_U` is `⨍ x in U, u x`, and "`w ∈ H¹(B_r)` is a weak solution of `-∇·(ā∇w) = 0` in `B_r`" is
  `IsL2HarmonicOn A (ball 0 r) w`. The statements hold for every symmetric matrix `A` with
  `1 ≤ A ≤ Λ` (`HomogenizedMatrixBounds A Λ`), in particular for `ā`, with constants depending only
  on `α, K, d, Λ` (not on `A`).
- (3.24) for `k = 1`: `QSH.exists_affine_scalarRms_ball_le`: for `h` `A`-harmonic in `B_ρ` there is an
  affine `c + q·x` with `‖h - c - q·x‖_{L̲²(B_t)} ≤ C (t/ρ)² ‖h‖_{L̲²(B_ρ)}` for `t < ρ/√Λ` and
  `|q| ≤ C ρ⁻¹ ‖h‖_{L̲²(B_ρ)}`, `C = C(d, Λ)`. The book derives (3.24) from (3.7) and leaves it as
  Exercise 3.5; here it follows from the harmonic expansion on balls (`harmonicExpansionBall`, the
  case `A = 1`) by the change of variables `x = M y` with `M Mᵀ = A`, which maps balls to
  ellipsoids `M B_t` with `B_t ⊆ M B_t ⊆ B_{√Λ t}`; the constant is uniform in `A` because
  `|det M| ≥ 1` and `Σ (M⁻¹)²_{ij} = tr A⁻¹ ≤ d`.
- Lemma 3.6, `k = 1`: `QSH.lemma_3_6_one`, with `affineFlatness u r = inf_ℓ ‖u - ℓ‖_{L̲²(B_r)}` over the
  affine functions (the `ā`-harmonic polynomials of degree at most one), for `α > 0` (the book has
  `α ∈ [0, 1]`; for `α = 0` and `K ≥ 1` the inequality is immediate from
  `inf_ℓ ‖u - ℓ‖_{L̲²(B_{θr})} ≤ θ^{-d/2} ‖u - (u)_{B_r}‖_{L̲²(B_r)}`, and the book's choice
  `θ = (C_k 2^{2+d/2})^{-2/α}` needs `α > 0`). The proof is the book's, through the improvement step
  for a given affine function (`QSH.exists_affine_improvement`), with `θ ≤ (16 (C + 1) 2^{d/2})^{-2/α}`
  and `θ < 1/(2√Λ)`. The cases `k ≥ 2` are not formalized (they need (3.7) for `k ≥ 2`).
- Lemma 3.4: `QSH.lemma_3_4`: `α > 0` (the bound `α ≤ 1` of the book is not used), `K ≥ 1`, `X ≥ 1`,
  `R ≥ 2X`, `u ∈ L²(B_R)` with the approximation (3.21) for `r ∈ [X, R/2]`; then (3.22) for every
  `r ∈ [X, R]`. The proof is the book's improvement-of-flatness iteration along the radii
  `r_j = θ^j R/2`, with two changes: the maximal function `M = sup_{r ∈ [R₀, R]} r⁻¹ ‖u - (u)_{B_r}‖`
  is replaced by the maximum over the radii `r_j ≥ R₀` (the other radii are compared with the
  neighbouring `r_j` at the end), and the affine minimizers `p_j` of `E₁(r_j)` are replaced by the
  affine functions produced by the improvement step, whose slopes are controlled by the same
  step; the bookkeeping is the discrete lemma `QSH.discrete_flatness_iteration` and the geometric
  bound `QSH.sum_rpow_neg_le`. Theorem 3.3 is not formalized: it needs Proposition 3.2, which uses
  Theorem 2.18 (Section 2.3, not formalized).

## Section 3.4: Lemma 3.23 (`Ch03/Sec04/Lemma323.lean`)

- Lemma 3.23: `QSH.lemma_3_23`, for `d ≥ 2` and `Λ > 1`, with `c = 4π²` and `C` chosen before the
  law, for the homogenization data given by Proposition 3.21 (`uniformGaussianCorrectorRate`).
  The gradient `∇φ_e` is `G e - e` for the corrected field `G e = ∑ᵢ eᵢ (eᵢ + ∇φ_{eᵢ})`
  (`correctedField`). The statement includes the almost sure integrability in `x` of the three
  densities against `Φ_{x,r}` and the integrability in the coefficient field of their averages.
- Proof: not the book's Poincaré inequality on the torus ((3.109) and Exercise 3.24), but the bound
  of the periodized heat kernel by Poisson summation (`abs_tsum_heatKernel_add_latticeShift_sub_one_le`),
  whose error `(1 + ∑_{k ≠ 0} e^{-4π² r² k²})^d - 1` is at most `C exp(-4π² r²)` for `r ≥ 1`
  (`periodizationError_le_exp`); the expectations of the Gaussian averages of the stationary
  densities are within this error of their cell means (`expectedAveragesBounds_of_scales`, the
  bound of the expectations (1) at a general rate `exp(-h(r))`, of which the rate `r^{-β}` of
  `expectedAveragesEstimateAt_of_scales` is the case `h(r) = β log r`), and the cell means are
  identified by Proposition 3.21 as in the expectations (1) above.

## Section 3.4: Definitions 3.14 and 3.15 (`Ch03/Sec04/StationaryFields.lean`)

- Definition 3.14: `QSH.IsStationaryRandomField P F` for `F : CoefficientField d Λ → Vec d → S`
  (the book's `F(x, a)` is `F a x`), with the joint measurability and, for every `z ∈ ℤ^d`,
  `F(x + z, a) = F(x, T_z a)` for almost every `x`, `P`-almost surely; `T_z` is `translate`.
- Definition 3.15: `QSH.IsStationaryPotentialField P F`; `F(·, a)` is the gradient of a function in
  `H¹_loc(ℝ^d)` in the sense of the library: a weak gradient on `ℝ^d`, the function and the field
  being square integrable on every ball. The corrector gradients belong to `L²_pot`
  (`Corrector.isStationaryPotentialField_grad`).

## Section 5.1: Lemma 5.2 (`Ch05/Sec01/Lemma52.lean`)

- Lemma 5.2 (1): `QSH.lemma_5_2_tendstoInDistribution`: for `Vec d`-valued random variables `Xₙ` on
  probability spaces `(Ωₙ, Pₙ)` and `X` on `(Ω', P')`, almost everywhere measurable, if
  `λ·Xₙ → λ·X` in distribution (`TendstoInDistribution`) for every `λ`, then `Xₙ → X` in
  distribution.
- Lemma 5.2 (2): `QSH.lemma_5_2_map_eq`: if the laws of `λ·X₁` and `λ·X` agree for every `λ`, then
  the laws of `X₁` and `X` agree (`P₁.map X₁ = P.map X`).
- Proof: the book refers to the Fourier transform. The vectors are carried to
  `EuclideanSpace ℝ (Fin d)` (`⟪x, t⟫ = t·x`, `inner_euclideanSpace_equiv_symm`); (1) is Lévy's
  continuity theorem (`TendstoInDistribution.of_tendsto_charFun`) with
  `charFun_map_eq_charFun_map_inner_one`, as in Mathlib's Cramér–Wold theorem
  `tendstoInDistribution_iff_tendstoInDistribution_inner` (one probability space there), and (2) is
  the uniqueness of characteristic functions (`Measure.ext_of_charFun`).

## Section 5.1: Lemma 5.10 (`Ch05/Sec01/Lemma510.lean`)

- Lemma 5.10: `QSH.lemma_5_10`: for `f : Vec d → ℝ` smooth (`ContDiff ℝ ⊤`) with compact support and
  `∫ f = 0` there is a smooth compactly supported `F : Vec d → Vec d` with
  `∑ᵢ ∂ᵢ Fᵢ = f` (`coordinateDerivative`).
- Proof: the book's construction, with `h` the normalized smooth bump of `ContDiffBump` supported
  in `(-R, R)`, where `R ≥ 1` bounds the support of `f` in the sup norm (in place of the reduction
  to `supp f ⊆ B₁`), `g₀ = f`, `g_{k+1}(x) = h(x_k) ∫ g_k(x + s e_k) ds` (`bumpLineSeq`; this is the
  book's `g_{k+1}` after the translation `y_k = x_k + s`) and
  `F_k(x) = ∫_{-∞}^0 (g_k - g_{k+1})(x + s e_k) ds`. The smoothness of the `g_k` and the `F_k` is
  `QSH.contDiff_setIntegral_add_smul` (differentiation under the integral, by induction on the
  order); `∂_k F_k = g_k - g_{k+1}` is the fundamental theorem of calculus on `(-∞, 0]`
  (`fderiv_setIntegral_Iic_apply`); `F_k` has compact support because
  `∫ g_{k+1}(x + s e_k) ds = ∫ g_k(x + s e_k) ds` (`integral_bumpLineSeq_succ`). The book observes
  `g_d = h(x₁)⋯h(x_d) ∫ f = 0`; here `g_d = c ∏ h(x_j)` (`bumpLineSeq_eq_prefix_mul`,
  `eq_of_invariant`) and `c = ∫ g_d = ∫ f - ∫ ∇·F = 0`.

## Section 5.4: the notation (5.79) and Lemmas 5.27, 5.28 and 5.30 (`Ch05/Sec04/NearGaussian.lean`)

- (5.79), `X = N(σ², λ₁, c)`: `QSH.IsNearGaussian P X v λ₁ c` with `v = σ²`; for every
  `λ ∈ (-λ₁, λ₁)` the integrability of `exp(λ X)` is part of the definition.
- Lemma 5.27: `QSH.lemma_5_27`, for a measurable `X` with `exp(2|X|)` integrable; the constant
  is that of Lemma A.8 (`exists_abs_log_integral_exp_sub_le`), since `C|λ|³ ≤ C λ₁ λ²` for
  `|λ| < λ₁`.
- Lemma 5.28: `QSH.lemma_5_28`, for `X : Fin k → Ω → ℝ` measurable and independent in the sense
  of `iIndepFun`; the conditions `σ, λ₁, c ≥ 0` are not needed. The proof is the book's, from the
  additivity of the logarithm of the moment generating function (`iIndepFun.cgf_sum`).
- Lemma 5.30: `QSH.lemma_5_30`, for `s ∈ (1, 2]` (the book fixes `s ∈ (1, 2)` in (5.82)) and every
  real `λ₂`; the hypotheses are `σ ∈ ℝ`, `c ≥ 0`, `λ₁ ≤ λ₂`, `θ ∈ (0, 1/2]`, `X₁` measurable with
  `X₁ = N(σ², λ₁, c)`, and `X₂` centered with `X₂ ≤ O_s(θ)` and `-X₂ ≤ O_s(θ)` (the notation
  `X₂ = O_s(θ)` after (A.2)); `X₁` need not be centered. The constant is `C = 4 + K C_A²` with
  `K = max(1, (C_A λ₂)^{s/(s-1) - 2})` and `C_A` the constant of Lemma A.9. The proof is the book's:
  Hölder's inequality (5.100)–(5.101) with `ρ = (1 - θ^{1/2})⁻¹` and `ρ' = θ^{-1/2}`
  (`log_integral_exp_add_le`), and Lemma A.9 for `X₂`, which gives
  `log E[exp(ρ' λ X₂)] ≤ K C_A² θ λ²` for `|λ| ≤ λ₂` (`CenteredOsBound.log_integral_exp_le`).

## Appendix E: Lemma E.6 (`AppE/ReverseHolderImprovement.lean`)

- `QSH.lemma_E_6`: for `0 < p < q < r ≤ ∞` (exponents in `ℝ≥0∞`) and `A, a > 0` there is
  `C : ℝ≥0`, chosen before the dimension, the measure and the function, such that for every measure
  `μ` on `Vec n`, Borel `U`, Borel `S σ ⊆ U` (`σ ∈ (0, 1]`) and `f` in `L^p(U; μ) ∩ L^r(U; μ)` with
  (E.18) for all `1/2 ≤ σ' < σ ≤ 1`, `‖f‖_{L^r(S (2/3); μ)} ≤ C ‖f‖_{L^p(U; μ)}`. The conclusion is
  on `⅔U`, as printed (the display fraction is `2/3` in both the book and arXiv v2); Lemma C.6 gives
  the bound at `1/2` and is applied to `t ↦ ρ((2t + 1)/3)`, which carries `[1/2, 1)` onto
  `[2/3, 1)`.
- `QSH.reverseHolder_improvement` is the same statement on any measurable space; it does not use the
  measurability of `U` and of the sets `S σ`.
- Proof: the book's. Hölder's inequality `‖f‖_q ≤ ‖f‖_p^h ‖f‖_r^{1-h}` for
  `1/q = h/p + (1 - h)/r` is `eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow` (Mathlib's generalized
  Hölder inequality for `‖f‖^h · ‖f‖^{1-h}`), and Young's inequality is the weighted
  arithmetic-geometric mean inequality (`mul_rpow_mul_rpow_le_half_add`), with the constant
  `h (2(1 - h))^{(1-h)/h} A^{1/h}` and exponent `a/h`.

## Section 10.1: Definition 10.2 (`Ch10/Sec01/VariationalRepresentation.lean`)

- Definition 10.2: `QSH.VariationallyRepresents F φ`, with the convexity of `(p, q) ↦ F(p, q)` on
  `ℝ^d × ℝ^d`.
- The quadratic form (10.7) is `QSH.linearRepresentative a`, for a constant matrix `a` (the book's
  `a(x)` at a fixed `x`), with `s` and `m` the symmetric and antisymmetric parts of `a`
  (`symmetricPart`, `antisymmetricPart`). For `a` with `ξ·aξ > 0` for `ξ ≠ 0`, the identity
  `A(p, q) - p·q = ½ (a p - q)·s⁻¹(a p - q)` (`linearRepresentative_sub_dot`, the computation
  before (10.7)) gives (10.10) and (10.11), and with the convexity of nonnegative quadratic forms
  (`convexOn_dotProduct_mulVec`), `variationallyRepresents_linearRepresentative`.

## Appendix B: Definition B.2, Theorems B.8–B.10 and Proposition B.11 for first-order spaces (`AppB/SobolevSpaces.lean`, `AppB/TheoremB8.lean`, `AppB/TheoremB9.lean`, `AppB/PropositionB11.lean`, `AppB/ConvexMorreySmooth.lean`, `AppB/ConvexMorrey.lean`, `AppB/TheoremB10.lean`)

- Definition B.2, the case `k = 1`: `QSH.IsW1p U p u g` (`u` and `g` in `L^p(U)`, `∇u = g` weakly in
  `U` in the sense of `HasWeakGradient`), the norm (B.1) `QSH.w1pNorm U p u g =
  ‖u‖_{L^p(U)} + ∑ᵢ ‖gᵢ‖_{L^p(U)}` with values in `[0, ∞]`, and `QSH.IsW01p U p u g`, the closure of
  the test functions `IsSpatialTest U` for this norm. The spaces with `k ≥ 2`, the rescaled norm
  `‖v‖_{W̲^{k,p}(U)}` for `|U| < ∞` and `W^{k,p}_loc(U)` are not defined.
- Norms: the volume-normalized norm `‖f‖_{L̲^q(U)}` of the book is `PDE.eLpMeanNormOn U q f` of the
  elliptic regularity library (the `L^q` norm for the normalized restricted volume); `|∇v|` is the
  Euclidean norm. In (B.7) and (B.8) the norms of `v - w` and `∇v` are the normalized ones: this
  is the reading in which both sides scale in the same way, as the factor `r^k` requires. The balls
  `B_r(z)` of Theorems B.9 and B.10 have any center.
- Theorem B.8: `QSH.theorem_B_8_one`, the case `k = 1`, with `C(p, d)`; the range `p ∈ [1, d)` is
  empty unless `d ≥ 2`. Proof: the Gagliardo–Nirenberg–Sobolev inequality of the elliptic regularity
  library, `PDE.exists_sobolev_constant`, and `|∇v| ≤ ∑ᵢ |∂ᵢ v|`.
- Theorem B.9: `QSH.theorem_B_9_one`, the case `k = 1`: the infimum is over `w ∈ ℝ = P₀`; the
  second conjunct is the statement for `W^{1,p}_0(B_r(z))` with `w = 0`. Proof: the Sobolev–Poincaré
  inequality on bounded convex domains `PDE.exists_convexSobolevPoincare_constant` with
  `w = (v)_{B_r(z)}`, and the zero-boundary inequality of `PDE.exists_sobolev_constant` rescaled
  with `|B_r(z)| ≤ (2r)^d`.
- Theorem B.10: `QSH.theorem_B_10_one`, the case `k = 1`, for `d ≥ 1` (the book's standing
  assumption is `d ≥ 2`; for `d = 0` the zero-boundary statement fails, since every function on the
  point `ℝ⁰` is a limit of test functions) and `p ∈ (d, ∞]` as an element of `[0, ∞]`. The three
  conjuncts are (B.8), (B.8) with `w = 0` on `W^{1,p}_0(B_r(z))`, and (B.9). Proof: Morrey's
  inequality for `C¹` functions on bounded convex sets (Gilbarg–Trudinger, Lemma 7.16), copied
  with its Apache 2.0 header from `SuperdiffusionCLT/Section7/Prereq/Morrey.lean` of
  scottnarmstrong/SuperdiffusionCLT (`QSH.ConvexMorrey`), passed to `W^{1,p}` on bounded convex
  domains with the smooth approximants `PDE.W1pFunction.convexApproxSmoothW1p`
  (`QSH.ae_abs_sub_integralAverage_le_of_convex`); for `W^{1,p}_0(B_r(z))`, each test function is
  bounded by its oscillation on `B_{2r}(z)` and the bound passes to the limit; (B.9) covers `ℝ^d`
  by the balls `B_{√d}(z)`, `z ∈ ℤ^d`. The exponent `p = ∞` is reduced to `p = d + 1`.
- Proposition B.11: `QSH.proposition_B_11_convex`, the case `α = 1` for a bounded open convex `U`
  (the book: a bounded Lipschitz domain, and for `α < 1` a cube), with unnormalized norms and
  `C(p, U, d)`. Proof: `PDE.exists_convexSobolevPoincare_constant` and the passage between
  normalized and unnormalized norms. Bounded Lipschitz domains (Definition B.1) and the fractional
  case (Definition B.3) are not done.

## Section 1.4: Lemma 1.16 and Proposition 1.15 (`Ch01/Sec04/`, `AppB/NegativeSobolevTwo.lean`)

- Definition B.4 for the order `2`, normalized as in (0.29): `QSH.negativeSobolevTwoNorm q U f` is the
  supremum of `|⨍_U f ψ|` over the test functions `ψ` of `U` with `sobolevTwoTestNorm q' U ψ ≤ 1`,
  where `q' = q.conjExponent` is the Hölder conjugate in `[1, ∞]` (so `q = 1` has `q' = ∞`) and
  `sobolevTwoTestNorm` is the normalized norm (B.1) of order `2`, the multi-indices `e_i + e_j` of
  order two written as the pairs `i ≤ j`. The conventions are those of `negativeSobolevOneNorm`
  (Appendix C); `vectorNegativeSobolevOneNorm` is the sum of the norms of the components, and
  `IsL2Sol U g` is `g ∈ L²_sol(U)` of (0.34).
- Lemma 1.16: `QSH.lemma_1_16`, for `d ≥ 2` (the book's standing assumption) and a bounded open
  convex `U`, with the normalized norms and `C(U, q, d)`; for a fixed `U` they are comparable to the
  unnormalized norms of the statement. The book does not specify `U`; its proof uses the
  Sobolev–Poincaré inequality on `U` (Proposition B.11), proved here on convex domains.
  `QSH.lemma_1_16_quantitative` gives `C = C(q, d, κ) D` on domains of diameter at most `D` with
  `|U| ≥ κ D^d`, the form used on `□_m`. Proof: the book's, with Morrey's inequality for the test
  functions (Theorem B.10), the Sobolev–Poincaré inequality (Proposition B.11), the extension of the
  `H^{-1}` pairing to `H¹₀(U)` (Appendix C) and `φ u ∈ H¹₀(U)` (elliptic regularity library).
- Proposition 1.15: `QSH.proposition_1_15`, for `d ≥ 2`, with the right side
  `C (3^{-2m} + E(m))^{1/2}`. The book prints `C 3^{-2m} + C E(m)` in (1.53). The proof it indicates
  (Proposition 1.10, Lemma 1.13 and Lemma 1.16) gives the square root of that quantity: (1.40)
  bounds `‖a∇v - āp‖_{Ĥ̲^{-1}(□_m)}` and `‖∇v - p‖_{Ĥ̲^{-1}(□_m)}` by `3^m (C 3^{-2m} + C E(m))^{1/2}`,
  (1.45) bounds `‖v - ℓ_p‖_{L̲²(□_m)}` by the latter, and Lemma 1.16 on `□_m` has the constant `C 3^m`
  and is linear in these norms. Theorem 1.17 uses `E′(ε)^{1/2}`, in line with this form. The
  minimizer is `v = ℓ_p + u` with gradient `p + g`, as in Proposition 1.10.

## Section 2.3: Theorem 2.17 (`Ch02/Sec03/HatNormAlgebra.lean`, `Ch02/Sec03/HomogenizedInverse.lean`, `Ch02/Sec03/MaximizerHatBound.lean`, `Ch02/Sec03/CoarseDeviationOs.lean`, `Ch02/Sec03/Theorem217.lean`)

- Lean: `QSH.theorem_2_17`, for `d ≥ 2` and `Λ > 1`, the hypotheses of Theorem 2.4 on which the
  proof rests. `∃ α ∈ (0, 1/d], ∀ s ∈ (0, d), ∃ C > 0`, for every law satisfying (0.10)–(0.11) and
  every `m`, there is a random variable `Y` with `OsBound P Y 1 (C 3^{m - ms})` such that, for every
  coefficient field, `p, q ∈ B₁` and every maximizer `v` of (2.9) on `□_m` (unique up to the
  gradient, `IsDefectMaximizer.ae_eq`) of gradient `g`, the left side of (2.66) is at most
  `C 3^{m - mα(d-s)} + Y`. This is (2.66) with the convention `X ≤ A + O₁(θ)` of (0.42), with one
  `Y` for all `p, q` and all maximizers, so the measurability of the left side is not needed. The
  norms are the normalized `Ĥ̲⁻¹(□_m)` norms of (0.31) (`vectorHatNegativeSobolevNorm`, the sum
  over the components), with values in `[0, ∞]`; `ā⁻¹` is the matrix inverse, and `ā ā⁻¹ q = q`
  by the lower bound `|e|² ≤ e · āe` of (1.25) (`homogenizedMatrix_mulVec_inv_mulVec`).
- Proof: the book's. (2.67): by Lemma 2.1, `-v(·, □_m, e, 0)` is the minimizer of `μ(□_m, e)`, so
  Proposition 1.10 bounds its gradient and flux; by (2.18) the maximizer is
  `v(·, p, 0) + v(·, ā⁻¹q, q) - v(·, ā⁻¹q, 0)` up to its gradient; the last terms are bounded by
  `‖f‖_{Ĥ̲⁻¹(□_m)} ≤ 3^m ‖f‖_{L̲²(□_m)}`, (2.19) and the completed square (2.12)
  (`dualityDefect_homogenizedMatrix_le`). This gives `vectorHat_defectMaximizer_le`, a bound by
  `K₁ (1 + 3^m E(m)^{1/2}) + K₂ 3^m (|a(□_m) - ā| + |a*(□_m) - ā|)^{1/2}` without squares.
  (2.68): Theorem 2.4 with `(s + d)/2` in place of `s`, stationarity for the subcubes, Lemma A.3
  and the triangle inequality for `O_{2d}`, and Young's inequality (2.23) with
  `ρ = 3^{-mβ(d-s)}`, `β = 1/(2(2d-1))` (`sqrt_coarseDeviation_le_os`). The book passes to `O_d`
  by Lemma A.3; `O_{2d}` is used here so that Lemma A.3, stated for `s < s'`, applies also for
  `d = 2`, and the square in (2.69) is not needed since `E(m)^{1/2}` is the weighted sum itself. The term
  `J(□_m, ā⁻¹q, q)^{1/2}` is bounded by (2.65), `X^{1/2} ≤ 2c^{1/2} + c^{-1/2}(X - c)₊`
  (`sqrt_le_two_mul_sqrt_add_os`). The exponent is `α = min(α₀/4, β)`, `α₀` that of Theorem 2.4.
