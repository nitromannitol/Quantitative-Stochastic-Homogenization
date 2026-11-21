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
- Lemma A.7 is not formalized.

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

## Proposition 4.3, Proposition 4.10 and Theorem 4.6 (ii) (`Ch04/Sec01/`, `Ch04/Sec02/`, `Ch04/Sec03/`)

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
- **Remark 4.18, (4.70), and Theorem 4.6 (ii).** `ExpectationEstimates` states (4.70);
  `expectationJ1Estimate_of_trialGap` proves it from the trial, with the mean bound
  `OsBound.integral_le_factorial_mul` for `O_t` variables with `t < 1`.
- **(5.58).** `theorem46_expectation_and_558`, `estimate558` and `estimate558_of_trialGap`:
  `|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ O_s(C r^{-d/2})` for every `s ∈ (0, 2)`, with
  Theorem 4.6 (ii), from Theorem 4.6 (iii) (`additiveStructure_J1`) and (4.70); for `s < 1` the
  triangle inequality is replaced by `X + Y ≤ 2 max(X, Y)`.
