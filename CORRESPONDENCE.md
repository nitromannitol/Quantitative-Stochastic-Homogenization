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
- **Lemma A.4.** Only the case `s ≥ 1` with `C_s = 1` for finite sums is formalized
  (`osBound_finset_sum`); the general measure and the case `s < 1` are not.
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
- **Lemma A.10.** `centeredOsBound_integral` is the case of a constant scale `θ` on a finite measure
  `μ ≠ 0`, with the scale `μ(E) θ = ∫ θ dμ` and `C = 1`, for a jointly measurable family; the book
  allows a measurable scale `θ(x)` and an arbitrary measure. `exists_centeredOsBound_integral_sub`
  combines it with Lemma A.9 for the centered average of a bounded family with
  `|V(x)| ≤ O_s(θ)`.
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
- Lemmas A.5, A.7 and A.8 are not formalized.

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
- Appendix A for almost surely measurable random variables (`AppA/AlmostSureOsBound.lean`):
  `AEOsBound P X s θ` holds if and only if `X` agrees almost surely with a measurable `Y ≤ O_s(θ)`.

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
