# Roadmap

**Current priority.** The frozen statements needed by [einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean), listed in [FROZEN.md](FROZEN.md): seven statements, E1–E7. All seven are proved with no hypothesis (`Ch05/Sec04/FrozenProved.lean`); their rows in FROZEN.md are in the state `proved` and point to these theorems, since a proof after the markers of a frozen file would close an import cycle, as explained in [README.md](README.md). The full-book list follows below.

## Numbering and status

The numbered results below are those of the Springer edition of the book (Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, Grundlehren der mathematischen Wissenschaften 352, 2019), read from its text: definitions, theorems, propositions, lemmas and corollaries, by chapter and section. The counter of a chapter is shared with remarks, examples and exercises, which are not listed, so the numbers are not consecutive. The numbering differs from that of the arXiv version (arXiv:1705.05300v2), in which exercises have their own counter: for instance Proposition 5.14 here is Proposition 5.9 there. The appendices have no sections and one module each. In Appendix A, A.2 is a remark and A.6 an exercise.

A name in the second column is the one given in the heading of the result in the book. The statuses are `not started`, `in progress` (with the note `moving from einstein-relation-lean` when the work is being moved from that repository), `statement frozen` (the statement is registered in [FROZEN.md](FROZEN.md)), `proved` (for a definition: `defined`), with a pointer to [CORRESPONDENCE.md](CORRESPONDENCE.md) when the Lean statement differs from the book.

The book has **226 numbered results**: 38 theorems, 37 propositions, 124 lemmas, 6 corollaries and 21 definitions. 53 of them are proved or defined, in Appendix A, Section 1.2 (Lemma 1.1), Section 1.3 (Definition 1.2 and Propositions 1.7–1.8), Section 1.4 (Propositions 1.10 and 1.12, Lemma 1.13 and Corollary 1.14), Section 2.1 (Lemmas 2.1, 2.2 and 2.7 and Theorem 2.4), Section 2.2 (Proposition 2.11, Lemmas 2.12, 2.13, 2.15 and 2.16 and Definition 2.14), Section 3.2 (Lemma 3.4), Section 3.4 (Lemma 3.16 and Proposition 3.21), the opening of Chapter 4 (Theorem 4.1), Section 4.1 (Definition 4.2, Proposition 4.3 and Lemma 4.4), Section 4.2 (Definitions 4.7–4.9 and Propositions 4.10–4.12), Section 4.3 (Lemma 4.13), Section 4.4 (Lemma 4.21), Section 5.1 (Lemma 5.2), Section 5.3 (Lemma 5.24), Section 5.4 (Lemma 5.29), Appendix C (Lemmas C.2 and C.4–C.6 and Corollary C.3) and Appendix D (Lemmas D.3 and D.4), and 13 are in progress.

## Moving from einstein-relation-lean

- Moved: the `O_s` calculus of Appendix A (all its numbered results, Lemmas A.1, A.3–A.5 and A.7–A.12, proved), Definitions 4.7–4.9, Theorem 4.6, parts (i), (iii) and (iv), conditional on Propositions 4.10–4.12, and the semigroup property of the heat kernel (Chapter 4, opening).
- Moved, in the form used as the sublinear corrector input: Lemma 3.17, Lemma 6.1 and Proposition 6.2 (`sublinearCorrectors`), with the classification of `A₁` from the first-order Liouville theorem (`firstOrderLiouville`, proved). Proved inside einstein-relation-lean and to move here later: Proposition 5.14 (the existence of white noise).

## Summary by chapter

| Chapter | Title | Numbered results | Proved or defined | In progress |
| --- | --- | --- | --- | --- |
| 1 | Introduction and Qualitative Theory | 12 | 8 | 1 |
| 2 | Convergence of the Subadditive Quantities | 12 | 10 | 0 |
| 3 | Regularity on Large Scales | 23 | 3 | 6 |
| 4 | Quantitative Description of First-Order Correctors | 25 | 12 | 2 |
| 5 | Scaling Limits of First-Order Correctors | 19 | 3 | 0 |
| 6 | Quantitative Two-Scale Expansions | 13 | 0 | 2 |
| 7 | Calderón–Zygmund Gradient L^p Estimates | 10 | 0 | 0 |
| 8 | Estimates for Parabolic Problems | 19 | 0 | 0 |
| 9 | Decay of the Parabolic Semigroup | 18 | 0 | 0 |
| 10 | Linear Equations with Nonsymmetric Coefficients | 16 | 0 | 0 |
| 11 | Nonlinear Equations | 12 | 0 | 0 |
| Appendix A | The O_s Notation | 10 | 10 | 0 |
| Appendix B | Function Spaces and Elliptic Equations on Lipschitz Domains | 16 | 0 | 0 |
| Appendix C | The Meyers L^{2+δ} Estimate | 9 | 5 | 1 |
| Appendix D | Sobolev Norms and Heat Flow | 5 | 2 | 1 |
| Appendix E | Parabolic Green Functions | 7 | 0 | 0 |
| | **Total** | **226** | **49** | **12** |

## Front matter

The chapters "Assumptions and Examples" and "Notation" state no numbered result. Modules: `Front/Assumptions.lean` and `Front/Notation.lean`. Status: not started.

## Chapter 1: Introduction and Qualitative Theory

### 1.1 A Brief and Informal Introduction to Homogenization, module `Ch01/Sec01BriefIntroduction.lean`

No numbered result.

### 1.2 The Subadditive Quantity μ and Its Basic Properties, module `Ch01/Sec02SubadditiveQuantity.lean` (proofs in `Ch01/Sec02/DirichletEnergyBounds.lean`, `Ch01/Sec02/DirichletEnergyMeasurability.lean`, `Ch01/Sec02/DirichletEnergyTests.lean`, `Ch01/Sec02/TestPoincare.lean`, `Ch01/Sec02/DirichletMinimizer.lean` and `Ch01/Sec02/Lemma11.lean`)

| Result | Name | Status |
| --- | --- | --- |
| Lemma 1.1 | Basic properties of μ | proved for bounded sets of positive measure (`lemma_1_1`: the matrix `a(U)` of (1.9)–(1.10), `coarseMatrix`; the subadditivity (1.11) for partitions by disjoint open sets; the existence, uniqueness and first variation (1.12) of the minimizer; the quadratic response (1.13)); see CORRESPONDENCE.md |

### 1.3 Convergence of the Subadditive Quantity, module `Ch01/Sec03ConvergenceOfSubadditiveQuantity.lean` (proofs in `Ch01/Sec03/ParallelogramQuadratic.lean`, `Ch01/Sec03/SubadditiveLimit.lean`, `Ch01/Sec03/DirichletEnergyCorrectorBounds.lean`, `Ch01/Sec03/LocalMeasurability.lean`, `Ch01/Sec03/TriadicPartition.lean`, `Ch01/Sec03/Proposition17.lean`, `Ch01/Sec03/MinimizerOscillation.lean` and `Ch01/Sec03/Proposition18.lean`)

| Result | Name | Status |
| --- | --- | --- |
| Definition 1.2 | Homogenized coefficients | defined (the limit (1.22) exists and equals `½ e·āe` with `ā` symmetric, `exists_homogenizedMatrix`; the bounds (1.25) for homogenization data, `HomogenizationData.homogenizedMatrixBounds`; see CORRESPONDENCE.md) |
| Proposition 1.7 |  | proved (`proposition_1_7`, for the Frobenius norm of matrices, with `C(d, Λ)` chosen before the law; `homogenizedMatrix`, and the modulus `ω` of (1.27), `omegaModulus`; the measurability (1.29), `measurable_dirichletEnergy_localSigma`); see CORRESPONDENCE.md |
| Proposition 1.8 |  | proved (`proposition_1_8`, for every choice of the minimizers, with `C(d, Λ)` chosen before the law; the estimate (1.35), `minimizer_setAverage_sq_le`); see CORRESPONDENCE.md |

### 1.4 Weak Convergence of Gradients and Fluxes, module `Ch01/Sec04WeakConvergenceOfGradientsAndFluxes.lean` (proofs in `Ch01/Sec04/Proposition111.lean`, `Ch01/Sec04/HatNegativeSobolev.lean`, `Ch01/Sec04/CubePoincare.lean`, `Ch01/Sec04/TriadicChildren.lean`, `Ch01/Sec04/Proposition112.lean`, `Ch01/Sec04/FluxAverage.lean`, `Ch01/Sec04/SubcubeAverages.lean`, `Ch01/Sec04/Proposition110.lean`, `Ch01/Sec04/Lemma113.lean` and `Ch01/Sec04/Corollary114.lean`)

| Result | Name | Status |
| --- | --- | --- |
| Proposition 1.10 |  | proved (`proposition_1_10`, for every minimizer `v(·, □_m, p) = ℓ_p + u` with gradient `p + g`, with `C(d, Λ)` chosen before the law, `E(m)` of (1.39) for the Frobenius norm and the `Ĥ⁻¹` norm of a vector field the sum of the norms of its components; (1.49), `IsDirichletMinimizer.setAverage_flux_eq`); see CORRESPONDENCE.md |
| Proposition 1.11 |  | in progress: proved for `d ≠ 4` (`proposition_1_11_of_ne_four`, (1.41)); in every dimension, the bound `C Σ_{n ≤ m} 3^{n-m}(3^{-dn/4} + ω(⌈n/2⌉))` of the proof (`proposition_1_11`) and the limit `E[E(m)] → 0` (`tendsto_integral_coarseDeviation`), with `E(m)` of (1.39), `coarseDeviation`; (1.41) for `d = 4` is not proved, since the book's bound of the geometric sum does not hold there, see CORRESPONDENCE.md |
| Proposition 1.12 | Multiscale Poincaré inequality | proved (`proposition_1_12`, with the normalized `Ĥ⁻¹(□_m)` norm of (0.31), `hatNegativeSobolevNorm`, and the normalized `H¹` norm of (0.26), `h1Norm`; the Poincaré inequality (1.43) on cubes, `setIntegral_sq_sub_setAverage_le`); see CORRESPONDENCE.md |
| Lemma 1.13 |  | proved (`lemma_1_13`, (1.44) for `H¹(□_m)` and (1.45) for `H¹₀(□_m)`, both with the `Ĥ⁻¹(□_m)` norm of the gradient); see CORRESPONDENCE.md |
| Corollary 1.14 |  | proved (`corollary_1_14`; in the conventions of the coarse-graining library, `exists_originCube_multiscalePoincare`) |
| Proposition 1.15 |  | not started |
| Lemma 1.16 | Div-curl lemma | not started |

### 1.5 Homogenization of the Dirichlet Problem, module `Ch01/Sec05HomogenizationOfDirichletProblem.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 1.17 |  | not started |

## Chapter 2: Convergence of the Subadditive Quantities

### 2.1 The Dual Subadditive Quantity μ*, module `Ch02/Sec01DualSubadditiveQuantity.lean` (proofs in `Ch02/Sec01/DualEnergy.lean`, `Ch02/Sec01/DualMaximizer.lean`, `Ch02/Sec01/Lemma21.lean`, `Ch02/Sec01/DefectMaximizer.lean`, `Ch02/Sec01/Lemma22.lean` and `Ch02/Sec01/Lemma27.lean`; Theorem 2.4 in `Ch02/Sec01/DualEnergyMeasurability.lean`, `Ch02/Sec01/DefectTrials.lean`, `Ch02/Sec01/SkewCutoff.lean`, `Ch02/Sec01/CorrectorTrials.lean`, `Ch02/Sec01/CubeCorrectorDefect.lean` and `Ch02/Sec01/Theorem24.lean`)

| Result | Name | Status |
| --- | --- | --- |
| Lemma 2.1 |  | proved for bounded open convex sets (`lemma_2_1`: (2.9) with `dualityDefect`, the quantity `J` of (2.6), and `dualEnergy`, the quantity `μ*` of (2.1); the maximizer of (2.1) exists, `exists_isDualMaximizer`, and the maximizer of (2.9) is its difference with the minimizer of (1.7)); see CORRESPONDENCE.md |
| Lemma 2.2 | Basic properties of J | proved for bounded open convex sets (`lemma_2_2`: the matrices `coarseDualMatrix` `a*(U)` and `coarseDualInvMatrix` `a*⁻¹(U)`, (2.11)–(2.17)); see CORRESPONDENCE.md |
| Theorem 2.4 |  | proved for `Λ > 1` and the Frobenius norm (`theorem_2_4`; the proof uses the first-order and flux correctors above a random scale, not Proposition 2.11, which the book uses; `X ≤ A + O₁(θ)` is `OsBound P (X - A) 1 θ`); see CORRESPONDENCE.md |
| Lemma 2.7 |  | proved for bounded open convex sets (`lemma_2_7`, for the Frobenius norm); see CORRESPONDENCE.md |

### 2.2 Quantitative Convergence of the Subadditive Quantities, module `Ch02/Sec02QuantitativeConvergence.lean` (proofs in `Ch02/Sec02/Proposition211.lean`, `Ch02/Sec02/Lemma212.lean`, `Ch02/Sec02/Definition214.lean`, `Ch02/Sec02/MaximizerAverage.lean`, `Ch02/Sec02/DualEnergyLocal.lean`, `Ch02/Sec02/DualEnergyTranslation.lean`, `Ch02/Sec02/AdditivityDefect.lean`, `Ch02/Sec02/SubcubeMeanGradient.lean`, `Ch02/Sec02/SubcubeVariance.lean`, `Ch02/Sec02/Lemma213.lean`, `Ch02/Sec02/MaximizerMeasurability.lean`, `Ch02/Sec02/PartitionMeanGradient.lean`, `Ch02/Sec02/SubcubeDeviation.lean`, `Ch02/Sec02/Lemma215.lean`, `Ch02/Sec02/CubeCaccioppoli.lean` and `Ch02/Sec02/Lemma216.lean`)

| Result | Name | Status |
| --- | --- | --- |
| Proposition 2.11 |  | proved for `Λ > 1` (`proposition_2_11`, from Theorem 2.4 and (2.12); the book proves Theorem 2.4 from it); see CORRESPONDENCE.md |
| Lemma 2.12 |  | proved for bounded open sets and partitions by open sets, for given maximizers (they exist on bounded open convex sets, `exists_isDefectMaximizer`) (`lemma_2_12`); see CORRESPONDENCE.md |
| Lemma 2.13 |  | proved (`lemma_2_13`, with `C` depending only on `d`; `τ_n` is `additivityDefect`, `var` is `vecVariance`); see CORRESPONDENCE.md |
| Definition 2.14 |  | defined for bounded open convex sets (`averagedDualMatrix`, the inverse of the entrywise expectation `expectedDualInvMatrix` of `a*⁻¹(U)`; (2.42), `averagedDualMatrix_bounds`); see CORRESPONDENCE.md |
| Lemma 2.15 |  | proved (`lemma_2_15`, for every choice of the maximizers, centered by the mean of `v - ℓ`); see CORRESPONDENCE.md |
| Lemma 2.16 |  | proved (`lemma_2_16`); see CORRESPONDENCE.md |

### 2.3 Quantitative Homogenization of the Dirichlet Problem, module `Ch02/Sec03QuantitativeDirichletHomogenization.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 2.17 |  | not started |
| Theorem 2.18 |  | not started |

## Chapter 3: Regularity on Large Scales

### 3.1 Brief Review of Classical Elliptic Regularity, module `Ch03/Sec01ClassicalEllipticRegularity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 3.2 | Harmonic approximation | not started |

### 3.2 A C^{0,1}-Type Estimate, module `Ch03/Sec02LipschitzTypeEstimate.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 3.3 | Quenched C^{0,1}-type estimate | not started |
| Lemma 3.4 |  | proved, for every symmetric `A` with `1 ≤ A ≤ Λ` (in particular `ā`), with a constant depending only on `α, K, d, Λ` (`lemma_3_4`, module `Ch03/Sec02/Lemma34.lean`), from the harmonic expansion on balls (`harmonicExpansionBall`); see CORRESPONDENCE.md |
| Lemma 3.6 |  | in progress (the case `k = 1`, for `α > 0`, proved as `lemma_3_6_one`, module `Ch03/Sec02/Lemma34.lean`; the cases `k ≥ 2` need the `C^{k,1}` estimate (3.7) for `k ≥ 2`) |

### 3.3 Higher-Order Regularity Theory and Liouville Theorems, module `Ch03/Sec03HigherOrderRegularityAndLiouville.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 3.8 | Higher regularity theory | in progress (case `k = 1`, the classification of `A₁`, proved as `firstOrderLiouville` from the harmonic approximation on ellipsoids `harmonicApproximation`; the cases `k ≥ 2` are not proved) |
| Lemma 3.9 |  | not started |
| Corollary 3.10 | Higher regularity theory, generalized | not started |

### 3.4 The First-Order Correctors, module `Ch03/Sec04FirstOrderCorrectors.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 3.14 | Stationary random field | in progress (used for the corrector gradients only, as the fields `measurable_grad` and `stationary` of `Corrector`) |
| Definition 3.15 | Stationary random potential field | in progress (used for the corrector gradients only, as the fields `weak_gradient` and `locally_square_integrable` of `Corrector`) |
| Lemma 3.16 |  | proved (every law satisfying (0.10)–(0.11) has correctors with jointly measurable stationary gradients and homogenization data, `homogenizationDataExists`; the gradients of `A₁` are the corrected fields for all homogenization data, `ae_gradientsOfA1AreCorrected_of_liouville` with `firstOrderLiouville`; see CORRESPONDENCE.md) |
| Lemma 3.17 |  | in progress (the oscillation and energy bounds (3.85) and (3.86) with the exponent `1 - β(d - s)` of the book, with a random scale that depends on the slope, `sublinearCorrectors`; see CORRESPONDENCE.md) |
| Proposition 3.21 |  | proved, with constants chosen before the law and at every center (`uniformGaussianCorrectorRate`), from the homogenization theorem at a polynomial scale in high contrast; the identification of the homogenized matrix of the homogenization data with the matrix of the bounds, `homogenized_eq_of_basisBounds`, is not in the book (see CORRESPONDENCE.md) |
| Lemma 3.22 |  | not started |
| Lemma 3.23 |  | in progress (expectation bound (1) from Proposition 3.21 as `expectedAveragesEstimate_of_rate`, with rate `r^{-β}` for every `β`; see CORRESPONDENCE.md) |

### 3.5 Boundary Regularity, module `Ch03/Sec05BoundaryRegularity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 3.26 | Quenched C^{0,1}-type estimate, boundary version | not started |
| Lemma 3.29 |  | not started |
| Lemma 3.30 |  | not started |
| Lemma 3.31 | Harmonic approximation, boundary version | not started |
| Lemma 3.32 |  | not started |
| Lemma 3.35 |  | not started |
| Lemma 3.37 |  | not started |
| Theorem 3.38 | Higher regularity theory in half spaces | not started |

### 3.6 Optimality of the Regularity Theory, module `Ch03/Sec06OptimalityOfRegularityTheory.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 3.40 |  | not started |

## Chapter 4: Quantitative Description of First-Order Correctors

### Opening of the chapter, module `Ch04/Opening.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 4.1 |  | proved, (4.2) with `s = 1`, with a constant chosen before the law: the frozen statement E1 with no hypothesis (`averagedCorrectorGradient_holds`), (4.4)-(4.7) and `s ≠ 1` not formalized; from the estimate with compact tests (`compactTestFiniteBall`, `averagedCorrectorGradient_of_compactTests`) through the single-slope estimate on classes of laws (`averagedCorrectorGradient_of_linearSlope`) and the linear estimate (`averagedCorrectorGradient_of_linearAverage_uniform`); see CORRESPONDENCE.md |

### 4.1 The Energy Quantity J₁ and Its Basic Properties, module `Ch04/Sec01EnergyQuantityJ1.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 4.2 | Nondegeneracy at Ψ | defined (`J1Nondegenerate`, module `Ch04/Sec01/Lemma44.lean`) |
| Proposition 4.3 |  | proved, from Proposition 3.21, with an explicit constant (`flucEstimateAt_of_gaussianCorrectorRate`, `proposition43_at`) and with constants chosen before the law for bounded jointly measurable versions of `J₁` (`uniformBaseFluctuation_holds`); see CORRESPONDENCE.md |
| Lemma 4.4 | Basic properties of J₁ | proved, almost surely, for the masks `Ψ ≥ 0` with `∫ Ψ = 1` on which the gradients of `A₁` form a `d`-dimensional subspace of `L²(Ψ)` (`J1Mask`, which holds almost surely for the heat kernel masks, `ae_j1Mask_heatKernel`), with the constants `16` and `16 Λ` in (4.17)–(4.18) and the factor `½` in the left inequality of (4.15) (`lemma_4_4`, module `Ch04/Sec01/Lemma44.lean`); see CORRESPONDENCE.md |
| Definition 4.5 | Minimal scale 𝒴ₛ | not started (it is the maximum of the minimal scales of Theorem 3.8 and Propositions 3.21 and 4.3; Theorem 3.8 is proved only for `k = 1`) |

### 4.2 The Additive Structure of J₁, module `Ch04/Sec02AdditiveStructureOfJ1.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 4.6 | The additive structure of J₁ | in progress: parts (i), (iii), (iv) proved conditional on Propositions 4.10–4.12 and the initial exponent of Proposition 4.3 (see CORRESPONDENCE.md); parts (i) and (iii) with constants chosen before the law proved (`uniformAdditivityJ1_holds`, `uniformFluctuationJ1_holds`, the statements `UniformAdditivityJ1` and `UniformFluctuationJ1`), and part (iv) in the form (5.85), the frozen statement E6 (`localizedEnergy_holds`); part (ii), with (5.58), conditional on the same inputs, (4.70) and the measurability of `a ↦ J1Heat a z r p q` (`theorem46_expectation_and_558`) and, for every law with a constant that depends on the law, on Proposition 3.21, the Borel joint measurability of `J1Heat` and Propositions 4.11 and 4.12 (`estimate558_of_law`); (5.58) with a constant chosen before the law proved (`uniformEnergyEstimate_holds`) |
| Definition 4.7 | Add(s, α) | defined (see CORRESPONDENCE.md) |
| Definition 4.8 | Fluc(s, α) | defined (see CORRESPONDENCE.md) |
| Definition 4.9 | Loc(s, δ, α) | defined (see CORRESPONDENCE.md) |
| Proposition 4.10 | Improvement of additivity | proved, for bounded jointly measurable versions of `J₁` and with constants chosen before the law, with (4.70) (`uniformImprovementOfAdditivity_holds`, `uniformExpectationEstimates_holds`), from Proposition 3.21 and the heat identity (H) (`uniformGaussianInputs_holds`); also: the heat identity (H) of the route and the pathwise heat bound for every law and all homogenization data, `heatPathwiseBound_of_lawHypotheses`, with a kernel of mass `(d + 1)/u` in `exists_heatPathwiseKernel`; (5.58) for every law from Proposition 3.21, the Borel joint measurability of `J1Heat` and the conclusions of Propositions 4.11 and 4.12, `estimate558_of_law`, with a constant that depends on the law; with constants chosen before the law, the Borel measurability being replaced by bounded jointly measurable versions of `J₁`, from Proposition 3.21 with constants chosen before the law and the heat identity, `uniformImprovementOfAdditivity_of_gaussianInputs`; see CORRESPONDENCE.md |
| Proposition 4.11 | Localization estimates | proved, at the exponents of the bootstrap, with constants chosen before the law, for bounded jointly measurable versions of `J₁` (`uniformLocalizationEstimates_holds`), from the single-slope estimate of Lemma 4.21 on the classes of laws with the linear estimate (`uniformLocalizationEstimates_of_linearSlope`), the Gaussian inputs being proved; see CORRESPONDENCE.md |
| Proposition 4.12 | Fluctuation estimates | proved, with the constant of the conclusion chosen before the law (`exists_flucEstimateAt_of_add_local`; see CORRESPONDENCE.md) |

### 4.3 Improvement of Additivity, module `Ch04/Sec03ImprovementOfAdditivity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 4.13 |  | proved, from `Fluc(s, α)` with the constant chosen before the law, for bounded jointly measurable versions of `J₁`, with the linear estimate (`exists_uniform_commutator_linear_of_fluctuations`, through `exists_uniform_commutator_of_fluctuations` with Proposition 3.21 and the expectations (1)); see CORRESPONDENCE.md |
| Lemma 4.14 |  | not started |
| Lemma 4.15 |  | not started |
| Lemma 4.16 |  | not started |
| Lemma 4.17 |  | not started |

### 4.4 Localization Estimates, module `Ch04/Sec04LocalizationEstimates.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 4.19 | Multiscale Poincaré inequality, heat kernel version | not started |
| Lemma 4.20 |  | not started (for Lemma 4.21 it is replaced by the finite-ball observation (`finiteBallObservation_of_compactTests`) from the estimate with compact tests, a deterministic finite-ball estimate above a random radius with tests chosen for each law, which is proved from the first-order and flux correctors (`compactTestFiniteBall`); see CORRESPONDENCE.md) |
| Lemma 4.21 |  | proved, on the classes of laws with the linear estimate at an exponent above the construction exponent, with constants chosen before the law (`uniformLinearSlopeEstimates_holds`), and (5.85): the frozen statement E6 with no hypothesis (`localizedEnergy_holds`); the single-slope estimate from the excess decay of one slope in high contrast (`ballExcessDecay`), the observation of the smoothed correctors (`smoothedCorrectorObservation_of_gaussianGradient`) and the finite-ball observation (`slopeEstimateOnClass_of_linear_finiteBall`), the finite-ball observation from the estimate with compact tests (`finiteBallObservation_of_compactTests`, `compactTestFiniteBall`), and (5.85) from the single-slope estimate (`localizedEnergy_of_linearSlope`, `localizedEnergy_of_compactTests`); see CORRESPONDENCE.md |
| Lemma 4.22 |  | not started |

### 4.5 Fluctuation Estimates, module `Ch04/Sec05FluctuationEstimates.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 4.23 |  | not started |

### 4.6 Corrector Estimates in Weak Norms, module `Ch04/Sec06CorrectorEstimatesInWeakNorms.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 4.24 | Corrector estimates in W^{-α,p} | in progress ((4.126) with `p = 2`, integer `m > d/2` and `s = 1`: the frozen statement E7 with no hypothesis (`negativeSobolevCorrector_holds`), from the commutator and linear estimates with constants chosen before the law (`negativeSobolevCorrector_of_commutator_linear`, `negativeSobolevCorrector_of_compactTests`); see CORRESPONDENCE.md) |
| Lemma 4.25 |  | not started |

### 4.7 Corrector Oscillation Estimates in Two Dimensions, module `Ch04/Sec07CorrectorOscillationInTwoDimensions.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 4.27 |  | not started |

## Chapter 5: Scaling Limits of First-Order Correctors

### 5.1 White Noise and the Gaussian Free Field, module `Ch05/Sec01WhiteNoiseAndGaussianFreeField.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 5.1 | Scalar white noise | not started |
| Lemma 5.2 | Cramér–Wold lemma | proved, for `ℝ^d`-valued random variables on possibly different probability spaces (`lemma_5_2_tendstoInDistribution`, `lemma_5_2_map_eq`, module `Ch05/Sec01/Lemma52.lean`), from Lévy's continuity theorem and the uniqueness of characteristic functions in Mathlib; see CORRESPONDENCE.md |
| Definition 5.5 | Vector white noise | not started |
| Definition 5.8 | Gradient GFF | not started |
| Lemma 5.10 |  | not started |

### 5.2 Explicit Constructions of Random Fields, module `Ch05/Sec02ExplicitConstructionsOfRandomFields.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 5.14 | Construction of white noise | not started (proved inside einstein-relation-lean, will move here later) |
| Lemma 5.16 |  | not started |
| Proposition 5.21 | Construction of gradient GFF | not started |

### 5.3 Heuristic Derivation of the Scaling Limit, module `Ch05/Sec03HeuristicScalingLimit.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 5.23 | Coarsened coefficients | not started |
| Lemma 5.24 |  | proved, (5.63)-(5.64) with `s = 1`: the frozen statement E5 with no hypothesis (`coarsenedCoefficientEstimates_holds`), from (5.58) with a constant chosen before the law (`uniformEnergyEstimate_holds`) and the first-order Liouville theorem (`coarsenedCoefficientEstimates_of_energyEstimate`, `coarsenedCoefficientEstimates_of_compactTests`); see CORRESPONDENCE.md |

### 5.4 A Central Limit Theorem for J₁, module `Ch05/Sec04CentralLimitTheoremForJ1.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 5.25 |  | not started |
| Theorem 5.26 |  | not started |
| Lemma 5.27 |  | not started |
| Lemma 5.28 |  | not started |
| Lemma 5.29 |  | proved: (i)-(iii) for centered local additive fields, and for the localized energy the frozen statements E4, E2 and E3 with no hypothesis (`blockCLT_holds`, `blockBoundary_holds`, `blockChange_holds`), from Theorem 4.6 (i) with constants chosen before the law (`uniformAdditivityJ1_holds`, `blockCLT_of_uniformAdditivity`, `blockBoundary_of_uniformAdditivity`, `blockChange_of_uniformAdditivity`); see CORRESPONDENCE.md |
| Lemma 5.30 |  | not started |

### 5.5 Convergence of the Correctors to a Gaussian Free Field, module `Ch05/Sec05ConvergenceToGaussianFreeField.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 5.32 | Scaling limit of the corrector | not started |
| Lemma 5.35 |  | not started |
| Lemma 5.36 |  | not started |

## Chapter 6: Quantitative Two-Scale Expansions

### 6.1 The Flux Correctors, module `Ch06/Sec01FluxCorrectors.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 6.1 |  | in progress (skew symmetry up to a constant matrix and the divergence identity (6.6), `fluxCorrectorDivergence`, with the constant given by an existence statement; (6.7) is the definition of `FluxCorrector`; see CORRESPONDENCE.md) |
| Proposition 6.2 | Flux corrector estimates | in progress (the oscillation bound of the flux corrector in `sublinearCorrectors`; see CORRESPONDENCE.md) |

### 6.2 Quantitative Two-Scale Expansions Without Boundaries, module `Ch06/Sec02TwoScaleExpansionWithoutBoundaries.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 6.4 | Quantitative two-scale expansion | not started |
| Lemma 6.7 |  | not started |
| Lemma 6.8 |  | not started |
| Lemma 6.9 |  | not started |

### 6.3 Two-Scale Expansions for the Dirichlet Problem, module `Ch06/Sec03TwoScaleExpansionForDirichletProblem.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 6.11 | Quantitative two-scale expansion for the Dirichlet problem | not started |
| Lemma 6.13 |  | not started |
| Lemma 6.14 |  | not started |
| Theorem 6.15 | Quantitative two-scale expansion for the Neumann problem | not started |

### 6.4 Boundary Layer Estimates, module `Ch06/Sec04BoundaryLayerEstimates.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 6.17 | Optimal L² homogenization error estimate | not started |
| Proposition 6.18 | Dirichlet boundary layer estimate | not started |
| Proposition 6.19 | Estimates for v^ε | not started |

## Chapter 7: Calderón–Zygmund Gradient L^p Estimates

### 7.1 Interior Calderón–Zygmund Estimates, module `Ch07/Sec01InteriorCalderonZygmund.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 7.1 | Gradient L^p-type estimates | not started |
| Lemma 7.2 |  | not started |
| Proposition 7.3 |  | not started |
| Lemma 7.6 |  | not started |

### 7.2 Global Calderón–Zygmund Estimates, module `Ch07/Sec02GlobalCalderonZygmund.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 7.7 | Global gradient L^p-type estimates | not started |
| Lemma 7.8 |  | not started |
| Lemma 7.15 |  | not started |

### 7.3 W^{1,p}-Type Estimates for the Two-Scale Expansion Error, module `Ch07/Sec03W1pEstimatesForTwoScaleExpansionError.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 7.16 | Two-scale expansion, L^p estimates | not started |
| Proposition 7.17 | L^p-type estimates for the two-scale expansion | not started |
| Lemma 7.18 |  | not started |

## Chapter 8: Estimates for Parabolic Problems

### 8.1 Function Spaces and Some Basic Estimates, module `Ch08/Sec01FunctionSpacesAndBasicEstimates.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 8.1 | Parabolic Caccioppoli inequality | not started |
| Lemma 8.2 | L² gradient estimate in time slices | not started |

### 8.2 Homogenization of the Cauchy–Dirichlet Problem, module `Ch08/Sec02CauchyDirichletHomogenization.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 8.3 |  | not started |
| Lemma 8.4 |  | not started |
| Lemma 8.5 |  | not started |
| Lemma 8.6 |  | not started |

### 8.3 A Parabolic C^{0,1}-Type Estimate, module `Ch08/Sec03ParabolicLipschitzTypeEstimate.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 8.7 | Parabolic C^{0,1}-type estimate | not started |
| Lemma 8.9 |  | not started |
| Lemma 8.11 |  | not started |

### 8.4 Parabolic Higher Regularity and Liouville Theorems, module `Ch08/Sec04ParabolicHigherRegularityAndLiouville.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 8.12 | Parabolic higher regularity theory | not started |

### 8.5 Decay of the Green Functions and Their Gradients, module `Ch08/Sec05DecayOfGreenFunctions.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 8.15 | Parabolic Green function decay bounds | not started |
| Theorem 8.16 | Elliptic Green function decay bounds | not started |
| Lemma 8.19 |  | not started |

### 8.6 Homogenization of the Green Functions, module `Ch08/Sec06HomogenizationOfGreenFunctions.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 8.20 | Homogenization of the parabolic Green function | not started |
| Corollary 8.21 | Homogenization of the elliptic Green function | not started |
| Lemma 8.22 |  | not started |
| Lemma 8.23 |  | not started |
| Lemma 8.24 |  | not started |
| Lemma 8.25 |  | not started |

## Chapter 9: Decay of the Parabolic Semigroup

### 9.1 Optimal Decay of the Parabolic Semigroup, module `Ch09/Sec01OptimalDecayOfSemigroup.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 9.1 | Optimal decay of the parabolic semigroup | not started |
| Lemma 9.2 |  | not started |
| Lemma 9.3 | Localization of P | not started |
| Lemma 9.4 | Localization of u | not started |
| Lemma 9.5 |  | not started |
| Lemma 9.6 |  | not started |
| Lemma 9.7 |  | not started |
| Lemma 9.8 |  | not started |
| Lemma 9.9 |  | not started |
| Lemma 9.10 |  | not started |

### 9.2 Homogenization of the Green Functions: Optimal Scaling, module `Ch09/Sec02OptimalScalingOfGreenFunctions.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 9.12 | Optimal convergence of the parabolic Green function | not started |
| Corollary 9.13 | Optimal convergence of the elliptic Green function | not started |
| Lemma 9.14 |  | not started |
| Lemma 9.15 |  | not started |
| Definition 9.16 |  | not started |
| Lemma 9.17 |  | not started |
| Lemma 9.18 |  | not started |
| Lemma 9.19 |  | not started |

## Chapter 10: Linear Equations with Nonsymmetric Coefficients

### 10.1 Variational Formulation of General Linear Equations, module `Ch10/Sec01VariationalFormulation.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 10.2 |  | not started |
| Proposition 10.3 |  | not started |

### 10.2 The Double-Variable Subadditive Quantities, module `Ch10/Sec02DoubleVariableSubadditiveQuantities.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 10.5 |  | not started |
| Lemma 10.7 |  | not started |
| Lemma 10.8 | Caccioppoli inequality in S(U) | not started |
| Lemma 10.9 |  | not started |
| Lemma 10.10 | Basic properties of J | not started |

### 10.3 Convergence of the Subadditive Quantities, module `Ch10/Sec03ConvergenceOfSubadditiveQuantities.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 10.11 |  | not started |
| Lemma 10.12 |  | not started |
| Lemma 10.13 |  | not started |
| Lemma 10.14 |  | not started |
| Definition 10.15 |  | not started |
| Lemma 10.16 |  | not started |
| Lemma 10.17 |  | not started |

### 10.4 Quantitative Homogenization of the Dirichlet Problem, module `Ch10/Sec04QuantitativeDirichletHomogenization.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 10.19 | Weak convergence of (S, AS) | not started |
| Theorem 10.20 |  | not started |

## Chapter 11: Nonlinear Equations

### 11.1 Assumptions and Preliminaries, module `Ch11/Sec01AssumptionsAndPreliminaries.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 11.1 | Caccioppoli inequality | not started |

### 11.2 Subadditive Quantities and Basic Properties, module `Ch11/Sec02SubadditiveQuantities.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 11.2 | Basic properties of μ and μ* | not started |

### 11.3 Convergence of the Subadditive Quantities, module `Ch11/Sec03ConvergenceOfSubadditiveQuantities.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 11.4 |  | not started |
| Lemma 11.5 |  | not started |
| Lemma 11.6 |  | not started |
| Lemma 11.7 |  | not started |
| Proposition 11.8 |  | not started |

### 11.4 Quantitative Homogenization of the Dirichlet Problem, module `Ch11/Sec04QuantitativeDirichletHomogenization.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 11.10 |  | not started |
| Lemma 11.11 |  | not started |
| Lemma 11.12 |  | not started |

### 11.5 C^{0,1}-Type Estimate, module `Ch11/Sec05LipschitzTypeEstimate.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 11.13 | Quenched C^{0,1}-type estimate | not started |
| Proposition 11.14 | Harmonic approximation | not started |

## Appendix A: The O_s Notation

Module `AppA/OsNotation.lean`.

| Result | Name | Status |
| --- | --- | --- |
| Lemma A.1 | Tail probability | proved |
| Lemma A.3 |  | proved |
| Lemma A.4 |  | proved (see CORRESPONDENCE.md) |
| Lemma A.5 | Laplace transform | proved (see CORRESPONDENCE.md) |
| Lemma A.7 |  | proved (see CORRESPONDENCE.md) |
| Lemma A.8 |  | proved (see CORRESPONDENCE.md) |
| Lemma A.9 |  | proved (see CORRESPONDENCE.md) |
| Lemma A.10 |  | proved (see CORRESPONDENCE.md) |
| Lemma A.11 |  | proved |
| Lemma A.12 |  | proved (see CORRESPONDENCE.md) |

## Appendix B: Function Spaces and Elliptic Equations on Lipschitz Domains

Module `AppB/FunctionSpacesAndEllipticEquations.lean`.

| Result | Name | Status |
| --- | --- | --- |
| Definition B.1 | C^{k,α} domain | not started |
| Definition B.2 | Sobolev space W^{k,p}(U) | not started |
| Definition B.3 | Sobolev space W^{α,p}(U) | not started |
| Definition B.4 | Sobolev space W^{-α,p}(U) | not started |
| Definition B.7 | Besov space B^{p,p}_α(∂U) | not started |
| Theorem B.8 | Global Sobolev inequality | not started |
| Theorem B.9 | Local Sobolev–Poincaré inequality | not started |
| Theorem B.10 | Morrey's inequality | not started |
| Proposition B.11 | Sobolev–Poincaré–Wirtinger inequality | not started |
| Proposition B.13 | Embedding between fractional Sobolev spaces | not started |
| Proposition B.14 | Extension theorem | not started |
| Proposition B.15 | Sobolev trace theorem | not started |
| Proposition B.16 |  | not started |
| Lemma B.17 | Interior H² estimate | not started |
| Proposition B.18 | Global H² estimate | not started |
| Lemma B.19 |  | not started |

## Appendix C: The Meyers L^{2+δ} Estimate

Module `AppC/MeyersEstimate.lean` (proofs in `AppC/VitaliCovering.lean`, `AppC/IterationLemma.lean`, `AppC/NegativeSobolevPairing.lean`, `AppC/InteriorCaccioppoli.lean`, `AppC/ReverseHolder.lean`, `AppC/BallLebesgueDifferentiation.lean`, `AppC/GehringBallEstimates.lean`, `AppC/GehringLevelSet.lean`, `AppC/GehringIntegration.lean`, `AppC/GehringLemma.lean` and `AppC/InteriorMeyers.lean`).

| Result | Name | Status |
| --- | --- | --- |
| Theorem C.1 | Interior Meyers estimate | in progress (for `d ≥ 2`: the case `h = ∇·H` of the proof, with `‖H‖_{L̲^{(2+δ)∧p}(B_r)}` on the right, `theorem_C_1_divergence`; the statement of the book given the representation of Remark B.6 and Proposition B.16, `theorem_C_1`; see CORRESPONDENCE.md) |
| Lemma C.2 | Interior Caccioppoli inequality | proved (`lemma_C_2`; see CORRESPONDENCE.md) |
| Corollary C.3 |  | proved (`corollary_C_3`, for `d ≥ 2`; see CORRESPONDENCE.md) |
| Lemma C.4 | Gehring's lemma | proved (`lemma_C_4`; see CORRESPONDENCE.md) |
| Lemma C.5 | Vitali covering lemma | proved (`lemma_C_5`); see CORRESPONDENCE.md |
| Lemma C.6 |  | proved (`lemma_C_6`; see CORRESPONDENCE.md) |
| Theorem C.7 | Global Meyers estimate | not started (needs the Lipschitz domains of Appendix B, the constant κ_U of (C.13) and Proposition B.16) |
| Lemma C.8 | Global Caccioppoli estimate | not started (needs the Lipschitz domains of Appendix B and κ_U) |
| Corollary C.9 |  | not started (needs Lemma C.8 and the Sobolev–Poincaré inequality for functions vanishing on a set of positive measure) |

## Appendix D: Sobolev Norms and Heat Flow

Module `AppD/SobolevNormsAndHeatFlow.lean` (proofs in `AppD/MaximalFunction.lean`, `AppD/HeatEnergyIdentity.lean`, `AppD/HeatGradientKernel.lean`, `AppD/HeatGradientL2.lean`, `AppD/LemmaD3.lean` and `AppD/PropositionD2.lean`).

| Result | Name | Status |
| --- | --- | --- |
| Proposition D.1 |  | not started (a variant of the first inequality of (D.1) for `p = 2` and integer orders, with the normalized norm of `H^{-m}(B_1)`, is used for (4.126): `negativeIntegerSobolevNorm_le_heatBracket`; see CORRESPONDENCE.md) |
| Proposition D.2 |  | in progress (the case `q = 2`, `α ∈ ℕ` of (D.3), `propositionD2_two`, which is Lemma D.3; see CORRESPONDENCE.md) |
| Lemma D.3 |  | proved (`lemmaD3`; see CORRESPONDENCE.md) |
| Lemma D.4 |  | proved (`lemmaD4`; see CORRESPONDENCE.md) |
| Proposition D.5 |  | not started |

## Appendix E: Parabolic Green Functions

Module `AppE/ParabolicGreenFunctions.lean`.

| Result | Name | Status |
| --- | --- | --- |
| Proposition E.1 |  | not started |
| Proposition E.3 |  | not started |
| Lemma E.4 |  | not started |
| Lemma E.5 |  | not started |
| Lemma E.6 |  | not started |
| Lemma E.7 |  | not started |
| Lemma E.8 |  | not started |
