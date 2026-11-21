# Roadmap

**Current priority.** The frozen statements needed by [einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean), listed in [FROZEN.md](FROZEN.md). The list is empty so far. The full-book list follows below.

## Numbering and status

The numbered results below are those of the Springer edition of the book (Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, Grundlehren der mathematischen Wissenschaften 352, 2019), read from its text: definitions, theorems, propositions, lemmas and corollaries, by chapter and section. The counter of a chapter is shared with remarks, examples and exercises, which are not listed, so the numbers are not consecutive. The numbering differs from that of the arXiv version (arXiv:1705.05300v2), in which exercises have their own counter: for instance Proposition 5.14 here is Proposition 5.9 there. The appendices have no sections and one module each. In Appendix A, A.2 is a remark and A.6 an exercise.

A name in the second column is the one given in the heading of the result in the book. The statuses are `not started`, `in progress` (with the note `moving from einstein-relation-lean` when the work is being moved from that repository), `statement frozen` (the statement is registered in [FROZEN.md](FROZEN.md)), `proved` (for a definition: `defined`), with a pointer to [CORRESPONDENCE.md](CORRESPONDENCE.md) when the Lean statement differs from the book.

The book has **226 numbered results**: 38 theorems, 37 propositions, 124 lemmas, 6 corollaries and 21 definitions. 9 of them are proved or defined, all in Appendix A and Section 4.2, and 2 are in progress.

## Moving from einstein-relation-lean

- Moved: the `O_s` calculus of Appendix A (Lemmas A.1, A.3 and A.9–A.12 proved, Lemma A.4 for finite sums), Definitions 4.7–4.9, Theorem 4.6, parts (i), (iii) and (iv), conditional on Propositions 4.10–4.12, and the semigroup property of the heat kernel (Chapter 4, opening). Lemmas A.5, A.7 and A.8 are not formalized.
- Proved inside einstein-relation-lean and to move here later: Lemma 3.17, Lemma 6.1 and Proposition 6.2, in the form used as the sublinear corrector input, and Proposition 5.14 (the existence of white noise).

## Summary by chapter

| Chapter | Title | Numbered results | Proved or defined | In progress |
| --- | --- | --- | --- | --- |
| 1 | Introduction and Qualitative Theory | 12 | 0 | 0 |
| 2 | Convergence of the Subadditive Quantities | 12 | 0 | 0 |
| 3 | Regularity on Large Scales | 23 | 0 | 0 |
| 4 | Quantitative Description of First-Order Correctors | 25 | 3 | 1 |
| 5 | Scaling Limits of First-Order Correctors | 19 | 0 | 0 |
| 6 | Quantitative Two-Scale Expansions | 13 | 0 | 0 |
| 7 | Calderón–Zygmund Gradient L^p Estimates | 10 | 0 | 0 |
| 8 | Estimates for Parabolic Problems | 19 | 0 | 0 |
| 9 | Decay of the Parabolic Semigroup | 18 | 0 | 0 |
| 10 | Linear Equations with Nonsymmetric Coefficients | 16 | 0 | 0 |
| 11 | Nonlinear Equations | 12 | 0 | 0 |
| Appendix A | The O_s Notation | 10 | 6 | 1 |
| Appendix B | Function Spaces and Elliptic Equations on Lipschitz Domains | 16 | 0 | 0 |
| Appendix C | The Meyers L^{2+δ} Estimate | 9 | 0 | 0 |
| Appendix D | Sobolev Norms and Heat Flow | 5 | 0 | 0 |
| Appendix E | Parabolic Green Functions | 7 | 0 | 0 |
| | **Total** | **226** | **9** | **2** |

## Front matter

The chapters "Assumptions and Examples" and "Notation" state no numbered result. Modules: `Front/Assumptions.lean` and `Front/Notation.lean`. Status: not started.

## Chapter 1: Introduction and Qualitative Theory

### 1.1 A Brief and Informal Introduction to Homogenization, module `Ch01/Sec01BriefIntroduction.lean`

No numbered result.

### 1.2 The Subadditive Quantity μ and Its Basic Properties, module `Ch01/Sec02SubadditiveQuantity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 1.1 | Basic properties of μ | not started |

### 1.3 Convergence of the Subadditive Quantity, module `Ch01/Sec03ConvergenceOfSubadditiveQuantity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 1.2 | Homogenized coefficients | not started |
| Proposition 1.7 |  | not started |
| Proposition 1.8 |  | not started |

### 1.4 Weak Convergence of Gradients and Fluxes, module `Ch01/Sec04WeakConvergenceOfGradientsAndFluxes.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 1.10 |  | not started |
| Proposition 1.11 |  | not started |
| Proposition 1.12 | Multiscale Poincaré inequality | not started |
| Lemma 1.13 |  | not started |
| Corollary 1.14 |  | not started |
| Proposition 1.15 |  | not started |
| Lemma 1.16 | Div-curl lemma | not started |

### 1.5 Homogenization of the Dirichlet Problem, module `Ch01/Sec05HomogenizationOfDirichletProblem.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 1.17 |  | not started |

## Chapter 2: Convergence of the Subadditive Quantities

### 2.1 The Dual Subadditive Quantity μ*, module `Ch02/Sec01DualSubadditiveQuantity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 2.1 |  | not started |
| Lemma 2.2 | Basic properties of J | not started |
| Theorem 2.4 |  | not started |
| Lemma 2.7 |  | not started |

### 2.2 Quantitative Convergence of the Subadditive Quantities, module `Ch02/Sec02QuantitativeConvergence.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 2.11 |  | not started |
| Lemma 2.12 |  | not started |
| Lemma 2.13 |  | not started |
| Definition 2.14 |  | not started |
| Lemma 2.15 |  | not started |
| Lemma 2.16 |  | not started |

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
| Lemma 3.4 |  | not started |
| Lemma 3.6 |  | not started |

### 3.3 Higher-Order Regularity Theory and Liouville Theorems, module `Ch03/Sec03HigherOrderRegularityAndLiouville.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 3.8 | Higher regularity theory | not started |
| Lemma 3.9 |  | not started |
| Corollary 3.10 | Higher regularity theory, generalized | not started |

### 3.4 The First-Order Correctors, module `Ch03/Sec04FirstOrderCorrectors.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 3.14 | Stationary random field | not started |
| Definition 3.15 | Stationary random potential field | not started |
| Lemma 3.16 |  | not started |
| Lemma 3.17 |  | not started (its sublinear-corrector input is proved inside einstein-relation-lean and will move here later) |
| Proposition 3.21 |  | not started |
| Lemma 3.22 |  | not started |
| Lemma 3.23 |  | not started |

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
| Theorem 4.1 |  | not started |

### 4.1 The Energy Quantity J₁ and Its Basic Properties, module `Ch04/Sec01EnergyQuantityJ1.lean`

| Result | Name | Status |
| --- | --- | --- |
| Definition 4.2 | Nondegeneracy at Ψ | not started |
| Proposition 4.3 |  | not started |
| Lemma 4.4 | Basic properties of J₁ | not started |
| Definition 4.5 | Minimal scale 𝒴ₛ | not started |

### 4.2 The Additive Structure of J₁, module `Ch04/Sec02AdditiveStructureOfJ1.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 4.6 | The additive structure of J₁ | in progress: parts (i), (iii), (iv) proved conditional on Propositions 4.10–4.12 and the initial exponent of Proposition 4.3 (see CORRESPONDENCE.md); part (ii) not started |
| Definition 4.7 | Add(s, α) | defined (see CORRESPONDENCE.md) |
| Definition 4.8 | Fluc(s, α) | defined (see CORRESPONDENCE.md) |
| Definition 4.9 | Loc(s, δ, α) | defined (see CORRESPONDENCE.md) |
| Proposition 4.10 | Improvement of additivity | not started |
| Proposition 4.11 | Localization estimates | not started |
| Proposition 4.12 | Fluctuation estimates | not started |

### 4.3 Improvement of Additivity, module `Ch04/Sec03ImprovementOfAdditivity.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 4.13 |  | not started |
| Lemma 4.14 |  | not started |
| Lemma 4.15 |  | not started |
| Lemma 4.16 |  | not started |
| Lemma 4.17 |  | not started |

### 4.4 Localization Estimates, module `Ch04/Sec04LocalizationEstimates.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 4.19 | Multiscale Poincaré inequality, heat kernel version | not started |
| Lemma 4.20 |  | not started |
| Lemma 4.21 |  | not started |
| Lemma 4.22 |  | not started |

### 4.5 Fluctuation Estimates, module `Ch04/Sec05FluctuationEstimates.lean`

| Result | Name | Status |
| --- | --- | --- |
| Lemma 4.23 |  | not started |

### 4.6 Corrector Estimates in Weak Norms, module `Ch04/Sec06CorrectorEstimatesInWeakNorms.lean`

| Result | Name | Status |
| --- | --- | --- |
| Theorem 4.24 | Corrector estimates in W^{-α,p} | not started |
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
| Lemma 5.2 | Cramér–Wold lemma | not started |
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
| Lemma 5.24 |  | not started |

### 5.4 A Central Limit Theorem for J₁, module `Ch05/Sec04CentralLimitTheoremForJ1.lean`

| Result | Name | Status |
| --- | --- | --- |
| Proposition 5.25 |  | not started |
| Theorem 5.26 |  | not started |
| Lemma 5.27 |  | not started |
| Lemma 5.28 |  | not started |
| Lemma 5.29 |  | not started |
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
| Lemma 6.1 |  | not started (its sublinear-corrector input is proved inside einstein-relation-lean and will move here later) |
| Proposition 6.2 | Flux corrector estimates | not started (its sublinear-corrector input is proved inside einstein-relation-lean and will move here later) |

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
| Lemma A.4 |  | in progress: the case `s ≥ 1` for finite sums (see CORRESPONDENCE.md) |
| Lemma A.5 | Laplace transform | not started |
| Lemma A.7 |  | not started |
| Lemma A.8 |  | not started |
| Lemma A.9 |  | proved (see CORRESPONDENCE.md) |
| Lemma A.10 |  | proved for a constant scale on a finite measure (see CORRESPONDENCE.md) |
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

Module `AppC/MeyersEstimate.lean`.

| Result | Name | Status |
| --- | --- | --- |
| Theorem C.1 | Interior Meyers estimate | not started |
| Lemma C.2 | Interior Caccioppoli inequality | not started |
| Corollary C.3 |  | not started |
| Lemma C.4 | Gehring's lemma | not started |
| Lemma C.5 | Vitali covering lemma | not started |
| Lemma C.6 |  | not started |
| Theorem C.7 | Global Meyers estimate | not started |
| Lemma C.8 | Global Caccioppoli estimate | not started |
| Corollary C.9 |  | not started |

## Appendix D: Sobolev Norms and Heat Flow

Module `AppD/SobolevNormsAndHeatFlow.lean`.

| Result | Name | Status |
| --- | --- | --- |
| Proposition D.1 |  | not started |
| Proposition D.2 |  | not started |
| Lemma D.3 |  | not started |
| Lemma D.4 |  | not started |
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
