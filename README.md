# Quantitative stochastic homogenization and large-scale regularity

[![CI](https://github.com/nitromannitol/Quantitative-Stochastic-Homogenization/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Quantitative-Stochastic-Homogenization/actions/workflows/build.yml)

A Lean 4 formalization, in progress, of the book

> Scott Armstrong, Tuomo Kuusi and Jean-Christophe Mourrat,
> *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
> Grundlehren der mathematischen Wissenschaften 352, Springer, 2019
> ([arXiv:1705.05300](https://arxiv.org/abs/1705.05300),
> [doi:10.1007/978-3-030-15545-2](https://doi.org/10.1007/978-3-030-15545-2)).

The book shows that, on large scales, solutions of a divergence-form elliptic equation with random
coefficients are close to solutions of an equation with constant coefficients, with explicit rates.
The formalization is partial: of the 226 numbered results of the book, 71 are proved (or, for
definitions, defined), mostly in Chapters 1 to 5 and Appendices A, C and D, and 27 are in progress.
The library has no `sorry` and uses only the standard axioms.

The book is not included in this repository. Results are cited by the numbering of the Springer
edition; [`ROADMAP.md`](ROADMAP.md) lists every numbered result with its status.

## The book

The book studies the elliptic equation `−∇·(a(x)∇u) = 0` in `ℝᵈ` with a random coefficient field
`a`. The field takes values in the symmetric matrices with `I ≤ a(x) ≤ ΛI`. Its law is invariant
under translations by `ℤᵈ` and has a unit range of dependence: the restrictions of `a` to two sets
at distance at least one are independent. These are the standing assumptions (0.6), (0.10) and
(0.11) of the book.

On large scales the solutions behave like those of an equation `−∇·(ā∇u) = 0` with a constant,
deterministic matrix `ā`, the *homogenized matrix*. The book makes this quantitative. It proves an
algebraic rate of convergence for subadditive energy quantities (Chapter 2). It proves a regularity
theory that holds above a random scale with a stretched exponential moment (Chapter 3). It derives
optimal bounds on the first-order correctors `φ_e` (Chapter 4) and their scaling limit, a Gaussian
free field (Chapter 5). Later chapters treat two-scale expansions, Calderón–Zygmund estimates,
parabolic equations, nonsymmetric coefficients and nonlinear equations.

## The main theorems in Lean

| Book | Lean declaration |
| --- | --- |
| Definition 1.2, the homogenized matrix | `QSH.exists_homogenizedMatrix` |
| Proposition 1.12, multiscale Poincaré inequality | `QSH.proposition_1_12` |
| Theorem 2.4 | `QSH.theorem_2_4` |
| Theorem 2.17 | `QSH.theorem_2_17` |
| Proposition 3.2, harmonic approximation | `QSH.proposition_3_2` |
| Theorem 3.3, quenched `C^{0,1}`-type estimate | `QSH.theorem_3_3` |
| Theorem 3.8 (i)–(iii), every `k` | `QSH.theorem_3_8` |
| Lemma 3.16, existence of the correctors | `QSH.homogenizationDataExists` |
| Proposition 3.21 | `QSH.uniformGaussianCorrectorRate` |
| Theorem 4.1, (4.2) with `s = 1` | `QSH.averagedCorrectorGradient_holds` |
| Theorem 4.6 (i) | `QSH.uniformAdditivityJ1_holds` |
| Theorem 4.6 (iii) | `QSH.uniformFluctuationJ1_holds` |
| Theorem 4.24, (4.126) with `p = 2` | `QSH.negativeSobolevCorrector_holds` |
| Lemma 5.24 | `QSH.coarsenedCoefficientEstimates_holds` |
| Lemma 5.29 (i) | `QSH.blockCLT_holds` |
| Lemma 8.1, parabolic Caccioppoli inequality | `QSH.lemma_8_1` |
| Proposition 10.3 | `QSH.GeneralCoefficientField.proposition_10_3` |
| Theorem C.1, interior Meyers estimate | `QSH.theorem_C_1` |

How to read the statements: a coefficient field is `QSH.CoefficientField d Λ`, and the standing
assumptions on its law `P` are `QSH.LawHypotheses P`. The book writes `X ≤ O_s(θ)` for
`E[exp((X/θ)ˢ)] ≤ 2` (Appendix A); in Lean this is `QSH.OsBound P X s θ`. Most statements fix
`d ≥ 2` and `Λ > 1`, choose the constants, and then hold for every law that satisfies
`LawHypotheses`, as the constants of the book depend only on `d`, `Λ` and the exponents. Every other
numbered result is named in [`ROADMAP.md`](ROADMAP.md), with its module.

Seven statements are pinned for the formalization of the Einstein relation in
[einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean). Each is a
proposition in [`Frozen/`](QuantitativeStochasticHomogenization/Frozen/), fixed by its hash in
[`FROZEN.md`](FROZEN.md). All seven are proved with no hypothesis in
[`Ch05/Sec04/FrozenProved.lean`](QuantitativeStochasticHomogenization/Ch05/Sec04/FrozenProved.lean),
a separate module because the modules the proofs use import the pinned files.

| id | Book | Pinned statement | Proof |
| --- | --- | --- | --- |
| E1 | Theorem 4.1, (4.2) | `QSH.Frozen.averagedCorrectorGradient` | `QSH.averagedCorrectorGradient_holds` |
| E2 | Lemma 5.29 (ii), (5.91)–(5.92) | `QSH.Frozen.blockBoundary` | `QSH.blockBoundary_holds` |
| E3 | Lemma 5.29 (iii) | `QSH.Frozen.blockChange` | `QSH.blockChange_holds` |
| E4 | Lemma 5.29 (i), (5.90) | `QSH.Frozen.blockCLT` | `QSH.blockCLT_holds` |
| E5 | Lemma 5.24, (5.63)–(5.64) | `QSH.Frozen.coarsenedCoefficientEstimates` | `QSH.coarsenedCoefficientEstimates_holds` |
| E6 | (5.85), Theorem 4.6 (iv) | `QSH.Frozen.localizedEnergy` | `QSH.localizedEnergy_holds` |
| E7 | Theorem 4.24, (4.126) | `QSH.Frozen.negativeSobolevCorrector` | `QSH.negativeSobolevCorrector_holds` |

## All numbered results

[`ROADMAP.md`](ROADMAP.md) gives the status of each of the 226 numbered results, with its Lean
declaration and module. By chapter:

| Chapter | Title | Numbered results | Proved or defined | In progress |
| --- | --- | --- | --- | --- |
| 1 | Introduction and Qualitative Theory | 12 | 8 | 4 |
| 2 | Convergence of the Subadditive Quantities | 12 | 11 | 1 |
| 3 | Regularity on Large Scales | 23 | 9 | 2 |
| 4 | Quantitative Description of First-Order Correctors | 25 | 12 | 3 |
| 5 | Scaling Limits of First-Order Correctors | 19 | 8 | 0 |
| 6 | Quantitative Two-Scale Expansions | 13 | 0 | 2 |
| 7 | Calderón–Zygmund Gradient `Lᵖ` Estimates | 10 | 0 | 1 |
| 8 | Estimates for Parabolic Problems | 19 | 1 | 0 |
| 9 | Decay of the Parabolic Semigroup | 18 | 0 | 0 |
| 10 | Linear Equations with Nonsymmetric Coefficients | 16 | 3 | 1 |
| 11 | Nonlinear Equations | 12 | 0 | 0 |
| A | The `O_s` Notation | 10 | 10 | 0 |
| B | Function Spaces and Elliptic Equations on Lipschitz Domains | 16 | 0 | 7 |
| C | The Meyers `L^{2+δ}` Estimate | 9 | 6 | 3 |
| D | Sobolev Norms and Heat Flow | 5 | 2 | 3 |
| E | Parabolic Green Functions | 7 | 1 | 0 |
| | **Total** | **226** | **71** | **27** |

**Proved.**

- **Chapter 1.** The homogenized matrix (Definition 1.2), Lemma 1.1, Propositions 1.7, 1.8, 1.10 and
  1.12 (the multiscale Poincaré inequality), Lemma 1.13 and Corollary 1.14.
- **Chapter 2.** The rate of convergence of the subadditive quantities (Theorem 2.4 and
  Proposition 2.11), the weak convergence with a rate of the gradients and fluxes of the maximizers
  (Theorem 2.17), and Lemmas 2.1, 2.2, 2.7, 2.12, 2.13, 2.15 and 2.16, with Definition 2.14.
- **Chapter 3.** Harmonic approximation (Proposition 3.2), the large-scale `C^{0,1}`-type estimate
  (Theorem 3.3), Lemmas 3.4 and 3.6, Definitions 3.14 and 3.15, the existence of correctors
  (Lemma 3.16), Proposition 3.21 and Lemma 3.23. Statements (i)–(iii) of Theorem 3.8, the higher
  regularity theory, hold for every `k`, with a random scale that depends on `k`.
- **Chapter 4.** Theorem 4.1 in the form (4.2) with `s = 1`, Proposition 4.3, Lemma 4.4, Definitions
  4.2 and 4.7 to 4.9, Propositions 4.10 to 4.12, Lemma 4.13 and Lemma 4.21. Parts (i) and (iii) of
  Theorem 4.6, its part (iv) in the form (5.85), and the estimate (4.126) of Theorem 4.24 with
  `p = 2` and `s = 1` are proved.
- **Chapter 5.** The Cramér–Wold lemma (Lemma 5.2), Lemma 5.10, Definition 5.23, Lemma 5.24 and
  Lemmas 5.27 to 5.30.
- **Chapters 8 and 10.** The parabolic Caccioppoli inequality (Lemma 8.1), Definition 10.2,
  Proposition 10.3 and Lemma 10.9.
- **Appendices.** All of Appendix A; the interior Meyers estimate and its lemmas (Theorem C.1,
  Lemma C.2, Corollary C.3, Lemmas C.4 to C.6); Lemmas D.3, D.4 and E.6.

**Not proved.**

- **Chapter 1.** Proposition 1.11 is proved for `d ≠ 4` only (see [Corrections](#corrections)).
  Proposition 1.15, Lemma 1.16 and Theorem 1.17 are in progress.
- **Chapter 3.** The dimension formula (3.42) of Theorem 3.8, and a single random scale for all `k`.
  Lemma 3.9, Corollary 3.10, Lemma 3.22 and all of Sections 3.5 (boundary regularity) and 3.6.
  Lemma 3.17 is in progress: its bounds (3.85)–(3.86) hold with a random scale that depends on the
  slope.
- **Chapter 4.** Part (ii) of Theorem 4.6 is proved only under further hypotheses, and (4.4)–(4.7)
  of Theorem 4.1 are not formalized. Lemma 4.22 is in progress. Definition 4.5, Lemmas 4.14 to
  4.17, 4.19, 4.20, 4.23 and 4.25 and Proposition 4.27 are not started.
- **Chapter 5.** The central limit theorem for `J₁` (Proposition 5.25, Theorem 5.26) and the
  convergence of the correctors to a Gaussian free field (Theorem 5.32).
- **Chapters 6 to 11.** Chapters 6, 7, 9 and 11 have no proved result; Lemma 6.1, Proposition 6.2
  and Lemma 7.2 are in progress. Chapter 8 has only Lemma 8.1, and Chapter 10 the three results
  above, with Lemma 10.10 in progress.
- **Lipschitz domains.** Theorems 1.17 and 2.18 and the global results of Appendices B and C are in
  progress on bounded convex domains or domains with a boundary density condition.

## Corrections

The Lean statements follow the Springer edition. [`CORRESPONDENCE.md`](CORRESPONDENCE.md) records
every place where a Lean statement or proof departs from the book. Three of these correct the book:

- **Proposition 1.11.** The proof bounds `Σ_{n ≤ m} 3^{n−m} 3^{−dn/4}` by `C 3^{−(d/4 ∧ 1)m}`, which
  fails for `d = 4`, where the sum is `(m + 1) 3^{−m}`. So (1.41) is proved for `d ≠ 4`; the limit
  `E[E(m)] → 0` is proved in every dimension.
- **Lemma 4.4, (4.15).** The left inequality holds with the factor `½`:
  `½ ‖∇v‖²_{L²(Ψ)} ≤ J₁(Ψ, p, q)`. For `a = 1` the printed form fails when `p ≠ q`.
- **Lemma 7.2.** The book assumes (7.6) and (7.7) only for balls centred in `B_{1/2}`, but its proof
  uses them at balls whose centres need not lie there. `QSH.lemma_7_2` proves the conclusion on
  `B_{1/4}` under the printed hypotheses, and `QSH.lemma_7_2_ball` assumes them on every ball, the
  form that the proof of Proposition 7.3 supplies.

## Scope

- **`Λ > 1`.** Most results assume `Λ > 1`; when `Λ = 1` the field is the identity.
- **Different proofs.** The correctors and several estimates of Chapters 2 to 6 are obtained from
  the homogenization theorem at a polynomial scale in high contrast of Armstrong, Kuusi and Loher
  ([HighContrastHomogenization](https://github.com/scottnarmstrong/HighContrastHomogenization)),
  not by the proofs of the book. For instance Theorem 2.4 is proved from the correctors, and
  Proposition 2.11 from Theorem 2.4, the reverse of the book's order.
- **Lemma 4.20** is replaced, in the proof of Lemma 4.21, by an estimate with compact tests
  (`QSH.compactTestFiniteBall`) proved from the first-order and flux correctors.
- **Random scales.** Random scales are real valued, and statements hold for almost every coefficient
  field.
- [`CORRESPONDENCE.md`](CORRESPONDENCE.md) records every departure from the book: a different proof,
  a hypothesis made explicit, or a measurability fact that the book takes for granted.

## Checking the proofs

- **No `sorry`.** [`scripts/check_frozen.py`](scripts/check_frozen.py) rejects `sorry`, `axiom`,
  `admit`, `sorryAx`, `native_decide`, `unsafe` and similar tokens in the library. It also rejects
  any change to a pinned statement or to a definition it uses.
- **Standard axioms only.**
  [`Meta/AxiomsAudit.lean`](QuantitativeStochasticHomogenization/Meta/AxiomsAudit.lean) fails to
  compile when a declaration of the library depends on an axiom other than `propext`,
  `Classical.choice` and `Quot.sound`.
- **Continuous integration.** The **CI** workflow builds the library, rejects any warning, and runs
  the checker of the pinned statements and the axiom audit. There is no comparator pair.

`QuantitativeStochasticHomogenization/` contains 601 Lean files with about 141,000 lines.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The dependencies are public repositories, pinned to exact revisions in
[`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json):

- Lean and mathlib `v4.35.0-rc2`.
- [CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining), the homogenization library
  of Armstrong and Kuusi, at `310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be`.
- [HighContrastHomogenization](https://github.com/scottnarmstrong/HighContrastHomogenization) at
  `7a13dbcd8d6609264a713373f5c69ceeac870472`.
- [EllipticRegularityLean](https://github.com/scottnarmstrong/EllipticRegularityLean) at
  `1e29da02bcc6e3c2359a5b8e0559e76d02ec4002`.
- [subdiffusive-process](https://github.com/nitromannitol/subdiffusive-process) at
  `4c6b8fa60357a07fd5713e5104a6cc70f8e432dc`, which brings
  [MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess) at
  `666cda029098a1106914fc9fa7abd1727573284a`.

## Repository layout

```text
QuantitativeStochasticHomogenization.lean   the root module, importing every module below
QuantitativeStochasticHomogenization/       namespace QSH
  Front/                 the chapters "Assumptions and Examples" and "Notation"
  Ch01/ ... Ch11/        one directory per chapter, one module per section (Sec01..., Sec02..., ...)
  Ch04/Opening.lean      the text of Chapter 4 before Section 4.1 (it states Theorem 4.1)
  AppA/ ... AppE/        one module per appendix
  Frozen/                the seven statements pinned for the formalization of the Einstein relation
  Meta/AxiomsAudit.lean  the axiom audit, compiled by `lake build`, not imported by the root
scripts/                 the checker of the pinned statements and the warning checker
ROADMAP.md               every numbered result of the book, with its status
FROZEN.md                the pinned statements, with their hashes
CORRESPONDENCE.md        where the Lean proofs depart from the book
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI
(GPT), under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel.

## Authors and citation

The Lean formalization is by **Ahmed Bou-Rabee**. To cite it, use [`CITATION.cff`](CITATION.cff).

## Licence

No licence has been chosen for this repository yet.
