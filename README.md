# Quantitative stochastic homogenization and large-scale regularity

A **Lean 4** formalization, in progress, of the book

> Scott Armstrong, Tuomo Kuusi and Jean-Christophe Mourrat,
> *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
> Grundlehren der mathematischen Wissenschaften 352, Springer, 2019
> ([arXiv:1705.05300](https://arxiv.org/abs/1705.05300),
> [doi:10.1007/978-3-030-15545-2](https://doi.org/10.1007/978-3-030-15545-2)).

The book is not included in this repository. The numbered results are cited by the numbering of the
Springer edition; see [`ROADMAP.md`](ROADMAP.md).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and is set up to
use four public libraries: [CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining), the
homogenization library of Armstrong and Kuusi,
[HighContrastHomogenization](https://github.com/scottnarmstrong/HighContrastHomogenization),
[EllipticRegularityLean](https://github.com/scottnarmstrong/EllipticRegularityLean), and
[subdiffusive-process](https://github.com/nitromannitol/subdiffusive-process).

## The book

The book presents the quantitative homogenization and large-scale regularity theory for elliptic
equations in divergence form with random coefficients. The coefficient field is uniformly elliptic,
stationary under translations by `ℤᵈ`, and has a unit range of dependence (the standing assumptions,
(0.6), (0.10) and (0.11) of the book). Its chapters are:

| Chapter | Title |
| --- | --- |
| 1 | Introduction and Qualitative Theory |
| 2 | Convergence of the Subadditive Quantities |
| 3 | Regularity on Large Scales |
| 4 | Quantitative Description of First-Order Correctors |
| 5 | Scaling Limits of First-Order Correctors |
| 6 | Quantitative Two-Scale Expansions |
| 7 | Calderón–Zygmund Gradient `Lᵖ` Estimates |
| 8 | Estimates for Parabolic Problems |
| 9 | Decay of the Parabolic Semigroup |
| 10 | Linear Equations with Nonsymmetric Coefficients |
| 11 | Nonlinear Equations |
| A–E | The `O_s` notation; function spaces and elliptic equations on Lipschitz domains; the Meyers `L^{2+δ}` estimate; Sobolev norms and heat flow; parabolic Green functions |

## Status

[`ROADMAP.md`](ROADMAP.md) lists every numbered result of the book (226 of them, by chapter and
section) with its status. Where a proof departs from the book, [`CORRESPONDENCE.md`](CORRESPONDENCE.md)
records it. Proved so far, besides the `O_s` calculus of Appendix A and Definitions 4.7–4.9:

- Section 1.3: the limit (1.22) of the expected energy on the triadic cubes and the homogenized
  matrix of Definition 1.2 (`exists_homogenizedMatrix`), from the parallelogram identity and the
  subadditivity (1.11) of the energy.
- Lemma 3.16: every law satisfying (0.10)–(0.11) has first-order correctors with jointly measurable
  stationary gradients, hence homogenization data (`homogenizationDataExists`), built from the
  correctors of the homogenization theorem at a polynomial scale in high contrast.
- The first-order Liouville theorem (Theorem 3.8 for `k = 1`, `firstOrderLiouville`) with the
  harmonic approximation on ellipsoids (`harmonicApproximation`) that it rests on, and the harmonic
  expansion on balls.
- The bounds (3.85) and (3.86) of Lemma 3.17, Lemma 6.1 with the divergence identity (6.6), where the
  statement gives a deterministic vector and the proof identifies it, and Proposition 6.2 for the
  correctors (`sublinearCorrectors`), from the homogenization theorem at a polynomial scale in high
  contrast.
- The heat identity (H) of the route of Proposition 4.10 and the pathwise heat bound for every law
  and all homogenization data (`heatPathwiseBound_of_lawHypotheses`, and with a kernel of mass
  `(d + 1)/u`, `exists_heatPathwiseKernel`); hence (5.58) for every law, with a constant that depends
  on the law, from Proposition 3.21, the joint measurability of `J₁` and the conclusions of
  Propositions 4.11 and 4.12 (`estimate558_of_law`).
- Parts (i), (iii) and (iv) of Theorem 4.6 conditional on Propositions 4.10–4.12, and Lemma 5.29
  (i)–(iii) for centered local additive fields.
- The bootstrap of Theorem 4.6 with constants chosen before the law: Definitions 4.7–4.9 with their
  constants, Propositions 4.3, 4.10 and 4.12 and Lemma 4.13 with constants chosen before the law for
  bounded jointly measurable versions of `J₁`, and Proposition 4.11 at the exponents of the bootstrap
  from the single-slope estimate of Lemma 4.21 on classes of laws; hence Theorem 4.6 (i) and (iii),
  the Gaussian gradient bound and (5.58) with constants chosen before the law from Proposition 3.21
  with constants chosen before the law and that single-slope estimate.

Some of this material was moved here from
[einstein-relation-lean](https://github.com/nitromannitol/einstein-relation-lean). The current
priority is the frozen statements E1–E7 needed by that repository, listed in
[`FROZEN.md`](FROZEN.md), all in the state `draft`. All seven are proved in the library from two
inputs with constants chosen before the law that are not yet proved
(`Ch05/Sec04/FrozenFromInputs.lean`): Proposition 3.21 (`UniformGaussianCorrectorRate`) and the
single-slope estimate of Lemma 4.21 on the classes of the laws with the linear estimate at an
exponent above the construction exponent (`UniformLinearSlopeEstimates`). The theorems are
`averagedCorrectorGradient_of_rate_slope` (E1), `blockBoundary_of_rate_slope` (E2),
`blockChange_of_rate_slope` (E3), `blockCLT_of_rate_slope` (E4),
`coarsenedCoefficientEstimates_of_rate_slope` (E5, through (5.58)), `localizedEnergy_of_rate_slope`
(E6) and `negativeSobolevCorrector_of_rate_slope` (E7). The heat identity (H) and the existence of
homogenization data enter through `exists_heatPathwiseKernel` and `homogenizationDataExists`.

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
- CoarseGraining at `310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be`.
- HighContrastHomogenization at `7a13dbcd8d6609264a713373f5c69ceeac870472`.
- EllipticRegularityLean at `1e29da02bcc6e3c2359a5b8e0559e76d02ec4002`.
- subdiffusive-process at `4c6b8fa60357a07fd5713e5104a6cc70f8e432dc`, which brings
  [MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess) at
  `666cda029098a1106914fc9fa7abd1727573284a`.

The continuous-integration workflow ([`.github/workflows/build.yml`](.github/workflows/build.yml))
builds the library, rejects any warning, runs
[`scripts/check_frozen.py`](scripts/check_frozen.py), which rejects `axiom`, `admit`,
`native_decide`, `unsafe` and similar tokens and any change to a frozen statement or to a definition
it uses, and compiles
[`QuantitativeStochasticHomogenization/Meta/AxiomsAudit.lean`](QuantitativeStochasticHomogenization/Meta/AxiomsAudit.lean),
which fails when a declaration of the library uses an axiom other than `propext`, `Classical.choice`
and `Quot.sound`.

## Repository layout

```text
QuantitativeStochasticHomogenization.lean   the root module, importing every module below
QuantitativeStochasticHomogenization/       namespace QSH
  Front/                 the chapters "Assumptions and Examples" and "Notation"
  Ch01/ ... Ch11/        one directory per chapter, one module per section (Sec01..., Sec02..., ...)
  Ch04/Opening.lean      the text of Chapter 4 before Section 4.1 (it states Theorem 4.1)
  AppA/ ... AppE/        one module per appendix
  Frozen/                statements frozen for the formalization of the Einstein relation
  Meta/AxiomsAudit.lean  the axiom audit, compiled by `lake build`, not imported by the root
scripts/                 the frozen-statement checker and the warning checker
ROADMAP.md               every numbered result of the book, with its status
FROZEN.md                the frozen statements, with their hashes
CORRESPONDENCE.md        where the Lean proofs depart from the book
```

## How this was built

The Lean code is written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT),
under the direction of the author. Every proof is checked by the Lean kernel.

## Authors and citation

The Lean formalization is by **Ahmed Bou-Rabee**. To cite it, use [`CITATION.cff`](CITATION.cff).

## Licence

No licence has been chosen for this repository yet.
