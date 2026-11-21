# Correspondence with the book

This file records where the Lean development departs from the book (Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Springer, 2019): a result
proved by a route different from the proof in the book, a hypothesis that the book leaves implicit
and the statement makes explicit, a measurability, integrability or summability fact that the
book takes for granted, and any other difference between a statement of the book and its Lean
form. Each entry names the numbered result of the book and the Lean declaration.

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
