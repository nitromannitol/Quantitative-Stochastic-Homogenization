import Lake
open Lake DSL

package QuantitativeStochasticHomogenization

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

-- The coarse-graining library of Armstrong and Kuusi (library name `Homogenization`).
require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be"

-- Homogenization at a polynomial scale in high contrast (Armstrong, Kuusi, Loher): non-isotropic
-- quantitative homogenization, first-order correctors, Liouville theorem, large-scale regularity.
require «HighContrastHomogenization» from git
  "https://github.com/scottnarmstrong/HighContrastHomogenization" @ "7a13dbcd8d6609264a713373f5c69ceeac870472"

-- De Giorgi–Nash–Moser, Harnack, parabolic Caccioppoli, Nash–Aronson, Schauder.
require «elliptic_regularity» from git
  "https://github.com/scottnarmstrong/EllipticRegularityLean" @ "1e29da02bcc6e3c2359a5b8e0559e76d02ec4002"

-- Reversible diffusion `a⁻¹ ∇·(a ∇)` in a random environment (Armstrong, Bou-Rabee, Kuusi).
require SubdiffusiveProcess from git
  "https://github.com/nitromannitol/subdiffusive-process" @ "4c6b8fa60357a07fd5713e5104a6cc70f8e432dc"

-- The root module and every module under `QuantitativeStochasticHomogenization/`.
@[default_target]
lean_lib QuantitativeStochasticHomogenization where
  globs := #[.andSubmodules `QuantitativeStochasticHomogenization]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
