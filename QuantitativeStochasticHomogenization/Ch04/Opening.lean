import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Chapter 4, opening: Quantitative Description of First-Order Correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 4, the text before Section 4.1. Numbered results: Theorem 4.1.

Defined here: the heat kernel masks `Φ_{z,r}` of (4.1).
-/

noncomputable section

namespace QSH

/-- The heat kernel `(4πt)^{-d/2} exp(-|x|²/(4t))`. -/
def euclideanHeatKernel {d : ℕ} (t : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq x) / (4 * t))

/-- **The mask `Φ_{z,r}`**, (4.1): `Φ_{z,r}(x) = Φ(r², x - z)`. -/
def heatKernel {d : ℕ} (z : Vec d) (r : ℝ) (x : Vec d) : ℝ :=
  euclideanHeatKernel (r ^ 2) (x - z)

end QSH
