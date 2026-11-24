import QuantitativeStochasticHomogenization.Front.Notation

/-!
# The normalized `Ĥ⁻¹(U)` norm

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the notation (0.26) and (0.31).

* `H1 U u g`: `u ∈ H¹(U)` with weak gradient `g`, both in `L²(U)`;
* `h1Norm U u g`: the normalized norm `‖u‖_{H̲¹(U)} = |U|^{-1/d} ‖u‖_{L̲²(U)} + ‖∇u‖_{L̲²(U)}`
  of (0.26);
* `hatNegativeSobolevNorm U f`: the normalized norm of (0.31) of the dual space `Ĥ⁻¹(U)` of
  `H¹(U)`, `‖f‖_{Ĥ̲⁻¹(U)} = sup {⨍_U f v : v ∈ H¹(U), ‖v‖_{H̲¹(U)} ≤ 1}`, with values in `[0, ∞]`;
* `vectorHatNegativeSobolevNorm U F`: the sum of the `Ĥ⁻¹(U)` norms of the components of a
  vector field, as `vectorNegativeIntegerSobolevNorm` for (0.29).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `u ∈ H¹(U)` with weak gradient `g`: `u` and `g` are in `L²(U)` and `∇u = g` weakly in `U`. -/
def H1 (U : Set (Vec d)) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp g 2 (volume.restrict U) ∧ HasWeakGradient U u g

/-- The normalized `H¹(U)` norm `|U|^{-1/d} ‖u‖_{L̲²(U)} + ‖∇u‖_{L̲²(U)}`, (0.26). -/
def h1Norm (U : Set (Vec d)) (u : Vec d → ℝ) (g : Vec d → Vec d) : ℝ :=
  (volume U).toReal ^ ((-1 : ℝ) / d) * scalarRms volume U u + vectorRms volume U g

/-- **The normalized `Ĥ⁻¹(U)` norm** of (0.31): the norm of `v ↦ ⨍_U f v` on the unit ball of
`H¹(U)` for the normalized norm (0.26). -/
def hatNegativeSobolevNorm (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ v : {v : (Vec d → ℝ) × (Vec d → Vec d) // H1 U v.1 v.2 ∧ h1Norm U v.1 v.2 ≤ 1},
    ENNReal.ofReal |⨍ x in U, f x * v.1.1 x ∂volume|

/-- The sum of the `Ĥ⁻¹(U)` norms of the components of a vector field. -/
def vectorHatNegativeSobolevNorm (U : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ j : Fin d, hatNegativeSobolevNorm U (fun x => F x j)

/-- A bound of the pairings with the unit ball of `H¹(U)` bounds the `Ĥ⁻¹(U)` norm. -/
theorem hatNegativeSobolevNorm_le_ofReal {U : Set (Vec d)} {f : Vec d → ℝ} {B : ℝ}
    (h : ∀ (v : Vec d → ℝ) (g : Vec d → Vec d), H1 U v g → h1Norm U v g ≤ 1 →
      |⨍ x in U, f x * v x ∂volume| ≤ B) :
    hatNegativeSobolevNorm U f ≤ ENNReal.ofReal B :=
  iSup_le fun v => ENNReal.ofReal_le_ofReal (h v.1.1 v.1.2 v.2.1 v.2.2)

end QSH
