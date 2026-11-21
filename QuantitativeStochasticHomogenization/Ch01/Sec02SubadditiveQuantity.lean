import QuantitativeStochasticHomogenization.Front.Assumptions

/-!
# Section 1.2: The Subadditive Quantity μ and Its Basic Properties

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 1 (Introduction and Qualitative Theory), Section 1.2. Numbered results of this section:
Lemma 1.1.

Defined here: `H¹₀(U)` and the Dirichlet energy `μ(U, e)` of (1.7).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

/-- `u ∈ H¹₀(U)` with weak gradient `g`, as used in (1.7). -/
def H01 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp g 2 (volume.restrict U) ∧
    HasWeakGradient U u g ∧
    ∃ v : ℕ → Vec d → ℝ, (∀ n, IsSpatialTest U (v n)) ∧
      Tendsto (fun n => ∫ x in U, (v n x - u x) ^ 2 ∂volume) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in U, euclideanSq (gradient (v n) x - g x) ∂volume) atTop (𝓝 0)

/-- **The Dirichlet energy `μ(U, e)`**, (1.7). -/
def dirichletEnergy {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (U : Set (Vec d)) (e : Vec d) :
    ℝ :=
  sInf {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), H01 U u g ∧
    E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume}

end QSH
