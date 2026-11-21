import QuantitativeStochasticHomogenization.Ch01.Sec02SubadditiveQuantity

/-!
# Section 3.4: The First-Order Correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 3 (Regularity on Large Scales), Section 3.4. Numbered results of this section: Proposition
3.21; Lemmas 3.16, 3.17, 3.22, 3.23; Definitions 3.14, 3.15.

Defined here: first-order correctors (Definitions 3.14-3.15, Lemma 3.16) and the homogenized
matrix characterized by Definition 1.2 and (1.22).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

/-- **A first-order corrector `φ_e`**, Definitions 3.14-3.15 and Lemma 3.16: a stationary
locally `H¹` potential with `-∇·a(e + ∇φ_e) = 0` and sublinear `L²` oscillation. -/
structure Corrector {d : ℕ} {Λ : ℝ} (P : Measure (CoefficientField d Λ)) (e : Vec d) where
  potential : CoefficientField d Λ → Vec d → ℝ
  grad : CoefficientField d Λ → Vec d → Vec d
  measurable_grad : Measurable (fun p : CoefficientField d Λ × Vec d => grad p.1 p.2)
  weak_gradient : ∀ᵐ a ∂P, HasWeakGradient Set.univ (potential a) (grad a)
  locally_square_integrable : ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R →
    MemLp (potential a) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (grad a) 2 (volume.restrict (ball 0 R))
  stationary : ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
    grad a (x + latticeShift z) = grad (translate (latticeShift z) a) x
  harmonic : ∀ᵐ a ∂P,
    HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + grad a x)) (fun _ => 0)
  sublinear : ∀ᵐ a ∂P, Tendsto
    (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (potential a x - ⨍ y in ball 0 R, potential a y ∂volume) ^ 2 ∂volume))
    atTop (𝓝 0)

/-- **Correctors and the homogenized matrix `ā`**: correctors in every direction and the
symmetric matrix of Definition 1.2 with the limit (1.22). -/
structure HomogenizationData {d : ℕ} {Λ : ℝ} (P : Measure (CoefficientField d Λ)) where
  corrector : ∀ e : Vec d, Corrector P e
  homogenized : Mat d
  symmetric : homogenized.transpose = homogenized
  variational_limit : ∀ e : Vec d,
    Tendsto (fun n : ℕ => ∫ a, dirichletEnergy a (triadicCube d n) e ∂P)
      atTop (𝓝 ((1 / 2 : ℝ) * dot e (homogenized.mulVec e)))

end QSH
