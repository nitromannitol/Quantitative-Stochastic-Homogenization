import QuantitativeStochasticHomogenization.Ch04.Sec01.BaseExponent
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyBounds

/-!
# The bounds `I ≤ ā ≤ Λ I`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Definition 1.2 and (1.22): the homogenized matrix satisfies `|ξ|² ≤ ξ·āξ ≤ Λ|ξ|²`.

`homogenizedMatrixBounds_of_integrable`: for a homogenization datum `S`, the bounds
`HomogenizedMatrixBounds S.homogenized Λ` used in Propositions 4.3 and 4.10 follow from the bounds
`½|ξ|² ≤ μ(□ₙ, ξ) ≤ ½Λ|ξ|²` of the Dirichlet energy and the limit (1.22), provided the Dirichlet
energies `a ↦ μ(□ₙ, ξ)` are integrable (the limit (1.22) is stated with Bochner integrals).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem volume_triadicCube_ne_zero (d n : ℕ) : volume (triadicCube d n) ≠ 0 := by
  rw [triadicCube, Real.volume_pi_Ioo, Finset.prod_ne_zero_iff]
  intro i _
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  have : (0 : ℝ) < 3 ^ n := by positivity
  linarith

theorem volume_triadicCube_ne_top (d n : ℕ) : volume (triadicCube d n) ≠ ⊤ := by
  rw [triadicCube, Real.volume_pi_Ioo]
  exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top

/-- **`I ≤ ā ≤ Λ I`** for a homogenization datum, from the bounds on the Dirichlet energy and
(1.22), given the integrability of the Dirichlet energies on the triadic cubes. -/
theorem homogenizedMatrixBounds_of_integrable {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (S : HomogenizationData P) (hΛ : 0 ≤ Λ)
    (hint : ∀ (n : ℕ) (ξ : Vec d),
      Integrable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P) :
    HomogenizedMatrixBounds S.homogenized Λ := by
  intro ξ
  have hlim := S.variational_limit ξ
  have hlow : ∀ n : ℕ, (1 / 2 : ℝ) * euclideanSq ξ ≤
      ∫ a, dirichletEnergy a (triadicCube d n) ξ ∂P := by
    intro n
    have h := integral_mono (integrable_const ((1 / 2 : ℝ) * euclideanSq ξ)) (hint n ξ)
      fun a => le_dirichletEnergy a (volume_triadicCube_ne_zero d n)
        (volume_triadicCube_ne_top d n) ξ
    simpa using h
  have hup : ∀ n : ℕ, ∫ a, dirichletEnergy a (triadicCube d n) ξ ∂P ≤
      (1 / 2 : ℝ) * Λ * euclideanSq ξ := by
    intro n
    have h := integral_mono (hint n ξ) (integrable_const ((1 / 2 : ℝ) * Λ * euclideanSq ξ))
      fun a => dirichletEnergy_le a (volume_triadicCube_ne_zero d n)
        (volume_triadicCube_ne_top d n) hΛ ξ
    simpa using h
  have h1 := ge_of_tendsto' hlim hlow
  have h2 := le_of_tendsto' hlim hup
  constructor <;> linarith

end QSH
