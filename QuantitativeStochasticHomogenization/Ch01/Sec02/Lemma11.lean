import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletMinimizer
import QuantitativeStochasticHomogenization.Ch01.Sec03.ParallelogramQuadratic

/-!
# Lemma 1.1: basic properties of `μ`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.2, Lemma 1.1, (1.9)–(1.13).

* `coarseMatrix a U`: the symmetric matrix `a(U)` of (1.10), `a(U)_{ij} = 2B(e_i, e_j)` for the
  polarization `B` of `p ↦ μ(U, p)`; `dirichletEnergy_eq_coarseMatrix` is (1.10) and
  `coarseMatrix_bounds` is (1.9). The book obtains the quadratic form from the linearity (1.15)
  of the minimizer; here it comes from the parallelogram identity `dirichletEnergy_parallelogram`.
* `lemma_1_1`: the four properties of the lemma, for a bounded set `U` of positive measure: the
  representation as a quadratic form, the subadditivity (1.11) for partitions by disjoint open
  sets, the first variation (existence, uniqueness and the characterization of the minimizer by
  (1.12)) and the quadratic response (1.13).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The matrix of a quadratic form -/

/-- The matrix `A_{ij} = 2 B(e_i, e_j)` of the polarization `B` of `L`. -/
def polarizationMatrix (L : Vec d → ℝ) : Mat d :=
  Matrix.of fun i j => 2 * polarization L (unitVector i) (unitVector j)

section Parallelogram

variable {L : Vec d → ℝ} (hL : ∀ x y, L (x + y) + L (x - y) = 2 * L x + 2 * L y)
include hL

theorem polarizationMatrix_transpose : (polarizationMatrix L).transpose = polarizationMatrix L := by
  ext i j
  simp only [polarizationMatrix, Matrix.transpose_apply, Matrix.of_apply]
  rw [polarization_comm hL]

/-- `L(x) = ½ x·Ax` for the polarization matrix `A` of a function with the parallelogram identity
and a quadratic bound. -/
theorem eq_half_dot_polarizationMatrix {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |L x| ≤ M * euclideanSq x)
    (x : Vec d) : L x = (1 / 2 : ℝ) * dot x ((polarizationMatrix L).mulVec x) := by
  rw [← polarization_self hL x, polarization_sum_left hL hM0 hM x x]
  simp only [dot, Matrix.mulVec, dotProduct, polarizationMatrix, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polarization_comm hL, polarization_sum_left hL hM0 hM x (unitVector i)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polarization_comm hL]
  ring

end Parallelogram

theorem one_le_of_coefficientField [NeZero d] (a : CoefficientField d Λ) : 1 ≤ Λ := by
  have h := a.elliptic 0 (unitVector 0)
  have h1 : euclideanSq (unitVector (0 : Fin d)) = 1 := by
    simp [euclideanSq, dot, unitVector, Pi.single_apply]
  rw [h1] at h
  linarith [h.1, h.2]

/-! ## The matrix `a(U)` -/

/-- **The coarse-grained matrix `a(U)`** of (1.10). -/
def coarseMatrix (a : CoefficientField d Λ) (U : Set (Vec d)) : Mat d :=
  polarizationMatrix (dirichletEnergy a U)

theorem abs_dirichletEnergy_le (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (e : Vec d) :
    |dirichletEnergy a U e| ≤ (1 / 2 * Λ) * euclideanSq e := by
  rw [abs_of_nonneg (dirichletEnergy_nonneg a U e)]
  exact dirichletEnergy_le a hU0 hU hΛ e

theorem coarseMatrix_transpose (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤) :
    (coarseMatrix a U).transpose = coarseMatrix a U :=
  polarizationMatrix_transpose (dirichletEnergy_parallelogram a hU)

/-- **(1.10)**: `μ(U, p) = ½ p·a(U)p`. -/
theorem dirichletEnergy_eq_coarseMatrix (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (e : Vec d) :
    dirichletEnergy a U e = (1 / 2 : ℝ) * dot e ((coarseMatrix a U).mulVec e) :=
  eq_half_dot_polarizationMatrix (dirichletEnergy_parallelogram a hU) (by positivity)
    (abs_dirichletEnergy_le a hU0 hU hΛ) e

/-- **(1.9)**: `Id ≤ a(U) ≤ Λ Id`. -/
theorem coarseMatrix_bounds (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (e : Vec d) :
    euclideanSq e ≤ dot e ((coarseMatrix a U).mulVec e) ∧
      dot e ((coarseMatrix a U).mulVec e) ≤ Λ * euclideanSq e := by
  have h := dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ e
  have h1 := le_dirichletEnergy a hU0 hU e
  have h2 := dirichletEnergy_le a hU0 hU hΛ e
  constructor <;> linarith

/-! ## Lemma 1.1 -/

/-- **Lemma 1.1 (Basic properties of `μ`).** For a bounded set `U ⊆ ℝ^d` of positive measure:

* *representation as a quadratic form*: `a(U)` is symmetric, `Id ≤ a(U) ≤ Λ Id` (1.9) and
  `μ(U, p) = ½ p·a(U)p` (1.10);
* *subadditivity* (1.11): for open, pairwise disjoint `U₁, …, U_N ⊆ U` with
  `|U \ ⋃ Uᵢ| = 0`, `μ(U, p) ≤ ∑ᵢ |Uᵢ|/|U| μ(Uᵢ, p)`;
* *first variation*: the minimizer `v(·, U, p) = ℓ_p + u` of (1.8) exists, is unique up to null
  sets, and the minimizers are exactly the solutions of (1.12);
* *quadratic response* (1.13): for `w ∈ H¹₀(U)` of weak gradient `h`,
  `½ ⨍_U |h - g|² ≤ ⨍_U ½ (p + h)·a(p + h) - μ(U, p) ≤ ½Λ ⨍_U |h - g|²`. -/
theorem lemma_1_1 [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (hU0 : volume U ≠ 0) :
    ((coarseMatrix a U).transpose = coarseMatrix a U ∧
      (∀ p : Vec d, euclideanSq p ≤ dot p ((coarseMatrix a U).mulVec p) ∧
        dot p ((coarseMatrix a U).mulVec p) ≤ Λ * euclideanSq p) ∧
      ∀ p : Vec d, dirichletEnergy a U p = (1 / 2 : ℝ) * dot p ((coarseMatrix a U).mulVec p)) ∧
    (∀ (ι : Type) [Fintype ι] (Q : ι → Set (Vec d)), (∀ k, IsOpen (Q k)) →
      Pairwise (Function.onFun Disjoint Q) → (∀ k, Q k ⊆ U) → volume (U \ ⋃ k, Q k) = 0 →
      ∀ p : Vec d, dirichletEnergy a U p ≤
        ∑ k, (volume.real (Q k) / volume.real U) * dirichletEnergy a (Q k) p) ∧
    (∀ p : Vec d, (∃ (u : Vec d → ℝ) (g : Vec d → Vec d), IsDirichletMinimizer a U p u g) ∧
      (∀ (u₁ u₂ : Vec d → ℝ) (g₁ g₂ : Vec d → Vec d), IsDirichletMinimizer a U p u₁ g₁ →
        IsDirichletMinimizer a U p u₂ g₂ →
        g₁ =ᵐ[volume.restrict U] g₂ ∧ u₁ =ᵐ[volume.restrict U] u₂) ∧
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        IsDirichletMinimizer a U p u g ↔ SolvesDirichletProblem a U p u g) ∧
    (∀ (p : Vec d) (u w : Vec d → ℝ) (g h : Vec d → Vec d), IsDirichletMinimizer a U p u g →
      H01 U w h →
      (1 / 2 : ℝ) * ⨍ x in U, euclideanSq (h x - g x) ≤
          trialEnergy a U p h - dirichletEnergy a U p ∧
        trialEnergy a U p h - dirichletEnergy a U p ≤
          Λ / 2 * ⨍ x in U, euclideanSq (h x - g x)) := by
  have hUt : volume U ≠ ⊤ := hU.measure_lt_top.ne
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  refine ⟨⟨coarseMatrix_transpose a hUt, coarseMatrix_bounds a hU0 hUt hΛ,
    dirichletEnergy_eq_coarseMatrix a hU0 hUt hΛ⟩, ?_, fun p => ⟨exists_isDirichletMinimizer a hU hU0 p,
    fun u₁ u₂ g₁ g₂ h₁ h₂ => h₁.ae_eq hU h₂, isDirichletMinimizer_iff_solvesDirichletProblem a hUt p⟩,
    fun p u w g h hmin hw => hmin.quadraticResponse hUt hw⟩
  intro ι _ Q hQo hdisj hsub hcover p
  exact dirichletEnergy_le_sum_of_partition a hUt hQo hdisj hsub hcover p

end QSH
