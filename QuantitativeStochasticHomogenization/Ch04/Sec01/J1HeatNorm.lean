import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatFormula
import HCPoly.Setup.SpectralBound

/-!
# `J₁` as half a squared norm

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1: `J₁(Φ_{z,r}, p, q) = ½ ‖-V*p + U*q‖²`. In the basis of corrector columns
`Wᵢ = eᵢ + ∇φ_{eᵢ}` of the gradients of `A₁`, with Gram matrix `G` of the inner product
`∫ Φ_{z,r} v · a w` and load `b`, `bᵢ = ∫ Φ_{z,r} (-p · a Wᵢ + q · Wᵢ)`, the closed form
`J₁ = ½ b · G⁻¹ b` is `½ |G^{-1/2} b|²`, with `G^{-1/2}` the positive semidefinite square root of
the positive semidefinite matrix `G⁻¹`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **`J₁ = ½ ‖-V*p + U*q‖²`**, from the first-order Liouville theorem. -/
theorem ae_J1Heat_eq_half_euclideanSq (hL : firstOrderLiouvilleStatement) (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ p q : Vec d,
      J1Heat a z r p q = (1 / 2 : ℝ) * euclideanSq
        ((_root_.Homogenization.HighContrast.matSqrt (J1Gram S a (heatKernel z r))⁻¹).mulVec
          (J1Load S a (heatKernel z r) p q)) := by
  filter_upwards [ae_J1Heat_eq_half_dot_inv hL hd hΛ hP S,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S] with a hJ hW
  intro z r hr p q
  obtain ⟨-, hJ'⟩ := hJ z r hr p q
  rw [hJ']
  obtain ⟨hM, -⟩ := integrable_heatKernel_gram_load S a z hr (fun i => hW i z r hr) p q
  have hkn : ∀ x, 0 ≤ heatKernel z r x := fun x =>
    euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hGpsd : (J1Gram S a (heatKernel z r)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun c => ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact J1Gram_transpose S a _
    · rw [star_trivial]
      exact J1Gram_nonneg S a _ hkn hM c
  obtain ⟨hTpsd, hTT⟩ := _root_.Homogenization.HighContrast.matSqrt_spec hGpsd.inv
  have hTt : (_root_.Homogenization.HighContrast.matSqrt (J1Gram S a (heatKernel z r))⁻¹).transpose =
      _root_.Homogenization.HighContrast.matSqrt (J1Gram S a (heatKernel z r))⁻¹ := by
    have h := hTpsd.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  congr 1
  conv_lhs => rw [← hTT, ← Matrix.mulVec_mulVec]
  change dotProduct _ (Matrix.mulVec _ (Matrix.mulVec _ _)) =
    dotProduct (Matrix.mulVec _ _) (Matrix.mulVec _ _)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hTt]

end QSH
