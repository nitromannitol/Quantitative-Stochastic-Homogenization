import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouville
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectorIndependence

/-!
# The dimension of `A₁`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 3.8 for `k = 1`, (3.39): under the first-order Liouville theorem, almost surely the
gradients of the elements of `A₁` are exactly the corrected affine gradients
`p + ∑ᵢ pᵢ ∇φ_{eᵢ}`, each with a unique slope `p`; so the space of gradients of `A₁` has
dimension `d`, and `A₁` has dimension `d + 1`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

theorem correctedAffineGrad_sub {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (c₁ c₂ x : Vec d) :
    correctedAffineGrad S a (c₁ - c₂) x = correctedAffineGrad S a c₁ x - correctedAffineGrad S a c₂ x := by
  simp only [correctedAffineGrad, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  abel

/-- **`dim A₁ = d + 1`.** Under the first-order Liouville theorem, almost surely every element
of `A₁` has a corrected affine gradient with a unique slope, and every corrected affine function
is an element of `A₁`. -/
theorem ae_gradients_harmonicA1 (hL : firstOrderLiouvilleStatement) (hd : 2 ≤ d) {Λ : ℝ}
    (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, (∀ w : HarmonicA1 a, ∃! c : Vec d,
        ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a c x) ∧
      ∀ c : Vec d, ∃ w : HarmonicA1 a,
        w.potential = correctedAffine S a c ∧ w.grad = correctedAffineGrad S a c := by
  filter_upwards [hL d hd Λ hΛ P hP S, ae_exists_harmonicA1_correctedAffine S,
    ae_eq_zero_of_correctedAffineGrad_ae_eq_zero S] with a hcl hex hind
  refine ⟨fun w => ?_, hex⟩
  obtain ⟨-, c, -, hc⟩ := hcl w
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have h0 : ∀ᵐ x ∂(volume : Measure (Vec d)), correctedAffineGrad S a (c' - c) x = 0 := by
    filter_upwards [hc, hc'] with x hx hx'
    rw [correctedAffineGrad_sub, ← hx, ← hx', sub_self]
  exact sub_eq_zero.mp (hind (c' - c) h0)

end QSH
