import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouville
import QuantitativeStochasticHomogenization.Ch04.Sec01EnergyQuantityJ1

/-!
# `J₁` as a supremum over corrected affine functions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, (4.8): by the first-order Liouville theorem, the supremum defining `J₁(Ψ, p, q)` over
`A₁` is a supremum over the `d`-dimensional space of corrected affine gradients
`p' + ∑ᵢ p'ᵢ ∇φ_{eᵢ}`, for every mask `Ψ` and all loads `p, q`, almost surely.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The objective of `J₁(Ψ, p, q)`, (4.8), at the corrected affine gradient of slope `c`. -/
def J1Objective {Λ : ℝ} {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q c : Vec d) : ℝ :=
  ∫ x, mask x * (-(1 / 2 : ℝ) * dot (correctedAffineGrad S a c x)
      ((a x).mulVec (correctedAffineGrad S a c x)) -
    dot p ((a x).mulVec (correctedAffineGrad S a c x)) + dot q (correctedAffineGrad S a c x))

/-- **`J₁` over corrected affine functions.** If every element of `A₁` has a corrected affine
gradient almost surely (Theorem 3.8 for `k = 1`), then almost surely, for every mask and all
loads, `J₁(Ψ, p, q)` is the supremum of its objective over the corrected affine gradients. -/
theorem ae_J1_eq_sSup_range_J1Objective {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P)
    (hL : ∀ᵐ a ∂P, ∀ w : HarmonicA1 a, ∃ c : Vec d,
      ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = correctedAffineGrad S a c x) :
    ∀ᵐ a ∂P, ∀ (mask : Vec d → ℝ) (p q : Vec d),
      J1 a mask p q = sSup (Set.range (J1Objective S a mask p q)) := by
  filter_upwards [hL, ae_exists_harmonicA1_correctedAffine S] with a hcl hex
  intro mask p q
  unfold J1
  congr 1
  ext e
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨c, hc⟩ := hcl w
    refine ⟨c, ?_⟩
    unfold J1Objective
    refine integral_congr_ae ?_
    filter_upwards [hc] with x hx
    rw [hx]
  · rintro ⟨c, rfl⟩
    obtain ⟨w, -, hw⟩ := hex c
    refine ⟨w, ?_⟩
    unfold J1Objective
    rw [hw]

/-- **`J₁` over corrected affine functions, from the first-order Liouville theorem.** -/
theorem ae_J1_eq_sSup_range_J1Objective_of_liouville (hL : firstOrderLiouvilleStatement)
    (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (mask : Vec d → ℝ) (p q : Vec d),
      J1 a mask p q = sSup (Set.range (J1Objective S a mask p q)) := by
  refine ae_J1_eq_sSup_range_J1Objective S ?_
  filter_upwards [hL d hd Λ hΛ P hP S] with a ha w
  obtain ⟨-, c, -, hc⟩ := ha w
  exact ⟨c, hc⟩

end QSH
