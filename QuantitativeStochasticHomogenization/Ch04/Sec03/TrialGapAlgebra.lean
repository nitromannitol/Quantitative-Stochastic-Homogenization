import QuantitativeStochasticHomogenization.Ch04.Sec03.Proposition410

/-!
# The quadratic structure of `J₁` on a linear family of gradients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, (4.12)–(4.16), in the form used by the proof of Proposition 4.10.

For a family `G ξ = ∑ ξᵢ Wᵢ` of gradient fields whose `Ψ`-averages are integrable, the functional
of (4.8) at `G ξ` is the quadratic polynomial `-½ ξ·Aξ + l·ξ`, with the energy matrix
`A_{ij} = ∫ Ψ Wᵢ·aWⱼ` and the load `l_j = -p·∫ Ψ aWⱼ + q·∫ Ψ Wⱼ` (`j1Functional_fieldOf`). If the
gradients of `A₁` are exactly the fields `G ξ` and `A` is positive definite, then
`J₁(Ψ, p, q) = ½ l·A⁻¹l`, attained at `c = A⁻¹l`, and for every slope `k` the gap to the trial is
`J₁(Ψ, p, q) - L(k) = ½ (k - c)·A(k - c)` (`J1_sub_j1Functional_fieldOf`). The averaged gradient
`∫ Ψ G c` of the maximizer is the derivative of `J₁` in `q`:
`h·∫ Ψ G c = J₁(Ψ, p, q + h) - J₁(Ψ, p, q) - J₁(Ψ, 0, h)` ((4.16), (4.21);
`dot_integral_fieldOf_maximizer`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Linear families -/

/-- The field `G ξ = ∑ ξᵢ Wᵢ`. -/
def fieldOf (W : Fin d → Vec d → Vec d) (ξ : Vec d) (x : Vec d) : Vec d := ∑ i, ξ i • W i x

theorem correctedField_eq_fieldOf {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) : correctedField S a = fieldOf (correctedCoordinate S a) := rfl

/-- The energy matrix `A_{ij} = ∫ Ψ Wᵢ·aWⱼ`. -/
def energyMatrix (a : CoefficientField d Λ) (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d) :
    Mat d :=
  Matrix.of fun i j => ∫ x, mask x * dot (W i x) ((a x).mulVec (W j x))

/-- The load `l_j = -p·∫ Ψ aWⱼ + q·∫ Ψ Wⱼ`. -/
def loadVector (a : CoefficientField d Λ) (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (p q : Vec d) : Vec d :=
  fun j => -dot p (∫ x, mask x • (a x).mulVec (W j x)) + dot q (∫ x, mask x • W j x)

/-- The `Ψ`-averages of the gradients, fluxes and energy densities of the family are integrable. -/
structure IntegrableFamily (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) : Prop where
  grad : ∀ i, Integrable fun x => mask x • W i x
  flux : ∀ i, Integrable fun x => mask x • (a x).mulVec (W i x)
  energy : ∀ i j, Integrable fun x => mask x * dot (W i x) ((a x).mulVec (W j x))

theorem dot_fieldOf (W : Fin d → Vec d → Vec d) (q ξ x : Vec d) :
    dot q (fieldOf W ξ x) = ∑ j, ξ j * dot q (W j x) := by
  simp only [fieldOf, dot_eq_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem dot_mulVec_fieldOf (W : Fin d → Vec d → Vec d) (M : Mat d) (p ξ x : Vec d) :
    dot p (M.mulVec (fieldOf W ξ x)) = ∑ j, ξ j * dot p (M.mulVec (W j x)) := by
  simp only [fieldOf, dot_eq_dotProduct, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum,
    dotProduct_smul, smul_eq_mul]

theorem dot_fieldOf_mulVec_fieldOf (W : Fin d → Vec d → Vec d) (M : Mat d) (ξ x : Vec d) :
    dot (fieldOf W ξ x) (M.mulVec (fieldOf W ξ x)) =
      ∑ i, ∑ j, ξ i * ξ j * dot (W i x) (M.mulVec (W j x)) := by
  have h : ∀ i, dot (ξ i • W i x) (M.mulVec (fieldOf W ξ x)) =
      ∑ j, ξ i * ξ j * dot (W i x) (M.mulVec (W j x)) := by
    intro i
    rw [dot_eq_dotProduct, smul_dotProduct, ← dot_eq_dotProduct, dot_mulVec_fieldOf, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [fieldOf, dot_eq_dotProduct, sum_dotProduct] at h ⊢
  exact Finset.sum_congr rfl fun i _ => h i

theorem dot_mulVec_eq_sum (A : Mat d) (ξ : Vec d) :
    dot ξ (A.mulVec ξ) = ∑ i, ∑ j, ξ i * ξ j * A i j := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dot_eq_sum (l ξ : Vec d) : dot l ξ = ∑ j, ξ j * l j := by
  simp only [dot]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The functional of (4.8) on the family is quadratic**: `L(ξ) = -½ ξ·Aξ + l·ξ`. -/
theorem j1Functional_fieldOf (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : IntegrableFamily a mask W) (p q ξ : Vec d) :
    j1Functional a mask p q (fieldOf W ξ) =
      -(1 / 2 : ℝ) * dot ξ ((energyMatrix a mask W).mulVec ξ) +
        dot (loadVector a mask W p q) ξ := by
  have hpt : (fun x => mask x * (-(1 / 2 : ℝ) * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x)) -
      dot p ((a x).mulVec (fieldOf W ξ x)) + dot q (fieldOf W ξ x))) =
      fun x => (-(1 / 2 : ℝ) * ∑ i, ∑ j, ξ i * ξ j *
          (mask x * dot (W i x) ((a x).mulVec (W j x))) -
        ∑ j, ξ j * dot p (mask x • (a x).mulVec (W j x))) +
        ∑ j, ξ j * dot q (mask x • W j x) := by
    funext x
    rw [dot_fieldOf_mulVec_fieldOf, dot_mulVec_fieldOf, dot_fieldOf]
    simp only [dot_eq_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    have e1 : ∀ i j, mask x * (-(1 / 2 : ℝ) * (ξ i * ξ j * (W i x ⬝ᵥ (a x).mulVec (W j x)))) =
        -(1 / 2 : ℝ) * (ξ i * ξ j * (mask x * (W i x ⬝ᵥ (a x).mulVec (W j x)))) := fun i j => by
      ring
    have e2 : ∀ j, mask x * (ξ j * (p ⬝ᵥ (a x).mulVec (W j x))) =
        ξ j * (mask x * (p ⬝ᵥ (a x).mulVec (W j x))) := fun j => by ring
    have e3 : ∀ j, mask x * (ξ j * (q ⬝ᵥ W j x)) = ξ j * (mask x * (q ⬝ᵥ W j x)) := fun j => by
      ring
    rw [mul_add, mul_sub]
    simp only [Finset.mul_sum, e1, e2, e3]
  have hE : ∀ i j, Integrable fun x => ξ i * ξ j * (mask x * dot (W i x) ((a x).mulVec (W j x))) :=
    fun i j => (hW.energy i j).const_mul _
  have hEi : ∀ i, Integrable fun x => ∑ j, ξ i * ξ j *
      (mask x * dot (W i x) ((a x).mulVec (W j x))) :=
    fun i => integrable_finsetSum _ fun j _ => hE i j
  have hEs : Integrable fun x => ∑ i, ∑ j, ξ i * ξ j *
      (mask x * dot (W i x) ((a x).mulVec (W j x))) :=
    integrable_finsetSum _ fun i _ => hEi i
  have hF : ∀ j, Integrable fun x => ξ j * dot p (mask x • (a x).mulVec (W j x)) :=
    fun j => (integrable_dot_left p (hW.flux j)).const_mul _
  have hFs : Integrable fun x => ∑ j, ξ j * dot p (mask x • (a x).mulVec (W j x)) :=
    integrable_finsetSum _ fun j _ => hF j
  have hG : ∀ j, Integrable fun x => ξ j * dot q (mask x • W j x) :=
    fun j => (integrable_dot_left q (hW.grad j)).const_mul _
  have hGs : Integrable fun x => ∑ j, ξ j * dot q (mask x • W j x) :=
    integrable_finsetSum _ fun j _ => hG j
  have hI : Integrable fun x => -(1 / 2 : ℝ) * ∑ i, ∑ j, ξ i * ξ j *
      (mask x * dot (W i x) ((a x).mulVec (W j x))) -
        ∑ j, ξ j * dot p (mask x • (a x).mulVec (W j x)) := (hEs.const_mul _).sub hFs
  unfold j1Functional
  rw [hpt, integral_add hI hGs, integral_sub (hEs.const_mul _) hFs,
    integral_const_mul, integral_finsetSum _ fun i _ => hEi i, integral_finsetSum _ fun j _ => hF j,
    integral_finsetSum _ fun j _ => hG j, dot_mulVec_eq_sum, dot_eq_sum]
  have h1 : ∀ i, (∫ x, ∑ j, ξ i * ξ j * (mask x * dot (W i x) ((a x).mulVec (W j x)))) =
      ∑ j, ξ i * ξ j * energyMatrix a mask W i j := by
    intro i
    rw [integral_finsetSum _ fun j _ => hE i j]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]; rfl
  have h2 : ∀ j, (∫ x, ξ j * dot p (mask x • (a x).mulVec (W j x))) =
      ξ j * dot p (∫ x, mask x • (a x).mulVec (W j x)) := fun j => by
    rw [integral_const_mul, dot_integral p (hW.flux j)]
  have h3 : ∀ j, (∫ x, ξ j * dot q (mask x • W j x)) = ξ j * dot q (∫ x, mask x • W j x) :=
    fun j => by rw [integral_const_mul, dot_integral q (hW.grad j)]
  simp only [h1, h2, h3, loadVector]
  have h4 : ∑ j, ξ j * (-dot p (∫ x, mask x • (a x).mulVec (W j x)) +
      dot q (∫ x, mask x • W j x)) = ∑ j, ξ j * dot q (∫ x, mask x • W j x) -
        ∑ j, ξ j * dot p (∫ x, mask x • (a x).mulVec (W j x)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h4]
  ring

end QSH
