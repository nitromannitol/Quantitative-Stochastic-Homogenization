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

/-! ## The maximizer and the gap to a trial -/

theorem energyMatrix_transpose (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) : (energyMatrix a mask W).transpose = energyMatrix a mask W := by
  ext i j
  simp only [Matrix.transpose_apply, energyMatrix, Matrix.of_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [dot_mulVec_comm (a.symmetric x)]

theorem loadVector_add_right (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (p q h : Vec d) :
    loadVector a mask W p (q + h) = loadVector a mask W p q + loadVector a mask W 0 h := by
  funext j
  simp only [loadVector, Pi.add_apply, dot_eq_dotProduct, add_dotProduct, zero_dotProduct, neg_zero,
    zero_add]
  ring

/-- The maximizing slope `c = A⁻¹ l`. -/
def maximizerSlope (a : CoefficientField d Λ) (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (p q : Vec d) : Vec d :=
  (energyMatrix a mask W)⁻¹.mulVec (loadVector a mask W p q)

/-- Completing the square: `-½ ξ·Aξ + l·ξ = (-½ c·Ac + l·c) - ½ (ξ - c)·A(ξ - c)` for `c = A⁻¹l`. -/
theorem quadratic_eq_sub {A : Mat d} (hAsymm : A.transpose = A) (hA : IsUnit A.det)
    (l ξ : Vec d) :
    -(1 / 2 : ℝ) * dot ξ (A.mulVec ξ) + dot l ξ =
      (-(1 / 2 : ℝ) * dot (A⁻¹.mulVec l) (A.mulVec (A⁻¹.mulVec l)) + dot l (A⁻¹.mulVec l)) -
        (1 / 2 : ℝ) * dot (ξ - A⁻¹.mulVec l) (A.mulVec (ξ - A⁻¹.mulVec l)) := by
  set c := A⁻¹.mulVec l with hc
  have hy : A.mulVec c = l := mulVec_inv_mulVec hA l
  have hs := dot_mulVec_comm hAsymm ξ c
  rw [hy] at hs
  have hc1 : dot l ξ = dot ξ l := dotProduct_comm _ _
  simp only [Matrix.mulVec_sub, hy, dot_eq_dotProduct, sub_dotProduct, dotProduct_sub] at hs hc1 ⊢
  have hc2 : c ⬝ᵥ l = l ⬝ᵥ c := dotProduct_comm _ _
  linarith

theorem dot_inv_mulVec_comm {A : Mat d} (hAsymm : A.transpose = A) (l l' : Vec d) :
    dot l (A⁻¹.mulVec l') = dot l' (A⁻¹.mulVec l) := by
  have h : A⁻¹.transpose = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hAsymm]
  exact dot_mulVec_comm h l l'

/-- **`J₁` on a linear family spanning `A₁`**: if the gradients of `A₁` are exactly the fields
`G ξ` up to null sets, the family is integrable and the energy matrix `A` is invertible with
`ξ·Aξ ≥ 0`, then `J₁(Ψ, p, q) = ½ l·A⁻¹l` and, for every slope `k`, the gap to the trial `G k` is
`J₁(Ψ, p, q) - L(k) = ½ (k - c)·A(k - c)` with `c = A⁻¹l`. -/
theorem J1_sub_j1Functional_fieldOf (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : IntegrableFamily a mask W)
    (hspan : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, w.grad =ᵐ[volume] fieldOf W ξ)
    (hreal : ∀ ξ : Vec d, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] fieldOf W ξ)
    (hA : IsUnit (energyMatrix a mask W).det)
    (hpsd : ∀ ξ : Vec d, 0 ≤ dot ξ ((energyMatrix a mask W).mulVec ξ)) (p q : Vec d) :
    J1 a mask p q = (1 / 2 : ℝ) * dot (loadVector a mask W p q) (maximizerSlope a mask W p q) ∧
      ∀ k : Vec d, J1 a mask p q - j1Functional a mask p q (fieldOf W k) =
        (1 / 2 : ℝ) * dot (k - maximizerSlope a mask W p q)
          ((energyMatrix a mask W).mulVec (k - maximizerSlope a mask W p q)) := by
  set A := energyMatrix a mask W with hAdef
  set l := loadVector a mask W p q with hl
  set c := maximizerSlope a mask W p q with hcdef
  have hcA : c = A⁻¹.mulVec l := rfl
  have hAsymm : A.transpose = A := energyMatrix_transpose a mask W
  have hy : A.mulVec c = l := mulVec_inv_mulVec hA l
  have hval : ∀ ξ, j1Functional a mask p q (fieldOf W ξ) =
      -(1 / 2 : ℝ) * dot ξ (A.mulVec ξ) + dot l ξ := j1Functional_fieldOf a mask W hW p q
  have hsq : ∀ ξ, j1Functional a mask p q (fieldOf W ξ) =
      j1Functional a mask p q (fieldOf W c) - (1 / 2 : ℝ) * dot (ξ - c) (A.mulVec (ξ - c)) := by
    intro ξ
    rw [hval, hval, quadratic_eq_sub hAsymm hA l ξ, ← hcA]
  have hcval : j1Functional a mask p q (fieldOf W c) = (1 / 2 : ℝ) * dot l c := by
    rw [hval, hy, show dot c l = dot l c from dotProduct_comm _ _]
    ring
  -- the supremum
  have hJ : J1 a mask p q = j1Functional a mask p q (fieldOf W c) := by
    rw [J1_eq_sSup_j1Functional]
    have hmem : j1Functional a mask p q (fieldOf W c) ∈
        {e : ℝ | ∃ w : HarmonicA1 a, e = j1Functional a mask p q w.grad} := by
      obtain ⟨w, hw⟩ := hreal c
      exact ⟨w, (j1Functional_congr_ae a mask p q hw).symm⟩
    have hub : ∀ e ∈ {e : ℝ | ∃ w : HarmonicA1 a, e = j1Functional a mask p q w.grad},
        e ≤ j1Functional a mask p q (fieldOf W c) := by
      rintro e ⟨w, rfl⟩
      obtain ⟨ξ, hξ⟩ := hspan w
      rw [j1Functional_congr_ae a mask p q hξ, hsq ξ]
      linarith [hpsd (ξ - c)]
    exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)
  refine ⟨hJ.trans hcval, fun k => ?_⟩
  rw [hJ, hsq k]
  ring

/-- **The averaged gradient of the maximizer is the derivative of `J₁` in `q`** ((4.16),
(4.21)): `h·∫ Ψ G c = J₁(Ψ, p, q + h) - J₁(Ψ, p, q) - J₁(Ψ, 0, h)`. -/
theorem dot_integral_fieldOf_maximizer (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : IntegrableFamily a mask W)
    (hspan : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, w.grad =ᵐ[volume] fieldOf W ξ)
    (hreal : ∀ ξ : Vec d, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] fieldOf W ξ)
    (hA : IsUnit (energyMatrix a mask W).det)
    (hpsd : ∀ ξ : Vec d, 0 ≤ dot ξ ((energyMatrix a mask W).mulVec ξ)) (p q h : Vec d) :
    dot h (∫ x, mask x • fieldOf W (maximizerSlope a mask W p q) x) =
      J1 a mask p (q + h) - J1 a mask p q - J1 a mask 0 h := by
  set A := energyMatrix a mask W
  have hAsymm : A.transpose = A := energyMatrix_transpose a mask W
  have hJ := fun p q => (J1_sub_j1Functional_fieldOf a mask W hW hspan hreal hA hpsd p q).1
  rw [hJ p (q + h), hJ p q, hJ 0 h]
  simp only [maximizerSlope, loadVector_add_right a mask W p q h, Matrix.mulVec_add]
  -- the gradient average of the maximizer
  set c := A⁻¹.mulVec (loadVector a mask W p q) with hc
  have hint : ∀ j, Integrable fun x => c j • (mask x • W j x) := fun j => (hW.grad j).smul (c j)
  have hlin : (∫ x, mask x • fieldOf W c x) = ∑ j, c j • ∫ x, mask x • W j x := by
    have : (fun x => mask x • fieldOf W c x) = fun x => ∑ j, c j • (mask x • W j x) := by
      funext x
      simp only [fieldOf, Finset.smul_sum, smul_comm (mask x)]
    rw [this, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_congr rfl fun j _ => integral_smul _ _
  have hdot : dot h (∫ x, mask x • fieldOf W c x) = dot (loadVector a mask W 0 h) c := by
    rw [hlin, dot_eq_sum (loadVector a mask W 0 h) c]
    simp only [dot_eq_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul, loadVector,
      zero_dotProduct, neg_zero, zero_add]
  rw [hdot]
  have hsymm := dot_inv_mulVec_comm hAsymm (loadVector a mask W p q) (loadVector a mask W 0 h)
  simp only [dot_eq_dotProduct, add_dotProduct, dotProduct_add] at hsymm ⊢
  have e1 : loadVector a mask W 0 h ⬝ᵥ c = c ⬝ᵥ loadVector a mask W 0 h := dotProduct_comm _ _
  linarith

end QSH
