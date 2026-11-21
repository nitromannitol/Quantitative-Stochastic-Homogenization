import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAverages

/-!
# The averaged flux of the maximizer

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, (4.16) and (4.20), in the form used for Lemma 4.13 here.

On a linear family of gradients spanning `A₁` with an invertible energy matrix, the averaged flux
`∫ Ψ a G c` of the maximizer is minus the derivative of `J₁` in `p`:
`h·∫ Ψ a G c = -(J₁(Ψ, p + h, q) - J₁(Ψ, p, q) - J₁(Ψ, h, 0))`
(`dot_integral_flux_fieldOf_maximizer`). At a good scale it is the flux polarization vector
`-4 (J₁(½(p + eᵢ), q/2) - J₁(p/2, q/2) - J₁(eᵢ/2, 0))`
(`integral_flux_maximizer_eq_fluxPolarizationVector`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem loadVector_add_left (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (p q h : Vec d) :
    loadVector a mask W (p + h) q = loadVector a mask W p q + loadVector a mask W h 0 := by
  funext j
  simp only [loadVector, Pi.add_apply, dot_eq_dotProduct, add_dotProduct, zero_dotProduct]
  ring

/-- **The averaged flux of the maximizer is minus the derivative of `J₁` in `p`.** -/
theorem dot_integral_flux_fieldOf_maximizer (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (hW : IntegrableFamily a mask W)
    (hspan : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, w.grad =ᵐ[volume] fieldOf W ξ)
    (hreal : ∀ ξ : Vec d, ∃ w : HarmonicA1 a, w.grad =ᵐ[volume] fieldOf W ξ)
    (hA : IsUnit (energyMatrix a mask W).det)
    (hpsd : ∀ ξ : Vec d, 0 ≤ dot ξ ((energyMatrix a mask W).mulVec ξ)) (p q h : Vec d) :
    dot h (∫ x, mask x • (a x).mulVec (fieldOf W (maximizerSlope a mask W p q) x)) =
      -(J1 a mask (p + h) q - J1 a mask p q - J1 a mask h 0) := by
  set A := energyMatrix a mask W
  have hAsymm : A.transpose = A := energyMatrix_transpose a mask W
  have hJ := fun p q => (J1_sub_j1Functional_fieldOf a mask W hW hspan hreal hA hpsd p q).1
  rw [hJ (p + h) q, hJ p q, hJ h 0]
  simp only [maximizerSlope, loadVector_add_left a mask W p q h, Matrix.mulVec_add]
  set c := A⁻¹.mulVec (loadVector a mask W p q) with hc
  have hint : ∀ j, Integrable fun x => c j • (mask x • (a x).mulVec (W j x)) := fun j =>
    (hW.flux j).smul (c j)
  have hlin : (∫ x, mask x • (a x).mulVec (fieldOf W c x)) =
      ∑ j, c j • ∫ x, mask x • (a x).mulVec (W j x) := by
    have : (fun x => mask x • (a x).mulVec (fieldOf W c x)) =
        fun x => ∑ j, c j • (mask x • (a x).mulVec (W j x)) := by
      funext x
      simp only [fieldOf, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum, smul_comm (mask x)]
    rw [this, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_congr rfl fun j _ => integral_smul _ _
  have hdot : dot h (∫ x, mask x • (a x).mulVec (fieldOf W c x)) =
      -dot (loadVector a mask W h 0) c := by
    rw [hlin, dot_eq_sum (loadVector a mask W h 0) c]
    simp only [dot_eq_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul, loadVector,
      zero_dotProduct, add_zero]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hdot]
  have hsymm := dot_inv_mulVec_comm hAsymm (loadVector a mask W p q) (loadVector a mask W h 0)
  simp only [dot_eq_dotProduct, add_dotProduct, dotProduct_add] at hsymm ⊢
  have e1 : loadVector a mask W h 0 ⬝ᵥ c = c ⬝ᵥ loadVector a mask W h 0 := dotProduct_comm _ _
  linarith

/-- The flux polarization vector `-4 (J₁(½(p + eᵢ), q/2) - J₁(p/2, q/2) - J₁(eᵢ/2, 0))`. -/
def fluxPolarizationVector (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (p q : Vec d) :
    Vec d :=
  fun i => -4 * (J1Heat a y r ((1 / 2 : ℝ) • (p + unitVector i)) ((1 / 2 : ℝ) • q) -
    J1Heat a y r ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) - J1Heat a y r ((1 / 2 : ℝ) • unitVector i) 0)

section Polarization

variable {P : Measure (CoefficientField d Λ)}

/-- At a good scale, the flux polarization vector is the averaged flux of the maximizer. -/
theorem integral_flux_maximizer_eq_fluxPolarizationVector (S : HomogenizationData P)
    (a : CoefficientField d Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) (r : ℝ) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (p q : Vec d) :
    (∫ x, heatKernel y r x • (a x).mulVec (correctedField S a
      (maximizerSlope a (heatKernel y r) (correctedCoordinate S a) p q) x)) =
      fluxPolarizationVector a y r p q := by
  set W := correctedCoordinate S a with hWdef
  set mask := heatKernel y r with hmask
  have hW := integrableFamily_of_averages S a y r ε havg
  set A := energyMatrix a mask W with hAdef
  have hAξ : ∀ ξ, (1 - 2 * ε) * euclideanSq ξ ≤ dot ξ (A.mulVec ξ) := by
    intro ξ
    rw [dot_energyMatrix_eq_integral a mask W hW ξ]
    have h0 : |(∫ x, mask x * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x))) -
        dot ξ (S.homogenized.mulVec ξ)| ≤ 2 * ε * euclideanNorm ξ ^ 2 := (havg ξ).2.2.2.2.2
    have h := abs_le.mp h0
    have h1 := (hA ξ).1
    rw [euclideanNorm_sq] at h
    nlinarith [h.1]
  have hpos : ∀ ξ, ξ ≠ 0 → 0 < dot ξ (A.mulVec ξ) := by
    intro ξ hξ
    have h1 := hAξ ξ
    have h2 : 0 < euclideanSq ξ := by
      rcases (euclideanSq_nonneg ξ).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_zero_of_euclideanSq_le_zero h.symm.le) hξ
    nlinarith
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hpos v hv0
    rw [hv, dot_eq_dotProduct, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hpsd : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ) := fun ξ =>
    (mul_nonneg (by linarith) (euclideanSq_nonneg ξ)).trans (hAξ ξ)
  funext i
  have hpol := dot_integral_flux_fieldOf_maximizer a mask W hW hspan.1 hspan.2 hdet hpsd
    ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) ((1 / 2 : ℝ) • unitVector i)
  rw [maximizerSlope_smul] at hpol
  have hlin : (∫ x, mask x • (a x).mulVec (fieldOf W ((1 / 2 : ℝ) •
      maximizerSlope a mask W p q) x)) =
      (1 / 2 : ℝ) • ∫ x, mask x • (a x).mulVec (fieldOf W (maximizerSlope a mask W p q) x) := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fieldOf_smul, Matrix.mulVec_smul, smul_comm (mask x)]
  rw [hlin, ← smul_add] at hpol
  have hdot : dot ((1 / 2 : ℝ) • unitVector i)
      ((1 / 2 : ℝ) • ∫ x, mask x • (a x).mulVec (fieldOf W (maximizerSlope a mask W p q) x)) =
      (1 / 4 : ℝ) * (∫ x, mask x • (a x).mulVec (fieldOf W (maximizerSlope a mask W p q) x)) i := by
    simp only [dot_eq_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, unitVector,
      single_dotProduct, one_mul]
    ring
  rw [hdot] at hpol
  simp only [fluxPolarizationVector, J1Heat]
  show (∫ x, mask x • (a x).mulVec (fieldOf W (maximizerSlope a mask W p q) x)) i = _
  linarith

end Polarization

end QSH
