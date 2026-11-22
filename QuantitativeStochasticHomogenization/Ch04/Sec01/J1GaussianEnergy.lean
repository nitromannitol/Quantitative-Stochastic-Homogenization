import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatFormula
import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouville
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma

/-!
# Gaussian integrability of the energies of `A₁`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1: almost surely, for every element `w` of `A₁`, every center `z` and every radius
`r > 0`, the energy `Φ_{z,r} |∇w|²` is integrable. By the first-order Liouville theorem
`∇w = ∑ᵢ pᵢ (eᵢ + ∇φ_{eᵢ})`, and `|∑ᵢ pᵢ Wᵢ|² ≤ d ∑ᵢ pᵢ² |Wᵢ|²`, with each `Φ_{z,r} |Wᵢ|²`
integrable.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanSq_finsetSum_le {ι : Type*} (s : Finset ι) (v : ι → Vec d) :
    euclideanSq (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, euclideanSq (v i) := by
  unfold euclideanSq dot
  simp only [Finset.sum_apply]
  calc ∑ k, (∑ i ∈ s, v i k) * (∑ i ∈ s, v i k)
      ≤ ∑ k, (s.card : ℝ) * ∑ i ∈ s, v i k ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [← sq]
        exact sq_sum_le_card_mul_sum_sq
    _ = s.card * ∑ i ∈ s, ∑ k, v i k * v i k := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [sq]

/-- **Gaussian integrability of the energies of `A₁`**, from the first-order Liouville theorem. -/
theorem ae_integrable_heatKernel_mul_euclideanSq_grad (hL : firstOrderLiouvilleStatement)
    (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (w : HarmonicA1 a) (z : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel z r x * euclideanSq (w.grad x)) := by
  filter_upwards [hL d hd Λ hΛ P hP S,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S] with a hLa hint
  intro w z r hr
  obtain ⟨c, p, -, hg⟩ := hLa w
  have hK : Measurable (heatKernel (d := d) z r) :=
    (measurable_euclideanHeatKernel (r ^ 2)).comp (measurable_id.sub measurable_const)
  have hKnn : ∀ x, 0 ≤ heatKernel z r x := fun x =>
    euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hmeasG : Measurable (correctedAffineGrad S a p) := by
    have h : correctedAffineGrad S a p = fun x => ∑ i, p i • correctorColumn S a i x := by
      funext x
      exact correctedAffineGrad_eq_sum S a p x
    rw [h]
    exact Finset.measurable_sum _ fun i _ => (measurable_correctorColumn S a i).const_smul (p i)
  have hmaj : Integrable (fun x => (d : ℝ) * ∑ i, p i ^ 2 *
      (heatKernel z r x * euclideanSq (correctorColumn S a i x))) :=
    (integrable_finsetSum _ fun i _ => (hint i z r hr).const_mul (p i ^ 2)).const_mul _
  have hG : Integrable (fun x => heatKernel z r x * euclideanSq (correctedAffineGrad S a p x)) := by
    refine hmaj.mono' ?_ (Eventually.of_forall fun x => ?_)
    · have hsq : Measurable fun v : Vec d => euclideanSq v := by
        unfold euclideanSq dot
        fun_prop
      exact (hK.mul (hsq.comp hmeasG)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hKnn x) (euclideanSq_nonneg _)),
        correctedAffineGrad_eq_sum]
      have h1 := euclideanSq_finsetSum_le Finset.univ (fun i => p i • correctorColumn S a i x)
      simp only [Finset.card_univ, Fintype.card_fin, euclideanSq_smul] at h1
      calc heatKernel z r x * euclideanSq (∑ i, p i • correctorColumn S a i x)
          ≤ heatKernel z r x * ((d : ℝ) * ∑ i, p i ^ 2 * euclideanSq (correctorColumn S a i x)) :=
            mul_le_mul_of_nonneg_left h1 (hKnn x)
        _ = (d : ℝ) * ∑ i, p i ^ 2 * (heatKernel z r x * euclideanSq (correctorColumn S a i x)) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
  refine hG.congr ?_
  filter_upwards [hg] with x hx
  rw [hx]

end QSH
