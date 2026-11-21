import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimates
import QuantitativeStochasticHomogenization.Ch04.Opening.Theorem41

/-!
# Lemma 5.24 from (5.58) and the structure (4.12) of `A₁` by the corrected fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, Lemma 5.24 with `s = 1` (`QSH.Frozen.coarsenedCoefficientEstimates`).

The structure of `A₁` used in `coarsenedCoefficientEstimates_of` follows from (4.12) in the form
`GradientsOfA1AreCorrected` (the gradients of `A₁` are, up to null sets, the corrected fields
`∑ᵢ ξᵢ (eᵢ + ∇φ_{eᵢ})`, Theorem 3.8 with `k = 1`) and the finite energy of the corrected
coordinates against the masks (`HasGaussianCorrectorEnergy`, Lemma 3.17).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem euclideanSq_sum_le {ι : Type*} (s : Finset ι) (v : ι → Vec d) :
    euclideanSq (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, euclideanSq (v i) := by
  simp only [euclideanSq, dot, Finset.sum_apply]
  rw [Finset.sum_comm (s := s), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => v i k)
  simpa [sq] using this

theorem euclideanSq_smul (c : ℝ) (v : Vec d) : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section Corrected

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)

/-- The corrected fields `ξ ↦ ∑ᵢ ξᵢ (eᵢ + ∇φ_{eᵢ})` as a linear family. -/
def correctedFieldFamily (a : CoefficientField d Λ) : Vec d →ₗ[ℝ] Vec d → Vec d where
  toFun ξ := correctedField S a ξ
  map_add' ξ η := by
    funext x
    simp only [correctedField, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c ξ := by
    funext x
    simp only [correctedField, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      mul_smul]

theorem measurable_correctedField (a : CoefficientField d Λ) (ξ : Vec d) :
    Measurable (correctedField S a ξ) := by
  unfold correctedField correctedCoordinate
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_const.add
    ((S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left)).const_smul (ξ i)

/-- **(4.12) by the corrected fields gives the linear structure of `A₁`.** -/
theorem linearA1Gradients_of_corrected {a : CoefficientField d Λ}
    (hcorr : GradientsOfA1AreCorrected S a)
    (hint : ∀ (i : Fin d) (z : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel z r x *
        euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x)))
    (z : Vec d) {r : ℝ} (hr : 0 < r) : LinearA1Gradients a (heatKernel z r) := by
  refine ⟨correctedFieldFamily S a, fun w => hcorr.1 w, fun ξ => hcorr.2 ξ, fun ξ => ?_⟩
  have hm : AEMeasurable (correctedFieldFamily S a ξ) volume :=
    (measurable_correctedField S a ξ).aemeasurable
  have hbound : Integrable (fun x => (d : ℝ) * ∑ i, ξ i ^ 2 *
      (heatKernel z r x * euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x))) :=
    (integrable_finsetSum _ fun i _ => (hint i z r hr).const_mul _).const_mul _
  refine Integrable.mono' hbound
    (((integrable_heatKernel z hr).aestronglyMeasurable.aemeasurable.mul
      (aemeasurable_dot hm hm)).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  have h2 := euclideanSq_sum_le Finset.univ (fun i => ξ i • correctedCoordinate S a i x)
  simp only [Finset.card_univ, Fintype.card_fin, euclideanSq_smul] at h2
  have hk := heatKernel_nonneg z r x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (euclideanSq_nonneg _))]
  change heatKernel z r x * euclideanSq (∑ i, ξ i • correctedCoordinate S a i x) ≤ _
  calc heatKernel z r x * euclideanSq (∑ i, ξ i • correctedCoordinate S a i x)
      ≤ heatKernel z r x * ((d : ℝ) * ∑ i, ξ i ^ 2 * euclideanSq (correctedCoordinate S a i x)) :=
        mul_le_mul_of_nonneg_left h2 hk
    _ = (d : ℝ) * ∑ i, ξ i ^ 2 * (heatKernel z r x *
          euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [correctedCoordinate]; ring

end Corrected

/-- **`QSH.Frozen.coarsenedCoefficientEstimates`** from (5.58) with a constant `C₀(d, Λ)`, the
measurability of `J₁`, (4.12) by the corrected fields, the finite Gaussian energy of the corrected
coordinates, and the almost sure measurability of the flux defect of (5.64). -/
theorem coarsenedCoefficientEstimates_of_corrected
    (h558 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀)
    (hJm : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        AEMeasurable (fun a => J1Heat a z r p q) P)
    (hcorr : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ S : HomogenizationData P, ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hen : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ S : HomogenizationData P, HasGaussianCorrectorEnergy S)
    (hDm : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ S : HomogenizationData P, ∀ (z : Vec d) (r : ℝ),
        AEMeasurable (fun a => coarseFluxDefect a S.homogenized z r) P) :
    QSH.Frozen.coarsenedCoefficientEstimates := by
  refine coarsenedCoefficientEstimates_of h558 hJm ?_ hDm
  intro d hd Λ hΛ P hP S z r hr
  filter_upwards [hcorr d hd Λ hΛ P hP S, hen d hd Λ hΛ P hP S] with a h1 h2
  exact linearA1Gradients_of_corrected S h1 h2 z (by linarith)

end QSH
