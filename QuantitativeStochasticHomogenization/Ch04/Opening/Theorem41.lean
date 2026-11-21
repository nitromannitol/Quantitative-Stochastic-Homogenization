import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimates
import QuantitativeStochasticHomogenization.Frozen.AveragedCorrectorGradient
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorLinearCombination
import QuantitativeStochasticHomogenization.Ch04.Sec01.BaseExponent

/-!
# Theorem 4.1, (4.2), with `s = 1`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.1, (4.2), in the form of `QSH.Frozen.averagedCorrectorGradient`, from:

* homogenization data whose corrector gradients are linear in the direction, almost surely
  (`HasLinearCorrectorGradients`), as for the corrector of Lemma 3.16 constructed by projection;
* the finite energy of the corrected coordinates `eᵢ + ∇φ_{eᵢ}` against every mask `Φ_{z,r}`,
  almost surely (`HasGaussianCorrectorEnergy`, from Lemma 3.17);
* the estimate `|∫ Φ_{z,r} ∇φ_{eᵢ}| ≤ O_s(C r^{-d/2})` in the coordinate directions for one
  exponent `s ≥ 1` (`CoordinateGradientEstimate`), which is the linear estimate obtained in the
  proof of the improvement of additivity once the exponent `d/2` is reached.

The exponent `s` is lowered to `1` by `OsBound.mono_exponent`; the measurability of
`a ↦ |∫ Φ_{z,r} ∇φ_e(a, ·)|` follows from the joint measurability of the corrector gradient.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Data

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)

/-- The corrector gradients are linear in the direction, almost surely. -/
def HasLinearCorrectorGradients : Prop :=
  ∀ e : Vec d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
    (S.corrector e).grad a x = ∑ i, e i • (S.corrector (unitVector i)).grad a x

/-- The corrected coordinates `eᵢ + ∇φ_{eᵢ}` have finite energy against every mask, almost
surely. -/
def HasGaussianCorrectorEnergy : Prop :=
  ∀ᵐ a ∂P, ∀ (i : Fin d) (z : Vec d) (r : ℝ), 0 < r →
    Integrable (fun x => heatKernel z r x *
      euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x))

/-- `|∫ Φ_{z,r} ∇φ_{eᵢ}| ≤ O_s(C r^{-d/2})` in the coordinate directions. -/
def CoordinateGradientEstimate (s C : ℝ) : Prop :=
  ∀ (i : Fin d) (z : Vec d) (r : ℝ), 1 ≤ r →
    AEOsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector (unitVector i)).grad a y))
      s (C * r ^ (-(d : ℝ) / 2))

end Data

theorem measurable_heatKernel (z : Vec d) (r : ℝ) : Measurable (heatKernel z r) := by
  unfold heatKernel euclideanHeatKernel euclideanSq dot
  fun_prop

theorem measurable_euclideanNorm : Measurable (euclideanNorm (d := d)) := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem measurable_euclideanNorm_integral_heatKernel_grad {P : Measure (CoefficientField d Λ)}
    {e : Vec d} (φ : Corrector P e) (z : Vec d) (r : ℝ) :
    Measurable (fun a => euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)) := by
  have hf : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (y : Vec d) =>
      heatKernel z r y • φ.grad a y) :=
    (((measurable_heatKernel z r).comp measurable_snd).smul φ.measurable_grad).stronglyMeasurable
  exact measurable_euclideanNorm.comp
    (hf.integral_prod_right (ν := (volume : Measure (Vec d)))).measurable

theorem AEOsBound.osBound_of_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {s θ : ℝ} (h : AEOsBound P X s θ) (hX : Measurable X) : OsBound P X s θ :=
  ⟨hX, h.2.1, h.2.2.1, h.2.2.2⟩

theorem euclideanSq_sub_le (u v : Vec d) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, dot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (u i + v i)]

theorem euclideanNorm_sum_le {ι : Type*} (s : Finset ι) (v : ι → Vec d) :
    euclideanNorm (∑ i ∈ s, v i) ≤ ∑ i ∈ s, euclideanNorm (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euclideanNorm, euclideanSq, dot]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (euclideanNorm_add_le _ _).trans (add_le_add_right ih _)

section Estimate

variable {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P] {S : HomogenizationData P}

omit [IsProbabilityMeasure P] in
/-- Almost surely, the Gaussian average of `∇φ_e` is the combination of those of the coordinate
correctors, and all of them are integrable. -/
theorem ae_integral_heatKernel_grad_eq (hlin : HasLinearCorrectorGradients S)
    (hen : HasGaussianCorrectorEnergy S) (e : Vec d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y) ∧
      (∫ y, heatKernel z r y • (S.corrector e).grad a y) =
        ∑ i, e i • ∫ y, heatKernel z r y • (S.corrector (unitVector i)).grad a y := by
  filter_upwards [hlin e, hen] with a hle hena
  have hint : ∀ i : Fin d,
      Integrable (fun y => heatKernel z r y • (S.corrector (unitVector i)).grad a y) := fun i => by
    have hm : AEMeasurable ((S.corrector (unitVector i)).grad a) volume :=
      ((S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left).aemeasurable
    refine integrable_mask_smul (heatKernel_nonneg z r) (integrable_heatKernel z hr) hm ?_
    have hW := hena i z r hr
    refine Integrable.mono' ((hW.const_mul 2).add ((integrable_heatKernel z hr).const_mul 2))
      (((measurable_heatKernel z r).aemeasurable.mul (aemeasurable_dot hm hm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := euclideanSq_sub_le (unitVector i + (S.corrector (unitVector i)).grad a x)
      (unitVector i)
    rw [add_sub_cancel_left, euclideanSq_unitVector_eq_one] at h1
    have hk := heatKernel_nonneg z r x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (euclideanSq_nonneg _))]
    change heatKernel z r x * euclideanSq ((S.corrector (unitVector i)).grad a x) ≤
      2 * (heatKernel z r x * euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x)) +
        2 * heatKernel z r x
    nlinarith [mul_le_mul_of_nonneg_left h1 hk]
  have hint' : ∀ i : Fin d, Integrable (fun y => e i • (heatKernel z r y •
      (S.corrector (unitVector i)).grad a y)) := fun i => (hint i).smul (e i)
  have hsum : Integrable (fun y => ∑ i, e i • (heatKernel z r y •
      (S.corrector (unitVector i)).grad a y)) :=
    integrable_finsetSum _ fun i _ => hint' i
  have hcongr : (fun y => heatKernel z r y • (S.corrector e).grad a y) =ᵐ[volume]
      fun y => ∑ i, e i • (heatKernel z r y • (S.corrector (unitVector i)).grad a y) := by
    filter_upwards [hle] with y hy
    rw [hy, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨hsum.congr hcongr.symm, ?_⟩
  rw [integral_congr_ae hcongr, integral_finsetSum _ fun i _ => hint' i]
  exact Finset.sum_congr rfl fun i _ => integral_smul _ _

/-- **Theorem 4.1, (4.2), with `s = 1`**, for one law. -/
theorem averagedCorrectorGradient_osBound (hlin : HasLinearCorrectorGradients S)
    (hen : HasGaussianCorrectorEnergy S) {s C₁ : ℝ} (hs : 1 ≤ s)
    (hest : CoordinateGradientEstimate S s C₁) (hd : 0 < d) {e : Vec d}
    (he : euclideanNorm e < 1) (z : Vec d) {r : ℝ} (hr : 1 ≤ r) :
    (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y)) ∧
      OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y)) 1
        ((2 * Real.exp 1 - 1) * (d * C₁) * r ^ (-(d : ℝ) / 2)) := by
  have hr0 : 0 < r := by linarith
  have hae := ae_integral_heatKernel_grad_eq hlin hen e z hr0
  refine ⟨hae.mono fun a ha => ha.1, ?_⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
  have hsum := aeOsBound_finset_sum (P := P) Finset.univ hne hs fun i _ => hest i z r hr
  have hle : ∀ᵐ a ∂P, euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y) ≤
      ∑ i, euclideanNorm (∫ y, heatKernel z r y • (S.corrector (unitVector i)).grad a y) := by
    filter_upwards [hae] with a ha
    rw [ha.2]
    refine (euclideanNorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [euclideanNorm_smul_eq_abs_mul]
    have hei : |e i| ≤ 1 := (abs_apply_le_euclideanNorm e i).trans he.le
    exact mul_le_of_le_one_left (euclideanNorm_nonneg _) hei
  have hmeas := measurable_euclideanNorm_integral_heatKernel_grad (S.corrector e) z r
  have h1 := (hsum.of_le_ae hmeas.aemeasurable hle).osBound_of_measurable hmeas
  have h2 := h1.mono_exponent one_pos hs
  rw [inv_one, Real.rpow_one] at h2
  refine h2.mono_scale (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Estimate

/-- **`QSH.Frozen.averagedCorrectorGradient`** (Theorem 4.1, (4.2), with `s = 1`) from
homogenization data with linear corrector gradients, the finite Gaussian energy of the corrected
coordinates, and the estimate of their Gaussian averages at the rate `r^{-d/2}` for one exponent
`s ≥ 1`. -/
theorem averagedCorrectorGradient_of
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ s C₁ : ℝ, 1 ≤ s ∧ 0 < C₁ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        HasLinearCorrectorGradients S ∧ HasGaussianCorrectorEnergy S ∧
          CoordinateGradientEstimate S s C₁) :
    QSH.Frozen.averagedCorrectorGradient := by
  intro d hd Λ hΛ
  obtain ⟨s, C₁, hs, hC₁, hP⟩ := h d hd Λ hΛ
  have hd0 : 0 < d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have he1 : 0 < 2 * Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1
    linarith
  refine ⟨(2 * Real.exp 1 - 1) * (d * C₁), by positivity, fun P hPl => ?_⟩
  obtain ⟨S, hlin, hen, hest⟩ := hP P hPl
  have := hPl.1
  exact ⟨S, fun e he z r hr =>
    averagedCorrectorGradient_osBound hlin hen hs hest hd0 he z hr⟩

/-! ## Correctors linear in the direction -/

section Linearize

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)

theorem hasLinearCorrectorGradients_linearize : HasLinearCorrectorGradients S.linearize :=
  fun e => Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun x => by
    rw [HomogenizationData.linearize_grad]
    exact Finset.sum_congr rfl fun i _ => by rw [HomogenizationData.linearize_grad_unitVector]

theorem linearize_grad_unitVector_eq (i : Fin d) (a : CoefficientField d Λ) :
    (S.linearize.corrector (unitVector i)).grad a = (S.corrector (unitVector i)).grad a :=
  funext fun x => HomogenizationData.linearize_grad_unitVector S i a x

theorem HasGaussianCorrectorEnergy.linearize (h : HasGaussianCorrectorEnergy S) :
    HasGaussianCorrectorEnergy S.linearize := by
  filter_upwards [h] with a ha i z r hr
  rw [linearize_grad_unitVector_eq]
  exact ha i z r hr

theorem CoordinateGradientEstimate.linearize {s C : ℝ} (h : CoordinateGradientEstimate S s C) :
    CoordinateGradientEstimate S.linearize s C := fun i z r hr => by
  simp only [linearize_grad_unitVector_eq]
  exact h i z r hr

end Linearize

/-- **`QSH.Frozen.averagedCorrectorGradient`** (Theorem 4.1, (4.2), with `s = 1`) from
homogenization data with the finite Gaussian energy of the corrected coordinates and the estimate
of their Gaussian averages at the rate `r^{-d/2}` for one exponent `s ≥ 1`; the correctors are
replaced by the combinations of the coordinate correctors (`HomogenizationData.linearize`). -/
theorem averagedCorrectorGradient_of_coordinate
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ s C₁ : ℝ, 1 ≤ s ∧ 0 < C₁ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        HasGaussianCorrectorEnergy S ∧ CoordinateGradientEstimate S s C₁) :
    QSH.Frozen.averagedCorrectorGradient := by
  refine averagedCorrectorGradient_of fun d hd Λ hΛ => ?_
  obtain ⟨s, C₁, hs, hC₁, hP⟩ := h d hd Λ hΛ
  refine ⟨s, C₁, hs, hC₁, fun P hPl => ?_⟩
  obtain ⟨S, hen, hest⟩ := hP P hPl
  exact ⟨S.linearize, hasLinearCorrectorGradients_linearize S, hen.linearize, hest.linearize⟩

/-! ## The linear estimate in the form of the proof of the improvement of additivity -/

theorem correctedField_unitVector {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (i : Fin d) (x : Vec d) :
    correctedField S a (unitVector i) x = unitVector i + (S.corrector (unitVector i)).grad a x := by
  rw [correctedField, Finset.sum_eq_single i]
  · simp [unitVector, correctedCoordinate]
  · intro j _ hj
    simp [unitVector, Pi.single_apply, hj]
  · simp

/-- The coordinate estimate from the linear estimate `|∫ Φ_{z,r} G ξ - ξ| ≤ O_s(C (1 + |ξ|) r^{-d/2})`
of the proof of the improvement of additivity (`LinearAverageEstimate` at the exponent `d/2`). -/
theorem coordinateGradientEstimate_of_linearAverage {P : Measure (CoefficientField d Λ)}
    {S : HomogenizationData P} (hen : HasGaussianCorrectorEnergy S) {s C : ℝ}
    (h : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
      OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ)) s
        (C * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2)))) :
    CoordinateGradientEstimate S s (2 * C) := fun i z r hr => by
  have hr0 : 0 < r := by linarith
  have hb := h z r hr (unitVector i)
  rw [euclideanNorm_unitVector] at hb
  refine (hb.aeOsBound_of_ae_eq ?_).mono_scale (le_of_eq (by rw [neg_div]; ring))
  filter_upwards [hen] with a ha
  have hint : Integrable (fun y => heatKernel z r y • (S.corrector (unitVector i)).grad a y) := by
    have hm : AEMeasurable ((S.corrector (unitVector i)).grad a) volume :=
      ((S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left).aemeasurable
    refine integrable_mask_smul (heatKernel_nonneg z r) (integrable_heatKernel z hr0) hm ?_
    refine Integrable.mono' (((ha i z r hr0).const_mul 2).add
      ((integrable_heatKernel z hr0).const_mul 2))
      (((measurable_heatKernel z r).aemeasurable.mul (aemeasurable_dot hm hm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := euclideanSq_sub_le (unitVector i + (S.corrector (unitVector i)).grad a x)
      (unitVector i)
    rw [add_sub_cancel_left, euclideanSq_unitVector_eq_one] at h1
    have hk := heatKernel_nonneg z r x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (euclideanSq_nonneg _))]
    change heatKernel z r x * euclideanSq ((S.corrector (unitVector i)).grad a x) ≤
      2 * (heatKernel z r x * euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x)) +
        2 * heatKernel z r x
    nlinarith [mul_le_mul_of_nonneg_left h1 hk]
  have hconst : Integrable (fun y => heatKernel z r y • unitVector (d := d) i) :=
    (integrable_heatKernel z hr0).smul_const _
  have heq : (∫ x, heatKernel z r x • correctedField S a (unitVector i) x) - unitVector i =
      ∫ y, heatKernel z r y • (S.corrector (unitVector i)).grad a y := by
    simp only [correctedField_unitVector, smul_add]
    rw [integral_add hconst hint, integral_smul_const, integral_heatKernel z hr0, one_smul]
    abel
  simp only [heq]

end QSH
