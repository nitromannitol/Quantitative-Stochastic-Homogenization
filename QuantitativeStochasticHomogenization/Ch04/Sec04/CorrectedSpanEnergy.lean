import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationEstimateReductionMass

/-!
# Gaussian energies of `A₁` through a spanning family of corrected gradients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.22, (4.104): when the gradients of the elements of `A₁` are linear combinations
`∑ ξ_i W_i` of fixed fields `W_i` (the corrected unit gradients `e_i + ∇φ_{e_i}`, Theorem 3.8 with
`k = 1`), the integrability of the Gaussian energies of `A₁` follows from that of the `W_i`, and
the comparison of the Gaussian energies outside and inside `B_T(z)` is a comparison of the Gram
matrices of the `W_i` outside and inside the ball.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {z : Vec d} {T r : ℝ}

theorem euclideanSq_sum_smul_le (ξ : Vec d) (W : Fin d → Vec d) :
    euclideanSq (∑ i, ξ i • W i) ≤ d * ∑ i, ξ i ^ 2 * euclideanSq (W i) := by
  have hn : euclideanNorm (∑ i, ξ i • W i) ≤ ∑ i, |ξ i| * euclideanNorm (W i) := by
    have h : ∀ s : Finset (Fin d), euclideanNorm (∑ i ∈ s, ξ i • W i) ≤
        ∑ i ∈ s, |ξ i| * euclideanNorm (W i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [euclideanNorm, euclideanSq, dot]
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        refine (euclideanNorm_add_le_add _ _).trans (add_le_add ?_ ih)
        rw [euclideanNorm_eq_euclideanSpace_norm, euclideanNorm_eq_euclideanSpace_norm,
          WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    exact h Finset.univ
  have hsq : euclideanSq (∑ i, ξ i • W i) ≤ (∑ i, |ξ i| * euclideanNorm (W i)) ^ 2 := by
    rw [← sq_euclideanNorm]
    exact pow_le_pow_left₀ (zero_le_euclideanNorm _) hn 2
  refine hsq.trans ?_
  have h1 : (∑ i, |ξ i| * euclideanNorm (W i)) ^ 2 ≤
      (d : ℝ) * ∑ i, (|ξ i| * euclideanNorm (W i)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |ξ i| * euclideanNorm (W i))
    simpa using this
  refine h1.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, sq_abs, sq_euclideanNorm]

theorem HarmonicA1.aemeasurable_grad {a : CoefficientField d Λ} (w : HarmonicA1 a) :
    AEMeasurable w.grad volume := by
  refine aemeasurable_pi_iff.2 fun k => ?_
  have h := (w.weak_gradient k).2.1.aestronglyMeasurable
  rw [Measure.restrict_univ] at h
  exact h.aemeasurable

theorem CoefficientField.aemeasurable_field (a : CoefficientField d Λ) :
    AEMeasurable a.field volume :=
  aemeasurable_pi_iff.2 fun k => aemeasurable_pi_iff.2 fun l =>
    (a.locally_integrable k l).aestronglyMeasurable.aemeasurable

theorem continuous_energyIntegrandFun (p q : Vec d) :
    Continuous fun Ag : Mat d × Vec d =>
      -(1 / 2 : ℝ) * dot Ag.2 (Ag.1.mulVec Ag.2) - dot p (Ag.1.mulVec Ag.2) + dot q Ag.2 := by
  simp only [dot, Matrix.mulVec, dotProduct]
  fun_prop

/-- **Integrability of the Gaussian energies of `A₁`** from that of a spanning family. -/
theorem integrable_energy_of_span {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ) (hr : r ≠ 0)
    (p q : Vec d) (W : Fin d → Vec d → Vec d)
    (hW : ∀ i, Integrable (fun x => heatKernel z r x * euclideanSq (W i x)))
    (w : HarmonicA1 a) (ξ : Vec d) (hξ : ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x) :
    Integrable (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) := by
  set c0 := linearCoefficient d Λ p q
  set K := ((d : ℝ) * Λ / 2 + c0 / 2) * d
  have hmeas : AEStronglyMeasurable (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) volume := by
    have h1 : AEMeasurable (fun x => (a.field x, w.grad x)) volume :=
      a.aemeasurable_field.prodMk w.aemeasurable_grad
    have h2 := ((continuous_energyIntegrandFun p q).measurable.comp_aemeasurable h1).aestronglyMeasurable
    exact (continuous_heatKernel_right z r).aestronglyMeasurable.mul h2
  have hbound : Integrable (fun x => heatKernel z r x *
      (K * ∑ i, ξ i ^ 2 * euclideanSq (W i x)) + c0 / 2 * heatKernel z r x) := by
    have hsum : Integrable (fun x => ∑ i, ξ i ^ 2 * (heatKernel z r x * euclideanSq (W i x))) :=
      integrable_finsetSum _ fun i _ => (hW i).const_mul _
    refine ((hsum.const_mul K).add ((integrable_heatKernel_mask z hr).const_mul (c0 / 2))).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine hbound.mono' hmeas ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatKernel_pos_of_ne z hr x)]
  have h1 := abs_energy_integrand_le a hΛ p q x (w.grad x)
  have h2 : euclideanSq (w.grad x) ≤ d * ∑ i, ξ i ^ 2 * euclideanSq (W i x) := by
    rw [hx]; exact euclideanSq_sum_smul_le ξ (fun i => W i x)
  have hA : 0 ≤ (d : ℝ) * Λ / 2 + c0 / 2 := by
    have : 0 ≤ c0 := by
      simp only [c0, linearCoefficient]
      exact add_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)
        (Nat.cast_nonneg d)) hΛ) (Finset.sum_nonneg fun k _ => abs_nonneg _)
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hΛ
    linarith
  have hk := (heatKernel_pos_of_ne z hr x).le
  have h3 : |-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)| ≤
      K * ∑ i, ξ i ^ 2 * euclideanSq (W i x) + c0 / 2 := by
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left h2 hA
    simp only [K]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hk]

/-- **Integrability of the outer Gaussian energy of `A₁`** from that of a spanning family. -/
theorem integrableOn_outer_of_span {a : CoefficientField d Λ} (W : Fin d → Vec d → Vec d)
    (hW : ∀ i, Integrable (fun x => heatKernel z r x * euclideanSq (W i x)))
    (w : HarmonicA1 a) (ξ : Vec d) (hξ : ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x) (hr : r ≠ 0) :
    IntegrableOn (fun x => heatKernel z r x * euclideanSq (w.grad x)) (ball z T)ᶜ volume := by
  have hsum : Integrable (fun x => (d : ℝ) * ∑ i, ξ i ^ 2 * (heatKernel z r x *
      euclideanSq (W i x))) :=
    (integrable_finsetSum _ fun i _ => (hW i).const_mul _).const_mul _
  have hmeas : AEStronglyMeasurable (fun x => heatKernel z r x * euclideanSq (w.grad x)) volume :=
    (continuous_heatKernel_right z r).aestronglyMeasurable.mul
      (continuous_euclideanSq.measurable.comp_aemeasurable w.aemeasurable_grad).aestronglyMeasurable
  refine (hsum.mono' hmeas ?_).integrableOn
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_pos_of_ne z hr x).le
    (zero_le_euclideanSq _))]
  have h2 : euclideanSq (w.grad x) ≤ d * ∑ i, ξ i ^ 2 * euclideanSq (W i x) := by
    rw [hx]; exact euclideanSq_sum_smul_le ξ (fun i => W i x)
  have hk := (heatKernel_pos_of_ne z hr x).le
  calc heatKernel z r x * euclideanSq (w.grad x)
      ≤ heatKernel z r x * (d * ∑ i, ξ i ^ 2 * euclideanSq (W i x)) :=
        mul_le_mul_of_nonneg_left h2 hk
    _ = (d : ℝ) * ∑ i, ξ i ^ 2 * (heatKernel z r x * euclideanSq (W i x)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- **The outer/inner comparison for `A₁`** from the comparison of the Gaussian energies of the
combinations of a spanning family. -/
theorem outer_le_of_span {a : CoefficientField d Λ} (W : Fin d → Vec d → Vec d) {κ : ℝ}
    (hgram : ∀ ξ : Vec d,
      ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) ≤
        κ * ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x))
    (w : HarmonicA1 a) (ξ : Vec d) (hξ : ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x) :
    ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x) ≤
      κ * ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x) := by
  have e1 : ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x) =
      ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) :=
    integral_congr_ae (ae_restrict_of_ae (hξ.mono fun x hx => by simp only [hx]))
  have e2 : ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x) =
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) :=
    integral_congr_ae (ae_restrict_of_ae (hξ.mono fun x hx => by simp only [hx]))
  rw [e1, e2]
  exact hgram ξ

/-- **The almost sure hypotheses of Lemma 4.22 from a spanning family**: if the gradients of
`A₁` are combinations of fields `W_i` with integrable Gaussian energies, whose combinations satisfy
the outer/inner comparison with constant `κ`, it remains to give the approximation property of
Lemma 4.21 with error `η`, the smallness of the Gaussian mass outside the ball and the bound `Z`. -/
theorem LocalizationApproximationAtUniform.of_span {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ)
    (hr : r ≠ 0) {S σ θ C : ℝ} {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} {η κ Zv : ℝ}
    (hT : 0 ≤ T) (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (W : Fin d → Vec d → Vec d)
    (hW : ∀ i, Integrable (fun x => heatKernel z r x * euclideanSq (W i x)))
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x)
    (hgram : ∀ ξ : Vec d,
      ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) ≤
        κ * ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x))
    (hAV : ∀ w : HarmonicA1 a,
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ 2 * linearCoefficient d Λ p q + 1 →
      ∃ c : Vec d, ‖(fun k => scaleLp hr (w.ballGrad z T k)) -
        (fun k => scaleLp hr (pairCombination (fun i => (B.coordinate i).toPair) c k))‖ ≤ η)
    (hVA : ∀ c : Vec d,
      ‖(fun k => scaleLp hr (pairCombination (fun i => (B.coordinate i).toPair) c k))‖ ≤
        2 * linearCoefficient d Λ p q + 1 →
      ∃ w : HarmonicA1 a,
        ‖(fun k => scaleLp hr (pairCombination (fun i => (B.coordinate i).toPair) c k)) -
          (fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ η)
    (hZ : (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
          (κ * (d * (2 * linearCoefficient d Λ p q + 1) ^ 2)) +
        linearCoefficient d Λ p q / 2 *
          ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)))) +
      ((d : ℝ) ^ 2 * Λ * (2 * (2 * linearCoefficient d Λ p q + 1) + η) / 2 +
        linearCoefficient d Λ p q) * η ≤ Zv) :
    LocalizationApproximationAtUniform a z T r hr B p q η κ Zv := by
  refine ⟨hT, hη, hκ, hsmall, fun w => ?_, fun w => ?_, fun w => ?_, hAV, hVA, hZ⟩
  · obtain ⟨ξ, hξ⟩ := hrep w
    exact integrable_energy_of_span hΛ hr p q W hW w ξ hξ
  · obtain ⟨ξ, hξ⟩ := hrep w
    exact integrableOn_outer_of_span W hW w ξ hξ hr
  · obtain ⟨ξ, hξ⟩ := hrep w
    exact outer_le_of_span W hgram w ξ hξ

end QSH
