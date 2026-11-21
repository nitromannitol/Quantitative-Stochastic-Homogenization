import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedSpanEnergy

/-!
# The outer/inner comparison of Gaussian energies from Gram bounds

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.22, (4.104). The mask of scale `r` is `2^{d/2} exp(-|x - z|²/(8r²))` times the
mask of scale `√2 r`; outside `B_T(z)` the factor is at most `2^{d/2} exp(-T²/(8r²))`. Hence, if
the Gaussian energies of fields `W_i` at scale `√2 r` are at most `E` and the energies inside
`B_T(z)` at scale `r` of their combinations `∑ ξ_i W_i` are at least `m |ξ|²`, then the energy of
every combination outside the ball is at most `2^{d/2} exp(-T²/(8r²)) d E / m` times its energy
inside the ball.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {z : Vec d} {T r : ℝ}

theorem heatKernelPeak_eq_mul_sqrt_two (d : ℕ) (r : ℝ) :
    heatKernelPeak d r = (2 : ℝ) ^ ((d : ℝ) / 2) * heatKernelPeak d (Real.sqrt 2 * r) := by
  unfold heatKernelPeak
  have h2 : 4 * Real.pi * (Real.sqrt 2 * r) ^ 2 = 2 * (4 * Real.pi * r ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [h2, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ 4 * Real.pi * r ^ 2), ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]

/-- The mask of scale `r` is `2^{d/2} exp(-|x - z|²/(8r²))` times the mask of scale `√2 r`. -/
theorem heatKernel_eq_mul_heatKernel_sqrt_two (z : Vec d) {r : ℝ} (hr : r ≠ 0) (x : Vec d) :
    heatKernel z r x = (2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z)) *
        heatKernel z (Real.sqrt 2 * r) x := by
  rw [heatKernel_eq_exp, heatKernel_eq_exp, heatKernelPeak_eq_mul_sqrt_two d r]
  have h2 : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2]
  have he : Real.exp (-(1 / (4 * r ^ 2)) * euclideanSq (x - z)) =
      Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z)) *
        Real.exp (-(1 / (4 * (2 * r ^ 2))) * euclideanSq (x - z)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [he]
  ring

theorem sqrt_two_mul_ne_zero {r : ℝ} (hr : r ≠ 0) : Real.sqrt 2 * r ≠ 0 :=
  mul_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) hr

/-- The mask of scale `r` is at most `2^{d/2}` times the mask of scale `√2 r`. -/
theorem heatKernel_le_mul_heatKernel_sqrt_two (z : Vec d) {r : ℝ} (hr : r ≠ 0) (x : Vec d) :
    heatKernel z r x ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * heatKernel z (Real.sqrt 2 * r) x := by
  rw [heatKernel_eq_mul_heatKernel_sqrt_two z hr x]
  have hk := (heatKernel_pos_of_ne z (sqrt_two_mul_ne_zero hr) x).le
  have he : Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z)) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity))
      (zero_le_euclideanSq _))
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) he) hk

/-- Outside `B_T(z)`, the mask of scale `r` is at most `2^{d/2} exp(-T²/(8r²))` times the mask of
scale `√2 r`. -/
theorem heatKernel_le_of_mem_compl_ball (z : Vec d) {r T : ℝ} (hr : r ≠ 0) (hT : 0 ≤ T)
    {x : Vec d} (hx : x ∈ (ball z T)ᶜ) :
    heatKernel z r x ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      heatKernel z (Real.sqrt 2 * r) x := by
  rw [heatKernel_eq_mul_heatKernel_sqrt_two z hr x]
  have hxT : T ≤ euclideanNorm (x - z) := not_lt.1 hx
  have hsq : T ^ 2 ≤ euclideanSq (x - z) := by
    rw [← sq_euclideanNorm]; exact pow_le_pow_left₀ hT hxT 2
  have he : Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z)) ≤
      Real.exp (-(T ^ 2) / (8 * r ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    have h8 : 0 < 8 * r ^ 2 := by positivity
    rw [neg_div, neg_mul, neg_le_neg_iff, div_le_iff₀ h8]
    field_simp
    linarith
  have hk := (heatKernel_pos_of_ne z (sqrt_two_mul_ne_zero hr) x).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hk

/-- Integrability against the mask of scale `r` from integrability against the mask of scale
`√2 r`. -/
theorem Integrable.heatKernel_of_sqrt_two (z : Vec d) {r : ℝ} (hr : r ≠ 0) {f : Vec d → ℝ}
    (hf : Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x * f x)) :
    Integrable (fun x => heatKernel z r x * f x) := by
  have hc : Continuous (fun x : Vec d => (2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_euclideanSq.comp (continuous_id.sub continuous_const))))
  have hb : ∀ᵐ x : Vec d, ‖(2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (-(1 / (8 * r ^ 2)) * euclideanSq (x - z))‖ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := by
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (zero_le_euclideanSq _)))
  refine (hf.bdd_mul hc.aestronglyMeasurable hb).congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [heatKernel_eq_mul_heatKernel_sqrt_two z hr x]
  ring

/-- **The outer/inner comparison from Gram bounds**: if the Gaussian energies at scale `√2 r` of
the fields `W_i` are at most `E` and the energy inside `B_T(z)` of every combination `∑ ξ_i W_i`
is at least `m |ξ|²`, then the energy outside `B_T(z)` of every combination is at most
`2^{d/2} exp(-T²/(8r²)) d E / m` times its energy inside. -/
theorem outer_le_of_gaussianGram (hr : r ≠ 0) (hT : 0 ≤ T) (W : Fin d → Vec d → Vec d)
    {E m : ℝ} (hm : 0 < m) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x) ≤ E)
    (hlow : ∀ ξ : Vec d, m * euclideanSq ξ ≤
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x)) (ξ : Vec d) :
    ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) * (d * E / m) *
        ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) := by
  have hε0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) := by positivity
  have hr2 := sqrt_two_mul_ne_zero hr
  let g : Vec d → ℝ := fun x => (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
    ((d : ℝ) * ∑ i, ξ i ^ 2 * (heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)))
  have hgint : Integrable g :=
    ((integrable_finsetSum _ fun i _ => (hW i).const_mul _).const_mul _).const_mul _
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg hε0 (mul_nonneg (Nat.cast_nonneg d)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (mul_nonneg (heatKernel_pos_of_ne z hr2 x).le (zero_le_euclideanSq _))))
  have hpt : ∀ x ∈ (ball z T)ᶜ,
      heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) ≤ g x := by
    intro x hx
    have h1 := heatKernel_le_of_mem_compl_ball z hr hT hx
    have h2 := euclideanSq_sum_smul_le ξ (fun i => W i x)
    have hk2 := (heatKernel_pos_of_ne z hr2 x).le
    have hsum : ∑ i, ξ i ^ 2 * (heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)) =
        heatKernel z (Real.sqrt 2 * r) x * ∑ i, ξ i ^ 2 * euclideanSq (W i x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    calc heatKernel z r x * euclideanSq (∑ i, ξ i • W i x)
        ≤ ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
            heatKernel z (Real.sqrt 2 * r) x) *
            ((d : ℝ) * ∑ i, ξ i ^ 2 * euclideanSq (W i x)) :=
          mul_le_mul h1 h2 (zero_le_euclideanSq _) (mul_nonneg hε0 hk2)
      _ = g x := by
          simp only [g]
          rw [hsum]
          ring
  have hA : ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) ≤
      ∫ x in (ball z T)ᶜ, g x :=
    integral_mono_of_nonneg (Eventually.of_forall fun x =>
        mul_nonneg (heatKernel_pos_of_ne z hr x).le (zero_le_euclideanSq _))
      hgint.integrableOn
      ((ae_restrict_iff' (measurableSet_ball z T).compl).2 (Eventually.of_forall hpt))
  have hB : ∫ x in (ball z T)ᶜ, g x ≤ ∫ x, g x :=
    setIntegral_le_integral hgint (Eventually.of_forall hg0)
  have hC : ∫ x, g x ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      ((d : ℝ) * (E * euclideanSq ξ)) := by
    simp only [g]
    rw [integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun i _ => (hW i).const_mul _]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)) hε0
    simp_rw [integral_const_mul]
    calc ∑ i, ξ i ^ 2 * ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)
        ≤ ∑ i, ξ i ^ 2 * E :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE i) (sq_nonneg _)
      _ = E * euclideanSq ξ := by
          simp only [euclideanSq, dot, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hD : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      ((d : ℝ) * (E * euclideanSq ξ)) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) * (d * E / m) *
        ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x) := by
    have hc : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) * (d * E / m) :=
      mul_nonneg hε0 (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hE0) hm.le)
    have he : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
        ((d : ℝ) * (E * euclideanSq ξ)) =
        (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) * (d * E / m) *
          (m * euclideanSq ξ) := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left (hlow ξ) hc
  exact hA.trans (hB.trans (hC.trans hD))

/-- **The almost sure hypotheses of Lemma 4.22 from Gram bounds of a spanning family**: as
`LocalizationApproximationAtUniform.of_span`, with the integrability and the outer/inner
comparison given by the Gaussian energies at scale `√2 r` of the spanning fields (at most `E`)
and the lower Gram bound `m` inside `B_T(z)`; any `κ ≥ 2^{d/2} exp(-T²/(8r²)) d E / m` works. -/
theorem LocalizationApproximationAtUniform.of_gaussianGram {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hr : r ≠ 0) {S σ θ C : ℝ} {B : LocalizedBasis a z T S σ θ C} {p q : Vec d}
    {η κ Zv E m : ℝ} (hT : 0 ≤ T) (hη : 0 ≤ η)
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (W : Fin d → Vec d → Vec d) (hm : 0 < m) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x) ≤ E)
    (hlow : ∀ ξ : Vec d, m * euclideanSq ξ ≤
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, ξ i • W i x))
    (hκ : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) * (d * E / m) ≤ κ)
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x)
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
  have hc0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) * (d * E / m) :=
    mul_nonneg (by positivity) (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hE0) hm.le)
  refine LocalizationApproximationAtUniform.of_span hΛ hr hT hη (hc0.trans hκ) hsmall W
    (fun i => Integrable.heatKernel_of_sqrt_two z hr (hW i)) hrep (fun ξ => ?_) hAV hVA hZ
  refine (outer_le_of_gaussianGram hr hT W hm hE0 hW hE hlow ξ).trans ?_
  refine mul_le_mul_of_nonneg_right hκ (setIntegral_nonneg (measurableSet_ball z T) fun x _ =>
    mul_nonneg (heatKernel_pos_of_ne z hr x).le (zero_le_euclideanSq _))

end QSH
