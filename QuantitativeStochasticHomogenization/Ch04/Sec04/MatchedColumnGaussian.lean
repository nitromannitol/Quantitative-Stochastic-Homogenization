import QuantitativeStochasticHomogenization.Ch04.Sec04.MatchedColumnDistances

/-!
# Matched columns in the Gaussian norm

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21, (4.91). The hypotheses of `localizationDistances_of_matched` in the form in which
the proof produces them: fields `V_i` on `B_T(z)` whose combinations are exactly the gradients of
`A₁` there, whose Gaussian Gram matrix inside `B_T(z)` is at least `m`, and which are within `ρ`
of the gradients of the localized coordinates in `L²(Φ_{z,r}, B_T(z))`. Combined with
`LocalizationApproximationAtUniform.of_corrected`, the almost sure hypotheses of Lemma 4.22
reduce to these properties of matched columns (the content of Lemma 4.21) together with the
properties of the corrected coordinates.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {z : Vec d} {T r : ℝ}

theorem coeFn_sum_smul_toLp {ι : Type*} [Fintype ι] (c : ι → ℝ) {f : ι → Vec d → ℝ}
    (hf : ∀ i, MemLp (f i) 2 (ballMeasure z T)) :
    (⇑(∑ i, c i • (hf i).toLp (f i)) : Vec d → ℝ) =ᵐ[ballMeasure z T]
      fun x => ∑ i, c i * f i x := by
  have h1 := Lp.coeFn_fun_finsetSum Finset.univ fun i => c i • (hf i).toLp (f i)
  have h2 : ∀ᵐ x ∂ballMeasure z T, ∀ i, (⇑(c i • (hf i).toLp (f i)) : Vec d → ℝ) x = c i * f i x := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (c i) ((hf i).toLp (f i)), (hf i).coeFn_toLp] with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  exact Finset.sum_congr rfl fun i _ => hx2 i

/-- The rescaled tuple of the `L²(B_T(z))` classes of the components of a field. -/
def scaledFieldTuple (hr : r ≠ 0) (V : Vec d → Vec d)
    (hV : ∀ k, MemLp (fun x => V x k) 2 (ballMeasure z T)) : Fin d → Lp ℝ 2 (ballMeasure z T) :=
  fun k => scaleLp hr ((hV k).toLp (fun x => V x k))

/-- **The lower bound of matched columns** from their Gaussian Gram bound: if
`m |c|² ≤ ∫_{B_T(z)} Φ_{z,r} |∑ c_i V_i|²`, then `(√m / d) ∑ |c_i| ≤ ‖∑ c_i G_i‖`. -/
theorem mul_sum_abs_le_norm_sum_scaledFieldTuple (hr : r ≠ 0) (hd : 0 < d)
    (V : Fin d → Vec d → Vec d) (hV : ∀ i k, MemLp (fun x => V i x k) 2 (ballMeasure z T))
    {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ c : Vec d, m * euclideanSq c ≤
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, c i • V i x)) (c : Vec d) :
    Real.sqrt m / d * ∑ i, |c i| ≤ ‖∑ i, c i • scaledFieldTuple hr (V i) (hV i)‖ := by
  set u : Fin d → Lp ℝ 2 (ballMeasure z T) := fun k =>
    ∑ i, c i • (hV i k).toLp (fun x => V i x k) with hu
  have hGc : ∑ i, c i • scaledFieldTuple hr (V i) (hV i) = fun k => scaleLp hr (u k) := by
    funext k
    simp only [hu, scaledFieldTuple, scaleLp_sum, scaleLp_smul, Finset.sum_apply, Pi.smul_apply]
  have h1 := integral_heat_euclideanSq_le hr u
  have h2 : ∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x) =
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, c i • V i x) := by
    refine integral_congr_ae ?_
    have := ae_all_iff.2 fun k => coeFn_sum_smul_toLp c (f := fun i x => V i x k)
      (fun i => hV i k)
    filter_upwards [this] with x hx
    congr 2
    funext k
    rw [hu, hx k]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h3 : (∑ i, |c i|) ^ 2 ≤ d * euclideanSq c := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    simp only [euclideanSq, dot]
    exact Finset.sum_congr rfl fun i _ => by rw [sq_abs, sq]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have key : (Real.sqrt m / d * ∑ i, |c i|) ^ 2 ≤
      ‖∑ i, c i • scaledFieldTuple hr (V i) (hV i)‖ ^ 2 := by
    have e : (Real.sqrt m / d * ∑ i, |c i|) ^ 2 = m / d ^ 2 * (∑ i, |c i|) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hm]
    rw [e, hGc]
    have h4 : m / d ^ 2 * (∑ i, |c i|) ^ 2 ≤ m / d ^ 2 * (d * euclideanSq c) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : m / d ^ 2 * (d * euclideanSq c) = (m * euclideanSq c) / d := by
      field_simp
    rw [h2] at h1
    calc m / d ^ 2 * (∑ i, |c i|) ^ 2 ≤ (m * euclideanSq c) / d := h4.trans (le_of_eq h5)
      _ ≤ (d * ‖fun k => scaleLp hr (u k)‖ ^ 2) / d :=
          div_le_div_of_nonneg_right ((hlow c).trans h1) hdpos.le
      _ = ‖fun k => scaleLp hr (u k)‖ ^ 2 := mul_div_cancel_left₀ _ hdpos.ne'
  have hX : 0 ≤ Real.sqrt m / d * ∑ i, |c i| :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hdpos.le)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  exact (pow_le_pow_iff_left₀ hX (norm_nonneg _) two_ne_zero).1 key

/-- **The closeness of a localized coordinate to a matched column** in the rescaled norm, from
the weighted `L²(Φ_{z,r}, B_T(z))` distance of the gradients. -/
theorem norm_scaled_coordinate_sub_le {Λ : ℝ} {a : CoefficientField d Λ} (hr : r ≠ 0)
    (w : LocalHarmonic a z T) (V : Vec d → Vec d)
    (hV : ∀ k, MemLp (fun x => V x k) 2 (ballMeasure z T)) :
    ‖(fun k => scaleLp hr (w.toPair.2 k)) - scaledFieldTuple hr V hV‖ ≤
      Real.sqrt (∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x - V x)) := by
  refine (norm_scaleLp_sub_le hr _ _).trans
    (Real.sqrt_le_sqrt (le_of_eq (integral_congr_ae ?_)))
  have h1 := ae_all_iff.2 fun k => w.toPair_snd_ae k
  have h2 := ae_all_iff.2 fun k => (hV k).coeFn_toLp
  filter_upwards [h1, h2] with x hx1 hx2
  congr 2
  funext k
  rw [hx1 k, hx2 k, Pi.sub_apply]

/-- **The rescaled gradient of an element of `A₁` that is a combination of matched columns.** -/
theorem scaled_ballGrad_eq_sum {Λ : ℝ} {a : CoefficientField d Λ} (hr : r ≠ 0)
    (w : HarmonicA1 a) (V : Fin d → Vec d → Vec d)
    (hV : ∀ i k, MemLp (fun x => V i x k) 2 (ballMeasure z T)) (c : Vec d)
    (hw : ∀ᵐ x ∂ballMeasure z T, w.grad x = ∑ i, c i • V i x) :
    (fun k => scaleLp hr (w.ballGrad z T k)) =
      ∑ i, c i • scaledFieldTuple hr (V i) (hV i) := by
  funext k
  have hk : w.ballGrad z T k = ∑ i, c i • (hV i k).toLp (fun x => V i x k) := by
    refine Lp.ext ?_
    unfold HarmonicA1.ballGrad
    filter_upwards [(w.memLp_grad_ball (z := z) (T := T) k).coeFn_toLp,
      coeFn_sum_smul_toLp c (f := fun i x => V i x k) (fun i => hV i k), hw] with x h1 h2 h3
    rw [h1, h2]
    show w.grad x k = ∑ i, c i * V i x k
    rw [h3]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hk, scaleLp_sum]
  simp only [scaleLp_smul, Finset.sum_apply, Pi.smul_apply, scaledFieldTuple]

/-- **The almost sure hypotheses of Lemma 4.22 from corrected coordinates and matched columns**:
the hypotheses of `LocalizationApproximationAtUniform.of_corrected`, with the approximation
property of Lemma 4.21 given by fields `V_i` on `B_T(z)` whose combinations are exactly the
gradients of `A₁` there, with Gaussian Gram matrix at least `m_V > 0` inside `B_T(z)`, and within
`ρ ≤ √m_V / (2d)` of the gradients of the localized coordinates in `L²(Φ_{z,r}, B_T(z))`. -/
theorem LocalizationApproximationAtUniform.of_matched {Λ : ℝ} {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hd : 0 < d) (hr : 0 < r) (hrT : r ≤ T) {S σ θ C : ℝ}
    {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} {η κ Zv E ε mV ρ : ℝ}
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (u : Fin d → Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (hu : ∀ i, MemLp (u i) 2 (ballMeasure z r))
    (hWT : ∀ i j, MemLp (fun x => W i x j) 2 (ballMeasure z T))
    (hgrad : ∀ i, HasWeakGradient (ball z r) (u i) (W i)) (c : Fin d → ℝ)
    (hsub : ∀ i, ∫ x in ball z r, (u i x - (x - z) i - c i) ^ 2 ≤
      ε ^ 2 * r ^ 2 * volume.real (ball z r))
    (hε : (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (W i x) ≤ E)
    (hκ : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      (d * E / heatGramConstant d) ≤ κ)
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d, ∀ᵐ x, w.grad x = ∑ i, ξ i • W i x)
    (V : Fin d → Vec d → Vec d) (hV : ∀ i k, MemLp (fun x => V i x k) 2 (ballMeasure z T))
    (hmV : 0 < mV)
    (hVlow : ∀ c : Vec d, mV * euclideanSq c ≤
      ∫ x in ball z T, heatKernel z r x * euclideanSq (∑ i, c i • V i x))
    (hVspan : ∀ w : HarmonicA1 a, ∃ c : Vec d, ∀ᵐ x ∂ballMeasure z T,
      w.grad x = ∑ i, c i • V i x)
    (hVmem : ∀ c : Vec d, ∃ w : HarmonicA1 a, ∀ᵐ x ∂ballMeasure z T,
      w.grad x = ∑ i, c i • V i x)
    (hρ0 : 0 ≤ ρ)
    (hVclose : ∀ i, ∫ x in ball z T, heatKernel z r x *
      euclideanSq ((B.coordinate i).grad x - V i x) ≤ ρ ^ 2)
    (hρ : ρ ≤ Real.sqrt mV / d / 2)
    (hη : 2 * (2 * linearCoefficient d Λ p q + 1) * ρ / (Real.sqrt mV / d) ≤ η)
    (hZ : (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
          (κ * (d * (2 * linearCoefficient d Λ p q + 1) ^ 2)) +
        linearCoefficient d Λ p q / 2 *
          ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)))) +
      ((d : ℝ) ^ 2 * Λ * (2 * (2 * linearCoefficient d Λ p q + 1) + η) / 2 +
        linearCoefficient d Λ p q) * η ≤ Zv) :
    LocalizationApproximationAtUniform a z T r hr.ne' B p q η κ Zv := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hμ : 0 < Real.sqrt mV / d := div_pos (Real.sqrt_pos.2 hmV) hdpos
  have hdist := localizationDistances_of_matched (L := 2 * linearCoefficient d Λ p q + 1)
    hr.ne' B (fun i => scaledFieldTuple hr.ne' (V i) (hV i)) hμ hρ0 hρ
    (fun w => (hVspan w).imp fun c hc => scaled_ballGrad_eq_sum hr.ne' w V hV c hc)
    (fun c => (hVmem c).imp fun w hw => scaled_ballGrad_eq_sum hr.ne' w V hV c hw)
    (fun i => (norm_scaled_coordinate_sub_le hr.ne' (B.coordinate i) (V i) (hV i)).trans
      ((Real.sqrt_le_sqrt (hVclose i)).trans (le_of_eq (Real.sqrt_sq hρ0))))
    (mul_sum_abs_le_norm_sum_scaledFieldTuple hr.ne' hd V hV hmV.le hVlow)
  have hη0 : 0 ≤ η := by
    refine le_trans ?_ hη
    have hL : 0 ≤ 2 * linearCoefficient d Λ p q + 1 := by
      have : 0 ≤ linearCoefficient d Λ p q := by
        simp only [linearCoefficient]
        exact add_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)
          (Nat.cast_nonneg d)) hΛ) (Finset.sum_nonneg fun k _ => abs_nonneg _)
      linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hρ0) hμ.le
  exact LocalizationApproximationAtUniform.of_corrected hΛ hr hrT hη0 hsmall u W hu hWT hgrad c
    hsub hε hE0 hW hE hκ hrep
    (fun w hw => (hdist.1 w hw).imp fun c hc => hc.trans hη)
    (fun c hc => (hdist.2 c hc).imp fun w hw => hw.trans hη) hZ

end QSH
