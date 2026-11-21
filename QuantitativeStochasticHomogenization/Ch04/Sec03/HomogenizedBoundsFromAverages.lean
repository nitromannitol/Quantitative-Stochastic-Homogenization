import QuantitativeStochasticHomogenization.Ch04.Sec03.EnergyFromRate

/-!
# The bounds on `ā` from the expectations of the averages

Jensen's inequality, first for the heat kernel average and then for the expectation, gives
`|E ∫ Φ_{0,r} G ξ|² ≤ E ∫ Φ_{0,r} G ξ·aG ξ` and `|E ∫ Φ_{0,r} aG ξ|² ≤ Λ E ∫ Φ_{0,r} G ξ·aG ξ`,
the latter by `|av|² ≤ Λ v·av` (`euclideanSq_coefficient_mulVec_le`). Letting `r → ∞` in the
expectations (1) of the averages gives `|ξ|² ≤ ξ·āξ` and `|āξ|² ≤ Λ ξ·āξ`, hence `I ≤ ā ≤ Λ I`
(`homogenizedMatrixBounds_of_expectedAverages`). Consequently (5.58) holds without the
measurability of the Dirichlet energies (`estimate558_of_heatBound_and_rate`).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- Every matrix satisfies `ξ·Mξ ≤ K |ξ|²` for some `K`. -/
theorem exists_dot_mulVec_le (M : Mat d) :
    ∃ K : ℝ, ∀ ξ : Vec d, dot ξ (M.mulVec ξ) ≤ K * euclideanSq ξ := by
  refine ⟨∑ i, ∑ j, |M i j|, fun ξ => ?_⟩
  have hb : ∀ i j, ξ i * (M i j * ξ j) ≤ |M i j| * euclideanSq ξ := by
    intro i j
    have h1 := abs_apply_le_euclideanNorm ξ i
    have h2 := abs_apply_le_euclideanNorm ξ j
    have h3 : |ξ i| * |ξ j| ≤ euclideanSq ξ := by
      rw [← euclideanNorm_sq]
      nlinarith [abs_nonneg (ξ i), abs_nonneg (ξ j), euclideanNorm_nonneg ξ]
    calc ξ i * (M i j * ξ j) ≤ |ξ i * (M i j * ξ j)| := le_abs_self _
      _ = |M i j| * (|ξ i| * |ξ j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ |M i j| * euclideanSq ξ := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  calc dot ξ (M.mulVec ξ) = ∑ i, ∑ j, ξ i * (M i j * ξ j) := by
        simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |M i j| * euclideanSq ξ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = (∑ i, ∑ j, |M i j|) * euclideanSq ξ := by simp only [Finset.sum_mul]

/-- `|a v|² ≤ Λ v·av` for a coefficient field. -/
theorem euclideanSq_coefficient_mulVec_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (x v : Vec d) :
    euclideanSq ((a x).mulVec v) ≤ Λ * dot v ((a x).mulVec v) := by
  have hcs := dot_mulVec_sq_le (a.symmetric x) (fun ξ => (a.elliptic x ξ).1) ((a x).mulVec v) v
  have h2 := (a.elliptic x ((a x).mulVec v)).2
  have hv0 : 0 ≤ dot v ((a x).mulVec v) := (euclideanSq_nonneg v).trans (a.elliptic x v).1
  have he : dot ((a x).mulVec v) ((a x).mulVec v) = euclideanSq ((a x).mulVec v) := rfl
  rw [he] at hcs
  by_cases hs : euclideanSq ((a x).mulVec v) = 0
  · rw [hs]; exact mul_nonneg hΛ hv0
  · have hs' : 0 < euclideanSq ((a x).mulVec v) :=
      lt_of_le_of_ne (euclideanSq_nonneg _) (Ne.symm hs)
    have h3 : euclideanSq ((a x).mulVec v) ^ 2 ≤
        Λ * euclideanSq ((a x).mulVec v) * dot v ((a x).mulVec v) :=
      hcs.trans (mul_le_mul_of_nonneg_right h2 hv0)
    have h4 : euclideanSq ((a x).mulVec v) * euclideanSq ((a x).mulVec v) ≤
        euclideanSq ((a x).mulVec v) * (Λ * dot v ((a x).mulVec v)) := by nlinarith
    exact le_of_mul_le_mul_left h4 hs'

/-- **The averaged flux is bounded by the averaged energy**: `|∫ Φ av|² ≤ Λ ∫ Φ v·av`. -/
theorem euclideanSq_fluxAverage_le_energy (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (y : Vec d)
    {r : ℝ} (hr : 0 < r) {v : Vec d → Vec d}
    (hav : Integrable fun x => heatKernel y r x • (a x).mulVec (v x))
    (hE : Integrable fun x => heatKernel y r x * dot (v x) ((a x).mulVec (v x))) :
    euclideanSq (∫ x, heatKernel y r x • (a x).mulVec (v x)) ≤
      Λ * ∫ x, heatKernel y r x * dot (v x) ((a x).mulVec (v x)) := by
  have havm : AEStronglyMeasurable (fun x => (a x).mulVec (v x)) volume :=
    (aemeasurable_pi_iff.mpr fun i =>
      (aestronglyMeasurable_apply_of_heatKernel_smul y hr hav i).aemeasurable).aestronglyMeasurable
  have hc : ∀ i, AEStronglyMeasurable (fun x => (a x).mulVec (v x) i) volume := fun i =>
    (continuous_apply i).comp_aestronglyMeasurable havm
  have hsqm : AEStronglyMeasurable
      (fun x => heatKernel y r x * euclideanSq ((a x).mulVec (v x))) volume := by
    simp only [euclideanSq, dot]
    exact (heatKernel_aestronglyMeasurable y r).mul (Finset.aestronglyMeasurable_fun_sum _
      fun i _ => (hc i).mul (hc i))
  have hpt : ∀ x, heatKernel y r x * euclideanSq ((a x).mulVec (v x)) ≤
      Λ * (heatKernel y r x * dot (v x) ((a x).mulVec (v x))) := fun x => by
    have h0 := heatKernel_nonneg y r x
    have := mul_le_mul_of_nonneg_left (euclideanSq_coefficient_mulVec_le a hΛ x (v x)) h0
    linarith
  have hav2 : Integrable fun x => heatKernel y r x * euclideanSq ((a x).mulVec (v x)) :=
    (hE.const_mul Λ).mono' hsqm (Eventually.of_forall fun x => by
      have h0 := heatKernel_nonneg y r x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (euclideanSq_nonneg _))]
      exact hpt x)
  refine (euclideanSq_integral_heatKernel_le y hr hav hav2).trans ?_
  rw [← integral_const_mul]
  exact integral_mono hav2 (hE.const_mul Λ) hpt

/-- Jensen's inequality for the expectation of a square. -/
theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Integrable f P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  set m := ∫ ω, f ω ∂P with hm
  have hexp : (fun ω => (f ω - m) ^ 2) = fun ω => f ω ^ 2 - 2 * m * f ω + m ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => f ω ^ 2 - 2 * m * f ω) P := hf2.sub (hf.const_mul _)
  have h0 : 0 ≤ ∫ ω, (f ω - m) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hc : ∫ _ω, m ^ 2 ∂P = m ^ 2 := by simp
  rw [hexp, integral_add i1 (integrable_const _), integral_sub hf2 (hf.const_mul _),
    integral_const_mul, hc, ← hm] at h0
  nlinarith

/-- Jensen's inequality for the expectation of a random vector: `|E V|² ≤ E |V|²`. -/
theorem euclideanSq_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → Vec d} (hV : Integrable V P)
    (hV2 : Integrable (fun ω => euclideanSq (V ω)) P) :
    euclideanSq (∫ ω, V ω ∂P) ≤ ∫ ω, euclideanSq (V ω) ∂P := by
  have hc : ∀ k, Integrable (fun ω => V ω k) P := Integrable.eval hV
  have hc2 : ∀ k, Integrable (fun ω => V ω k ^ 2) P := fun k =>
    hV2.mono' ((hc k).aestronglyMeasurable.pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← euclideanNorm_sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_le_euclideanNorm (V ω) k) 2)
  have hsum : euclideanSq (∫ ω, V ω ∂P) = ∑ k, (∫ ω, V ω k ∂P) ^ 2 := by
    simp only [euclideanSq, dot]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_integral hc k, sq]
  have hsum2 : ∫ ω, euclideanSq (V ω) ∂P = ∑ k, ∫ ω, V ω k ^ 2 ∂P := by
    simp only [euclideanSq, dot]
    rw [integral_finsetSum]
    · simp only [sq]
    · intro k _
      simpa only [sq] using hc2 k
  rw [hsum, hsum2]
  exact Finset.sum_le_sum fun k _ => sq_integral_le_integral_sq (hc k) (hc2 k)

/-- **`I ≤ ā ≤ Λ I` from the expectations of the averages.** -/
theorem homogenizedMatrixBounds_of_expectedAverages {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (S : HomogenizationData P) (hΛ : 0 ≤ Λ)
    (hint : AveragesIntegrable P S) {β : ℝ} (hβ : 0 < β) (hexp : ExpectedAveragesEstimate P S β) :
    HomogenizedMatrixBounds S.homogenized Λ := by
  obtain ⟨C, hC, hE⟩ := hexp
  intro ξ
  have hn0 : 0 ≤ euclideanNorm ξ := euclideanNorm_nonneg ξ
  have hCn : 0 ≤ C * euclideanNorm ξ := mul_nonneg hC.le hn0
  have hcont : Continuous fun v : Vec d => euclideanSq v := by
    unfold euclideanSq dot; fun_prop
  have key : ∀ r : ℝ, 1 ≤ r →
      euclideanSq ξ ≤ dot ξ (S.homogenized.mulVec ξ) +
        (C * euclideanSq ξ + 2 * (C * euclideanNorm ξ) * (euclideanNorm ξ + C * euclideanNorm ξ) +
          (C * euclideanNorm ξ) ^ 2) * r ^ (-β) ∧
      euclideanNorm (S.homogenized.mulVec ξ) ^ 2 ≤ Λ * dot ξ (S.homogenized.mulVec ξ) +
        (Λ * (C * euclideanSq ξ) + 2 * (C * euclideanNorm ξ) *
          (euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ) +
          (C * euclideanNorm ξ) ^ 2) * r ^ (-β) := by
    intro r hr
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    obtain ⟨hi1, hi2, hi3, hb1, hb2, hb3⟩ := hE 0 r hr ξ
    have hρ0 : 0 ≤ r ^ (-β) := Real.rpow_nonneg hr0.le _
    have hρ1 : r ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith)
    have hP : ∀ᵐ a ∂P, euclideanSq (∫ x, heatKernel 0 r x • correctedField S a ξ x) ≤
        ∫ x, heatKernel 0 r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
      filter_upwards [hint 0] with a ha
      obtain ⟨h1, h2, h3⟩ := ha r hr ξ
      exact (euclideanSq_averages_le_energy a hΛ 0 hr0 h1 h2 h3).1
    have hF : ∀ᵐ a ∂P,
        euclideanSq (∫ x, heatKernel 0 r x • (a x).mulVec (correctedField S a ξ x)) ≤
        Λ * ∫ x, heatKernel 0 r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
      filter_upwards [hint 0] with a ha
      obtain ⟨-, h2, h3⟩ := ha r hr ξ
      exact euclideanSq_fluxAverage_le_energy a hΛ 0 hr0 h2 h3
    have hPsq : Integrable
        (fun a => euclideanSq (∫ x, heatKernel 0 r x • correctedField S a ξ x)) P :=
      hi3.mono' (hcont.comp_aestronglyMeasurable hi1.aestronglyMeasurable) (by
        filter_upwards [hP] with a ha
        rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg _)]
        exact ha)
    have hFsq : Integrable (fun a =>
        euclideanSq (∫ x, heatKernel 0 r x • (a x).mulVec (correctedField S a ξ x))) P :=
      (hi3.const_mul Λ).mono' (hcont.comp_aestronglyMeasurable hi2.aestronglyMeasurable) (by
        filter_upwards [hF] with a ha
        rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg _)]
        exact ha)
    have hPm2 := (euclideanSq_integral_le hi1 hPsq).trans (integral_mono_ae hPsq hi3 hP)
    have hFm2 := (euclideanSq_integral_le hi2 hFsq).trans
      ((integral_mono_ae hFsq (hi3.const_mul Λ) hF).trans (le_of_eq (integral_const_mul _ _)))
    set Pm := ∫ a, (∫ x, heatKernel 0 r x • correctedField S a ξ x) ∂P with hPm
    set Fm := ∫ a, (∫ x, heatKernel 0 r x • (a x).mulVec (correctedField S a ξ x)) ∂P with hFm
    set Em := ∫ a, (∫ x, heatKernel 0 r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∂P with hEm
    set ρ := r ^ (-β) with hρ
    have hEle : Em ≤ dot ξ (S.homogenized.mulVec ξ) + C * euclideanSq ξ * ρ := by
      linarith [(abs_le.mp hb3).2]
    have e1 : (C * euclideanNorm ξ * ρ) ^ 2 ≤ (C * euclideanNorm ξ) ^ 2 * ρ := by
      have : ρ ^ 2 ≤ ρ := by nlinarith
      calc (C * euclideanNorm ξ * ρ) ^ 2 = (C * euclideanNorm ξ) ^ 2 * ρ ^ 2 := by ring
        _ ≤ (C * euclideanNorm ξ) ^ 2 * ρ := mul_le_mul_of_nonneg_left this (sq_nonneg _)
    have hδ1 : C * euclideanNorm ξ * ρ ≤ C * euclideanNorm ξ := mul_le_of_le_one_right hCn hρ1
    have hδ0 : 0 ≤ C * euclideanNorm ξ * ρ := mul_nonneg hCn hρ0
    constructor
    · have hn_le : euclideanNorm ξ ≤ euclideanNorm Pm + C * euclideanNorm ξ * ρ := by
        have h := euclideanNorm_sub_le Pm (Pm - ξ)
        rw [sub_sub_cancel] at h
        linarith
      have hp_le : euclideanNorm Pm ≤ euclideanNorm ξ + C * euclideanNorm ξ * ρ := by
        have h := euclideanNorm_add_le (Pm - ξ) ξ
        rw [sub_add_cancel] at h
        linarith
      have e2 : 2 * euclideanNorm Pm * (C * euclideanNorm ξ * ρ) ≤
          2 * (C * euclideanNorm ξ) * (euclideanNorm ξ + C * euclideanNorm ξ) * ρ := by
        have h : euclideanNorm Pm ≤ euclideanNorm ξ + C * euclideanNorm ξ := by linarith
        have h2 : 0 ≤ 2 * (C * euclideanNorm ξ) * ρ := by positivity
        calc 2 * euclideanNorm Pm * (C * euclideanNorm ξ * ρ)
            = 2 * (C * euclideanNorm ξ) * ρ * euclideanNorm Pm := by ring
          _ ≤ 2 * (C * euclideanNorm ξ) * ρ * (euclideanNorm ξ + C * euclideanNorm ξ) :=
            mul_le_mul_of_nonneg_left h h2
          _ = 2 * (C * euclideanNorm ξ) * (euclideanNorm ξ + C * euclideanNorm ξ) * ρ := by ring
      calc euclideanSq ξ = euclideanNorm ξ ^ 2 := (euclideanNorm_sq ξ).symm
        _ ≤ (euclideanNorm Pm + C * euclideanNorm ξ * ρ) ^ 2 := pow_le_pow_left₀ hn0 hn_le 2
        _ = euclideanSq Pm + 2 * euclideanNorm Pm * (C * euclideanNorm ξ * ρ) +
            (C * euclideanNorm ξ * ρ) ^ 2 := by rw [← euclideanNorm_sq Pm]; ring
        _ ≤ (dot ξ (S.homogenized.mulVec ξ) + C * euclideanSq ξ * ρ) +
            2 * (C * euclideanNorm ξ) * (euclideanNorm ξ + C * euclideanNorm ξ) * ρ +
            (C * euclideanNorm ξ) ^ 2 * ρ := by linarith
        _ = dot ξ (S.homogenized.mulVec ξ) + (C * euclideanSq ξ + 2 * (C * euclideanNorm ξ) *
            (euclideanNorm ξ + C * euclideanNorm ξ) + (C * euclideanNorm ξ) ^ 2) * ρ := by ring
    · have hq_le : euclideanNorm (S.homogenized.mulVec ξ) ≤
          euclideanNorm Fm + C * euclideanNorm ξ * ρ := by
        have h := euclideanNorm_sub_le Fm (Fm - S.homogenized.mulVec ξ)
        rw [sub_sub_cancel] at h
        linarith
      have hf_le : euclideanNorm Fm ≤
          euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ * ρ := by
        have h := euclideanNorm_add_le (Fm - S.homogenized.mulVec ξ) (S.homogenized.mulVec ξ)
        rw [sub_add_cancel] at h
        linarith
      have e2 : 2 * euclideanNorm Fm * (C * euclideanNorm ξ * ρ) ≤
          2 * (C * euclideanNorm ξ) *
            (euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ) * ρ := by
        have h : euclideanNorm Fm ≤
            euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ := by linarith
        have h2 : 0 ≤ 2 * (C * euclideanNorm ξ) * ρ := by positivity
        calc 2 * euclideanNorm Fm * (C * euclideanNorm ξ * ρ)
            = 2 * (C * euclideanNorm ξ) * ρ * euclideanNorm Fm := by ring
          _ ≤ 2 * (C * euclideanNorm ξ) * ρ *
              (euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ) :=
            mul_le_mul_of_nonneg_left h h2
          _ = 2 * (C * euclideanNorm ξ) *
              (euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ) * ρ := by ring
      have hΛE := mul_le_mul_of_nonneg_left hEle hΛ
      calc euclideanNorm (S.homogenized.mulVec ξ) ^ 2
          ≤ (euclideanNorm Fm + C * euclideanNorm ξ * ρ) ^ 2 :=
            pow_le_pow_left₀ (euclideanNorm_nonneg _) hq_le 2
        _ = euclideanSq Fm + 2 * euclideanNorm Fm * (C * euclideanNorm ξ * ρ) +
            (C * euclideanNorm ξ * ρ) ^ 2 := by rw [← euclideanNorm_sq Fm]; ring
        _ ≤ Λ * (dot ξ (S.homogenized.mulVec ξ) + C * euclideanSq ξ * ρ) +
            2 * (C * euclideanNorm ξ) *
              (euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ) * ρ +
            (C * euclideanNorm ξ) ^ 2 * ρ := by linarith
        _ = Λ * dot ξ (S.homogenized.mulVec ξ) + (Λ * (C * euclideanSq ξ) +
            2 * (C * euclideanNorm ξ) *
              (euclideanNorm (S.homogenized.mulVec ξ) + C * euclideanNorm ξ) +
            (C * euclideanNorm ξ) ^ 2) * ρ := by ring
  -- the limits `r → ∞`
  have hlim : ∀ c K : ℝ, Tendsto (fun r : ℝ => c + K * r ^ (-β)) atTop (𝓝 c) := fun c K => by
    have h1 : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
    have := h1.add ((tendsto_rpow_neg_atTop hβ).const_mul K)
    simpa using this
  have hlow : euclideanSq ξ ≤ dot ξ (S.homogenized.mulVec ξ) :=
    ge_of_tendsto (hlim _ _) (eventually_atTop.2 ⟨1, fun r hr => (key r hr).1⟩)
  have hq2 : euclideanNorm (S.homogenized.mulVec ξ) ^ 2 ≤ Λ * dot ξ (S.homogenized.mulVec ξ) :=
    ge_of_tendsto (hlim _ _) (eventually_atTop.2 ⟨1, fun r hr => (key r hr).2⟩)
  refine ⟨hlow, ?_⟩
  have hdq : dot ξ (S.homogenized.mulVec ξ) ≤
      euclideanNorm ξ * euclideanNorm (S.homogenized.mulVec ξ) :=
    (le_abs_self _).trans (abs_dot_le ξ _)
  have hq0 := euclideanNorm_nonneg (S.homogenized.mulVec ξ)
  have hqΛ : euclideanNorm (S.homogenized.mulVec ξ) ≤ Λ * euclideanNorm ξ := by
    by_cases hq : euclideanNorm (S.homogenized.mulVec ξ) = 0
    · rw [hq]; exact mul_nonneg hΛ hn0
    · have hqp : 0 < euclideanNorm (S.homogenized.mulVec ξ) := lt_of_le_of_ne hq0 (Ne.symm hq)
      have h1 := mul_le_mul_of_nonneg_left hdq hΛ
      have h2 : euclideanNorm (S.homogenized.mulVec ξ) * euclideanNorm (S.homogenized.mulVec ξ) ≤
          euclideanNorm (S.homogenized.mulVec ξ) * (Λ * euclideanNorm ξ) := by nlinarith
      exact le_of_mul_le_mul_left h2 hqp
  calc dot ξ (S.homogenized.mulVec ξ) ≤
        euclideanNorm ξ * euclideanNorm (S.homogenized.mulVec ξ) := hdq
    _ ≤ euclideanNorm ξ * (Λ * euclideanNorm ξ) := mul_le_mul_of_nonneg_left hqΛ hn0
    _ = Λ * euclideanSq ξ := by rw [← euclideanNorm_sq]; ring

/-- **(5.58) and Theorem 4.6 (ii)** from the structure (4.12) of `A₁`, Proposition 3.21 at every
exponent `τ ∈ (0, d)`, the expectations (1) of the averages, the measurability of `J₁`, of the
trial and of the flux averages, the bound from the heat identity (H), and the conclusions of
Propositions 4.11 and 4.12. -/
theorem estimate558_of_heatBound_and_rate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (hmeasF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdr : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK⟩ := exists_dot_mulVec_le S.homogenized
  obtain ⟨C1, μ1, -, hμ1, hr1⟩ := hrate 1 one_pos hdr
  obtain ⟨CN1, -, hN1⟩ := gaussianEnergyBound_of_rate S hK one_pos hμ1.le hr1
  have hint := averagesIntegrable_of_energyBound S hΛ.le hN1
  have hA := homogenizedMatrixBounds_of_expectedAverages S hΛ.le hint one_pos (hexp 1 one_pos hd1')
  have hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN :=
    fun τ hτ0 hτd => by
      obtain ⟨C, μ, -, hμ', hr⟩ := hrate τ hτ0 hτd
      exact gaussianEnergyBound_of_rate S (fun ξ => (hA ξ).2) hτ0 hμ'.le hr
  have hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d),
      Measurable (fun a => gradientAverage S a z r ξ) ∧
        Measurable (fun a => fluxAverage S a z r ξ) := fun z r ξ =>
    ⟨measurable_gradientAverage S z r ξ, measurable_fluxAverage_of S hmeasF z r ξ⟩
  refine estimate558_of_linearAverages hd S hΛ.le hA hspan hrate hN
    (trialIntegrable_of_energyBound S hΛ.le hN1) hmeasJ hmeasL ?_
    (fun β hβ hβd => trialObjectiveExpectation_of_expectedAverages S hint (hexp β hβ hβd))
    h411 h412 hs0 hs2
  intro s' α hs0' hs2' hα0 hα hF
  set τ : ℝ := (s' * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s' * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s' ≤ τ / ((d : ℝ) / 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hτ1
  obtain ⟨CN, -, hNτ⟩ := hN τ hτ0 hτ2
  exact linearAverageEstimate_of_heat hd1 S hΛ.le hs0' hα0
    (commutatorEstimate_of_flucJ1 hd1 S hΛ hA hspan hmeasJ hrate hN hexp hint hmeasA hs0' hs2'
      hα0 hα hF)
    hheat (measurable_commutatorNorm S hmeasF) (fun z r ξ => (hmeasA z r ξ).1) hNτ hτs hint

end QSH
