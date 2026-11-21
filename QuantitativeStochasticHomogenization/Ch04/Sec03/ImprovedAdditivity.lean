import QuantitativeStochasticHomogenization.Ch04.Sec03.AdditivityFromTrial

/-!
# The improvement `Add(s, α + η)` of Proposition 4.10

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10, the statement `Fluc(s, α) ⟹ Add(s, α + η)`.

The additivity defect `Δ = ∫ Φ_{z,ρ} J₁(Φ_{·,r}) - J₁(Φ_{z,R})` is nonnegative and at most the
average `G` of the trial gap, which is `O_{s/2}(C r^{-2α})` under the trial gap estimate. On the
other hand Proposition 4.3, at an exponent `τ > s d/2`, bounds `Δ` by `2δ + B`, where
`δ = 14 C r^{-μ}` is deterministic and `B = K (∫ Φ_{z,ρ}(y) (X(y)/r)^{τ/s} dy + (X(z)/R)^{τ/s})`
collects the events below the random scales `X` of Proposition 4.3, so that `B ≤ O_s(C r^{-τ/s})`.
Since `0 ≤ Δ ≤ G` and `Δ ≤ 2δ + B`, `Δ ≤ √(2δ) √G + B`, which is `O_s(C r^{-α-η})` with
`η = min(μ/2, τ/s - d/2)` (`addJ1_improved_of_trialGap`).

Proved here also: Lemma A.4 for the heat kernel averages at every exponent
(`osBound_integral_heatKernel_mul`) and the triangle inequality with a constant at every exponent
(`osBound_add_of_pos`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Two rules of `O_s` at every exponent -/

/-- The constant of Lemma A.4 used here: `1` for `t ≥ 1`, and `(1 + (1 - t)/(t log 2))^{1/t}` below. -/
def averageConstant (t : ℝ) : ℝ := max 1 ((1 + (1 - t) / (t * Real.log 2)) ^ t⁻¹)

theorem one_le_averageConstant (t : ℝ) : 1 ≤ averageConstant t := le_max_left _ _

/-- **Lemma A.4 for heat kernel averages**: for a jointly measurable nonnegative family with
`F(y) ≤ O_t(θ)` for every `y`, almost surely `y ↦ Φ_{z,ρ}(y) F(y)` is integrable and
`∫ Φ_{z,ρ}(y) F(y) dy ≤ O_t(C_t θ)`. -/
theorem osBound_integral_heatKernel_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Vec d → Ω → ℝ} (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ y ω, 0 ≤ F y ω) {t θ : ℝ} (hF : ∀ y, OsBound P (F y) t θ) (z : Vec d) {ρ : ℝ}
    (hρ : 0 < ρ) :
    (∀ᵐ ω ∂P, Integrable fun y => heatKernel z ρ y * F y ω) ∧
      OsBound P (fun ω => ∫ y, heatKernel z ρ y * F y ω) t (averageConstant t * θ) := by
  have hθ : 0 < θ := (hF z).scale_pos
  have hΦm : Measurable fun y : Vec d => heatKernel z ρ y :=
    ((continuous_heatKernel_uncurry ρ).comp (continuous_const.prodMk continuous_id)).measurable
  set X : Vec d → Ω → ℝ := fun y ω => heatKernel z ρ y * F y ω with hX
  have hXm : Measurable (Function.uncurry X) := (hΦm.comp measurable_fst).mul hFm
  have hX0 : ∀ y ω, 0 ≤ X y ω := fun y ω => mul_nonneg (heatKernel_nonneg _ _ _) (hF0 y ω)
  set w : Vec d → ℝ := fun y => heatKernel z ρ y * θ with hw
  have hwm : Measurable w := hΦm.mul_const _
  have hwi : Integrable w := (integrable_heatKernel z hρ).mul_const _
  have hwint : ∫ y, w y = θ := by rw [hw, integral_mul_const, integral_heatKernel z hρ, one_mul]
  have hwpos : 0 < ∫ y, w y := by rw [hwint]; exact hθ
  have hXos : ∀ y, OsBound P (X y) t (w y) := fun y => (hF y).const_mul (heatKernel_pos z hρ y)
  have ht : 0 < t := (hF z).exponent_pos
  rcases le_or_gt 1 t with ht1 | ht1
  · obtain ⟨h1, h2⟩ := osBound_integral ht1 hXm hX0 hwm hwi hwpos hXos
    rw [hwint] at h2
    exact ⟨h1, h2.mono_scale (le_mul_of_one_le_left hθ.le (one_le_averageConstant t))⟩
  · obtain ⟨h1, h2⟩ := osBound_integral_of_lt_one ht1 hXm hX0 hwm hwi hwpos hXos
    rw [hwint] at h2
    exact ⟨h1, h2.mono_scale (mul_le_mul_of_nonneg_right (le_max_right _ _) hθ.le)⟩

/-- **The triangle inequality at every exponent**, from `X + Y ≤ 2 max(X, Y)`. -/
theorem osBound_add_of_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {s θ₁ θ₂ : ℝ} (hX : OsBound P X s θ₁) (hY : OsBound P Y s θ₂) :
    OsBound P (fun ω => X ω + Y ω) s (2 * ((2 : ℝ) ^ s⁻¹ * max θ₁ θ₂)) := by
  refine ((osBound_max hX hY).const_mul two_pos).of_le (hX.1.add hY.1) fun ω => ?_
  have h1 := le_max_left (X ω) (Y ω)
  have h2 := le_max_right (X ω) (Y ω)
  linarith

/-! ## The improvement of additivity -/

section Improvement

variable {P : Measure (CoefficientField d Λ)}

theorem sqrt_bound_of_le {Δ G δ B : ℝ} (hΔ0 : 0 ≤ Δ) (hΔG : Δ ≤ G) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hΔ : Δ ≤ δ + B) : Δ ≤ Real.sqrt δ * Real.sqrt G + B := by
  have hG0 : 0 ≤ G := hΔ0.trans hΔG
  have hsΔ := Real.sqrt_le_sqrt hΔG
  have hsδ0 := Real.sqrt_nonneg δ
  have hsΔ0 := Real.sqrt_nonneg Δ
  have hΔsq := Real.mul_self_sqrt hΔ0
  have hδsq := Real.mul_self_sqrt hδ
  rcases le_total Δ δ with h | h
  · have h1 : Real.sqrt Δ ≤ Real.sqrt δ := Real.sqrt_le_sqrt h
    nlinarith [mul_le_mul h1 hsΔ hsΔ0 hsδ0]
  · have h1 : Real.sqrt δ ≤ Real.sqrt Δ := Real.sqrt_le_sqrt h
    have h2 : δ ≤ Real.sqrt δ * Real.sqrt G := by
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans hsΔ) hsδ0]
    linarith

theorem abs_sub_le_add_rpow_of_scale {v c b δ K x r' κ : ℝ} (hr' : 0 < r') (hκ : 0 ≤ κ)
    (hx : 0 ≤ x) (hδ0 : 0 ≤ δ) (hK : |v - c| ≤ K) (hb : x ≤ r' → |v - c| ≤ b) (hbδ : b ≤ δ) :
    |v - c| ≤ δ + K * (r'⁻¹ * x) ^ κ := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hK
  have hpow0 : 0 ≤ (r'⁻¹ * x) ^ κ := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hr'.le) hx) _
  by_cases hxr : x ≤ r'
  · have := hb hxr
    nlinarith [mul_nonneg hK0 hpow0]
  · have h1 : 1 ≤ r'⁻¹ * x := by
      rw [← div_eq_inv_mul, le_div_iff₀ hr']; linarith
    have h2 : 1 ≤ (r'⁻¹ * x) ^ κ := Real.one_le_rpow h1 hκ
    have h3 : K ≤ K * (r'⁻¹ * x) ^ κ := le_mul_of_one_le_right hK0 h2
    linarith

theorem improved_scale_first {r C A₂ C₂ μ α η : ℝ} (hr : 1 ≤ r) (hC : 0 < C) (hA₂ : 0 < A₂)
    (hC₂ : 0 < C₂) (hη : η ≤ μ / 2) :
    Real.sqrt (2 * (14 * C * r ^ (-μ))) * (A₂ * (C₂ * r ^ (-(2 * α)))) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (28 * C) * (A₂ * C₂) ^ (1 / 2 : ℝ) * r ^ (-(α + η)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have e1 : Real.sqrt (2 * (14 * C * r ^ (-μ))) = Real.sqrt (28 * C) * r ^ (-μ / 2) := by
    rw [show 2 * (14 * C * r ^ (-μ)) = 28 * C * r ^ (-μ) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (r ^ (-μ)), ← Real.rpow_mul hr0.le]
    congr 2; ring
  have e2 : (A₂ * (C₂ * r ^ (-(2 * α)))) ^ (1 / 2 : ℝ) =
      (A₂ * C₂) ^ (1 / 2 : ℝ) * r ^ (-α) := by
    rw [← mul_assoc, Real.mul_rpow (by positivity) (Real.rpow_nonneg hr0.le _),
      ← Real.rpow_mul hr0.le]
    congr 2; ring
  have e3 : r ^ (-μ / 2) * r ^ (-α) = r ^ (-(α + μ / 2)) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have h4 : r ^ (-(α + μ / 2)) ≤ r ^ (-(α + η)) := rpow_neg_le_rpow_neg hr (by linarith)
  have hc : 0 ≤ Real.sqrt (28 * C) * (A₂ * C₂) ^ (1 / 2 : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  rw [e1, e2]
  calc Real.sqrt (28 * C) * r ^ (-μ / 2) * ((A₂ * C₂) ^ (1 / 2 : ℝ) * r ^ (-α))
      = Real.sqrt (28 * C) * (A₂ * C₂) ^ (1 / 2 : ℝ) * (r ^ (-μ / 2) * r ^ (-α)) := by ring
    _ ≤ Real.sqrt (28 * C) * (A₂ * C₂) ^ (1 / 2 : ℝ) * r ^ (-(α + η)) := by
        rw [e3]; exact mul_le_mul_of_nonneg_left h4 hc

theorem improved_scale_second {r K s A₁ C' κ α η : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K) (hA₁ : 1 ≤ A₁)
    (hC' : 0 < C') (hακ : α + η ≤ κ) :
    K * (2 * ((2 : ℝ) ^ s⁻¹ * max (A₁ * (r⁻¹ * C') ^ κ) ((r⁻¹ * C') ^ κ))) ≤
      K * (2 * ((2 : ℝ) ^ s⁻¹ * (A₁ * C' ^ κ))) * r ^ (-(α + η)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hx0 : 0 ≤ (r⁻¹ * C') ^ κ := Real.rpow_nonneg (by positivity) _
  rw [max_eq_left (le_mul_of_one_le_left hx0 hA₁)]
  have e1 : (r⁻¹ * C') ^ κ = C' ^ κ * r ^ (-κ) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hr0.le) hC'.le, Real.inv_rpow hr0.le, Real.rpow_neg hr0.le]
    ring
  have h4 : r ^ (-κ) ≤ r ^ (-(α + η)) := rpow_neg_le_rpow_neg hr hακ
  have h0 : 0 ≤ K * (2 * ((2 : ℝ) ^ s⁻¹ * (A₁ * C' ^ κ))) := by
    have : 0 ≤ C' ^ κ := Real.rpow_nonneg hC'.le _
    have : 0 ≤ (2 : ℝ) ^ s⁻¹ := Real.rpow_nonneg (by norm_num) _
    positivity
  rw [e1]
  calc K * (2 * ((2 : ℝ) ^ s⁻¹ * (A₁ * (C' ^ κ * r ^ (-κ)))))
      = K * (2 * ((2 : ℝ) ^ s⁻¹ * (A₁ * C' ^ κ))) * r ^ (-κ) := by ring
    _ ≤ K * (2 * ((2 : ℝ) ^ s⁻¹ * (A₁ * C' ^ κ))) * r ^ (-(α + η)) :=
        mul_le_mul_of_nonneg_left h4 h0

/-- **Proposition 4.10, `Add(s, α + η)`**: under the inputs of Proposition 4.3 at an exponent
`τ ∈ (s d/2, ∞)` with rate `μ`, the trial gap estimate `O_{s/2}(C r^{-2α})` for some
`α ≤ d/2`, the almost sure integrability of the trial and the joint measurability of `J₁`,
`Add(s, α + η)` holds with `η = min(μ/2, τ/s - d/2)`. -/
theorem addJ1_improved_of_trialGap [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {s α τ C μ : ℝ} (hs0 : 0 < s) (hα : α ≤ (d : ℝ) / 2) (hτs : s * ((d : ℝ) / 2) < τ)
    (hC : 0 < C) (hμ : 0 < μ)
    (hrate : GaussianCorrectorRate P S τ C μ) (hgap : TrialGapEstimate P S (s / 2) (2 * α)) :
    AddJ1 P s (α + min (μ / 2) (τ / s - (d : ℝ) / 2)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hτ : 0 < τ := lt_of_le_of_lt (mul_nonneg hs0.le (by positivity)) hτs
  obtain ⟨C', hC', X, hXm, hX1, hX⟩ := proposition43 S hA hspan hτ hC hμ hrate
  obtain ⟨C₂, hC₂, hgap⟩ := hgap
  set κ : ℝ := τ / s with hκ
  have hκ0 : 0 < κ := div_pos hτ hs0
  have hκd : (d : ℝ) / 2 < κ := by rw [hκ, lt_div_iff₀ hs0]; linarith
  set η : ℝ := min (μ / 2) (κ - (d : ℝ) / 2) with hη
  set K : ℝ := 2 * |Λ| + 3 with hK
  have hK0 : 0 < K := by positivity
  set A₂ : ℝ := averageConstant (s / 2)
  set A₁ : ℝ := averageConstant s
  have hA₂ : 1 ≤ A₂ := one_le_averageConstant _
  have hA₁ : 1 ≤ A₁ := one_le_averageConstant _
  set c₁ : ℝ := Real.sqrt (28 * C) * (A₂ * C₂) ^ (1 / 2 : ℝ) with hc₁
  set c₂ : ℝ := K * (2 * ((2 : ℝ) ^ s⁻¹ * (A₁ * C' ^ κ))) with hc₂
  have hc₁0 : 0 < c₁ := mul_pos (Real.sqrt_pos.mpr (by positivity))
    (Real.rpow_pos_of_pos (by positivity) _)
  have hc₂0 : 0 < c₂ := by positivity
  refine ⟨2 * ((2 : ℝ) ^ s⁻¹ * (c₁ + c₂)), by positivity, ?_⟩
  intro z r R hr hrR p q hp hq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hR : 0 < R := hr0.trans hrR
  obtain ⟨hm, hos⟩ := hgap r hr p q hp hq
  set ρ := Real.sqrt (R ^ 2 - r ^ 2) with hρdef
  have hρ : 0 < ρ := sqrt_sq_sub_sq_pos hrR hr0.le
  have hJy : ∀ a : CoefficientField d Λ, Measurable fun y => J1Heat a y r p q := fun a =>
    (hmeasJ r p q).comp (measurable_const.prodMk measurable_id)
  have hint : ∀ a : CoefficientField d Λ,
      Integrable fun x => heatKernel z ρ x * J1Heat a x r p q := by
    intro a
    refine (integrable_heatKernel z hρ).mul_bdd (hJy a).aestronglyMeasurable
      (c := Λ * euclideanSq p + euclideanSq q) (Filter.Eventually.of_forall fun y => ?_)
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a y hr0 p q
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  refine ⟨Filter.Eventually.of_forall hint, ?_⟩
  -- the bounds on `J₁` and the homogenized energy
  have hp2 : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq2 : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  set c := homogenizedJ1 S.homogenized p q with hcdef
  have hcK := abs_homogenizedJ1_le hA hp.le hq.le
  have hJK : ∀ (a : CoefficientField d Λ) (y : Vec d) (r' : ℝ), 0 < r' →
      |J1Heat a y r' p q - c| ≤ K := by
    intro a y r' hr'
    obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a y hr' p q
    have : Λ * euclideanSq p ≤ |Λ| :=
      (mul_le_mul_of_nonneg_right (le_abs_self Λ) (euclideanSq_nonneg p)).trans
        (by nlinarith [abs_nonneg Λ])
    have := abs_sub (J1Heat a y r' p q) c
    rw [abs_of_nonneg h0] at this
    linarith
  set δ : ℝ := 14 * C * r ^ (-μ) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hpq2 : euclideanNorm p ^ 2 + euclideanNorm q ^ 2 ≤ 2 := by
    rw [euclideanNorm_sq, euclideanNorm_sq]; linarith
  -- the good-scale bound, at a fixed coefficient field
  have hgood : ∀ (a : CoefficientField d Λ) (y : Vec d) (r' : ℝ), r ≤ r' →
      (X a y ≤ r' → |J1Heat a y r' p q - c| ≤
        7 * (C * r' ^ (-μ)) * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2)) →
      |J1Heat a y r' p q - c| ≤ δ + K * (r'⁻¹ * X a y) ^ κ := by
    intro a y r' hrr' hb
    have hr'0 : 0 < r' := hr0.trans_le hrr'
    refine abs_sub_le_add_rpow_of_scale hr'0 hκ0.le (zero_le_one.trans (hX1 a y)) hδ0
      (hJK a y r' hr'0) hb ?_
    have h2 : r' ^ (-μ) ≤ r ^ (-μ) := Real.rpow_le_rpow_of_nonpos hr0 hrr' (by linarith)
    have h5 : 7 * (C * r' ^ (-μ)) * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2) ≤
        7 * (C * r ^ (-μ)) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC.le)
        (by norm_num)) hpq2 (by positivity)
        (mul_nonneg (by norm_num) (mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)))
    calc _ ≤ 7 * (C * r ^ (-μ)) * 2 := h5
      _ = δ := by rw [hδ]; ring
  -- the random variables
  set G : CoefficientField d Λ → ℝ :=
    fun a => ∫ y, heatKernel z ρ y * max (trialGap S a y r p q) 0 with hGdef
  obtain ⟨-, hG⟩ := osBound_integral_heatKernel_mul hm (fun _ _ => le_max_right _ _) hos z hρ
  have hG0 : ∀ a, 0 ≤ G a := fun a =>
    integral_nonneg fun y => mul_nonneg (heatKernel_nonneg _ _ _) (le_max_right _ _)
  have hsG : OsBound P (fun a => Real.sqrt (G a)) s
      ((A₂ * (C₂ * r ^ (-(2 * α)))) ^ (1 / 2 : ℝ)) := by
    have h := hG.rpow hG0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [show s / 2 / (1 / 2) = s by ring] at h
    simpa only [Real.sqrt_eq_rpow] using h
  set F : Vec d → CoefficientField d Λ → ℝ := fun y a => (r⁻¹ * X a y) ^ κ with hFdef
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_const.mul (hXm.comp measurable_swap)).pow_const κ
  have hF0 : ∀ y a, 0 ≤ F y a := fun y a =>
    Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hr0.le) (zero_le_one.trans (hX1 a y))) _
  have hFos : ∀ y, OsBound P (F y) s ((r⁻¹ * C') ^ κ) := by
    intro y
    have h := ((hX y).1.const_mul (inv_pos.mpr hr0)).rpow
      (fun a => mul_nonneg (inv_nonneg.mpr hr0.le) (zero_le_one.trans (hX1 a y))) hκ0
    rwa [show τ / κ = s by rw [hκ]; field_simp] at h
  obtain ⟨hB₁i, hB₁⟩ := osBound_integral_heatKernel_mul hFm hF0 hFos z hρ
  have hB₂ : OsBound P (fun a => (R⁻¹ * X a z) ^ κ) s ((r⁻¹ * C') ^ κ) := by
    have h := ((hX z).1.const_mul (inv_pos.mpr hR)).rpow
      (fun a => mul_nonneg (inv_nonneg.mpr hR.le) (zero_le_one.trans (hX1 a z))) hκ0
    rw [show τ / κ = s by rw [hκ]; field_simp] at h
    refine h.mono_scale (Real.rpow_le_rpow (by positivity) ?_ hκ0.le)
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hr0 hrR.le) hC'.le
  have hB : OsBound P (fun a => (∫ y, heatKernel z ρ y * F y a) + (R⁻¹ * X a z) ^ κ) s
      (2 * ((2 : ℝ) ^ s⁻¹ * max (A₁ * (r⁻¹ * C') ^ κ) ((r⁻¹ * C') ^ κ))) :=
    osBound_add_of_pos hB₁ hB₂
  -- the stochastic bound of the right-hand side
  have h2δ : 0 < 2 * δ := by positivity
  have hT1 := hsG.const_mul (Real.sqrt_pos.mpr h2δ)
  have hT2 := hB.const_mul hK0
  have hT := osBound_add_of_pos hT1 hT2
  -- measurability of the additivity defect
  have hΦm : Measurable fun y : Vec d => heatKernel z ρ y :=
    ((continuous_heatKernel_uncurry ρ).comp (continuous_const.prodMk continuous_id)).measurable
  have hmR : Measurable fun a : CoefficientField d Λ => J1Heat a z R p q :=
    (hmeasJ R p q).comp (measurable_id.prodMk measurable_const)
  have hmI : Measurable fun a : CoefficientField d Λ =>
      ∫ x, heatKernel z ρ x * J1Heat a x r p q := by
    have hsm : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (x : Vec d) =>
        heatKernel z ρ x * J1Heat a x r p q) :=
      ((hΦm.comp measurable_snd).mul (hmeasJ r p q)).stronglyMeasurable
    exact hsm.integral_prod_right.measurable
  have hmY : Measurable fun a : CoefficientField d Λ =>
      |J1Heat a z R p q - ∫ x, heatKernel z ρ x * J1Heat a x r p q| :=
    continuous_abs.measurable.comp (hmR.sub hmI)
  -- the good scales at almost every center, for almost every coefficient field
  set b : ℝ := 7 * (C * r ^ (-μ)) * (euclideanNorm p ^ 2 + euclideanNorm q ^ 2) with hbdef
  have hset : MeasurableSet {w : CoefficientField d Λ × Vec d |
      X w.1 w.2 ≤ r → |J1Heat w.1 w.2 r p q - c| ≤ b} := by
    have h1 : MeasurableSet {w : CoefficientField d Λ × Vec d | X w.1 w.2 ≤ r} :=
      measurableSet_le hXm measurable_const
    have h2 : MeasurableSet {w : CoefficientField d Λ × Vec d | |J1Heat w.1 w.2 r p q - c| ≤ b} :=
      measurableSet_le (continuous_abs.measurable.comp ((hmeasJ r p q).sub measurable_const))
        measurable_const
    have : {w : CoefficientField d Λ × Vec d | X w.1 w.2 ≤ r → |J1Heat w.1 w.2 r p q - c| ≤ b} =
        {w : CoefficientField d Λ × Vec d | X w.1 w.2 ≤ r}ᶜ ∪
          {w : CoefficientField d Λ × Vec d | |J1Heat w.1 w.2 r p q - c| ≤ b} :=
      Set.ext fun w => imp_iff_not_or
    rw [this]
    exact h1.compl.union h2
  have hgoodY : ∀ᵐ a ∂P, ∀ᵐ y ∂(volume : Measure (Vec d)),
      X a y ≤ r → |J1Heat a y r p q - c| ≤ b :=
    (Measure.ae_ae_comm hset).mpr (Filter.Eventually.of_forall fun y =>
      (hX y).2.mono fun a ha h => ha r h p q)
  -- the pointwise bound
  have hle : ∀ᵐ a ∂P, |J1Heat a z R p q - ∫ x, heatKernel z ρ x * J1Heat a x r p q| ≤
      Real.sqrt (2 * δ) * Real.sqrt (G a) +
        K * ((∫ y, heatKernel z ρ y * F y a) + (R⁻¹ * X a z) ^ κ) := by
    filter_upwards [hspan, htrial z, (hX z).2, hgoodY, hB₁i] with a hsa hta hgz hgy hB1int
    obtain ⟨h0, h1⟩ := additivityDefect_le_trialGap S a hsa z hr0 hrR p q
      (hJy a).aestronglyMeasurable (hta R (hr.trans hrR.le) p q)
    have hRb := hgood a z R hrR.le (fun h => hgz R h p q)
    have hyb : ∀ᵐ y ∂(volume : Measure (Vec d)),
        heatKernel z ρ y * J1Heat a y r p q ≤ heatKernel z ρ y * (c + δ + K * F y a) := by
      filter_upwards [hgy] with y hy
      have := hgood a y r le_rfl hy
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp this).2])
        (heatKernel_nonneg _ _ _)
    have hI2 : Integrable fun y => heatKernel z ρ y * (c + δ + K * F y a) := by
      have := ((integrable_heatKernel z hρ).mul_const (c + δ)).add (hB1int.const_mul K)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.add_apply]
      ring
    have hI2v : ∫ y, heatKernel z ρ y * (c + δ + K * F y a) =
        c + δ + K * ∫ y, heatKernel z ρ y * F y a := by
      have e : (fun y => heatKernel z ρ y * (c + δ + K * F y a)) =
          fun y => heatKernel z ρ y * (c + δ) + K * (heatKernel z ρ y * F y a) := by
        funext y; ring
      rw [e, integral_add ((integrable_heatKernel z hρ).mul_const _) (hB1int.const_mul K),
        integral_mul_const, integral_heatKernel z hρ, one_mul, integral_const_mul]
    have hJr := integral_mono_ae (hint a) hI2 hyb
    rw [hI2v] at hJr
    have hB0 : 0 ≤ (∫ y, heatKernel z ρ y * F y a) + (R⁻¹ * X a z) ^ κ :=
      add_nonneg (integral_nonneg fun y => mul_nonneg (heatKernel_nonneg _ _ _) (hF0 y a))
        (Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hR.le) (zero_le_one.trans (hX1 a z))) _)
    have hΔ : (∫ x, heatKernel z ρ x * J1Heat a x r p q) - J1Heat a z R p q ≤
        2 * δ + K * ((∫ y, heatKernel z ρ y * F y a) + (R⁻¹ * X a z) ^ κ) := by
      have := (abs_le.mp hRb).1
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg h0]
    exact sqrt_bound_of_le h0 h1 h2δ.le (mul_nonneg hK0.le hB0) hΔ
  refine (hT.of_le_ae hmY hle).mono_scale ?_
  -- the scale
  have hρr : 0 < r ^ (-(α + η)) := Real.rpow_pos_of_pos hr0 _
  have hη1 : η ≤ μ / 2 := min_le_left _ _
  have hη2 : η ≤ κ - (d : ℝ) / 2 := min_le_right _ _
  have hθ₁ : Real.sqrt (2 * δ) * (A₂ * (C₂ * r ^ (-(2 * α)))) ^ (1 / 2 : ℝ) ≤
      c₁ * r ^ (-(α + η)) :=
    improved_scale_first hr hC (zero_lt_one.trans_le hA₂) hC₂ hη1
  have hθ₂ : K * (2 * ((2 : ℝ) ^ s⁻¹ * max (A₁ * (r⁻¹ * C') ^ κ) ((r⁻¹ * C') ^ κ))) ≤
      c₂ * r ^ (-(α + η)) :=
    improved_scale_second hr hK0.le hA₁ hC' (by linarith)
  have hθ₁0 : 0 ≤ Real.sqrt (2 * δ) * (A₂ * (C₂ * r ^ (-(2 * α)))) ^ (1 / 2 : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hθ₂0 : 0 ≤ K * (2 * ((2 : ℝ) ^ s⁻¹ * max (A₁ * (r⁻¹ * C') ^ κ) ((r⁻¹ * C') ^ κ))) := by
    positivity
  have hmax := max_le_add_of_nonneg hθ₁0 hθ₂0
  have h2s : 0 < (2 : ℝ) ^ s⁻¹ := Real.rpow_pos_of_pos two_pos _
  calc 2 * ((2 : ℝ) ^ s⁻¹ * max (Real.sqrt (2 * δ) * (A₂ * (C₂ * r ^ (-(2 * α)))) ^ (1 / 2 : ℝ))
        (K * (2 * ((2 : ℝ) ^ s⁻¹ * max (A₁ * (r⁻¹ * C') ^ κ) ((r⁻¹ * C') ^ κ)))))
      ≤ 2 * ((2 : ℝ) ^ s⁻¹ * (c₁ * r ^ (-(α + η)) + c₂ * r ^ (-(α + η)))) := by
        gcongr
        exact hmax.trans (add_le_add hθ₁ hθ₂)
    _ = 2 * ((2 : ℝ) ^ s⁻¹ * (c₁ + c₂)) * r ^ (-(α + η)) := by ring

end Improvement

end QSH
