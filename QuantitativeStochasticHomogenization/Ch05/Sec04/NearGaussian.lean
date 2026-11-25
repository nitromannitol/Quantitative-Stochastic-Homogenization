import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Section 5.4: random variables close to a Gaussian

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.4. The notation `X = N(σ², λ₁, c)` of (5.79), `IsNearGaussian`, and the three lemmas on
it which drive the renormalization argument of the proof of Proposition 5.25:

* Lemma 5.27 (`lemma_5_27`): a centered variable with `E[exp(2|X|)] ≤ 2` is `N(E[X²], λ₁, C λ₁)`
  for every `λ₁ ∈ (0, 1]`, from Lemma A.8;
* Lemma 5.28 (`lemma_5_28`): the normalized sum `k^{-1/2} ∑ X_i` of independent variables which
  are `N(σ², λ₁, c)` is `N(σ², √k λ₁, c)`;
* Lemma 5.30 (`lemma_5_30`): the sum of an `N(σ², λ₁, c)` variable and a centered variable of
  size `O_s(θ)` is `N(σ², (1 - θ^{1/2}) λ₁, c + C θ^{1/2} (1 + σ² + c))`, from Hölder's
  inequality for exponential moments (`log_integral_exp_add_le`) and Lemma A.9.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace QSH

universe u

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The notation `X = N(σ², λ₁, c)`** of (5.79), with `v = σ²` and `l = λ₁`: for every
`λ ∈ (-λ₁, λ₁)`, the variable `exp(λ X)` is integrable and
`|log E[exp(λ X)] - v λ²/2| ≤ c λ²`. -/
def IsNearGaussian (P : Measure Ω) (X : Ω → ℝ) (v l c : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (-l) l, Integrable (fun ω => Real.exp (t * X ω)) P ∧
    |Real.log (∫ ω, Real.exp (t * X ω) ∂P) - v * t ^ 2 / 2| ≤ c * t ^ 2

/-- **Lemma 5.27**: there is `C` such that, if `E[exp(2|X|)] ≤ 2` and `E[X] = 0`, then
`X = N(E[X²], λ₁, C λ₁)` for every `λ₁ ∈ (0, 1]`. -/
theorem lemma_5_27 :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → ℝ), Measurable X → Integrable (fun ω => Real.exp (2 * |X ω|)) P →
        ∫ ω, Real.exp (2 * |X ω|) ∂P ≤ 2 → ∫ ω, X ω ∂P = 0 →
        ∀ l : ℝ, 0 < l → l ≤ 1 → IsNearGaussian P X (∫ ω, X ω ^ 2 ∂P) l (C * l) := by
  obtain ⟨C, hC, h⟩ := exists_abs_log_integral_exp_sub_le.{u}
  refine ⟨C, hC, fun P _ X hX hi h2 h0 l _ hl1 t ht => ?_⟩
  have htl : |t| < l := abs_lt.2 ht
  obtain ⟨hint, hb⟩ := (h P X hX hi h2 h0).2 t (by linarith)
  refine ⟨hint, hb.trans ?_⟩
  have h3 : |t| ^ 3 = |t| * t ^ 2 := by
    rw [← sq_abs t]
    ring
  rw [h3, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htl.le hC.le) (sq_nonneg t)

/-- **Lemma 5.28**: if `X₁, …, X_k` are independent and `X_i = N(σ², λ₁, c)` for every `i`, then
`k^{-1/2} ∑_i X_i = N(σ², √k λ₁, c)`. -/
theorem lemma_5_28 {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ}
    (hind : iIndepFun X P) (hX : ∀ i, Measurable (X i)) {σ l c : ℝ}
    (h : ∀ i, IsNearGaussian P (X i) (σ ^ 2) l c) :
    IsNearGaussian P (fun ω => (Real.sqrt k)⁻¹ * ∑ i, X i ω) (σ ^ 2) (Real.sqrt k * l) c := by
  intro t ht
  show Integrable (fun ω => Real.exp (t * ((Real.sqrt k)⁻¹ * ∑ i, X i ω))) P ∧
    |Real.log (∫ ω, Real.exp (t * ((Real.sqrt k)⁻¹ * ∑ i, X i ω)) ∂P) - σ ^ 2 * t ^ 2 / 2| ≤
      c * t ^ 2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, neg_zero] at ht
    exact absurd (ht.1.trans ht.2) (lt_irrefl 0)
  have hk0 : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  obtain ⟨u, hu_def⟩ : ∃ u, u = t / Real.sqrt k := ⟨_, rfl⟩
  have hu : u ∈ Set.Ioo (-l) l := by
    refine abs_lt.1 ?_
    rw [hu_def, abs_div, abs_of_pos hk0, div_lt_iff₀ hk0, mul_comm]
    exact abs_lt.2 ht
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      Integrable (fun ω => Real.exp (u * X i ω)) P := fun i _ => (h i u hu).1
  have heq : (fun ω => Real.exp (t * ((Real.sqrt k)⁻¹ * ∑ i, X i ω))) =
      fun ω => Real.exp (u * (∑ i ∈ Finset.univ, X i) ω) := by
    funext ω
    rw [Finset.sum_apply, hu_def]
    congr 1
    ring
  refine ⟨by rw [heq]; exact hind.integrable_exp_mul_sum hX hint, ?_⟩
  have hlog : Real.log (∫ ω, Real.exp (t * ((Real.sqrt k)⁻¹ * ∑ i, X i ω)) ∂P) =
      ∑ i, Real.log (∫ ω, Real.exp (u * X i ω) ∂P) := by
    rw [heq]
    exact hind.cgf_sum hX hint
  have hsq : (k : ℝ) * u ^ 2 = t ^ 2 := by
    rw [hu_def, div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    field_simp
  rw [hlog]
  calc |∑ i, Real.log (∫ ω, Real.exp (u * X i ω) ∂P) - σ ^ 2 * t ^ 2 / 2|
      = |∑ i : Fin k, (Real.log (∫ ω, Real.exp (u * X i ω) ∂P) - σ ^ 2 * u ^ 2 / 2)| := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← hsq]
        congr 1
        ring
    _ ≤ ∑ i : Fin k, |Real.log (∫ ω, Real.exp (u * X i ω) ∂P) - σ ^ 2 * u ^ 2 / 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, c * u ^ 2 := Finset.sum_le_sum fun i _ => (h i u hu).2
    _ = c * t ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hsq]
        ring

/-- **Hölder's inequality for exponential moments**: if `ρ, ρ'` are Hölder conjugate and
`exp(ρ t X)`, `exp(ρ' t Y)` are integrable, then `exp(t (X + Y))` is integrable and
`log E[exp(t (X + Y))] ≤ ρ⁻¹ log E[exp(ρ t X)] + ρ'⁻¹ log E[exp(ρ' t Y)]`, as in (5.100). -/
theorem log_integral_exp_add_le {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) {ρ ρ' : ℝ} (hρ : ρ.HolderConjugate ρ')
    {t : ℝ} (hXi : Integrable (fun ω => Real.exp (ρ * t * X ω)) P)
    (hYi : Integrable (fun ω => Real.exp (ρ' * t * Y ω)) P) :
    Integrable (fun ω => Real.exp (t * (X ω + Y ω))) P ∧
      Real.log (∫ ω, Real.exp (t * (X ω + Y ω)) ∂P) ≤
        ρ⁻¹ * Real.log (∫ ω, Real.exp (ρ * t * X ω) ∂P) +
          ρ'⁻¹ * Real.log (∫ ω, Real.exp (ρ' * t * Y ω) ∂P) := by
  have hρ0 : 0 < ρ := hρ.left_pos
  have hρ'0 : 0 < ρ' := hρ.right_pos
  have hsum : ρ⁻¹ + ρ'⁻¹ = 1 := by simpa using hρ.inv_add_inv_eq_inv
  have hpt : ∀ ω, Real.exp (t * (X ω + Y ω)) ≤
      ρ⁻¹ * Real.exp (ρ * t * X ω) + ρ'⁻¹ * Real.exp (ρ' * t * Y ω) := by
    intro ω
    have h := convexOn_exp.2 (Set.mem_univ (ρ * t * X ω)) (Set.mem_univ (ρ' * t * Y ω))
      (inv_nonneg.2 hρ0.le) (inv_nonneg.2 hρ'0.le) hsum
    simp only [smul_eq_mul] at h
    have e : ρ⁻¹ * (ρ * t * X ω) + ρ'⁻¹ * (ρ' * t * Y ω) = t * (X ω + Y ω) := by
      rw [show ρ⁻¹ * (ρ * t * X ω) = (ρ⁻¹ * ρ) * (t * X ω) by ring,
        show ρ'⁻¹ * (ρ' * t * Y ω) = (ρ'⁻¹ * ρ') * (t * Y ω) by ring,
        inv_mul_cancel₀ hρ0.ne', inv_mul_cancel₀ hρ'0.ne']
      ring
    rw [e] at h
    exact h
  have hint : Integrable (fun ω => Real.exp (t * (X ω + Y ω))) P := by
    refine ((hXi.const_mul ρ⁻¹).add (hYi.const_mul ρ'⁻¹)).mono'
      (Real.measurable_exp.comp_aemeasurable ((hX.add hY).const_mul t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact hpt ω
  have hmem : ∀ {Z : Ω → ℝ} {p : ℝ}, 0 < p → AEMeasurable Z P →
      Integrable (fun ω => Real.exp (p * t * Z ω)) P →
        MemLp (fun ω => Real.exp (t * Z ω)) (ENNReal.ofReal p) P := by
    intro Z p hp hZ hZi
    have hm : AEStronglyMeasurable (fun ω => Real.exp (t * Z ω)) P :=
      (Real.measurable_exp.comp_aemeasurable (hZ.const_mul t)).aestronglyMeasurable
    refine (integrable_norm_rpow_iff hm (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top).1 ?_
    refine hZi.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, Real.abs_exp, ← Real.exp_mul]
    congr 1
    ring
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hρ
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (t * X ω)).le)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (t * Y ω)).le)
    (hmem hρ0 hX hXi) (hmem hρ'0 hY hYi)
  have hL : ∫ ω, Real.exp (t * X ω) * Real.exp (t * Y ω) ∂P =
      ∫ ω, Real.exp (t * (X ω + Y ω)) ∂P := by
    congr 1
    funext ω
    rw [← Real.exp_add, mul_add]
  have hRX : ∫ ω, Real.exp (t * X ω) ^ ρ ∂P = ∫ ω, Real.exp (ρ * t * X ω) ∂P := by
    congr 1
    funext ω
    rw [← Real.exp_mul]
    congr 1
    ring
  have hRY : ∫ ω, Real.exp (t * Y ω) ^ ρ' ∂P = ∫ ω, Real.exp (ρ' * t * Y ω) ∂P := by
    congr 1
    funext ω
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hL, hRX, hRY] at hH
  have hA : 0 < ∫ ω, Real.exp (ρ * t * X ω) ∂P := mgf_pos hXi
  have hB : 0 < ∫ ω, Real.exp (ρ' * t * Y ω) ∂P := mgf_pos hYi
  have hC : 0 < ∫ ω, Real.exp (t * (X ω + Y ω)) ∂P := mgf_pos (X := fun ω => X ω + Y ω) hint
  refine ⟨hint, (Real.log_le_log hC hH).trans_eq ?_⟩
  rw [Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne',
    Real.log_rpow hA, Real.log_rpow hB, one_div, one_div]

/-- The exponential moments of a centered stochastic bound on a bounded range of parameters: if
`Y = 𝒪_s(θ₀)` and `|m| θ₀ ≤ b`, then `exp(m Y)` is integrable and
`log E[exp(m Y)] ≤ max(1, b^{s/(s-1) - 2}) (m θ₀)²`. -/
theorem CenteredOsBound.log_integral_exp_le {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {s θ₀ : ℝ} (h : CenteredOsBound P Y s θ₀) {m b : ℝ} (hb : |m| * θ₀ ≤ b) :
    Integrable (fun ω => Real.exp (m * Y ω)) P ∧
      Real.log (∫ ω, Real.exp (m * Y ω) ∂P) ≤ max 1 (b ^ (s / (s - 1) - 2)) * (m * θ₀) ^ 2 := by
  obtain ⟨-, hs1, hs2, hθ, hY⟩ := h
  have he : (fun ω => Real.exp (m * θ₀ * (θ₀⁻¹ * Y ω))) = fun ω => Real.exp (m * Y ω) := by
    funext ω
    rw [show m * θ₀ * (θ₀⁻¹ * Y ω) = m * Y ω * (θ₀ * θ₀⁻¹) by ring, mul_inv_cancel₀ hθ.ne',
      mul_one]
  obtain ⟨hi, hle⟩ := hY (m * θ₀)
  rw [he] at hi hle
  refine ⟨hi, ?_⟩
  have hpos : 0 < ∫ ω, Real.exp (m * Y ω) ∂P := mgf_pos hi
  refine (Real.log_le_log hpos hle).trans ?_
  rw [Real.log_exp]
  have hq : 2 ≤ s / (s - 1) := two_le_div_sub_one hs1 hs2
  have ht : |m * θ₀| ≤ b := by rwa [abs_mul, abs_of_pos hθ]
  refine max_le (le_mul_of_one_le_left (sq_nonneg _) (le_max_left _ _)) ?_
  have hne : s / (s - 1) - 2 + 2 ≠ 0 := ne_of_gt (by linarith)
  have hsplit : |m * θ₀| ^ (s / (s - 1)) = |m * θ₀| ^ (s / (s - 1) - 2) * (m * θ₀) ^ 2 := by
    have h2 : |m * θ₀| ^ (s / (s - 1)) = |m * θ₀| ^ (s / (s - 1) - 2 + 2) := by
      rw [sub_add_cancel]
    rw [h2, Real.rpow_add' (abs_nonneg (m * θ₀)) hne, Real.rpow_two, sq_abs]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact (Real.rpow_le_rpow (abs_nonneg _) ht (by linarith)).trans (le_max_right _ _)

private theorem upper_bound_of_holder {r t v c K A L₁ L₂ : ℝ} (hr0 : 0 < r) (hr34 : r ≤ 3 / 4)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hK : 0 ≤ K) (hA : A ≤ (1 - r) * L₁ + r * L₂)
    (h₁ : L₁ - v * ((1 - r)⁻¹ * t) ^ 2 / 2 ≤ c * ((1 - r)⁻¹ * t) ^ 2)
    (h₂ : L₂ ≤ K * r ^ 2 * t ^ 2) :
    A - v * t ^ 2 / 2 ≤ (c + (4 + K) * r * (1 + v + c)) * t ^ 2 := by
  have h1r : 0 < 1 - r := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = (1 - r)⁻¹ := ⟨_, rfl⟩
  rw [← hw] at h₁
  have hw1 : (1 - r) * w = 1 := by rw [hw, mul_inv_cancel₀ h1r.ne']
  have hw4 : w ≤ 1 + 4 * r := by
    rw [hw, ← one_div, div_le_iff₀ h1r]
    nlinarith [mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ 3 - 4 * r)]
  have hL₁ : (1 - r) * L₁ ≤ (v / 2 + c) * w * t ^ 2 := by
    have e : (1 - r) * (v * (w * t) ^ 2 / 2 + c * (w * t) ^ 2) = (v / 2 + c) * w * t ^ 2 := by
      calc (1 - r) * (v * (w * t) ^ 2 / 2 + c * (w * t) ^ 2)
          = ((1 - r) * w) * ((v / 2 + c) * w * t ^ 2) := by ring
        _ = (v / 2 + c) * w * t ^ 2 := by rw [hw1, one_mul]
    rw [← e]
    exact mul_le_mul_of_nonneg_left (by linarith) h1r.le
  have hKt : 0 ≤ K * r * t ^ 2 := mul_nonneg (mul_nonneg hK hr0.le) (sq_nonneg t)
  have hr1 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le (by linarith)
  have hr3 : 0 ≤ K * r * t ^ 2 * (1 - r ^ 2) := mul_nonneg hKt (sub_nonneg.2 hr1)
  have hL₂ : r * L₂ ≤ r * (K * r ^ 2 * t ^ 2) := mul_le_mul_of_nonneg_left h₂ hr0.le
  have hw' : (v / 2 + c) * w * t ^ 2 ≤ (v / 2 + c) * (1 + 4 * r) * t ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw4 (by linarith)) (sq_nonneg t)
  have e1 : 0 ≤ r * t ^ 2 := mul_nonneg hr0.le (sq_nonneg t)
  have e2 : 0 ≤ r * v * t ^ 2 := mul_nonneg (mul_nonneg hr0.le hv) (sq_nonneg t)
  have e3 : 0 ≤ K * r * v * t ^ 2 := mul_nonneg (mul_nonneg (mul_nonneg hK hr0.le) hv) (sq_nonneg t)
  have e4 : 0 ≤ K * r * c * t ^ 2 := mul_nonneg (mul_nonneg (mul_nonneg hK hr0.le) hc) (sq_nonneg t)
  linarith

private theorem lower_bound_of_holder {r t v c K A L L₂ : ℝ} (hr0 : 0 < r) (hr34 : r ≤ 3 / 4)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hK : 0 ≤ K) (hH : L ≤ (1 - r) * A + r * L₂)
    (h₁ : -(c * ((1 - r) * t) ^ 2) ≤ L - v * ((1 - r) * t) ^ 2 / 2)
    (h₂ : L₂ ≤ K * r ^ 2 * ((1 - r) * t) ^ 2) :
    -((c + (4 + K) * r * (1 + v + c)) * t ^ 2) ≤ A - v * t ^ 2 / 2 := by
  have h1r : 0 < 1 - r := by linarith
  have hr1 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le (by linarith)
  have hrL : r * L₂ ≤ r * (K * r ^ 2 * ((1 - r) * t) ^ 2) := mul_le_mul_of_nonneg_left h₂ hr0.le
  have hB : (1 - r) * ((1 - r) * t ^ 2 * (v / 2 - c - K * r ^ 3)) ≤ (1 - r) * A := by
    linarith
  have hB' := le_of_mul_le_mul_left hB h1r
  have hKt : 0 ≤ K * r * t ^ 2 := mul_nonneg (mul_nonneg hK hr0.le) (sq_nonneg t)
  have e1 : 0 ≤ r * t ^ 2 := mul_nonneg hr0.le (sq_nonneg t)
  have e2 : 0 ≤ r * v * t ^ 2 := mul_nonneg (mul_nonneg hr0.le hv) (sq_nonneg t)
  have e3 : 0 ≤ r * c * t ^ 2 := mul_nonneg (mul_nonneg hr0.le hc) (sq_nonneg t)
  have e4 : 0 ≤ K * r * v * t ^ 2 := mul_nonneg (mul_nonneg (mul_nonneg hK hr0.le) hv) (sq_nonneg t)
  have e5 : 0 ≤ K * r * c * t ^ 2 := mul_nonneg (mul_nonneg (mul_nonneg hK hr0.le) hc) (sq_nonneg t)
  have e6 : 0 ≤ K * r * t ^ 2 * (1 - r ^ 2) := mul_nonneg hKt (sub_nonneg.2 hr1)
  have e7 : 0 ≤ K * r ^ 4 * t ^ 2 := mul_nonneg (mul_nonneg hK (by positivity)) (sq_nonneg t)
  linarith

/-- **Lemma 5.30**: let `s ∈ (1, 2]` and `λ₂ ∈ ℝ`. There is `C(s, λ₂)` such that, for `σ ∈ ℝ`,
`c ≥ 0`, `λ₁ ≤ λ₂` and `θ ∈ (0, 1/2]`, if `X₁ = N(σ², λ₁, c)` and `X₂` is centered with
`X₂ = O_s(θ)`, then `X₁ + X₂ = N(σ², (1 - θ^{1/2}) λ₁, c + C θ^{1/2} (1 + σ² + c))`. -/
theorem lemma_5_30 {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (l₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₁ X₂ : Ω → ℝ) (σ c l₁ θ : ℝ), 0 ≤ c → l₁ ≤ l₂ → 0 < θ → θ ≤ 1 / 2 → Measurable X₁ →
        IsNearGaussian P X₁ (σ ^ 2) l₁ c → OsBound P X₂ s θ → OsBound P (fun ω => -X₂ ω) s θ →
        ∫ ω, X₂ ω ∂P = 0 →
        IsNearGaussian P (fun ω => X₁ ω + X₂ ω) (σ ^ 2) ((1 - Real.sqrt θ) * l₁)
          (c + C * Real.sqrt θ * (1 + σ ^ 2 + c)) := by
  obtain ⟨CA, hCA, hA9⟩ := exists_centeredOsBound_of_osBound.{u} hs1 hs2
  obtain ⟨K, hK⟩ : ∃ K, K = max 1 ((CA * l₂) ^ (s / (s - 1) - 2)) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    exact le_max_left _ _
  have hKC : 0 ≤ K * CA ^ 2 := mul_nonneg (by linarith) (sq_nonneg CA)
  refine ⟨4 + K * CA ^ 2, by linarith, ?_⟩
  intro Ω _ P _ X₁ X₂ σ c l₁ θ hc hl hθ hθ2 hX₁ hN hO hOn hm
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt θ := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by
    rw [hr]
    exact Real.sqrt_pos.2 hθ
  have hrθ : r ^ 2 = θ := by
    rw [hr]
    exact Real.sq_sqrt hθ.le
  have hr34 : r ≤ 3 / 4 := by nlinarith [hrθ, hθ2, hr0]
  have h1r : 0 < 1 - r := by linarith
  have hcen := hA9 P X₂ θ hO hOn hm
  have hX₂ : Measurable X₂ := hO.1
  have hrr : r⁻¹ * r ^ 2 = r := by rw [sq, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul]
  have hB : ∀ u : ℝ, |u| ≤ l₂ → Integrable (fun ω => Real.exp (r⁻¹ * u * X₂ ω)) P ∧
      Real.log (∫ ω, Real.exp (r⁻¹ * u * X₂ ω) ∂P) ≤ K * CA ^ 2 * r ^ 2 * u ^ 2 := by
    intro u hu
    have he : r⁻¹ * u * (CA * θ) = CA * r * u := by
      rw [← hrθ]
      calc r⁻¹ * u * (CA * r ^ 2) = CA * u * (r⁻¹ * r ^ 2) := by ring
        _ = CA * r * u := by rw [hrr]; ring
    have hb : |r⁻¹ * u| * (CA * θ) ≤ CA * l₂ := by
      have h1 : |r⁻¹ * u| * (CA * θ) = CA * (r * |u|) := by
        rw [← abs_of_pos (mul_pos hCA hθ), ← abs_mul, he, abs_mul, abs_mul, abs_of_pos hCA,
          abs_of_pos hr0, mul_assoc]
      rw [h1]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_of_le_one_left (abs_nonneg u) (by linarith)).trans hu) hCA.le
    obtain ⟨hi, hle⟩ := hcen.log_integral_exp_le hb
    refine ⟨hi, hle.trans_eq ?_⟩
    rw [← hK, he]
    ring
  have hHC : ((1 - r)⁻¹).HolderConjugate r⁻¹ :=
    ⟨by rw [inv_inv, inv_inv, inv_one]; ring, inv_pos.2 h1r, inv_pos.2 hr0⟩
  intro t ht
  have ht' : |t| < (1 - r) * l₁ := abs_lt.2 ht
  have hl0 : 0 < l₁ := pos_of_mul_pos_right (lt_of_le_of_lt (abs_nonneg t) ht') h1r.le
  have htl : |t| ≤ l₂ := by
    have : (1 - r) * l₁ ≤ l₁ := mul_le_of_le_one_left hl0.le (by linarith)
    linarith
  have hρt : (1 - r)⁻¹ * t ∈ Set.Ioo (-l₁) l₁ := by
    refine abs_lt.1 ?_
    rw [abs_mul, abs_of_pos (inv_pos.2 h1r), inv_mul_lt_iff₀ h1r]
    exact ht'
  obtain ⟨hNi, hNb⟩ := hN _ hρt
  obtain ⟨hBi, hBb⟩ := hB t htl
  obtain ⟨hint, hup⟩ := log_integral_exp_add_le hX₁.aemeasurable hX₂.aemeasurable hHC hNi hBi
  rw [inv_inv, inv_inv] at hup
  have hU := upper_bound_of_holder hr0 hr34 hc (sq_nonneg σ) hKC hup (abs_le.1 hNb).2 hBb
  have ht'mem : (1 - r) * t ∈ Set.Ioo (-l₁) l₁ := by
    refine abs_lt.1 ?_
    rw [abs_mul, abs_of_pos h1r]
    calc (1 - r) * |t| ≤ |t| := mul_le_of_le_one_left (abs_nonneg t) (by linarith)
      _ < (1 - r) * l₁ := ht'
      _ ≤ l₁ := mul_le_of_le_one_left hl0.le (by linarith)
  obtain ⟨-, hNb'⟩ := hN _ ht'mem
  have htl' : |-((1 - r) * t)| ≤ l₂ := by
    rw [abs_neg, abs_mul, abs_of_pos h1r]
    exact (mul_le_of_le_one_left (abs_nonneg t) (by linarith)).trans htl
  obtain ⟨hBi', hBb'⟩ := hB _ htl'
  rw [neg_sq] at hBb'
  have e0 : (1 - r)⁻¹ * ((1 - r) * t) = t := by
    rw [← mul_assoc, inv_mul_cancel₀ h1r.ne', one_mul]
  have hZi : Integrable (fun ω => Real.exp ((1 - r)⁻¹ * ((1 - r) * t) * (X₁ ω + X₂ ω))) P := by
    simpa only [e0] using hint
  have e1 : ∀ ω, r⁻¹ * ((1 - r) * t) * -X₂ ω = r⁻¹ * -((1 - r) * t) * X₂ ω := fun ω => by ring
  have hYi : Integrable (fun ω => Real.exp (r⁻¹ * ((1 - r) * t) * -X₂ ω)) P := by
    simpa only [e1] using hBi'
  obtain ⟨-, hlow⟩ := log_integral_exp_add_le (X := fun ω => X₁ ω + X₂ ω) (Y := fun ω => -X₂ ω)
    (hX₁.add hX₂).aemeasurable hX₂.neg.aemeasurable hHC hZi hYi
  simp only [add_neg_cancel_right, e0, e1, inv_inv] at hlow
  have hL := lower_bound_of_holder hr0 hr34 hc (sq_nonneg σ) hKC hlow (abs_le.1 hNb').1 hBb'
  refine ⟨hint, ?_⟩
  rw [abs_le]
  exact ⟨hL, hU⟩

end QSH
