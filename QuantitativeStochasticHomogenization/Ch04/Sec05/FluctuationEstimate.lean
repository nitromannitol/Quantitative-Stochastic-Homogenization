import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationScales

/-!
# The statement (4.117) of the proof of Proposition 4.12

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.5. For centered local additive fields (`CenteredLocalFields`) with
`s ∈ (1, 2]`, `β ∈ (0, d/2]`, `0 < η₁ < η₂`, `η₂(1+δ) < 1` and `η₁ α > β`, there is `C` such that
for every `R ≥ 1`, `r ∈ [R^{η₁}, R^{η₂}]`, `z` and measurable `f` with `|f| ≤ 1` vanishing off the
closed cube of side `R` around `z`, `R^{-d} ∫ f X(r) = 𝒪_s(C R^{-β})` (`exists_blockBound`).

The proof is the induction (4.118): `A(R₁, C) ⟹ A(2R₁, C(1 + K R₁^{-ε}))` for `R₁ ≥ R₀` and
`C ≥ C₁` (`exists_blockBound_step`), started from the base case and iterated along `2^n R₀`; the
product of the factors `1 + K (2^n R₀)^{-ε}` is bounded.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {s δ α B A : ℝ}

/-- **The induction step (4.118).** -/
theorem exists_blockBound_step (hd : 1 ≤ d)
    (hmono : Monotone F) (hs1 : 1 < s) (hs2 : s ≤ 2) (hB0 : 0 < B) (hA0 : 0 < A)
    {η₁ η₂ β : ℝ} (hβ : β ≤ (d : ℝ) / 2) (hδ : 0 < δ) (hη₁ : 0 < η₁)
    (hη₁₂ : η₁ < η₂) (hη₂ : η₂ * (1 + δ) < 1) (hα : β < η₁ * α) :
    ∃ ε R₀ K C₁ : ℝ, 0 < ε ∧ 1 ≤ R₀ ∧ 0 < K ∧ 0 < C₁ ∧
      ∀ (P : Measure Ω) [IsProbabilityMeasure P], HasUnitRange P F →
      ∀ (X : CenteredLocalFields P F s δ α B A) (R₁ C : ℝ), R₀ ≤ R₁ → C₁ ≤ C →
      BlockBound X η₁ η₂ β R₁ C → BlockBound X η₁ η₂ β (2 * R₁) (C * (1 + K * R₁ ^ (-ε))) := by
  obtain ⟨C₀, hC₀, hfar⟩ := exists_centeredOsBound_far_block (Ω := Ω) (F := F) (δ := δ)
    (α := α) (A := A) hs1 hs2 hB0
  have hη₂0 : 0 < η₂ := hη₁.trans hη₁₂
  set ε : ℝ := min (η₁ * α - β) (min ((1 - η₂ * (1 + δ)) / 4) ((1 - η₁ / η₂) / 2)) with hεdef
  have hq : η₁ / η₂ < 1 := (div_lt_one hη₂0).mpr hη₁₂
  have hε : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε1 : ε ≤ η₁ * α - β := min_le_left _ _
  have hε2 : ε ≤ (1 - η₂ * (1 + δ)) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ (1 - η₁ / η₂) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hη₁η₂ : η₁ ≤ (1 - 2 * ε) * η₂ := by
    have : η₁ / η₂ ≤ 1 - 2 * ε := by linarith
    rwa [div_le_iff₀ hη₂0] at this
  set κ₁ : ℝ := 1 - 2 * ε - η₁ * (1 + δ) with hκ₁def
  have hκ₁ : 0 < κ₁ := by
    have : η₁ * (1 + δ) < η₂ * (1 + δ) := mul_lt_mul_of_pos_right hη₁₂ (by linarith)
    linarith
  set κ₂ : ℝ := 1 - 2 * ε - η₂ with hκ₂def
  have hκ₂ : 0 < κ₂ := by
    have : η₂ ≤ η₂ * (1 + δ) := le_mul_of_one_le_right hη₂0.le (by linarith)
    linarith
  obtain ⟨Ce, hCe, hexp⟩ := exists_exp_neg_rpow_le (c := 1 / 8) (κ := 2 * κ₂) (by norm_num)
    (by positivity) (β + ε)
  set R₀ : ℝ := max 8 (max ((2 : ℝ) ^ (2 * ε)⁻¹) ((4 : ℝ) ^ κ₁⁻¹)) with hR₀def
  have hR₀8 : 8 ≤ R₀ := le_max_left _ _
  have hR₀2 : (2 : ℝ) ^ (2 * ε)⁻¹ ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hR₀4 : (4 : ℝ) ^ κ₁⁻¹ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  set K : ℝ := frameConst d + 1 with hKdef
  have hK : 0 < K := by have := frameConst_nonneg d; linarith
  set C₁ : ℝ := A * 2 ^ (η₁ * α) + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce)
    with hC₁def
  have hC₁ : 0 < C₁ := by
    have := hA0
    have := hB0
    positivity
  refine ⟨ε, R₀, K, C₁, hε, by linarith, hK, hC₁, fun P _ hF X R₁ C hR₁ hC hA => ?_⟩
  have hC0 : 0 ≤ C := hC₁.le.trans hC
  have hR₁0 : 0 < R₁ := by linarith
  have hfac : 1 ≤ 1 + K * R₁ ^ (-ε) := by
    have := mul_nonneg hK.le (Real.rpow_nonneg hR₁0.le (-ε))
    linarith
  intro R hR1 hRR r hr1 hr2 z f hf hf1 hfz
  by_cases hRle : R ≤ R₁
  · refine (hA R hR1 hRle r hr1 hr2 z f hf hf1 hfz).mono_scale ?_
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC0 hfac)
      (Real.rpow_nonneg (zero_le_one.trans hR1) _)
  push Not at hRle
  have hR8 : 8 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hR1' : 1 ≤ R := by linarith
  have hR2ε : 2 ≤ R ^ (2 * ε) :=
    le_rpow_of_rpow_inv_le (by norm_num) (by positivity) (by linarith)
  have hR₁2ε : 2 ≤ R₁ ^ (2 * ε) :=
    le_rpow_of_rpow_inv_le (by norm_num) (by positivity) (by linarith)
  have hRκ₁ : 4 ≤ R ^ κ₁ := le_rpow_of_rpow_inv_le (by norm_num) hκ₁ (by linarith)
  set R' : ℝ := R ^ (1 - 2 * ε) with hR'def
  have hR'eq : R' = R / R ^ (2 * ε) := by
    rw [hR'def, Real.rpow_sub hR0, Real.rpow_one]
  have hR'pos : 0 < R' := Real.rpow_pos_of_pos hR0 _
  have hR'1 : 1 ≤ R' := Real.one_le_rpow hR1' (by linarith)
  have hR'half : R' ≤ R / 2 := by
    rw [hR'eq]
    exact div_le_div_of_nonneg_left hR0.le (by norm_num) hR2ε
  have hR'R₁ : R' ≤ R₁ := by
    have h1 : R' ≤ (2 * R₁) ^ (1 - 2 * ε) :=
      Real.rpow_le_rpow hR0.le hRR (by linarith)
    have h2 : (2 * R₁) ^ (1 - 2 * ε) ≤ R₁ := by
      rw [Real.mul_rpow (by norm_num) hR₁0.le]
      have h3 : (2 : ℝ) ^ (1 - 2 * ε) ≤ 2 := by
        conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h4 : R₁ ^ (2 * ε) * R₁ ^ (1 - 2 * ε) = R₁ := by
        rw [← Real.rpow_add hR₁0]; ring_nf; exact Real.rpow_one R₁
      have h5 : 0 ≤ R₁ ^ (1 - 2 * ε) := Real.rpow_nonneg hR₁0.le _
      calc (2 : ℝ) ^ (1 - 2 * ε) * R₁ ^ (1 - 2 * ε) ≤ 2 * R₁ ^ (1 - 2 * ε) :=
            mul_le_mul_of_nonneg_right h3 h5
        _ ≤ R₁ ^ (2 * ε) * R₁ ^ (1 - 2 * ε) := mul_le_mul_of_nonneg_right hR₁2ε h5
        _ = R₁ := h4
    exact h1.trans h2
  set r₁ : ℝ := (R / 2) ^ η₁ with hr₁def
  have hR2 : 1 ≤ R / 2 := by linarith
  have hr₁ : 1 ≤ r₁ := Real.one_le_rpow hR2 hη₁.le
  have hr₁r : r₁ < r :=
    (Real.rpow_lt_rpow (by linarith) (by linarith) hη₁).trans_le hr1
  have hr₁hi : r₁ ≤ (R / 2) ^ η₂ := Real.rpow_le_rpow_of_exponent_le hR2 hη₁₂.le
  have hr₁lo' : R' ^ η₁ ≤ r₁ := Real.rpow_le_rpow hR'pos.le hR'half hη₁.le
  have hr₁hi' : r₁ ≤ R' ^ η₂ := by
    calc r₁ ≤ R ^ η₁ := Real.rpow_le_rpow (by linarith) (by linarith) hη₁.le
      _ ≤ R ^ ((1 - 2 * ε) * η₂) := Real.rpow_le_rpow_of_exponent_le hR1' hη₁η₂
      _ = R' ^ η₂ := by rw [hR'def, Real.rpow_mul hR0.le]
  set q : ℝ := R ^ (η₁ * (1 + δ)) with hqdef
  have hq1 : 1 ≤ q := Real.one_le_rpow hR1' (by positivity)
  have hρ₁q : r₁ ^ (1 + δ) ≤ q := by
    rw [hr₁def, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
  have hR'q : 4 * q ≤ R' := by
    have e : R' = q * R ^ κ₁ := by
      rw [hR'def, hqdef, ← Real.rpow_add hR0]
      congr 1
      ring
    rw [e]
    calc 4 * q ≤ R ^ κ₁ * q := mul_le_mul_of_nonneg_right hRκ₁ (by linarith)
      _ = q * R ^ κ₁ := mul_comm _ _
  have hsep : 1 < R' - 2 * r₁ ^ (1 + δ) := by linarith
  have hρ₁ : r₁ ^ (1 + δ) ≤ R' / 2 := by linarith
  set n : ℕ := ⌊R / (2 * R')⌋₊ with hndef
  have hn0 : (n : ℝ) ≤ R / (2 * R') := Nat.floor_le (by positivity)
  have hn1 : R / (2 * R') < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn : (n : ℝ) * R' ≤ R / 2 := by
    rw [le_div_iff₀ (by positivity)] at hn0
    linarith
  have hn' : R / 2 < ((n : ℝ) + 1) * R' := by
    rw [div_lt_iff₀ (by positivity)] at hn1
    linarith
  have hnR : (n : ℝ) ≤ R ^ (2 * ε) / 2 := by
    have : R / (2 * R') = R ^ (2 * ε) / 2 := by
      rw [hR'eq]
      field_simp
    linarith
  have hfarX : ∀ (r₁ : ℝ) {z : Vec d} {R ρ t : ℝ}, 0 < R → 0 < ρ → 0 ≤ t →
      ∀ {f : Vec d → ℝ}, Measurable f → (∀ x, |f x| ≤ 1) → (∀ x ∉ closedCube z R, f x = 0) →
      ∀ {S : Set (Vec d)}, MeasurableSet S →
      (∀ x ∈ closedCube z R, ∀ y ∈ S, t ≤ euclideanNorm (y - x)) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) *
        ∫ y, S.indicator (heatSmooth f ρ) y * X.field r₁ a y) s
        (C₀ * (B * 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * ρ ^ 2))))) :=
    fun r₁ => hfar P X r₁
  have hstep := centeredOsBound_block_step hd hF hmono X hA hβ hC0 hfarX (r := r)
    hR2 (by linarith) hr₁ hr₁r le_rfl hr₁hi hsep hR'1 hR'R₁ hr₁lo' hr₁hi' hρ₁ hn hn' z hf hf1
    hfz
  refine hstep.mono_scale ?_
  have hθ1 : A * r₁ ^ (-α) ≤ A * 2 ^ (η₁ * α) * R ^ (-(β + ε)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_half_rpow_neg_le hR1' (by linarith))
      hA0.le
  have hcard : ((latticeFrame d (n + 2) n).card : ℝ) ≤
      5 * d * 6 ^ (d - 1) * R ^ (2 * ε * ((d - 1 : ℕ) : ℝ)) := by
    have h1 : ((latticeFrame d (n + 2) n).card : ℝ) ≤
        ((5 * d * (2 * (n + 2) + 1) ^ (d - 1) : ℕ) : ℝ) := by
      exact_mod_cast card_latticeFrame_le n
    exact h1.trans (frame_count_le hR0 hnR (by linarith))
  have hθ3 := scale_cells_le hd hR1' hε.le hβ hC0 hcard
  have hr₁sq : r₁ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr₁r (by linarith) two_ne_zero
  have hρpos : 0 < Real.sqrt (r ^ 2 - r₁ ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hρr : Real.sqrt (r ^ 2 - r₁ ^ 2) ≤ R ^ η₂ := by
    refine (Real.sqrt_le_sqrt (by have := sq_nonneg r₁; linarith :
      r ^ 2 - r₁ ^ 2 ≤ r ^ 2)).trans ?_
    rw [Real.sqrt_sq (by linarith)]
    exact hr2
  have hθ4 : C₀ * (B * 2 ^ ((d : ℝ) / 2) *
      Real.exp (-(R' ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2)))) ≤
      C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-(β + ε)) := by
    have h1 := exp_far_le (ε := ε) hR1' hρpos hρr
    have h2 := hexp R hR1'
    have hB : 0 ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2)) := by
      have := hB0
      positivity
    calc C₀ * (B * 2 ^ ((d : ℝ) / 2) *
          Real.exp (-(R' ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2))))
        = C₀ * (B * 2 ^ ((d : ℝ) / 2)) *
          Real.exp (-(R' ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2))) := by ring
      _ ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2)) * (Ce * R ^ (-(β + ε))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hB
      _ = C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-(β + ε)) := by ring
  have hsplit : R ^ (-(β + ε)) = R ^ (-β) * R ^ (-ε) := by
    rw [neg_add, Real.rpow_add hR0]
  have hRε : R ^ (-ε) ≤ R₁ ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos hR₁0 hRle.le (by linarith)
  have hRβ : 0 ≤ R ^ (-β) := Real.rpow_nonneg hR0.le _
  have hfc := frameConst_nonneg d
  calc A * r₁ ^ (-α) + C * R ^ (-β) +
        R ^ (-(d : ℝ)) * (Real.sqrt (2 * 4 ^ d) * (Real.sqrt (latticeFrame d (n + 2) n).card *
          (R' ^ d * (C * R' ^ (-β))))) +
        C₀ * (B * 2 ^ ((d : ℝ) / 2) *
          Real.exp (-(R' ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2))))
      ≤ A * 2 ^ (η₁ * α) * R ^ (-(β + ε)) + C * R ^ (-β) +
          frameConst d * C * R ^ (-(β + ε)) +
          C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-(β + ε)) := by
        gcongr
    _ = C * R ^ (-β) + (C₁ + frameConst d * C) * (R ^ (-β) * R ^ (-ε)) := by
        rw [hsplit, hC₁def]
        ring
    _ ≤ C * R ^ (-β) + (C + frameConst d * C) * (R ^ (-β) * R₁ ^ (-ε)) := by
        gcongr
    _ = C * (1 + K * R₁ ^ (-ε)) * R ^ (-β) := by
        rw [hKdef]
        ring

/-- The product of the factors of the induction is bounded. -/
theorem prod_one_add_le_exp {K R₀ ε : ℝ} (hK : 0 ≤ K) (hR₀ : 0 < R₀) (hε : 0 < ε) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 + K * (2 ^ j * R₀) ^ (-ε)) ≤
      Real.exp (K * R₀ ^ (-ε) * (1 - (2 : ℝ) ^ (-ε))⁻¹) := by
  have hq0 : 0 < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos two_pos _
  have hq1 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hterm : ∀ j : ℕ, K * (2 ^ j * R₀) ^ (-ε) = K * R₀ ^ (-ε) * ((2 : ℝ) ^ (-ε)) ^ j := by
    intro j
    rw [Real.mul_rpow (by positivity) hR₀.le, ← Real.rpow_natCast (2 : ℝ) j,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) j,
      ← Real.rpow_mul (by norm_num)]
    ring_nf
  calc ∏ j ∈ Finset.range n, (1 + K * (2 ^ j * R₀) ^ (-ε))
      ≤ ∏ j ∈ Finset.range n, Real.exp (K * (2 ^ j * R₀) ^ (-ε)) := by
        refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
        · have := mul_nonneg hK (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j * R₀) (-ε))
          linarith
        · have := Real.add_one_le_exp (K * (2 ^ j * R₀) ^ (-ε))
          linarith
    _ = Real.exp (∑ j ∈ Finset.range n, K * (2 ^ j * R₀) ^ (-ε)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (K * R₀ ^ (-ε) * (1 - (2 : ℝ) ^ (-ε))⁻¹) := by
        refine Real.exp_le_exp.mpr ?_
        simp only [hterm]
        rw [← Finset.mul_sum]
        have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0.le hq1
        rw [← Finset.range_eq_Ico, pow_zero, one_div] at hg
        exact mul_le_mul_of_nonneg_left hg (mul_nonneg hK (Real.rpow_nonneg hR₀.le _))

/-- **The statement (4.117)** of the proof of Proposition 4.12. -/
theorem exists_blockBound (hd : 1 ≤ d) (hmono : Monotone F) (hs1 : 1 < s) (hs2 : s ≤ 2) (hB0 : 0 < B) (hA0 : 0 < A)
    {η₁ η₂ β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ (d : ℝ) / 2) (hδ : 0 < δ) (hη₁ : 0 < η₁)
    (hη₁₂ : η₁ < η₂) (hη₂ : η₂ * (1 + δ) < 1) (hα : β < η₁ * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure Ω) [IsProbabilityMeasure P], HasUnitRange P F →
      ∀ (X : CenteredLocalFields P F s δ α B A) (R₁ : ℝ), BlockBound X η₁ η₂ β R₁ C := by
  obtain ⟨ε, R₀, K, C₁, hε, hR₀, hK, hC₁, hstep⟩ :=
    exists_blockBound_step (Ω := Ω) hd hmono hs1 hs2 hB0 hA0 hβ hδ hη₁ hη₁₂ hη₂ hα
  obtain ⟨Cb, hCb, hbase⟩ := exists_blockBound_base (Ω := Ω) (F := F) (δ := δ) (α := α)
    (A := A) hs1 hs2 hB0
  have hR₀0 : 0 < R₀ := by linarith
  set C₂ : ℝ := max C₁ (Cb * B * R₀ ^ β) with hC₂def
  have hC₂ : 0 < C₂ := hC₁.trans_le (le_max_left _ _)
  set c : ℕ → ℝ := fun n => C₂ * ∏ j ∈ Finset.range n, (1 + K * (2 ^ j * R₀) ^ (-ε))
    with hcdef
  have hfac : ∀ j : ℕ, 1 ≤ 1 + K * (2 ^ j * R₀) ^ (-ε) := fun j => by
    have := mul_nonneg hK.le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j * R₀) (-ε))
    linarith
  have hcge : ∀ n, C₂ ≤ c n := fun n =>
    le_mul_of_one_le_right hC₂.le (Finset.one_le_prod₀ fun j _ => hfac j)
  set C : ℝ := C₂ * Real.exp (K * R₀ ^ (-ε) * (1 - (2 : ℝ) ^ (-ε))⁻¹) with hCdef
  refine ⟨C, by positivity, fun P _ hF X R₁ => ?_⟩
  have hind : ∀ n : ℕ, BlockBound X η₁ η₂ β (2 ^ n * R₀) (c n) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_mul, hcdef, Finset.range_zero, Finset.prod_empty, mul_one]
      exact hbase P X η₁ η₂ β R₀ C₂ hβ0.le (le_max_right _ _)
    | succ n ih =>
      have hR : R₀ ≤ 2 ^ n * R₀ := le_mul_of_one_le_left hR₀0.le (one_le_pow₀ one_le_two)
      have h := hstep P hF X (2 ^ n * R₀) (c n) hR ((le_max_left _ _).trans (hcge n)) ih
      rw [show 2 * (2 ^ n * R₀) = 2 ^ (n + 1) * R₀ by ring] at h
      simpa only [hcdef, Finset.prod_range_succ, mul_assoc] using h
  obtain ⟨n, hn⟩ := exists_nat_ge R₁
  have hR₁ : R₁ ≤ 2 ^ n * R₀ := by
    calc R₁ ≤ n := hn
      _ ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ n * R₀ := le_mul_of_one_le_right (by positivity) hR₀
  refine (hind n).mono hR₁ ?_
  exact mul_le_mul_of_nonneg_left (prod_one_add_le_exp hK.le hR₀0 hε n) hC₂.le

end QSH
