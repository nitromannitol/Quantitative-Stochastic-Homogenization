import QuantitativeStochasticHomogenization.Ch04.Sec05.BlockFields

/-!
# The induction on the scale in the proof of Proposition 4.12

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.5, prove Proposition 4.12 through the statement (4.117): block averages
`R^{-d} ∫_{□_R(z)} f J₁^{(δ)}(·, r)` of the centered localized energy, for `r ∈ [R^{η₁}, R^{η₂}]`
and `|f| ≤ 1`, are `𝒪_s(C R^{-β})`. This file proves (4.117) for an abstract family of fields with
the properties used there (`CenteredLocalFields`): bounded, jointly measurable, centered, local at
the radius `r^{1+δ}` in the sense of `LocFieldEstimate`, and additive in the sense of (4.116).

This part contains the setting, the statement `BlockBound` of `A(R₁, C)` and its base case.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

theorem continuous_heatKernel_prod (ρ : ℝ) :
    Continuous fun p : Vec d × Vec d => heatKernel p.1 ρ p.2 := by
  unfold heatKernel euclideanHeatKernel euclideanSq dot
  fun_prop

theorem measurable_heatKernel_prod (ρ : ℝ) :
    Measurable fun p : Vec d × Vec d => heatKernel p.1 ρ p.2 :=
  (continuous_heatKernel_prod ρ).measurable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Centered local fields** at exponent `s`, localization exponent `δ`, additivity exponent
`α`, bound `B` and additivity constant `A`: a family `X(r, a, x)` of random fields indexed by the
scale `r`, bounded by `B`, jointly measurable, local at the radius `r^{1+δ}` (as in
`LocFieldEstimate`), centered at every point, and additive:
`X(r, ·, x) - ∫ Φ_{x,√(r²-r₁²)} X(r₁, ·, ·) = 𝒪_s(A r₁^{-α})` for `1 ≤ r₁ < r`, the property
(4.116) of the centered localized energy. -/
structure CenteredLocalFields (P : Measure Ω) (F : Set (Vec d) → MeasurableSpace Ω)
    (s δ α B A : ℝ) where
  /-- The fields. -/
  field : ℝ → Ω → Vec d → ℝ
  abs_le : ∀ r a x, |field r a x| ≤ B
  measurable : ∀ r, Measurable fun w : Ω × Vec d => field r w.1 w.2
  isLocal : ∀ r, 1 ≤ r → ∀ U : Set (Vec d), MeasurableSet U →
    @Measurable (Ω × Vec d) ℝ
      (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
      (fun w => U.indicator (field r w.1) w.2)
  centered : ∀ r x, ∫ a, field r a x ∂P = 0
  additive : ∀ r₁ r, 1 ≤ r₁ → r₁ < r → ∀ x : Vec d,
    CenteredOsBound P (fun a => field r a x -
      ∫ y, heatKernel x (Real.sqrt (r ^ 2 - r₁ ^ 2)) y * field r₁ a y) s (A * r₁ ^ (-α))

variable {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω} {s δ α B A : ℝ}

/-- **The statement `A(R₁, C)`** of the proof of Proposition 4.12: for `1 ≤ R ≤ R₁`,
`r ∈ [R^{η₁}, R^{η₂}]`, every center and every measurable `f` with `|f| ≤ 1` vanishing off the
closed cube of side `R`, `R^{-d} ∫ f X(r, ·, ·) = 𝒪_s(C R^{-β})`. -/
def BlockBound (X : CenteredLocalFields P F s δ α B A) (η₁ η₂ β R₁ C : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R ≤ R₁ → ∀ r : ℝ, R ^ η₁ ≤ r → r ≤ R ^ η₂ →
    ∀ (z : Vec d) (f : Vec d → ℝ), Measurable f → (∀ x, |f x| ≤ 1) →
      (∀ x ∉ closedCube z R, f x = 0) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x) s (C * R ^ (-β))

theorem BlockBound.mono {X : CenteredLocalFields P F s δ α B A} {η₁ η₂ β R₁ R₁' C C' : ℝ}
    (h : BlockBound X η₁ η₂ β R₁ C) (hR : R₁' ≤ R₁) (hC : C ≤ C') :
    BlockBound X η₁ η₂ β R₁' C' := by
  intro R hR1 hRR r hr1 hr2 z f hf hf1 hfz
  refine (h R hR1 (hRR.trans hR) r hr1 hr2 z f hf hf1 hfz).mono_scale ?_
  exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (zero_le_one.trans hR1) _)

theorem measurable_block (X : CenteredLocalFields P F s δ α B A) (r : ℝ) {f : Vec d → ℝ}
    (hf : Measurable f) (c : ℝ) :
    Measurable fun a => c * ∫ x, f x * X.field r a x :=
  measurable_const.mul (measurable_integral_mul hf (X.measurable r))

theorem integral_block_eq_zero [IsProbabilityMeasure P] (X : CenteredLocalFields P F s δ α B A)
    (r : ℝ) {f : Vec d → ℝ} (hf : Integrable f) (c : ℝ) :
    ∫ a, c * (∫ x, f x * X.field r a x) ∂P = 0 := by
  rw [integral_const_mul, integral_integral_mul_eq_zero (X.measurable r) (X.abs_le r)
    (X.centered r) hf, mul_zero]

/-- **The base case**: for `R₁ ≥ 1` the statement `A(R₁, C)` holds for every
`C ≥ C(s) B R₁^β`, where `B` bounds the fields. -/
theorem exists_blockBound_base (hs1 : 1 < s) (hs2 : s ≤ 2) (hB0 : 0 < B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : Measure Ω) [IsProbabilityMeasure P]
      (X : CenteredLocalFields P F s δ α B A) (η₁ η₂ β R₁ C : ℝ), 0 ≤ β →
      C₀ * B * R₁ ^ β ≤ C → BlockBound X η₁ η₂ β R₁ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_abs_le hs1 hs2
  refine ⟨C₀, hC₀, fun P _ X η₁ η₂ β R₁ C hβ hC => ?_⟩
  intro R hR1 hRR r _ _ z f hf hf1 hfz
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hfi := integrable_of_abs_le_one_of_closedCube hf hf1 hR0.le hfz
  have hY : ∀ a, |R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x| ≤ B := by
    intro a
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hR0 _)]
    calc R ^ (-(d : ℝ)) * |∫ x, f x * X.field r a x|
        ≤ R ^ (-(d : ℝ)) * (B * R ^ d) :=
          mul_le_mul_of_nonneg_left ((abs_integral_mul_le (X.abs_le r) hfi a).trans
            (mul_le_mul_of_nonneg_left (integral_abs_le_of_closedCube hf hf1 hR0.le hfz)
              hB0.le)) (Real.rpow_nonneg hR0.le _)
      _ = B := by
          rw [← Real.rpow_natCast, mul_comm B, ← mul_assoc, ← Real.rpow_add hR0,
            neg_add_cancel, Real.rpow_zero, one_mul]
  have h := h₀ P _ B (measurable_block X r hf _) hB0 hY
    (integral_block_eq_zero X r hfi _)
  refine h.mono_scale ?_
  have h1 : R₁ ^ (-β) ≤ R ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hR0 hRR (by linarith)
  have hR₁ : 0 < R₁ := hR0.trans_le hRR
  have h2 : C₀ * B = C₀ * B * R₁ ^ β * R₁ ^ (-β) := by
    rw [mul_assoc (C₀ * B), ← Real.rpow_add hR₁, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [h2]
  calc C₀ * B * R₁ ^ β * R₁ ^ (-β) ≤ C * R₁ ^ (-β) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hR₁.le _)
    _ ≤ C * R ^ (-β) := mul_le_mul_of_nonneg_left h1
        ((mul_nonneg (mul_nonneg hC₀.le hB0.le) (Real.rpow_nonneg hR₁.le _)).trans hC)

end QSH
