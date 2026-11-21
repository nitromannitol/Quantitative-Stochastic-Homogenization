import QuantitativeStochasticHomogenization.Ch05.Sec04.Lemma529Boundary

/-!
# Lemma 5.29 (iii): change of the scale of a block

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29 (iii), for centered local additive fields: for `β ∈ [η₁, 1)` there is
`ε > 0` with `R^{-d} ∫_{□_R} X(r) = R^{-d} ∫_{□_R} X(R^{η₁}) + 𝒪_s(C R^{-d/2-ε})` for
`r ∈ [R^{η₁}, R^β]`. By Step 1 of Proposition 4.12 with `r₁ = R^{η₁}`, the left side is
`R^{-d} ∫ g X(R^{η₁})` with `g = 1_{□_R} ∗ Φ_{√(r²-r₁²)}`, up to `𝒪_s(C R^{-η₁ α})`. The difference
`g - 1_{□_R}` is tiny inside `□_{R-R^b}`, bounded by one in the layers `□_R \ □_{R-R^b}` and
`□_{R+R^b} \ □_R`, and has a Gaussian tail outside `□_{R+R^b}`; the layers are handled by
Lemma 5.29 (ii).

The width of the layers is `R^b` with `b = max((1+β)/2, (1+η₁(1+δ))/2)`. The book takes
`b = (1+β)/2`; Lemma 5.29 (ii) at the scale `R^{η₁}` needs `η₁(1+δ) ≤ b`, which `b = (1+β)/2`
gives only when `η₁(1+2δ) ≤ 1`.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {F : Set (Vec d) → MeasurableSpace Ω} {s δ α : ℝ}

/-- **Small blocks**: a block with a weight bounded by `τ` and vanishing off a closed cube of side
`R` is `𝒪_s(C(s) B τ)`. -/
theorem exists_centeredOsBound_small_block {B A : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (hB0 : 0 < B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : Measure Ω) [IsProbabilityMeasure P]
      (X : CenteredLocalFields P F s δ α B A) (r : ℝ) {z : Vec d} {R τ : ℝ}, 0 < R → 0 < τ →
      ∀ w : Vec d → ℝ, Measurable w → (∀ x, |w x| ≤ τ) → (∀ x ∉ closedCube z R, w x = 0) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, w x * X.field r a x) s (C₀ * (B * τ)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_abs_le hs1 hs2
  refine ⟨C₀, hC₀, fun P _ X r z R τ hR hτ w hw hwτ hwz => ?_⟩
  have hwi : Integrable w := by
    have he : w = (closedCube z R).indicator w := by
      funext x
      by_cases hx : x ∈ closedCube z R
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hwz x hx]
    rw [he, integrable_indicator_iff (measurableSet_closedCube z R)]
    have : IsFiniteMeasure (volume.restrict (closedCube z R)) :=
      ⟨by rw [Measure.restrict_apply_univ, volume_closedCube z hR.le]; exact ENNReal.ofReal_lt_top⟩
    exact Integrable.of_bound hw.aestronglyMeasurable τ
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hwτ x)
  have hint : ∫ x, |w x| ≤ τ * R ^ d := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedCube z R)
      (fun x hx => by rw [hwz x hx, abs_zero])]
    calc ∫ x in closedCube z R, |w x| ≤ ∫ _x in closedCube z R, τ :=
          setIntegral_mono_on hwi.abs.integrableOn (integrableOn_const (by
            rw [volume_closedCube z hR.le]; exact ENNReal.ofReal_ne_top))
            (measurableSet_closedCube z R) fun x _ => hwτ x
      _ = τ * R ^ d := by
          rw [setIntegral_const, smul_eq_mul, volume_real_closedCube z hR.le, mul_comm]
  have hY : ∀ a, |R ^ (-(d : ℝ)) * ∫ x, w x * X.field r a x| ≤ B * τ := by
    intro a
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hR _)]
    calc R ^ (-(d : ℝ)) * |∫ x, w x * X.field r a x| ≤ R ^ (-(d : ℝ)) * (B * (τ * R ^ d)) :=
          mul_le_mul_of_nonneg_left ((abs_integral_mul_le (X.abs_le r) hwi a).trans
            (mul_le_mul_of_nonneg_left hint hB0.le)) (Real.rpow_nonneg hR.le _)
      _ = B * τ := by
          have h1 : R ^ (-(d : ℝ)) * R ^ d = 1 := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
          calc R ^ (-(d : ℝ)) * (B * (τ * R ^ d)) = B * τ * (R ^ (-(d : ℝ)) * R ^ d) := by ring
            _ = B * τ := by rw [h1, mul_one]
  exact h₀ P _ (B * τ) (measurable_block X r hw _) (mul_pos hB0 hτ) hY
    (integral_block_eq_zero X r hwi _)

theorem cube_mono (z : Vec d) {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) : cube z R₁ ⊆ cube z R₂ :=
  fun _ hx i => (hx i).trans_le (by linarith)

theorem centeredOsBound_zero' {P : Measure Ω} [IsProbabilityMeasure P] {s θ : ℝ} (hs1 : 1 < s)
    (hs2 : s ≤ 2) (hθ : 0 < θ) : CenteredOsBound P (fun _ => (0 : ℝ)) s θ := by
  refine ⟨measurable_const, hs1, hs2, hθ, fun t => ⟨by simp, ?_⟩⟩
  simp only [mul_zero, Real.exp_zero, integral_const, probReal_univ, one_smul]
  exact Real.one_le_exp (le_max_of_le_left (sq_nonneg t))

/-- The heat average of the indicator of a cube: `0 ≤ g ≤ 1`, and `1 - g` is at most
`2^{d/2} exp(-(L/2)²/(8ρ²))` on the cube of side `R - L`. -/
theorem heatSmooth_cube_bounds (z : Vec d) {R L ρ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (x : Vec d) :
    0 ≤ heatSmooth ((cube z R).indicator fun _ => (1 : ℝ)) ρ x ∧
      heatSmooth ((cube z R).indicator fun _ => (1 : ℝ)) ρ x ≤ 1 ∧
      (x ∈ cube z (R - L) → 1 - heatSmooth ((cube z R).indicator fun _ => (1 : ℝ)) ρ x ≤
        2 ^ ((d : ℝ) / 2) * Real.exp (-((L / 2) ^ 2 / (8 * ρ ^ 2)))) := by
  have hm := measurableSet_cube z R
  have e : heatSmooth ((cube z R).indicator fun _ => (1 : ℝ)) ρ x =
      ∫ y in cube z R, heatKernel x ρ y := by
    unfold heatSmooth
    rw [← integral_indicator hm]
    congr 1
    funext y
    by_cases hy : y ∈ cube z R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul, heatKernel_comm]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  rw [e]
  have hi := integrable_heatKernel x hρ
  have htot : (∫ y in cube z R, heatKernel x ρ y) + ∫ y in (cube z R)ᶜ, heatKernel x ρ y = 1 := by
    rw [integral_add_compl hm hi, integral_heatKernel x hρ]
  have hc : 0 ≤ ∫ y in (cube z R)ᶜ, heatKernel x ρ y :=
    setIntegral_nonneg hm.compl fun y _ => heatKernel_nonneg x ρ y
  refine ⟨setIntegral_nonneg hm fun y _ => heatKernel_nonneg x ρ y, by linarith, fun hx => ?_⟩
  have hfar : ∀ y ∈ (cube z R)ᶜ, L / 2 ≤ euclideanNorm (y - x) := by
    intro y hy
    simp only [cube, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hy
    obtain ⟨i, hi⟩ := hy
    have hxi := hx i
    have h1 : |y i - x i| ≤ euclideanNorm (y - x) := by
      simpa using abs_apply_le_euclideanNorm' (y - x) i
    have h2 : |y i - z i| ≤ |y i - x i| + |x i - z i| := by
      calc |y i - z i| = |(y i - x i) + (x i - z i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have := setIntegral_heatKernel_le_of_far x hρ (by positivity) hm.compl hfar
  linarith

end QSH
