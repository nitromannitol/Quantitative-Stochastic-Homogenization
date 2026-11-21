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
`b = (1+β)/2`; Lemma 5.29 (ii) at the scale `R^{η₁}` needs `η₁(1+δ) ≤ b`, which holds for
`b = (1+β)/2` and every `β ≥ η₁` only when `η₁(1+2δ) ≤ 1`.
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
    0 ≤ heatWeightAverage ((cube z R).indicator fun _ => (1 : ℝ)) ρ x ∧
      heatWeightAverage ((cube z R).indicator fun _ => (1 : ℝ)) ρ x ≤ 1 ∧
      (x ∈ cube z (R - L) → 1 - heatWeightAverage ((cube z R).indicator fun _ => (1 : ℝ)) ρ x ≤
        2 ^ ((d : ℝ) / 2) * Real.exp (-((L / 2) ^ 2 / (8 * ρ ^ 2)))) := by
  have hm := measurableSet_cube z R
  have e : heatWeightAverage ((cube z R).indicator fun _ => (1 : ℝ)) ρ x =
      ∫ y in cube z R, heatKernel x ρ y := by
    unfold heatWeightAverage
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

/-- The four pieces of `g - 1_{□_R}`: the inner cube `□_{R-L}`, the inner layer, the outer
layer `□_{R+L} \ □_R` and the outside of `□_{R+L}`. -/
theorem indicator_cube_layers (z : Vec d) {R L : ℝ} (hL : 0 ≤ L) (g f : Vec d → ℝ)
    (hf : ∀ y ∉ cube z R, f y = 0) (y : Vec d) :
    g y - f y = (cube z (R - L)).indicator (fun y => g y - f y) y +
      (cube z R \ cube z (R - L)).indicator (fun y => g y - f y) y +
      (cube z (R + L) \ cube z R).indicator g y + (cube z (R + L))ᶜ.indicator g y := by
  have hm1 : cube z (R - L) ⊆ cube z R := cube_mono z (by linarith)
  have hm2 : cube z R ⊆ cube z (R + L) := cube_mono z (by linarith)
  by_cases h1 : y ∈ cube z (R - L)
  · simp [h1, hm1 h1, hm2 (hm1 h1)]
  · by_cases h2 : y ∈ cube z R
    · simp [h1, h2, hm2 h2]
    · by_cases h3 : y ∈ cube z (R + L)
      · simp [h1, h2, h3, hf y h2]
      · simp [h1, h2, h3, hf y h2]

variable {P : Measure Ω} {B A : ℝ}

/-- **The decomposition of the proof of Lemma 5.29 (iii)**: with `L = R^b`, the change of scale
from `r₁` to `r` of the block of `□_R` is bounded by the additivity defect, a block with small
weight on `□_{R-L}`, the boundary layers of `□_R` and `□_{R+L}`, and a far block. -/
theorem centeredOsBound_change_step [IsProbabilityMeasure P] (X : CenteredLocalFields P F s δ α B A)
    {η₁ Cl Cs Cf : ℝ}
    (hlay : ∀ R : ℝ, 1 ≤ R → ∀ b : ℝ, 0 ≤ b → b ≤ 1 → ∀ r : ℝ, R ^ (b * η₁) ≤ r →
      r ≤ R ^ (b / (1 + δ)) → ∀ (z : Vec d) (f : Vec d → ℝ), Measurable f → (∀ x, |f x| ≤ 1) →
      (∀ x, f x ≠ 0 → x ∈ cube z R \ cube z (R - R ^ b)) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x) s
        (Cl * R ^ (-(d : ℝ) / 2 - (1 - b) / 2)))
    (hsmall : ∀ (r : ℝ) {z : Vec d} {R τ : ℝ}, 0 < R → 0 < τ →
      ∀ w : Vec d → ℝ, Measurable w → (∀ x, |w x| ≤ τ) → (∀ x ∉ closedCube z R, w x = 0) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, w x * X.field r a x) s (Cs * (B * τ)))
    (hfar : ∀ (r₁ : ℝ) {z : Vec d} {R ρ t : ℝ}, 0 < R → 0 < ρ → 0 ≤ t → ∀ {f : Vec d → ℝ},
      Measurable f → (∀ x, |f x| ≤ 1) → (∀ x ∉ closedCube z R, f x = 0) →
      ∀ {S : Set (Vec d)}, MeasurableSet S →
      (∀ x ∈ closedCube z R, ∀ y ∈ S, t ≤ euclideanNorm (y - x)) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) *
        ∫ y, S.indicator (heatWeightAverage f ρ) y * X.field r₁ a y) s
        (Cf * (B * 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * ρ ^ 2))))))
    {R b r r₁ : ℝ} (hR : 1 ≤ R) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hr₁ : 1 ≤ r₁) (hr₁r : r₁ < r)
    (hlo : R ^ (b * η₁) ≤ r₁) (hhi : r₁ ≤ R ^ (b / (1 + δ)))
    (hlo' : (R + R ^ b) ^ (b * η₁) ≤ r₁) (hhi' : r₁ ≤ (R + R ^ b) ^ (b / (1 + δ)))
    (z : Vec d) :
    CenteredOsBound P (fun a =>
        (R ^ (-(d : ℝ)) * ∫ x, (cube z R).indicator (fun _ => (1 : ℝ)) x * X.field r a x) -
        R ^ (-(d : ℝ)) * ∫ x, (cube z R).indicator (fun _ => (1 : ℝ)) x * X.field r₁ a x) s
      (A * r₁ ^ (-α) +
        Cs * (B * (2 ^ ((d : ℝ) / 2) *
          Real.exp (-((R ^ b / 2) ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2))))) +
        Cl * R ^ (-(d : ℝ) / 2 - (1 - b) / 2) +
        R ^ (-(d : ℝ)) * (R + R ^ b) ^ d * (Cl * (R + R ^ b) ^ (-(d : ℝ) / 2 - (1 - b) / 2)) +
        Cf * (B * 2 ^ ((d : ℝ) / 2) *
          Real.exp (-((R ^ b / 2) ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2))))) := by
  classical
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set f : Vec d → ℝ := (cube z R).indicator fun _ => (1 : ℝ) with hfdef
  have hfm : Measurable f := measurable_const.indicator (measurableSet_cube z R)
  have hf_in : ∀ y ∈ cube z R, f y = 1 := fun y hy => Set.indicator_of_mem hy _
  have hf_out : ∀ y ∉ cube z R, f y = 0 := fun y hy => Set.indicator_of_notMem hy _
  have hf1 : ∀ x, |f x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ cube z R
    · rw [hf_in x hx, abs_one]
    · rw [hf_out x hx, abs_zero]; exact zero_le_one
  have hfz : ∀ x ∉ closedCube z R, f x = 0 := fun x hx =>
    hf_out x (fun h => hx (cube_subset_closedCube z R h))
  have hpos : 0 < r ^ 2 - r₁ ^ 2 :=
    sub_pos.mpr (pow_lt_pow_left₀ hr₁r (by linarith) two_ne_zero)
  set ρ : ℝ := Real.sqrt (r ^ 2 - r₁ ^ 2) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hpos
  set L : ℝ := R ^ b with hLdef
  have hL0 : 0 < L := Real.rpow_pos_of_pos hR0 b
  have hRR' : R ≤ R + L := by linarith
  have hR'0 : 0 < R + L := by linarith
  set g : Vec d → ℝ := heatWeightAverage f ρ with hgdef
  have hfi := integrable_of_abs_le_one_of_closedCube hfm hf1 hR0.le hfz
  have hgm : Measurable g := measurable_heatSmooth hfm ρ
  have hgi : Integrable g := integrable_heatSmooth hfi hfm hρ
  set E : ℝ := Real.exp (-((L / 2) ^ 2 / (8 * ρ ^ 2))) with hEdef
  have hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1 ∧ (y ∈ cube z (R - L) → 1 - g y ≤ 2 ^ ((d : ℝ) / 2) * E) :=
    fun y => heatSmooth_cube_bounds z hρ hL0.le y
  have hm1 : cube z (R - L) ⊆ cube z R := cube_mono z (by linarith)
  have hτ : 0 < 2 ^ ((d : ℝ) / 2) * E := by positivity
  have hS1 := measurableSet_cube z (R - L)
  have hS2 := (measurableSet_cube z R).diff (measurableSet_cube z (R - L))
  have hS3 := (measurableSet_cube z (R + L)).diff (measurableSet_cube z R)
  have hS4 := (measurableSet_cube z (R + L)).compl
  have hw1b : ∀ y, |(cube z (R - L)).indicator (fun y => g y - f y) y| ≤
      2 ^ ((d : ℝ) / 2) * E := by
    intro y
    by_cases hy : y ∈ cube z (R - L)
    · rw [Set.indicator_of_mem hy, hf_in y (hm1 hy)]
      obtain ⟨-, h1, h2⟩ := hgb y
      exact abs_le.mpr ⟨by linarith only [h2 hy], by linarith only [h1, hτ]⟩
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact hτ.le
  have hw2b : ∀ y, |(cube z R \ cube z (R - L)).indicator (fun y => g y - f y) y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ cube z R \ cube z (R - L)
    · rw [Set.indicator_of_mem hy, hf_in y hy.1]
      obtain ⟨h0, h1, -⟩ := hgb y
      exact abs_le.mpr ⟨by linarith only [h0], by linarith only [h1]⟩
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact zero_le_one
  have hw3b : ∀ y, |(cube z (R + L) \ cube z R).indicator g y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ cube z (R + L) \ cube z R
    · rw [Set.indicator_of_mem hy]
      obtain ⟨h0, h1, -⟩ := hgb y
      exact abs_le.mpr ⟨by linarith only [h0], h1⟩
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact zero_le_one
  have hw1z : ∀ y ∉ closedCube z R, (cube z (R - L)).indicator (fun y => g y - f y) y = 0 :=
    fun y hy => Set.indicator_of_notMem (fun h => hy (cube_subset_closedCube z R (hm1 h))) _
  have hw2s : ∀ y, (cube z R \ cube z (R - L)).indicator (fun y => g y - f y) y ≠ 0 →
      y ∈ cube z R \ cube z (R - R ^ b) := fun y hy => Set.mem_of_indicator_ne_zero hy
  have hR'b : R ^ b ≤ (R + L) ^ b := Real.rpow_le_rpow hR0.le hRR' hb0
  have hw3s : ∀ y, (cube z (R + L) \ cube z R).indicator g y ≠ 0 →
      y ∈ cube z (R + L) \ cube z ((R + L) - (R + L) ^ b) := by
    intro y hy
    have hmem : y ∈ cube z (R + L) \ cube z R := Set.mem_of_indicator_ne_zero hy
    exact ⟨hmem.1, fun h => hmem.2 (cube_mono z (by linarith) h)⟩
  have hT1 := centeredOsBound_block_additivity_defect X hr₁ hr₁r hR0 hfm (fun x => hf1 x) hfz
  have hW1 := hsmall r₁ hR0 hτ _ ((hgm.sub hfm).indicator hS1) hw1b hw1z
  have hW2 := hlay R hR b hb0 hb1 r₁ hlo hhi z _ ((hgm.sub hfm).indicator hS2) hw2b hw2s
  have hc : 0 < R ^ (-(d : ℝ)) * (R + L) ^ d := by positivity
  have hW3 := (hlay (R + L) (by linarith) b hb0 hb1 r₁ hlo' hhi' z _ (hgm.indicator hS3) hw3b
    hw3s).const_mul hc
  have hfarS : ∀ x ∈ closedCube z R, ∀ y ∈ (cube z (R + L))ᶜ, L / 2 ≤ euclideanNorm (y - x) := by
    intro x hx y hy
    simp only [cube, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hy
    obtain ⟨i, hi⟩ := hy
    have hxi := hx i
    have h1 : |y i - x i| ≤ euclideanNorm (y - x) := by
      simpa using abs_apply_le_euclideanNorm' (y - x) i
    have h2 : |y i - z i| ≤ |y i - x i| + |x i - z i| := by
      calc |y i - z i| = |(y i - x i) + (x i - z i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith only [hi, hxi, h1, h2]
  have hW4 : CenteredOsBound P (fun a => R ^ (-(d : ℝ)) *
      ∫ y, (cube z (R + L))ᶜ.indicator g y * X.field r₁ a y) s
      (Cf * (B * 2 ^ ((d : ℝ) / 2) * E)) :=
    hfar r₁ hR0 hρ (by positivity) hfm hf1 hfz hS4 hfarS
  have hsum := (((hT1.add hW1).add hW2).add hW3).add hW4
  refine hsum.congr_ae ((measurable_block X r hfm (R ^ (-(d : ℝ)))).sub
    (measurable_block X r₁ hfm (R ^ (-(d : ℝ))))) (Filter.Eventually.of_forall fun a => ?_)
  have hDint : Integrable fun x => f x * (X.field r a x -
      ∫ y, heatKernel x ρ y * X.field r₁ a y) := by
    refine hfi.mul_bdd (c := 2 * B) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((X.measurable r).comp measurable_prodMk_left).sub
        ((measurable_heatAverage _ (X.measurable r₁) ρ).comp
          measurable_prodMk_left)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      have h1 := X.abs_le r a x
      have h2 := X.abs_heatAverage_le r₁ a x hρ
      linarith only [h1, h2]
  have hHint : Integrable fun x => f x * ∫ y, heatKernel x ρ y * X.field r₁ a y := by
    refine hfi.mul_bdd (c := B) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((measurable_heatAverage _ (X.measurable r₁) ρ).comp
        measurable_prodMk_left).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact X.abs_heatAverage_le r₁ a x hρ
  have hsplit1 : ∫ x, f x * X.field r a x = (∫ x, f x * (X.field r a x -
      ∫ y, heatKernel x ρ y * X.field r₁ a y)) +
      ∫ x, f x * ∫ y, heatKernel x ρ y * X.field r₁ a y := by
    rw [← integral_add hDint hHint]
    congr 1
    funext x
    ring
  have hfub : ∫ x, f x * ∫ y, heatKernel x ρ y * X.field r₁ a y =
      ∫ y, g y * X.field r₁ a y :=
    integral_mul_heat_eq hfi hρ (G := fun y => X.field r₁ a y)
      ((X.measurable r₁).comp measurable_prodMk_left) (X.abs_le r₁ a)
  have hi1 : Integrable fun y => (cube z (R - L)).indicator (fun y => g y - f y) y *
      X.field r₁ a y := X.integrable_mul r₁ a ((hgi.sub hfi).indicator hS1)
  have hi2 : Integrable fun y => (cube z R \ cube z (R - L)).indicator (fun y => g y - f y) y *
      X.field r₁ a y := X.integrable_mul r₁ a ((hgi.sub hfi).indicator hS2)
  have hi3 := X.integrable_mul r₁ a (hgi.indicator hS3)
  have hi4 := X.integrable_mul r₁ a (hgi.indicator hS4)
  have hdec : (∫ y, g y * X.field r₁ a y) - ∫ y, f y * X.field r₁ a y =
      (∫ y, (cube z (R - L)).indicator (fun y => g y - f y) y * X.field r₁ a y) +
      (∫ y, (cube z R \ cube z (R - L)).indicator (fun y => g y - f y) y * X.field r₁ a y) +
      (∫ y, (cube z (R + L) \ cube z R).indicator g y * X.field r₁ a y) +
      ∫ y, (cube z (R + L))ᶜ.indicator g y * X.field r₁ a y := by
    have hfun : (fun y => g y * X.field r₁ a y - f y * X.field r₁ a y) = fun y =>
        (cube z (R - L)).indicator (fun y => g y - f y) y * X.field r₁ a y +
        (cube z R \ cube z (R - L)).indicator (fun y => g y - f y) y * X.field r₁ a y +
        (cube z (R + L) \ cube z R).indicator g y * X.field r₁ a y +
        (cube z (R + L))ᶜ.indicator g y * X.field r₁ a y := by
      funext y
      rw [← sub_mul, indicator_cube_layers z hL0.le g f hf_out y]
      ring
    rw [← integral_sub (X.integrable_mul r₁ a hgi) (X.integrable_mul r₁ a hfi), hfun,
      integral_add ?_ hi4, integral_add ?_ hi3, integral_add hi1 hi2]
    all_goals first | exact hi1.add hi2 | exact (hi1.add hi2).add hi3
  have hR'd : (R + L) ^ d * (R + L) ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR'0, add_neg_cancel, Real.rpow_zero]
  have hc' : R ^ (-(d : ℝ)) * (R + L) ^ d * (R + L) ^ (-(d : ℝ)) = R ^ (-(d : ℝ)) := by
    rw [mul_assoc, hR'd, mul_one]
  beta_reduce
  rw [hsplit1, hfub]
  linear_combination (-(R ^ (-(d : ℝ)))) * hdec +
    (∫ y, (cube z (R + L) \ cube z R).indicator g y * X.field r₁ a y) * hc'

/-- The gain of Lemma 5.29 (iii): `ε = min(η₁ α - d/2, (1 - b)/2)` with
`b = max((1+β)/2, (1+η₁(1+δ))/2)`. -/
noncomputable def changeGain (d : ℕ) (δ α η₁ β : ℝ) : ℝ :=
  min (η₁ * α - (d : ℝ) / 2) ((1 - max ((1 + β) / 2) ((1 + η₁ * (1 + δ)) / 2)) / 2)

omit [MeasurableSpace Ω] in
theorem changeGain_pos {η₁ η₂ β : ℝ} (hδ : 0 < δ) (hη₁₂ : η₁ < η₂) (hη₂ : η₂ * (1 + δ) < 1)
    (hα : (d : ℝ) / 2 < η₁ * α) (hβ1 : β < 1) : 0 < changeGain d δ α η₁ β := by
  have hη₁δ : η₁ * (1 + δ) < 1 := by
    have : η₁ * (1 + δ) < η₂ * (1 + δ) := mul_lt_mul_of_pos_right hη₁₂ (by linarith)
    linarith
  have hb1 : max ((1 + β) / 2) ((1 + η₁ * (1 + δ)) / 2) < 1 := max_lt (by linarith) (by linarith)
  exact lt_min (by linarith) (by linarith)

/-- **Lemma 5.29 (iii)**, for centered local additive fields, with the gain `changeGain`. -/
theorem exists_blockBound_change (hd : 1 ≤ d) (hmono : Monotone F) (hs1 : 1 < s) (hs2 : s ≤ 2)
    {η₁ η₂ β : ℝ} (hδ : 0 < δ) (hη₁ : 0 < η₁) (hη₁₂ : η₁ < η₂) (hη₂ : η₂ * (1 + δ) < 1)
    (hα : (d : ℝ) / 2 < η₁ * α) (hβ1 : β < 1) :
    ∀ B A : ℝ, 0 < B → 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure Ω) [IsProbabilityMeasure P], HasUnitRange P F →
      ∀ (X : CenteredLocalFields P F s δ α B A) (R : ℝ), 1 ≤ R → ∀ r : ℝ, R ^ η₁ ≤ r →
      r ≤ R ^ β → ∀ z : Vec d,
      CenteredOsBound P (fun a =>
        (R ^ (-(d : ℝ)) * ∫ x, (cube z R).indicator (fun _ => (1 : ℝ)) x * X.field r a x) -
        R ^ (-(d : ℝ)) * ∫ x, (cube z R).indicator (fun _ => (1 : ℝ)) x * X.field (R ^ η₁) a x)
        s (C * R ^ (-(d : ℝ) / 2 - changeGain d δ α η₁ β)) := by
  classical
  intro B A hB hA
  have hη₁δ : η₁ * (1 + δ) < 1 := by
    have : η₁ * (1 + δ) < η₂ * (1 + δ) := mul_lt_mul_of_pos_right hη₁₂ (by linarith)
    linarith
  set b : ℝ := max ((1 + β) / 2) ((1 + η₁ * (1 + δ)) / 2) with hbdef
  have hb1 : b < 1 := max_lt (by linarith) (by linarith)
  have hbβ : β < b := (by linarith : β < (1 + β) / 2).trans_le (le_max_left _ _)
  have hbη : η₁ * (1 + δ) ≤ b := (by linarith : η₁ * (1 + δ) ≤ (1 + η₁ * (1 + δ)) / 2).trans
    (le_max_right _ _)
  have hb0 : 0 ≤ b := (by positivity : (0 : ℝ) ≤ (1 + η₁ * (1 + δ)) / 2).trans (le_max_right _ _)
  set ε : ℝ := changeGain d δ α η₁ β with hεdef
  have hε : 0 < ε := changeGain_pos hδ hη₁₂ hη₂ hα hβ1
  obtain ⟨Cl, hCl, hlay⟩ := exists_blockBound_layer (Ω := Ω) (F := F) (δ := δ) (α := α) (B := B)
    (A := A) hd hmono hs1 hs2 hB hA hδ hη₁ hη₁₂ hη₂ hα
  obtain ⟨Cs, hCs, hsmall⟩ := exists_centeredOsBound_small_block (Ω := Ω) (F := F) (δ := δ)
    (α := α) (A := A) hs1 hs2 hB
  obtain ⟨Cf, hCf, hfar⟩ := exists_centeredOsBound_far_block (Ω := Ω) (F := F) (δ := δ)
    (α := α) (A := A) hs1 hs2 hB
  obtain ⟨Ce, hCe, hexp⟩ := exists_exp_neg_rpow_le (c := 1 / 32) (κ := 2 * (b - β))
    (by norm_num) (by linarith) ((d : ℝ) / 2 + ε)
  set Rth : ℝ := max 2 ((2 : ℝ) ^ (b / (1 - b))) with hRthdef
  have hRth : 0 < Rth := by positivity
  set C₁ : ℝ := A + Cs * B * 2 ^ ((d : ℝ) / 2) * Ce + Cl + 2 ^ d * Cl +
    Cf * B * 2 ^ ((d : ℝ) / 2) * Ce with hC₁def
  set C₂ : ℝ := 2 * (Cs * B) * Rth ^ ((d : ℝ) / 2 + ε) with hC₂def
  have hC1 : 0 ≤ C₁ := by positivity
  have hC2 : 0 ≤ C₂ := by positivity
  have hCpos : 0 < C₁ + C₂ + 1 := by linarith
  refine ⟨C₁ + C₂ + 1, hCpos, fun P _ hF X R hR r hr1 hr2 z => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set f : Vec d → ℝ := (cube z R).indicator fun _ => (1 : ℝ) with hfdef
  have hfm : Measurable f := measurable_const.indicator (measurableSet_cube z R)
  have hf1 : ∀ x, |f x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ cube z R
    · simp [hfdef, Set.indicator_of_mem hx]
    · simp [hfdef, Set.indicator_of_notMem hx]
  have hfz : ∀ x ∉ closedCube z R, f x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx (cube_subset_closedCube z R h)) _
  have hQ0 : 0 ≤ R ^ (-(d : ℝ) / 2 - ε) := Real.rpow_nonneg hR0.le _
  have hε1 : ε ≤ η₁ * α - (d : ℝ) / 2 := min_le_left _ _
  have hε2 : ε ≤ (1 - b) / 2 := min_le_right _ _
  by_cases hRs : R < Rth
  · have h1 := hsmall P X r hR0 one_pos f hfm hf1 hfz
    have h2 := (hsmall P X (R ^ η₁) hR0 one_pos f hfm hf1 hfz).neg
    refine ((h1.add h2).congr_ae ((measurable_block X r hfm (R ^ (-(d : ℝ)))).sub
      (measurable_block X (R ^ η₁) hfm (R ^ (-(d : ℝ)))))
      (Filter.Eventually.of_forall fun a => (sub_eq_add_neg _ _).symm)).mono_scale ?_
    have hle : (1 : ℝ) ≤ Rth ^ ((d : ℝ) / 2 + ε) * R ^ (-(d : ℝ) / 2 - ε) := by
      have h3 : Rth ^ (-((d : ℝ) / 2 + ε)) ≤ R ^ (-((d : ℝ) / 2 + ε)) :=
        Real.rpow_le_rpow_of_nonpos hR0 hRs.le (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      have h4 : Rth ^ ((d : ℝ) / 2 + ε) * Rth ^ (-((d : ℝ) / 2 + ε)) = 1 := by
        rw [← Real.rpow_add hRth, add_neg_cancel, Real.rpow_zero]
      rw [show -(d : ℝ) / 2 - ε = -((d : ℝ) / 2 + ε) by ring]
      calc (1 : ℝ) = Rth ^ ((d : ℝ) / 2 + ε) * Rth ^ (-((d : ℝ) / 2 + ε)) := h4.symm
        _ ≤ Rth ^ ((d : ℝ) / 2 + ε) * R ^ (-((d : ℝ) / 2 + ε)) :=
            mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hRth.le _)
    have h5 : Cs * (B * 1) + Cs * (B * 1) ≤ C₂ * R ^ (-(d : ℝ) / 2 - ε) := by
      calc Cs * (B * 1) + Cs * (B * 1) = 2 * (Cs * B) := by ring
        _ ≤ 2 * (Cs * B) * (Rth ^ ((d : ℝ) / 2 + ε) * R ^ (-(d : ℝ) / 2 - ε)) :=
            le_mul_of_one_le_right (by positivity) hle
        _ = C₂ * R ^ (-(d : ℝ) / 2 - ε) := by rw [hC₂def]; ring
    have h6 : 0 ≤ (C₁ + 1) * R ^ (-(d : ℝ) / 2 - ε) := mul_nonneg (by linarith) hQ0
    linarith only [h5, h6]
  push Not at hRs
  have hRth2 : (2 : ℝ) ^ (b / (1 - b)) ≤ R := (le_max_right _ _).trans hRs
  rcases eq_or_lt_of_le hr1 with heq | hlt
  · rw [← heq]
    exact (centeredOsBound_zero' hs1 hs2 (mul_pos hCpos (Real.rpow_pos_of_pos hR0 _))).congr_ae
      ((measurable_block X (R ^ η₁) hfm (R ^ (-(d : ℝ)))).sub
        (measurable_block X (R ^ η₁) hfm (R ^ (-(d : ℝ)))))
      (Filter.Eventually.of_forall fun a => (sub_self _).symm)
  set r₁ : ℝ := R ^ η₁ with hr₁def
  have hr₁1 : 1 ≤ r₁ := Real.one_le_rpow hR hη₁.le
  have hLR : R ^ b ≤ R := by
    calc R ^ b ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hb1.le
      _ = R := Real.rpow_one R
  have hRR' : R ≤ R + R ^ b := le_add_of_nonneg_right (Real.rpow_nonneg hR0.le b)
  have hηb : η₁ ≤ b / (1 + δ) := (le_div_iff₀ (by linarith)).mpr hbη
  have hlo : R ^ (b * η₁) ≤ r₁ :=
    Real.rpow_le_rpow_of_exponent_le hR (mul_le_of_le_one_left hη₁.le hb1.le)
  have hhi : r₁ ≤ R ^ (b / (1 + δ)) := Real.rpow_le_rpow_of_exponent_le hR hηb
  have h2b : (2 : ℝ) ^ b ≤ R ^ (1 - b) := by
    calc (2 : ℝ) ^ b = ((2 : ℝ) ^ (b / (1 - b))) ^ (1 - b) := by
          rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (by linarith)]
      _ ≤ R ^ (1 - b) := Real.rpow_le_rpow (by positivity) hRth2 (by linarith)
  have hR'bR : (R + R ^ b) ^ b ≤ R := by
    calc (R + R ^ b) ^ b ≤ (2 * R) ^ b := Real.rpow_le_rpow (by positivity) (by linarith) hb0
      _ = 2 ^ b * R ^ b := Real.mul_rpow (by norm_num) hR0.le
      _ ≤ R ^ (1 - b) * R ^ b := mul_le_mul_of_nonneg_right h2b (by positivity)
      _ = R := by rw [← Real.rpow_add hR0, sub_add_cancel, Real.rpow_one]
  have hlo' : (R + R ^ b) ^ (b * η₁) ≤ r₁ := by
    calc (R + R ^ b) ^ (b * η₁) = ((R + R ^ b) ^ b) ^ η₁ := Real.rpow_mul (by positivity) b η₁
      _ ≤ R ^ η₁ := Real.rpow_le_rpow (by positivity) hR'bR hη₁.le
  have hhi' : r₁ ≤ (R + R ^ b) ^ (b / (1 + δ)) :=
    hhi.trans (Real.rpow_le_rpow hR0.le hRR' (div_nonneg hb0 (by linarith)))
  have hstep := centeredOsBound_change_step X (hlay P hF X) (hsmall P X) (hfar P X) hR hb0
    hb1.le hr₁1 hlt hlo hhi hlo' hhi' z
  refine hstep.mono_scale ?_
  have hpos : 0 < r ^ 2 - r₁ ^ 2 :=
    sub_pos.mpr (pow_lt_pow_left₀ hlt (by linarith) two_ne_zero)
  set ρ : ℝ := Real.sqrt (r ^ 2 - r₁ ^ 2) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hpos
  have hρβ : ρ ^ 2 ≤ (R ^ β) ^ 2 := by
    rw [hρdef, Real.sq_sqrt hpos.le]
    have h1 := pow_le_pow_left₀ (by linarith) hr2 2
    linarith only [h1, sq_nonneg r₁]
  set L : ℝ := R ^ b with hLdef
  set E : ℝ := Real.exp (-((L / 2) ^ 2 / (8 * ρ ^ 2))) with hEdef
  have hQ : R ^ (-((d : ℝ) / 2 + ε)) = R ^ (-(d : ℝ) / 2 - ε) := by congr 1; ring
  have hE : E ≤ Ce * R ^ (-(d : ℝ) / 2 - ε) := by
    rw [← hQ]
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexp R hR)
    rw [neg_le_neg_iff]
    have hRβ : 0 < R ^ β := Real.rpow_pos_of_pos hR0 β
    have e1 : L = R ^ (b - β) * R ^ β := by rw [hLdef, ← Real.rpow_add hR0, sub_add_cancel]
    have e2 : R ^ (2 * (b - β)) = (R ^ (b - β)) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hR0.le, Real.rpow_two]
    have hkey : 1 / 32 * R ^ (2 * (b - β)) = (L / 2) ^ 2 / (8 * (R ^ β) ^ 2) := by
      rw [e2, e1]
      field_simp
      ring
    rw [hkey]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have b1 : A * r₁ ^ (-α) ≤ A * R ^ (-(d : ℝ) / 2 - ε) := by
    refine mul_le_mul_of_nonneg_left ?_ hA.le
    rw [hr₁def, ← Real.rpow_mul hR0.le]
    exact Real.rpow_le_rpow_of_exponent_le hR (by rw [mul_neg]; linarith)
  have b2 : Cs * (B * (2 ^ ((d : ℝ) / 2) * E)) ≤
      Cs * B * 2 ^ ((d : ℝ) / 2) * Ce * R ^ (-(d : ℝ) / 2 - ε) := by
    calc Cs * (B * (2 ^ ((d : ℝ) / 2) * E)) = Cs * B * 2 ^ ((d : ℝ) / 2) * E := by ring
      _ ≤ Cs * B * 2 ^ ((d : ℝ) / 2) * (Ce * R ^ (-(d : ℝ) / 2 - ε)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  have hlayR : R ^ (-(d : ℝ) / 2 - (1 - b) / 2) ≤ R ^ (-(d : ℝ) / 2 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have b3 : Cl * R ^ (-(d : ℝ) / 2 - (1 - b) / 2) ≤ Cl * R ^ (-(d : ℝ) / 2 - ε) :=
    mul_le_mul_of_nonneg_left hlayR hCl.le
  have hRd : R ^ (-(d : ℝ)) * R ^ d = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR0, neg_add_cancel, Real.rpow_zero]
  have hc2 : R ^ (-(d : ℝ)) * (R + L) ^ d ≤ 2 ^ d := by
    have h1 : (R + L) ^ d ≤ (2 * R) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    calc R ^ (-(d : ℝ)) * (R + L) ^ d ≤ R ^ (-(d : ℝ)) * (2 * R) ^ d :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ d * (R ^ (-(d : ℝ)) * R ^ d) := by ring
      _ = 2 ^ d := by rw [hRd, mul_one]
  have b4 : R ^ (-(d : ℝ)) * (R + L) ^ d * (Cl * (R + L) ^ (-(d : ℝ) / 2 - (1 - b) / 2)) ≤
      2 ^ d * Cl * R ^ (-(d : ℝ) / 2 - ε) := by
    have h1 : (R + L) ^ (-(d : ℝ) / 2 - (1 - b) / 2) ≤ R ^ (-(d : ℝ) / 2 - (1 - b) / 2) :=
      Real.rpow_le_rpow_of_nonpos hR0 hRR' (by
        have := Nat.cast_nonneg (α := ℝ) d
        linarith)
    calc R ^ (-(d : ℝ)) * (R + L) ^ d * (Cl * (R + L) ^ (-(d : ℝ) / 2 - (1 - b) / 2))
        ≤ 2 ^ d * (Cl * R ^ (-(d : ℝ) / 2 - (1 - b) / 2)) :=
          mul_le_mul hc2 (mul_le_mul_of_nonneg_left h1 hCl.le) (by positivity) (by positivity)
      _ ≤ 2 ^ d * (Cl * R ^ (-(d : ℝ) / 2 - ε)) := by gcongr
      _ = _ := by ring
  have b5 : Cf * (B * 2 ^ ((d : ℝ) / 2) * E) ≤
      Cf * B * 2 ^ ((d : ℝ) / 2) * Ce * R ^ (-(d : ℝ) / 2 - ε) := by
    calc Cf * (B * 2 ^ ((d : ℝ) / 2) * E) = Cf * B * 2 ^ ((d : ℝ) / 2) * E := by ring
      _ ≤ Cf * B * 2 ^ ((d : ℝ) / 2) * (Ce * R ^ (-(d : ℝ) / 2 - ε)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  have hCQ : (C₁ + C₂ + 1) * R ^ (-(d : ℝ) / 2 - ε) = (A + Cs * B * 2 ^ ((d : ℝ) / 2) * Ce + Cl +
      2 ^ d * Cl + Cf * B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-(d : ℝ) / 2 - ε) +
      (C₂ + 1) * R ^ (-(d : ℝ) / 2 - ε) := by
    rw [hC₁def]; ring
  have h0 : 0 ≤ (C₂ + 1) * R ^ (-(d : ℝ) / 2 - ε) := mul_nonneg (by linarith) hQ0
  linarith only [b1, b2, b3, b4, b5, hCQ, h0]

end QSH
