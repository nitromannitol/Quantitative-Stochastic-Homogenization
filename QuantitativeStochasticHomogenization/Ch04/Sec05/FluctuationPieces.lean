import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationInduction

/-!
# The pieces of the induction step in the proof of Proposition 4.12

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.5, Steps 1 and 2. For a block `R^{-d} ∫ f X(r, ·, ·)` this file proves:

* Step 1: the additivity (4.116) replaces `X(r)` by the heat average of `X(r₁)`, at the cost
  `𝒪_s(C r₁^{-α})` (`centeredOsBound_block_additivity_defect`), and Fubini's theorem turns the
  heat average into `∫ g X(r₁)` with `g = (f 1_{□_R}) ∗ Φ` (`integral_mul_heat_eq`), where
  `|g| ≤ 1` (`abs_heatSmooth_le_one`);
* the Gaussian tail (4.123): the part of `∫ g X(r₁)` far from the cube is bounded by a Gaussian of
  the distance (`centeredOsBound_far_block`);
* Euclidean neighbourhoods are open and separated sets have separated neighbourhoods.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

/-! ### Neighbourhoods -/

theorem continuous_euclideanNorm : Continuous fun x : Vec d => euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem isOpen_euclideanThickening (ρ : ℝ) (U : Set (Vec d)) :
    IsOpen (euclideanThickening ρ U) := by
  have e : euclideanThickening ρ U = ⋃ x ∈ U, {y : Vec d | euclideanNorm (y - x) < ρ} := by
    ext y
    simp [euclideanThickening]
  rw [e]
  exact isOpen_biUnion fun x _ =>
    isOpen_lt (continuous_euclideanNorm.comp (continuous_id.sub continuous_const))
      continuous_const

theorem measurableSet_euclideanThickening (ρ : ℝ) (U : Set (Vec d)) :
    MeasurableSet (euclideanThickening ρ U) :=
  (isOpen_euclideanThickening ρ U).measurableSet

/-- Neighbourhoods of radius `ρ` of two sets whose points differ by at least `g` in some coordinate,
with `g - 2ρ > 1`, are separated by a unit. -/
theorem separatedByUnit_euclideanThickening {U W : Set (Vec d)} {g ρ : ℝ} (hg : 1 < g - 2 * ρ)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ∃ i, g ≤ |u i - w i|) :
    SeparatedByUnit (euclideanThickening ρ U) (euclideanThickening ρ W) :=
  ⟨g - 2 * ρ, hg, fun _ hx _ hy => le_euclideanNorm_sub_of_near hUW hx hy⟩

/-- Points of the `ρ`-neighbourhood of `closedCube c L` are within `L/2 + ρ` of `c` in every
coordinate. -/
theorem abs_sub_lt_of_mem_euclideanThickening_closedCube {c : Vec d} {L ρ : ℝ} {x : Vec d}
    (hx : x ∈ euclideanThickening ρ (closedCube c L)) (i : Fin d) : |x i - c i| < L / 2 + ρ := by
  obtain ⟨u, hu, hxu⟩ := hx
  have h1 := hu i
  have h2 : |x i - u i| < ρ := by
    have := abs_apply_le_euclideanNorm' (x - u) i
    simp only [Pi.sub_apply] at this
    linarith
  calc |x i - c i| = |(x i - u i) + (u i - c i)| := by ring_nf
    _ ≤ |x i - u i| + |u i - c i| := abs_add_le _ _
    _ < L / 2 + ρ := by linarith

/-! ### Heat averages of blocks -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {s δ α : ℝ}

theorem measurable_heatAverage (G : Ω → Vec d → ℝ)
    (hG : Measurable fun w : Ω × Vec d => G w.1 w.2) (ρ : ℝ) :
    Measurable fun w : Ω × Vec d => ∫ y, heatKernel w.2 ρ y * G w.1 y := by
  have hH : Measurable fun p : (Ω × Vec d) × Vec d => heatKernel p.1.2 ρ p.2 * G p.1.1 p.2 :=
    ((measurable_heatKernel_prod ρ).comp ((measurable_snd.comp measurable_fst).prodMk
      measurable_snd)).mul (hG.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact hH.stronglyMeasurable.integral_prod_right'.measurable

/-- **Step 1 of the proof of Proposition 4.12**: in a block, replacing `X(r)` by the heat average
of `X(r₁)` costs `𝒪_s(C r₁^{-α})`. -/
theorem centeredOsBound_block_additivity_defect [IsProbabilityMeasure P]
    (X : CenteredLocalFields P F s δ α) {r₁ r : ℝ} (hr₁ : 1 ≤ r₁) (hr : r₁ < r) {z : Vec d}
    {R : ℝ} (hR : 0 < R) {f : Vec d → ℝ} (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1)
    (hfz : ∀ x ∉ closedCube z R, f x = 0) :
    CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, f x * (X.field r a x -
      ∫ y, heatKernel x (Real.sqrt (r ^ 2 - r₁ ^ 2)) y * X.field r₁ a y))
      s (X.addConst * r₁ ^ (-α)) := by
  have hDm : Measurable fun w : Ω × Vec d => X.field r w.1 w.2 -
      ∫ y, heatKernel w.2 (Real.sqrt (r ^ 2 - r₁ ^ 2)) y * X.field r₁ w.1 y :=
    (X.measurable r).sub (measurable_heatAverage _ (X.measurable r₁) _)
  have h := centeredOsBound_integral_closedCube hDm (fun x => X.additive r₁ r hr₁ hr x) hf hf1 hR
    hfz
  have h2 := h.const_mul (Real.rpow_pos_of_pos hR (-(d : ℝ)))
  convert h2 using 1
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero,
    one_mul]

/-- The heat average of a weight, `g(y) = ∫ f(x) Φ_{x,ρ}(y) dx`. -/
noncomputable def heatSmooth (f : Vec d → ℝ) (ρ : ℝ) (y : Vec d) : ℝ :=
  ∫ x, f x * heatKernel x ρ y

theorem measurable_heatKernel_prod_swap (ρ : ℝ) :
    Measurable fun p : Vec d × Vec d => heatKernel p.2 ρ p.1 := by
  have : Continuous fun p : Vec d × Vec d => heatKernel p.2 ρ p.1 := by
    unfold heatKernel euclideanHeatKernel euclideanSq dot
    fun_prop
  exact this.measurable

theorem measurable_heatSmooth {f : Vec d → ℝ} (hf : Measurable f) (ρ : ℝ) :
    Measurable (heatSmooth f ρ) := by
  have hH : Measurable fun p : Vec d × Vec d => f p.2 * heatKernel p.2 ρ p.1 :=
    (hf.comp measurable_snd).mul (measurable_heatKernel_prod_swap ρ)
  unfold heatSmooth
  exact hH.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_heatSmooth_le_one {f : Vec d → ℝ} (hf1 : ∀ x, |f x| ≤ 1) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec d) : |heatSmooth f ρ y| ≤ 1 := by
  unfold heatSmooth
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |f x * heatKernel x ρ y| ≤ ∫ x, heatKernel x ρ y := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (integrable_heatKernel_center y hρ) (Filter.Eventually.of_forall fun x => ?_)
        show |f x * heatKernel x ρ y| ≤ heatKernel x ρ y
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg x ρ y)]
        exact mul_le_of_le_one_left (heatKernel_nonneg x ρ y) (hf1 x)
    _ = 1 := integral_heatKernel_center y hρ

theorem integrable_heatWeight {f : Vec d → ℝ} (hf : Integrable f) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun p : Vec d × Vec d => |f p.1| * heatKernel p.1 ρ p.2)
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : Vec d × Vec d => |f p.1| * heatKernel p.1 ρ p.2)
      (volume.prod volume) :=
    (hf.abs.aestronglyMeasurable.comp_fst).mul (measurable_heatKernel_prod ρ).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact (integrable_heatKernel x hρ).const_mul |f x|
  have e : (fun x => ∫ y, ‖|f x| * heatKernel x ρ y‖) = fun x => |f x| := by
    funext x
    simp_rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (heatKernel_nonneg x ρ _)]
    rw [integral_const_mul, integral_heatKernel x hρ, mul_one]
  rw [e]
  exact hf.abs

/-- **Fubini for heat averages**: `∫ f(x) ∫ Φ_{x,ρ}(y) G(y) dy dx = ∫ g(y) G(y) dy`. -/
theorem integral_mul_heat_eq {f : Vec d → ℝ} (hf : Integrable f) {ρ : ℝ} (hρ : 0 < ρ)
    {G : Vec d → ℝ} (hG : Measurable G) {B : ℝ} (hGB : ∀ y, |G y| ≤ B) :
    ∫ x, f x * ∫ y, heatKernel x ρ y * G y = ∫ y, heatSmooth f ρ y * G y := by
  have hint : Integrable (fun p : Vec d × Vec d => f p.1 * (heatKernel p.1 ρ p.2 * G p.2))
      (volume.prod volume) := by
    refine ((integrable_heatWeight hf hρ).const_mul B).mono' ?_ (Filter.Eventually.of_forall
      fun p => ?_)
    · exact (hf.aestronglyMeasurable.comp_fst).mul
        ((measurable_heatKernel_prod ρ).aestronglyMeasurable.mul
          (hG.comp measurable_snd).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg _ ρ _)]
      have := hGB p.2
      have h0 := heatKernel_nonneg p.1 ρ p.2
      have h1 := abs_nonneg (f p.1)
      nlinarith [mul_nonneg h1 h0]
  have e1 : (fun x => f x * ∫ y, heatKernel x ρ y * G y) =
      fun x => ∫ y, f x * (heatKernel x ρ y * G y) := by
    funext x
    rw [integral_const_mul]
  rw [e1, integral_integral_swap hint]
  congr 1
  funext y
  unfold heatSmooth
  rw [← integral_mul_const]
  congr 1
  funext x
  ring

theorem integral_abs_heatSmooth_le {f : Vec d → ℝ} (hf : Integrable f) {ρ : ℝ} (hρ : 0 < ρ)
    (S : Set (Vec d)) :
    ∫ y in S, |heatSmooth f ρ y| ≤ ∫ x, |f x| * ∫ y in S, heatKernel x ρ y := by
  have hint := integrable_heatWeight hf hρ
  have hintS : Integrable (fun p : Vec d × Vec d => |f p.1| * heatKernel p.1 ρ p.2)
      (volume.prod (volume.restrict S)) :=
    hint.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc ∫ y in S, |heatSmooth f ρ y|
      ≤ ∫ y in S, ∫ x, |f x| * heatKernel x ρ y := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
          (hintS.integral_prod_right) (Filter.Eventually.of_forall fun y => ?_)
        unfold heatSmooth
        refine (abs_integral_le_integral_abs).trans_eq ?_
        congr 1
        funext x
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg x ρ y)]
    _ = ∫ x, ∫ y in S, |f x| * heatKernel x ρ y := (integral_integral_swap hintS).symm
    _ = ∫ x, |f x| * ∫ y in S, heatKernel x ρ y := by
        congr 1
        funext x
        rw [integral_const_mul]

/-! ### The far part -/

theorem integrable_heatSmooth {f : Vec d → ℝ} (hf : Integrable f) (hfm : Measurable f) {ρ : ℝ}
    (hρ : 0 < ρ) : Integrable (heatSmooth f ρ) := by
  have hint := integrable_heatWeight hf hρ
  refine hint.integral_prod_right.mono' (measurable_heatSmooth hfm ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  unfold heatSmooth
  refine (abs_integral_le_integral_abs).trans_eq ?_
  congr 1
  funext x
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg x ρ y)]

/-- **The far part of a block** (the Gaussian tail (4.123) in Step 2): if every `y ∈ S` is at
Euclidean distance at least `t` from every `x ∈ closedCube z R`, the centered block
`R^{-d} ∫_S g X(r₁)` is `𝒪_s(C(s) B 2^{d/2} exp(-t²/(8ρ²)))`. -/
theorem exists_centeredOsBound_far_block (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ [IsProbabilityMeasure P] (X : CenteredLocalFields P F s δ α) (r₁ : ℝ)
      {z : Vec d} {R ρ t : ℝ}, 0 < R → 0 < ρ → 0 ≤ t → ∀ {f : Vec d → ℝ}, Measurable f →
      (∀ x, |f x| ≤ 1) → (∀ x ∉ closedCube z R, f x = 0) → ∀ {S : Set (Vec d)}, MeasurableSet S →
      (∀ x ∈ closedCube z R, ∀ y ∈ S, t ≤ euclideanNorm (y - x)) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) *
        ∫ y, S.indicator (heatSmooth f ρ) y * X.field r₁ a y) s
        (C₀ * (X.bound * 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * ρ ^ 2))))) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_abs_le hs1 hs2
  refine ⟨C₀, hC₀, ?_⟩
  intro _ X r₁ z R ρ t hR hρ ht f hf hf1 hfz S hS hfar
  have hfi := integrable_of_abs_le_one_of_closedCube hf hf1 hR.le hfz
  set e : ℝ := 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * ρ ^ 2))) with hedef
  have he : 0 < e := by positivity
  have hgm : Measurable (S.indicator (heatSmooth f ρ)) := (measurable_heatSmooth hf ρ).indicator hS
  have hgi : Integrable (S.indicator (heatSmooth f ρ)) :=
    (integrable_heatSmooth hfi hf hρ).indicator hS
  have hint_g : ∫ y, |S.indicator (heatSmooth f ρ) y| ≤ R ^ d * e := by
    have e1 : (fun y => |S.indicator (heatSmooth f ρ) y|) =
        S.indicator (fun y => |heatSmooth f ρ y|) := by
      funext y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, abs_zero]
    rw [e1, integral_indicator hS]
    refine (integral_abs_heatSmooth_le hfi hρ S).trans ?_
    calc ∫ x, |f x| * ∫ y in S, heatKernel x ρ y ≤ ∫ x, |f x| * e := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            mul_nonneg (abs_nonneg _) (setIntegral_nonneg hS fun y _ => heatKernel_nonneg x ρ y))
            (hfi.abs.mul_const e) (Filter.Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ closedCube z R
          · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact setIntegral_heatKernel_le_of_far x hρ ht hS (fun y hy => hfar x hx y hy)
          · simp [hfz x hx]
      _ = (∫ x, |f x|) * e := integral_mul_const _ _
      _ ≤ R ^ d * e := mul_le_mul_of_nonneg_right
            (integral_abs_le_of_closedCube hf hf1 hR.le hfz) he.le
  have hbound : ∀ a, |R ^ (-(d : ℝ)) * ∫ y, S.indicator (heatSmooth f ρ) y * X.field r₁ a y| ≤
      X.bound * e := by
    intro a
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hR _)]
    calc R ^ (-(d : ℝ)) * |∫ y, S.indicator (heatSmooth f ρ) y * X.field r₁ a y|
        ≤ R ^ (-(d : ℝ)) * (X.bound * (R ^ d * e)) :=
          mul_le_mul_of_nonneg_left ((abs_integral_mul_le (X.abs_le r₁) hgi a).trans
            (mul_le_mul_of_nonneg_left hint_g X.bound_pos.le)) (Real.rpow_nonneg hR.le _)
      _ = X.bound * e := by
          rw [← Real.rpow_natCast, mul_left_comm, ← mul_assoc (R ^ (-(d : ℝ))),
            ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero, one_mul]
  have h := h₀ P _ (X.bound * e) (measurable_block X r₁ hgm _) (mul_pos X.bound_pos he) hbound
    (integral_block_eq_zero X r₁ hgi _)
  simpa only [hedef, mul_assoc] using h

end QSH
