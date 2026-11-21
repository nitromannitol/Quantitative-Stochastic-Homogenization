import QuantitativeStochasticHomogenization.Ch04.Sec06.GaussianAverageSquares
import QuantitativeStochasticHomogenization.Ch04.Sec06.HeatScaleSummation

/-!
# Section 4.6: the heat averages of a random field at one scale

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6. For a jointly measurable random field `F`:

* the norms `‖Y_{β,s}(F)‖_{L²(B_1)}` are jointly measurable in the positive scale and the sample
  (`measurable_eLpNorm_heatDerivativeAverage`), by the product formula of `∂^β Φ(t)`;
* at small scales, Young's inequality bounds them by the Gaussian `L²` norm of `F`
  (`ae_eLpNorm_heatDerivativeAverage_le_small`);
* at every scale, splitting `s = s/2 + s/2` bounds them by the Gaussian `L²` norm of the Gaussian
  averages `A_{s/2}(F)` (`ae_eLpNorm_heatDerivativeAverage_le_large`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The positive scale `s` for `s > 0`, and `1` otherwise. -/
def posScale (s : ℝ) : ℝ := if s ≤ 0 then 1 else s

theorem posScale_pos (s : ℝ) : 0 < posScale s := by
  unfold posScale
  split_ifs with h
  · exact one_pos
  · exact not_le.mp h

theorem measurable_posScale : Measurable posScale :=
  Measurable.ite measurableSet_Iic measurable_const measurable_id

theorem posScale_of_pos {s : ℝ} (hs : 0 < s) : posScale s = s := by
  simp [posScale, not_le.mpr hs]

theorem multiIndexDerivative_euclideanHeatKernel_eq_prod {t : ℝ} (ht : 0 < t) {k : ℕ}
    (β : Fin d → Fin (k + 1)) (v : Vec d) :
    multiIndexDerivative β (euclideanHeatKernel (d := d) t) v = ∏ i, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) *
      ((Real.sqrt (2 * t))⁻¹ ^ (β i).val *
        iteratedDeriv (β i).val stdGaussian1 ((Real.sqrt (2 * t))⁻¹ * v i)) := by
  rw [euclideanHeatKernel_eq_prodFun ht, multiIndexDerivative_prodFun
    (fun _ => contDiff_heatKernel1 t), prodFun]
  exact Finset.prod_congr rfl fun i _ => iteratedDeriv_heatKernel1 ht _ _

theorem measurable_multiIndexDerivative_euclideanHeatKernel {k : ℕ} (β : Fin d → Fin (k + 1)) :
    Measurable (fun p : ℝ × Vec d =>
      multiIndexDerivative β (euclideanHeatKernel (d := d) (posScale p.1)) p.2) := by
  have h : (fun p : ℝ × Vec d =>
      multiIndexDerivative β (euclideanHeatKernel (d := d) (posScale p.1)) p.2) = fun p =>
      ∏ i, (4 * Real.pi * posScale p.1) ^ (-(1 : ℝ) / 2) *
        ((Real.sqrt (2 * posScale p.1))⁻¹ ^ (β i).val *
          iteratedDeriv (β i).val stdGaussian1 ((Real.sqrt (2 * posScale p.1))⁻¹ * p.2 i)) := by
    funext p
    exact multiIndexDerivative_euclideanHeatKernel_eq_prod (posScale_pos p.1) β p.2
  rw [h]
  have hG : ∀ j : ℕ, Measurable (iteratedDeriv j stdGaussian1) := fun j =>
    (contDiff_stdGaussian1.continuous_iteratedDeriv j (by simp)).measurable
  have hσ : Measurable (fun p : ℝ × Vec d => posScale p.1) := measurable_posScale.comp measurable_fst
  refine Finset.measurable_prod _ fun i _ => ?_
  refine ((measurable_const.mul hσ).pow_const _).mul ?_
  refine (((measurable_const.mul hσ).sqrt.inv).pow_const _).mul ?_
  exact (hG _).comp (((measurable_const.mul hσ).sqrt.inv).mul
    ((measurable_pi_apply i).comp measurable_snd))

/-- **Joint measurability of the norms of the heat averages** in the positive scale and the
sample. -/
theorem measurable_eLpNorm_heatDerivativeAverage {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → Vec d → ℝ} (hFm : Measurable (Function.uncurry F)) {k : ℕ}
    (β : Fin d → Fin (k + 1)) :
    Measurable (fun p : ℝ × Ω =>
      eLpNorm (heatDerivativeAverage β (if p.1 ≤ 0 then 1 else p.1) (F p.2)) 2
        (volume.restrict (originBall d 1))) := by
  have hK := measurable_multiIndexDerivative_euclideanHeatKernel (d := d) β
  have hY : StronglyMeasurable (fun q : (ℝ × Ω) × Vec d =>
      heatDerivativeAverage β (posScale q.1.1) (F q.1.2) q.2) := by
    unfold heatDerivativeAverage
    refine StronglyMeasurable.integral_prod_right
      (f := fun (q : (ℝ × Ω) × Vec d) (x : Vec d) =>
        F q.1.2 x * multiIndexDerivative β (euclideanHeatKernel (d := d) (posScale q.1.1))
          (x - q.2)) ?_
    refine Measurable.stronglyMeasurable ?_
    refine (hFm.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd)).mul ?_
    exact hK.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.sub (measurable_snd.comp measurable_fst)))
  have hfun : (fun p : ℝ × Ω =>
      eLpNorm (heatDerivativeAverage β (if p.1 ≤ 0 then 1 else p.1) (F p.2)) 2
        (volume.restrict (originBall d 1))) = fun p =>
      (∫⁻ y in originBall d 1, ‖heatDerivativeAverage β (posScale p.1) (F p.2) y‖ₑ ^ (2 : ℝ)) ^
        (1 / (2 : ℝ)) := by
    funext p
    have hm : AEStronglyMeasurable (heatDerivativeAverage β (posScale p.1) (F p.2))
        (volume.restrict (originBall d 1)) :=
      (hY.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable.restrict
    rw [show (if p.1 ≤ 0 then (1 : ℝ) else p.1) = posScale p.1 from rfl,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
    norm_num
  rw [hfun]
  refine Measurable.pow_const ?_ _
  exact (hY.measurable.enorm.pow_const _).lintegral_prod_right'

theorem measurable_heatAverage_uncurry {Ω : Type*} [MeasurableSpace Ω] {F : Ω → Vec d → ℝ}
    (hFm : Measurable (Function.uncurry F)) :
    Measurable (fun q : (ℝ × Ω) × Vec d => heatAverage (q.1.1 / 2) (F q.1.2) q.2) := by
  have h : StronglyMeasurable (fun q : (ℝ × Ω) × Vec d =>
      ∫ x, F q.1.2 x * euclideanHeatKernel (q.1.1 / 2) (x - q.2)) := by
    refine StronglyMeasurable.integral_prod_right
      (f := fun (q : (ℝ × Ω) × Vec d) (x : Vec d) =>
        F q.1.2 x * euclideanHeatKernel (q.1.1 / 2) (x - q.2)) ?_
    refine Measurable.stronglyMeasurable ?_
    refine (hFm.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd)).mul ?_
    exact measurable_euclideanHeatKernel_uncurry.comp
      (((measurable_fst.comp (measurable_fst.comp measurable_fst)).div_const 2).prodMk
        (measurable_snd.sub (measurable_snd.comp measurable_fst)))
  exact h.measurable

/-- **Small scales**: Young's inequality against the Gaussian `L²` norm of the field. -/
theorem ae_eLpNorm_heatDerivativeAverage_le_small {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Ω → Vec d → ℝ} (hFm : Measurable (Function.uncurry F)) {k : ℕ}
    (β : Fin d → Fin (k + 1)) {C : ℝ} (hC0 : 0 ≤ C) {s : ℝ}
    (hC : ∀ G : Vec d → ℝ, AEStronglyMeasurable G volume →
      eLpNorm (heatDerivativeAverage β s G) 2 (volume.restrict (originBall d 1)) ≤
        ENNReal.ofReal (C * (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (β i).val)) *
          (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^
            (1 / 2 : ℝ))
    {R : Ω → ℝ} (hR : ∀ᵐ a ∂P, (∫⁻ x, ‖F a x‖ₑ ^ (2 : ℝ) *
      ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)) :
    ∀ᵐ a ∂P, eLpNorm (heatDerivativeAverage β s (F a)) 2 (volume.restrict (originBall d 1)) ≤
      ENNReal.ofReal (C * (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (β i).val) * max (R a) 0) := by
  filter_upwards [hR] with a ha
  have hFa : AEStronglyMeasurable (F a) volume :=
    (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine (hC _ hFa).trans ?_
  have hq : 0 ≤ C * (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (β i).val) := by positivity
  rw [ENNReal.ofReal_mul hq]
  gcongr
  exact ha.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- **All scales**: splitting the heat time, Young's inequality against the Gaussian `L²` norm of
the Gaussian averages `A_{s/2}(F)`. -/
theorem ae_eLpNorm_heatDerivativeAverage_le_large {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Ω → Vec d → ℝ} (hFm : Measurable (Function.uncurry F)) {k : ℕ}
    (β : Fin d → Fin (k + 1)) {C : ℝ} (hC0 : 0 ≤ C) {s : ℝ} (hs : 0 < s)
    (hC : ∀ G : Vec d → ℝ, AEStronglyMeasurable G volume →
      eLpNorm (heatDerivativeAverage β (s / 2) G) 2 (volume.restrict (originBall d 1)) ≤
        ENNReal.ofReal (C * (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (β i).val)) *
          (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^
            (1 / 2 : ℝ))
    (hFg : ∀ᵐ a ∂P, ∀ y, Integrable (fun x => F a x *
      euclideanHeatKernel (s / 2 + 2 * (s / 2)) (x - y)))
    (hint : ∀ᵐ a ∂P, Integrable (fun u => gaussWeight u * |heatAverage (s / 2) (F a) u| ^ (2 : ℝ))) :
    ∀ᵐ a ∂P, eLpNorm (heatDerivativeAverage β s (F a)) 2 (volume.restrict (originBall d 1)) ≤
      ENNReal.ofReal (C * (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (β i).val) *
        (∫ u, gaussWeight u * |heatAverage (s / 2) (F a) u| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
  filter_upwards [hFg, hint] with a ha hai
  have hFa : AEStronglyMeasurable (F a) volume :=
    (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have heq : heatDerivativeAverage β s (F a) =
      heatDerivativeAverage β (s / 2) (heatAverage (s / 2) (F a)) := funext fun y => by
    have h := heatDerivativeAverage_add (half_pos hs) (half_pos hs) β hFa y (ha y)
    rwa [add_halves] at h
  have hAm : AEStronglyMeasurable (heatAverage (s / 2) (F a)) volume := by
    have h := (measurable_heatAverage_uncurry hFm).comp
      ((measurable_const : Measurable fun _ : Vec d => ((s, a) : ℝ × Ω)).prodMk measurable_id)
    exact h.aestronglyMeasurable
  rw [heq]
  refine (hC _ hAm).trans ?_
  have hq : 0 ≤ C * (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (β i).val) := by positivity
  have hV0 : 0 ≤ ∫ u, gaussWeight u * |heatAverage (s / 2) (F a) u| ^ (2 : ℝ) :=
    integral_nonneg fun u => mul_nonneg (gaussWeight_pos u).le (Real.rpow_nonneg (abs_nonneg _) _)
  rw [ENNReal.ofReal_mul hq, ← ENNReal.ofReal_rpow_of_nonneg hV0 (by norm_num),
    ofReal_integral_eq_lintegral_ofReal hai (Eventually.of_forall fun u =>
      mul_nonneg (gaussWeight_pos u).le (Real.rpow_nonneg (abs_nonneg _) _))]
  refine le_of_eq ?_
  congr 2
  refine lintegral_congr fun u => ?_
  rw [ENNReal.ofReal_mul (gaussWeight_pos u).le, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
    (by norm_num), ← Real.enorm_eq_ofReal_abs, mul_comm]
  rfl

/-! ## The per-scale estimate -/

/-- The constant of Young's inequality `eLpNorm_heatDerivativeAverage_le`. -/
def youngConstant {k : ℕ} (β : Fin d → Fin (k + 1)) : ℝ :=
  (eLpNorm_heatDerivativeAverage_le β).choose

theorem youngConstant_nonneg {k : ℕ} (β : Fin d → Fin (k + 1)) : 0 ≤ youngConstant β :=
  (eLpNorm_heatDerivativeAverage_le β).choose_spec.1

theorem youngConstant_spec {k : ℕ} (β : Fin d → Fin (k + 1)) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (G : Vec d → ℝ) (hG : AEStronglyMeasurable G volume) :
    eLpNorm (heatDerivativeAverage β s G) 2 (volume.restrict (originBall d 1)) ≤
      ENNReal.ofReal (youngConstant β * (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (β i).val)) *
        (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^
          (1 / 2 : ℝ) :=
  (eLpNorm_heatDerivativeAverage_le β).choose_spec.2 s hs hs1 G hG

/-- The sum of the constants `youngConstant β_w + 1` over the words of length at most `n + 1`. -/
def heatScaleCoefficient (d n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 2), ∑ w : Fin k → Fin d, (youngConstant (countIndex w) + 1)

theorem youngConstant_add_one_le {n k : ℕ} (hk : k ≤ n + 1) (w : Fin k → Fin d) :
    youngConstant (countIndex w) + 1 ≤ heatScaleCoefficient d n := by
  unfold heatScaleCoefficient
  have h0 : ∀ k' (w' : Fin k' → Fin d), 0 ≤ youngConstant (countIndex w') + 1 := fun k' w' => by
    have := youngConstant_nonneg (countIndex w'); linarith
  calc youngConstant (countIndex w) + 1 ≤ ∑ w' : Fin k → Fin d, (youngConstant (countIndex w') + 1) :=
        Finset.single_le_sum (f := fun w' : Fin k → Fin d => youngConstant (countIndex w') + 1)
          (fun w' _ => h0 k w') (Finset.mem_univ w)
    _ ≤ _ := Finset.single_le_sum (f := fun k' => ∑ w' : Fin k' → Fin d,
          (youngConstant (countIndex w') + 1)) (fun k' _ => Finset.sum_nonneg fun w' _ => h0 k' w')
          (Finset.mem_range.mpr (by omega))

theorem inv_sqrt_pow_eq {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (Real.sqrt s)⁻¹ ^ k = s ^ (-(k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  congr 1
  ring

theorem inv_sqrt_two_mul_pow_le {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (Real.sqrt (2 * s))⁻¹ ^ k ≤ s ^ (-(k : ℝ) / 2) := by
  rw [← inv_sqrt_pow_eq hs]
  have h1 : Real.sqrt s ≤ Real.sqrt (2 * s) := Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ h2 h1) k

/-- **The per-scale estimate from the Gaussian energy and the Gaussian averages**: if the Gaussian
`L²` norm of `F` is `O_1(C₁)` and the Gaussian averages `A_t(F)(u)` are `O_1(C₂ ε^{d/2} t^{-d/4})` at
every center for `ε² ≤ t ≤ 1/2`, then `F` satisfies the per-scale estimate. -/
theorem heatScaleEstimate_of_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : 1 ≤ d) (n : ℕ) {F : Ω → Vec d → ℝ}
    (hFm : Measurable (Function.uncurry F)) {ε C₁ C₂ : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂)
    (hFg : ∀ᵐ a ∂P, ∀ τ : ℝ, 0 < τ → ∀ y,
      Integrable (fun x => F a x * euclideanHeatKernel τ (x - y)))
    {R : Ω → ℝ} (hRo : OsBound P R 1 C₁)
    (hR : ∀ᵐ a ∂P, (∫⁻ x, ‖F a x‖ₑ ^ (2 : ℝ) *
      ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a))
    (hA : ∀ t : ℝ, ε ^ 2 ≤ t → t ≤ 1 / 2 → ∀ u,
      OsBound P (fun a => |heatAverage t (F a) u|) 1 (C₂ * ε ^ ((d : ℝ) / 2) * t ^ (-(d : ℝ) / 4))) :
    HeatScaleEstimate P n F
      (heatScaleCoefficient d n * ((C₁ + gaussSquareConstant d * C₂) * 2 ^ ((d : ℝ) / 4))) ε := by
  set H := heatScaleCoefficient d n with hH
  set K := gaussSquareConstant d with hKdef
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK0 : 0 ≤ K := Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (integral_nonneg fun u => (gaussWeight_pos u).le)) _
  have hRm : Measurable R := hRo.1
  set V : ℝ → Ω → ℝ := fun s a => ∫ u, gaussWeight u * |heatAverage (s / 2) (F a) u| ^ (2 : ℝ)
    with hVdef
  have hVm : Measurable (Function.uncurry V) := by
    have h : StronglyMeasurable (fun p : ℝ × Ω =>
        ∫ u, gaussWeight u * |heatAverage (p.1 / 2) (F p.2) u| ^ (2 : ℝ)) := by
      refine StronglyMeasurable.integral_prod_right
        (f := fun (p : ℝ × Ω) (u : Vec d) =>
          gaussWeight u * |heatAverage (p.1 / 2) (F p.2) u| ^ (2 : ℝ)) ?_
      refine Measurable.stronglyMeasurable ?_
      exact (measurable_gaussWeight.comp measurable_snd).mul
        ((measurable_heatAverage_uncurry hFm).abs.pow_const _)
    exact h.measurable
  set Q : ∀ k : ℕ, (Fin k → Fin d) → ℝ → Ω → ℝ := fun k w s a =>
    if s ≤ 2 * ε ^ 2 then (youngConstant (countIndex w) + 1) *
      (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (countIndex w i).val) * max (R a) 0
    else (youngConstant (countIndex w) + 1) *
      (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (countIndex w i).val) * V s a ^ (1 / 2 : ℝ) with hQdef
  have hV0 : ∀ s a, 0 ≤ V s a := fun s a => integral_nonneg fun u =>
    mul_nonneg (gaussWeight_pos u).le (Real.rpow_nonneg (abs_nonneg _) _)
  have hC' : ∀ k (w : Fin k → Fin d), 0 < youngConstant (countIndex w) + 1 := fun k w => by
    have := youngConstant_nonneg (countIndex w); linarith
  refine ⟨Q, fun k w => ?_, fun k w s a => ?_, fun k w =>
    measurable_eLpNorm_heatDerivativeAverage hFm (countIndex w), fun k w hk s hs => ?_,
    fun k w hk s hs => ?_⟩
  · refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ ?_
    · exact (measurable_const.mul ((measurable_const.mul measurable_fst).sqrt.inv.pow_const _)).mul
        ((hRm.comp measurable_snd).max measurable_const)
    · exact (measurable_const.mul (((measurable_const.mul (measurable_fst.div_const 2)).sqrt.inv).pow_const
        _)).mul (hVm.pow_const _)
  · simp only [hQdef]
    have := hC' k w
    split_ifs
    · exact mul_nonneg (mul_nonneg this.le (by positivity)) (le_max_right _ _)
    · exact mul_nonneg (mul_nonneg this.le (by positivity)) (Real.rpow_nonneg (hV0 s a) _)
  · have hk' : (∑ i, (countIndex w i).val) = k := sum_countIndex w
    have hs0 : 0 < s := hs.1
    have hεd : 0 < ε ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hε _
    have hCH : youngConstant (countIndex w) + 1 ≤ H := youngConstant_add_one_le hk w
    have hH0 : 0 < H := (hC' k w).trans_le hCH
    have hspow : 0 < s ^ (-(k : ℝ) / 2) := Real.rpow_pos_of_pos hs0 _
    have hsd : 0 < s ^ (-(d : ℝ) / 4) := Real.rpow_pos_of_pos hs0 _
    have h2d : 0 < (2 : ℝ) ^ ((d : ℝ) / 4) := by positivity
    have hsplit : s ^ (-(k : ℝ) / 2 - (d : ℝ) / 4) = s ^ (-(k : ℝ) / 2) * s ^ (-(d : ℝ) / 4) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    have hKC : 0 ≤ K * C₂ * 2 ^ ((d : ℝ) / 4) := by positivity
    by_cases hsε : s ≤ 2 * ε ^ 2
    · have hQs : Q k w s = fun a => ((youngConstant (countIndex w) + 1) *
          (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (countIndex w i).val)) * max (R a) 0 := by
        funext a
        simp only [hQdef, hsε, ↓reduceIte]
      rw [hQs]
      have hq : 0 < (youngConstant (countIndex w) + 1) *
          (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (countIndex w i).val) :=
        mul_pos (hC' k w) (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _)
      refine (hRo.max_zero.const_mul hq).mono_scale ?_
      rw [hk']
      have h1 : (Real.sqrt (2 * s))⁻¹ ^ k ≤ s ^ (-(k : ℝ) / 2) := inv_sqrt_two_mul_pow_le hs0 k
      have h2 : 1 ≤ 2 ^ ((d : ℝ) / 4) * (s ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2)) := by
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have h4 : (2 * ε ^ 2) ^ (-(d : ℝ) / 4) ≤ s ^ (-(d : ℝ) / 4) :=
          Real.rpow_le_rpow_of_nonpos hs0 hsε (by linarith)
        have h3 : 2 ^ ((d : ℝ) / 4) * ((2 * ε ^ 2) ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2)) = 1 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast ε 2,
            ← Real.rpow_mul hε.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num),
            mul_assoc, ← Real.rpow_add hε,
            show (d : ℝ) / 4 + -(d : ℝ) / 4 = 0 by ring,
            show ((2 : ℕ) : ℝ) * (-(d : ℝ) / 4) + (d : ℝ) / 2 = 0 by push_cast; ring,
            Real.rpow_zero, Real.rpow_zero, one_mul]
        calc (1 : ℝ) = 2 ^ ((d : ℝ) / 4) * ((2 * ε ^ 2) ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2)) :=
              h3.symm
          _ ≤ 2 ^ ((d : ℝ) / 4) * (s ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2)) := by gcongr
      have hq0 : 0 ≤ (Real.sqrt (2 * s))⁻¹ ^ k := by positivity
      calc (youngConstant (countIndex w) + 1) * (Real.sqrt (2 * s))⁻¹ ^ k * C₁
          ≤ H * s ^ (-(k : ℝ) / 2) * C₁ := by gcongr
        _ ≤ H * s ^ (-(k : ℝ) / 2) * C₁ *
            (2 ^ ((d : ℝ) / 4) * (s ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2))) :=
          le_mul_of_one_le_right (by positivity) h2
        _ ≤ H * s ^ (-(k : ℝ) / 2) * (C₁ + K * C₂) *
            (2 ^ ((d : ℝ) / 4) * (s ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2))) := by
            gcongr
            have : 0 ≤ K * C₂ := by positivity
            linarith
        _ = _ := by rw [hsplit]; ring
    · have hsε' : 2 * ε ^ 2 < s := lt_of_not_ge hsε
      have hQl : Q k w s = fun a => ((youngConstant (countIndex w) + 1) *
          (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (countIndex w i).val)) * V s a ^ (1 / 2 : ℝ) := by
        funext a
        simp only [hQdef, hsε, ↓reduceIte]
      rw [hQl]
      have h2s : 2 * (s / 2) = s := by ring
      have hq : 0 < (youngConstant (countIndex w) + 1) *
          (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (countIndex w i).val) :=
        mul_pos (hC' k w) (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _)
      have hθA : 0 < C₂ * ε ^ ((d : ℝ) / 2) * (s / 2) ^ (-(d : ℝ) / 4) :=
        mul_pos (mul_pos hC₂ hεd) (Real.rpow_pos_of_pos (half_pos hs0) _)
      have hX : Measurable (Function.uncurry fun (u : Vec d) (a : Ω) =>
          heatAverage (s / 2) (F a) u) :=
        (measurable_heatAverage_uncurry hFm).comp
          ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
      obtain ⟨-, hVo⟩ := osBound_rpow_integral_sq hd hX hθA
        (hA (s / 2) (by linarith) (by linarith [hs.2]))
      refine (hVo.const_mul hq).mono_scale ?_
      rw [hk', h2s, inv_sqrt_pow_eq hs0 k]
      have hs2d : (s / 2) ^ (-(d : ℝ) / 4) = s ^ (-(d : ℝ) / 4) * 2 ^ ((d : ℝ) / 4) := by
        rw [Real.div_rpow hs0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
        congr 2
        ring
      rw [hs2d]
      calc (youngConstant (countIndex w) + 1) * s ^ (-(k : ℝ) / 2) *
            (K * (C₂ * ε ^ ((d : ℝ) / 2) * (s ^ (-(d : ℝ) / 4) * 2 ^ ((d : ℝ) / 4))))
          ≤ H * s ^ (-(k : ℝ) / 2) *
            (K * (C₂ * ε ^ ((d : ℝ) / 2) * (s ^ (-(d : ℝ) / 4) * 2 ^ ((d : ℝ) / 4)))) := by
            gcongr
        _ = H * s ^ (-(k : ℝ) / 2) * (K * C₂) *
            (2 ^ ((d : ℝ) / 4) * (s ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2))) := by ring
        _ ≤ H * s ^ (-(k : ℝ) / 2) * (C₁ + K * C₂) *
            (2 ^ ((d : ℝ) / 4) * (s ^ (-(d : ℝ) / 4) * ε ^ ((d : ℝ) / 2))) := by
            gcongr
            linarith
        _ = _ := by rw [hsplit]; ring
  · have hs0 : 0 < s := hs.1
    have hle : youngConstant (countIndex w) ≤ youngConstant (countIndex w) + 1 := by linarith
    by_cases hsε : s ≤ 2 * ε ^ 2
    · have h := ae_eLpNorm_heatDerivativeAverage_le_small (P := P) hFm (countIndex w)
        (youngConstant_nonneg _) (fun G hG => youngConstant_spec _ hs0 hs.2 G hG) hR
      filter_upwards [h] with a ha
      refine ha.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [hQdef, hsε, ↓reduceIte]
      have hq0 : 0 ≤ (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (countIndex w i).val) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hq0) (le_max_right _ _)
    · have hsε' : 2 * ε ^ 2 < s := lt_of_not_ge hsε
      have hs2 : s / 2 ≤ 1 := by linarith [hs.2]
      have hθA : 0 < C₂ * ε ^ ((d : ℝ) / 2) * (s / 2) ^ (-(d : ℝ) / 4) :=
        mul_pos (mul_pos hC₂ (Real.rpow_pos_of_pos hε _)) (Real.rpow_pos_of_pos (half_pos hs0) _)
      have hX : Measurable (Function.uncurry fun (u : Vec d) (a : Ω) =>
          heatAverage (s / 2) (F a) u) :=
        (measurable_heatAverage_uncurry hFm).comp
          ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
      obtain ⟨hint, -⟩ := osBound_rpow_integral_sq hd hX hθA
        (hA (s / 2) (by linarith) (by linarith [hs.2]))
      have hFg' : ∀ᵐ a ∂P, ∀ y, Integrable (fun x => F a x *
          euclideanHeatKernel (s / 2 + 2 * (s / 2)) (x - y)) := by
        filter_upwards [hFg] with a ha y
        exact ha _ (by positivity) y
      have h := ae_eLpNorm_heatDerivativeAverage_le_large hFm (countIndex w)
        (youngConstant_nonneg _) hs0 (fun G hG => youngConstant_spec _ (half_pos hs0) hs2 G hG)
        hFg' hint
      filter_upwards [h] with a ha
      refine ha.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [hQdef, hsε, ↓reduceIte]
      have hq0 : 0 ≤ (Real.sqrt (2 * (s / 2)))⁻¹ ^ (∑ i, (countIndex w i).val) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hq0)
        (Real.rpow_nonneg (hV0 s a) _)

end QSH
