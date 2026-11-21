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
    (β : Fin d → Fin (k + 1)) {C : ℝ} (hC0 : 0 ≤ C) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
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

end QSH
