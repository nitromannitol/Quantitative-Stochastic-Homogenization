import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Convolution with an integrable kernel on `L²`

Moved from einstein-relation-lean c97689e `EinsteinFull/Homogenization/KernelConvolutionL2.lean`.

Young's inequality in the form used for heat-kernel smoothing: convolution with a kernel `k`
maps `L²(ℝ^d)` to itself with norm at most `∫ |k|`. The proof is the weighted Cauchy–Schwarz
inequality followed by Tonelli's theorem and the translation invariance of Lebesgue measure.
For the heat kernel `Φ_t` this gives the contraction `‖Φ_t * f‖₂ ≤ ‖f‖₂`, and for its Hessian the
bound `‖∂ᵢ∂ⱼΦ_t * f‖₂ ≤ 2^(d/2) (2/t) ‖f‖₂`.
-/

open MeasureTheory

open scoped ENNReal

namespace QSH

theorem rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sq_rpow_half (X : ℝ≥0∞) : (X ^ 2) ^ (1 / 2 : ℝ) = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Weighted Cauchy–Schwarz inequality for lower Lebesgue integrals. -/
theorem sq_lintegral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w F : α → ℝ≥0∞}
    (hw : AEMeasurable w μ) (hF : AEMeasurable F μ) :
    (∫⁻ a, w a * F a ∂μ) ^ 2 ≤ (∫⁻ a, w a ∂μ) * ∫⁻ a, w a * F a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_norm_pow_le hw (hw.mul (hF.pow_const 2))
    (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hpt : ∀ a, w a ^ (1 / 2 : ℝ) * (w a * F a ^ 2) ^ (1 / 2 : ℝ) = w a * F a := by
    intro a
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half, ← mul_assoc, ← pow_two,
      rpow_half_sq]
  have h' : ∫⁻ a, w a * F a ∂μ ≤
      (∫⁻ a, w a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, w a * F a ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
    calc ∫⁻ a, w a * F a ∂μ
        = ∫⁻ a, w a ^ (1 / 2 : ℝ) * (w a * F a ^ 2) ^ (1 / 2 : ℝ) ∂μ :=
          lintegral_congr fun a => (hpt a).symm
      _ ≤ _ := h
  calc (∫⁻ a, w a * F a ∂μ) ^ 2
      ≤ ((∫⁻ a, w a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, w a * F a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, w a ∂μ) * ∫⁻ a, w a * F a ^ 2 ∂μ := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]

variable {d : ℕ}

/-- **Young's inequality**, `L¹ * L² ⊆ L²`, for lower integrals. -/
theorem lintegral_sq_kernel_le {k f : Vec d → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f) :
    ∫⁻ x, (∫⁻ y, k (x - y) * f y) ^ 2 ≤ (∫⁻ z, k z) ^ 2 * ∫⁻ y, f y ^ 2 := by
  have hkx : ∀ x : Vec d, Measurable fun y => k (x - y) := fun x =>
    hk.comp (measurable_const.sub measurable_id)
  have hmass : ∀ x : Vec d, ∫⁻ y, k (x - y) = ∫⁻ z, k z := fun x =>
    lintegral_sub_left_eq_self k x
  have hpt : ∀ x, (∫⁻ y, k (x - y) * f y) ^ 2 ≤
      (∫⁻ z, k z) * ∫⁻ y, k (x - y) * f y ^ 2 := by
    intro x
    have h := sq_lintegral_mul_le (μ := volume) (hkx x).aemeasurable hf.aemeasurable
    rwa [hmass x] at h
  have hjoint : Measurable (Function.uncurry fun x y : Vec d => k (x - y) * f y ^ 2) :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hf.comp measurable_snd).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, k (x - y) * f y) ^ 2
      ≤ ∫⁻ x, (∫⁻ z, k z) * ∫⁻ y, k (x - y) * f y ^ 2 := lintegral_mono hpt
    _ = (∫⁻ z, k z) * ∫⁻ x, ∫⁻ y, k (x - y) * f y ^ 2 :=
        lintegral_const_mul _ hjoint.lintegral_prod_right'
    _ = (∫⁻ z, k z) * ∫⁻ y, ∫⁻ x, k (x - y) * f y ^ 2 := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = (∫⁻ z, k z) * ∫⁻ y, (∫⁻ z, k z) * f y ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const _
            (show Measurable fun x : Vec d => k (x - y) from hk.comp (measurable_id.sub_const y)),
          lintegral_sub_right_eq_self k y]
    _ = (∫⁻ z, k z) ^ 2 * ∫⁻ y, f y ^ 2 := by
        rw [lintegral_const_mul _ (hf.pow_const 2)]
        ring

theorem eLpNorm_two_eq {f : Vec d → ℝ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume = (∫⁻ x, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- Convolution with a measurable kernel of a measurable function is strongly measurable. -/
theorem stronglyMeasurable_kernel {k f : Vec d → ℝ} (hk : Measurable k) (hf : Measurable f) :
    StronglyMeasurable (fun x => ∫ y, k (x - y) * f y) :=
  ((hk.comp (measurable_fst.sub measurable_snd)).mul
    (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'

/-- **Young's inequality**, `‖k * f‖₂ ≤ ‖k‖₁ ‖f‖₂`. -/
theorem eLpNorm_kernel_le {k f : Vec d → ℝ} (hk : Measurable k) (hf : Measurable f) :
    eLpNorm (fun x => ∫ y, k (x - y) * f y) 2 volume ≤
      (∫⁻ z, ‖k z‖ₑ) * eLpNorm f 2 volume := by
  rw [eLpNorm_two_eq (stronglyMeasurable_kernel hk hf).aestronglyMeasurable,
    eLpNorm_two_eq hf.aestronglyMeasurable]
  have hpt : ∀ x, ‖∫ y, k (x - y) * f y‖ₑ ^ 2 ≤ (∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 := by
    intro x
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
    simp_rw [enorm_mul]
  have hY := lintegral_sq_kernel_le (k := fun z => ‖k z‖ₑ) (f := fun y => ‖f y‖ₑ)
    hk.enorm hf.enorm
  calc (∫⁻ x, ‖∫ y, k (x - y) * f y‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((∫⁻ z, ‖k z‖ₑ) ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr
        exact (lintegral_mono hpt).trans hY
    _ = (∫⁻ z, ‖k z‖ₑ) * (∫⁻ y, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]

/-- Convolution with an integrable kernel maps `L²` to `L²`. -/
theorem memLp_kernel {k f : Vec d → ℝ} (hk : Measurable k) (hk1 : ∫⁻ z, ‖k z‖ₑ ≠ ⊤)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) :
    MemLp (fun x => ∫ y, k (x - y) * f y) 2 volume :=
  lt_of_le_of_lt (eLpNorm_kernel_le hk hf) (ENNReal.mul_lt_top hk1.lt_top hf2)

theorem measurable_euclideanHeatKernel (t : ℝ) :
    Measurable (euclideanHeatKernel (d := d) t) :=
  (continuous_euclideanHeatKernel t).measurable

theorem lintegral_enorm_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    ∫⁻ z : Vec d, ‖euclideanHeatKernel t z‖ₑ = 1 := by
  have h := (ofReal_integral_norm_eq_lintegral_enorm
    (integrable_euclideanHeatKernel (d := d) ht)).symm
  rw [h]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (euclideanHeatKernel_nonneg ht.le _)]
  rw [integral_euclideanHeatKernel ht, ENNReal.ofReal_one]

/-- The heat semigroup is a contraction of `L²`. -/
theorem eLpNorm_heatConv_le {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => ∫ y, euclideanHeatKernel t (x - y) * f y) 2 volume ≤
      eLpNorm f 2 volume := by
  have h := eLpNorm_kernel_le (measurable_euclideanHeatKernel (d := d) t) hf
  rwa [lintegral_enorm_euclideanHeatKernel ht, one_mul] at h

/-- The mixed Hessian of the heat kernel, as an explicit measurable function. -/
theorem heatHessian_eq {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel (d := d) t)) =
      fun z => euclideanHeatKernel t z * (z i * z j / (4 * t ^ 2) -
        (if i = j then 1 / (2 * t) else 0)) :=
  funext fun z => coordinateDerivative_two_euclideanHeatKernel t ht i j z

theorem measurable_heatHessian {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    Measurable
      (coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel (d := d) t))) := by
  rw [heatHessian_eq ht]
  exact (measurable_euclideanHeatKernel t).mul (by fun_prop)

end QSH
