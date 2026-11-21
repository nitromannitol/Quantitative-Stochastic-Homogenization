import QuantitativeStochasticHomogenization.Ch04.Sec06.HeatNegativeNorm
import QuantitativeStochasticHomogenization.AppD.HeatKernelMajorant

/-!
# Section 4.6: `L²(B_1)` bounds of the heat averages `Y_{β,s}`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6. Young's inequality with a Gaussian weight:
`‖Y_{β,s}(F)‖_{L²(B_1)} ≤ C_β (2s)^{-|β|/2} (∫ |F|² exp(-‖x‖²/32))^{1/2}` for `0 < s ≤ 1`
(`eLpNorm_heatDerivativeAverage_le`), from the Gaussian majorant of `∂^β Φ(s)`, the
Cauchy–Schwarz inequality against the probability density `Φ(2s)(· - y)`
(`lintegral_mul_rpow_two_le`) and the uniform Gaussian bound of `∫_{B_1} Φ(2s)(x - y) dy`
(`lintegral_euclideanHeatKernel_originBall_le`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Cauchy–Schwarz against a weight**: `(∫ g ρ)² ≤ (∫ g² ρ)(∫ ρ)`. -/
theorem lintegral_mul_rpow_two_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g ρ : α → ℝ≥0∞} (hg : AEMeasurable g μ) (hρ : AEMeasurable ρ μ) :
    (∫⁻ x, g x * ρ x ∂μ) ^ (2 : ℝ) ≤ (∫⁻ x, g x ^ (2 : ℝ) * ρ x ∂μ) * ∫⁻ x, ρ x ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hg.mul (hρ.pow_const (1 / 2 : ℝ))) (hρ.pow_const (1 / 2 : ℝ))
  have e1 : ∀ x, (g x * ρ x ^ (1 / 2 : ℝ)) * ρ x ^ (1 / 2 : ℝ) = g x * ρ x := fun x => by
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (g x * ρ x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = g x ^ (2 : ℝ) * ρ x := fun x => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (ρ x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = ρ x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, g x * ρ x ∂μ) ^ (2 : ℝ)
      ≤ ((∫⁻ x, g x ^ (2 : ℝ) * ρ x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, ρ x ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = (∫⁻ x, g x ^ (2 : ℝ) * ρ x ∂μ) * ∫⁻ x, ρ x ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem lintegral_euclideanHeatKernel_sub {t : ℝ} (ht : 0 < t) (y : Vec d) :
    ∫⁻ x, ENNReal.ofReal (euclideanHeatKernel t (x - y)) = 1 := by
  rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (euclideanHeatKernel t x)) y,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_euclideanHeatKernel ht)
      (Eventually.of_forall fun x => euclideanHeatKernel_nonneg ht.le x),
    integral_euclideanHeatKernel ht, ENNReal.ofReal_one]

/-- **The Gaussian weight of the unit ball**: `∫_{B_1} Φ(2s)(x - y) dy ≤ 2^{d/2} e^{1/16} e^{-‖x‖²/32}`
for `0 < s ≤ 1`. -/
theorem lintegral_euclideanHeatKernel_originBall_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (x : Vec d) :
    ∫⁻ y in originBall d 1, ENNReal.ofReal (euclideanHeatKernel (2 * s) (x - y)) ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / 2) * Real.exp (1 / 16)) *
        ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) := by
  have hs2 : 0 < 2 * s := by positivity
  set r := distUnitBall x with hr
  have hpt : ∀ y ∈ originBall d 1, ENNReal.ofReal (euclideanHeatKernel (2 * s) (x - y)) ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / 2) * Real.exp (-(r ^ 2) / 16)) *
        ENNReal.ofReal (euclideanHeatKernel (2 * (2 * s)) (x - y)) := fun y hy => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [euclideanHeatKernel_eq_mul hs2 (x - y)]
    have hK := euclideanHeatKernel_nonneg (by positivity : (0 : ℝ) ≤ 2 * (2 * s)) (x - y)
    have hy1 : ‖y‖ < 1 := norm_lt_one_of_mem_originBall hy
    have hry : r ≤ ‖x - y‖ := by
      rw [hr]
      unfold distUnitBall
      refine max_le ?_ (norm_nonneg _)
      have := norm_sub_norm_le x y
      linarith
    have hsq : r ^ 2 ≤ euclideanSq (x - y) := by
      have h0 : 0 ≤ r := le_max_right _ _
      calc r ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ h0 hry 2
        _ ≤ euclideanSq (x - y) := norm_sq_le_euclideanSq _
    have hexp : Real.exp (-(euclideanSq (x - y)) / (8 * (2 * s))) ≤
        Real.exp (-(r ^ 2) / 16) := by
      refine Real.exp_le_exp.mpr ?_
      have h0 : 0 ≤ r ^ 2 := sq_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * (2 * s)) (x - y) *
          Real.exp (-(euclideanSq (x - y)) / (8 * (2 * s)))
        ≤ 2 ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * (2 * s)) (x - y) *
          Real.exp (-(r ^ 2) / 16) := by gcongr
      _ = _ := by ring
  calc ∫⁻ y in originBall d 1, ENNReal.ofReal (euclideanHeatKernel (2 * s) (x - y))
      ≤ ∫⁻ y in originBall d 1, ENNReal.ofReal (2 ^ ((d : ℝ) / 2) * Real.exp (-(r ^ 2) / 16)) *
        ENNReal.ofReal (euclideanHeatKernel (2 * (2 * s)) (x - y)) :=
        setLIntegral_mono' isOpen_originBall_one.measurableSet hpt
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 ^ ((d : ℝ) / 2) * Real.exp (-(r ^ 2) / 16)) *
        ENNReal.ofReal (euclideanHeatKernel (2 * (2 * s)) (x - y)) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 ^ ((d : ℝ) / 2) * Real.exp (-(r ^ 2) / 16)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have h1 : ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * (2 * s)) (x - y)) = 1 := by
          have h2 : ∀ y : Vec d, euclideanHeatKernel (2 * (2 * s)) (x - y) =
              euclideanHeatKernel (2 * (2 * s)) (y - x) := fun y => by
            have h3 : euclideanSq (x - y) = euclideanSq (y - x) := by
              unfold euclideanSq dot
              exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
            unfold euclideanHeatKernel
            rw [h3]
          simp_rw [h2]
          exact lintegral_euclideanHeatKernel_sub (by positivity) x
        rw [h1, mul_one]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : Real.exp (-(r ^ 2) / 16) ≤ Real.exp (1 / 16) * Real.exp (-(‖x‖ ^ 2) / 32) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have := distUnitBall_sq_ge x
          rw [← hr] at this
          linarith
        calc 2 ^ ((d : ℝ) / 2) * Real.exp (-(r ^ 2) / 16)
            ≤ 2 ^ ((d : ℝ) / 2) * (Real.exp (1 / 16) * Real.exp (-(‖x‖ ^ 2) / 32)) := by gcongr
          _ = _ := by ring

/-- **Young's inequality for the heat averages**: for `0 < s ≤ 1`,
`‖Y_{β,s}(F)‖_{L²(B_1)} ≤ C_β (2s)^{-|β|/2} (∫ |F|² exp(-‖x‖²/32))^{1/2}`. -/
theorem eLpNorm_heatDerivativeAverage_le {k : ℕ} (β : Fin d → Fin (k + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ F : Vec d → ℝ,
      AEStronglyMeasurable F volume →
      eLpNorm (heatDerivativeAverage β s F) 2 (volume.restrict (originBall d 1)) ≤
        ENNReal.ofReal (C * (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (β i).val)) *
          (∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^
            (1 / 2 : ℝ) := by
  obtain ⟨C₀, hC₀, hk⟩ := abs_multiIndexDerivative_euclideanHeatKernel_le (d := d) β
  set Cw := 2 ^ ((d : ℝ) / 2) * Real.exp (1 / 16) with hCw
  have hCw0 : 0 ≤ Cw := by positivity
  refine ⟨C₀ * Real.sqrt Cw, by positivity, fun s hs hs1 F hFm => ?_⟩
  set q := (Real.sqrt (2 * s))⁻¹ ^ (∑ i, (β i).val) with hq
  have hq0 : 0 ≤ q := by positivity
  set c := C₀ * q with hc
  have hc0 : 0 ≤ c := mul_nonneg hC₀ hq0
  have hs2 : 0 < 2 * s := by positivity
  have hKc : Continuous (euclideanHeatKernel (d := d) (2 * s)) :=
    (contDiff_euclideanHeatKernel (2 * s)).continuous
  set ρ : Vec d → Vec d → ℝ≥0∞ := fun y x => ENNReal.ofReal (euclideanHeatKernel (2 * s) (x - y))
    with hρ
  have hρm : ∀ y, Measurable (ρ y) := fun y =>
    ENNReal.measurable_ofReal.comp (hKc.measurable.comp (measurable_id.sub_const y))
  have hρm' : ∀ x, Measurable (fun y => ρ y x) := fun x =>
    ENNReal.measurable_ofReal.comp (hKc.measurable.comp (measurable_const.sub measurable_id))
  have hρ1 : ∀ y, ∫⁻ x, ρ y x = 1 := fun y => lintegral_euclideanHeatKernel_sub hs2 y
  have hg : AEMeasurable (fun x => ‖F x‖ₑ) volume := hFm.enorm
  have hY : ∀ y, ‖heatDerivativeAverage β s F y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal c ^ (2 : ℝ) * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ρ y x := fun y => by
    have h1 : ‖heatDerivativeAverage β s F y‖ₑ ≤ ENNReal.ofReal c * ∫⁻ x, ‖F x‖ₑ * ρ y x := by
      unfold heatDerivativeAverage
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      rw [enorm_mul, mul_left_comm]
      gcongr
      calc ‖multiIndexDerivative β (euclideanHeatKernel (d := d) s) (x - y)‖ₑ
          = ENNReal.ofReal |multiIndexDerivative β (euclideanHeatKernel (d := d) s) (x - y)| :=
            Real.enorm_eq_ofReal_abs _
        _ ≤ ENNReal.ofReal (c * euclideanHeatKernel (2 * s) (x - y)) :=
            ENNReal.ofReal_le_ofReal (hk s hs (x - y))
        _ = ENNReal.ofReal c * ρ y x := ENNReal.ofReal_mul hc0
    calc ‖heatDerivativeAverage β s F y‖ₑ ^ (2 : ℝ)
        ≤ (ENNReal.ofReal c * ∫⁻ x, ‖F x‖ₑ * ρ y x) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal c ^ (2 : ℝ) * (∫⁻ x, ‖F x‖ₑ * ρ y x) ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ ENNReal.ofReal c ^ (2 : ℝ) * ((∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ρ y x) * ∫⁻ x, ρ y x) := by
          gcongr
          exact lintegral_mul_rpow_two_le hg (hρm y).aemeasurable
      _ = _ := by rw [hρ1, mul_one]
  have hc2 : ENNReal.ofReal c ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable (Function.uncurry fun y x => ‖F x‖ₑ ^ (2 : ℝ) * ρ y x)
      ((volume.restrict (originBall d 1)).prod volume) := by
    refine ((hg.pow_const (2 : ℝ)).comp_snd).mul ?_
    exact (ENNReal.measurable_ofReal.comp (hKc.measurable.comp
      (measurable_snd.sub measurable_fst))).aemeasurable
  have hint : ∫⁻ y in originBall d 1, ‖heatDerivativeAverage β s F y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal c ^ (2 : ℝ) * (ENNReal.ofReal Cw *
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) := by
    calc ∫⁻ y in originBall d 1, ‖heatDerivativeAverage β s F y‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ y in originBall d 1, ENNReal.ofReal c ^ (2 : ℝ) *
          ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ρ y x := lintegral_mono fun y => hY y
      _ = ENNReal.ofReal c ^ (2 : ℝ) * ∫⁻ y in originBall d 1,
          ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ρ y x := lintegral_const_mul' _ _ hc2
      _ = ENNReal.ofReal c ^ (2 : ℝ) * ∫⁻ x, ∫⁻ y in originBall d 1,
          ‖F x‖ₑ ^ (2 : ℝ) * ρ y x := by rw [lintegral_lintegral_swap hmeas]
      _ = ENNReal.ofReal c ^ (2 : ℝ) * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) *
          ∫⁻ y in originBall d 1, ρ y x := by
          congr 1
          exact lintegral_congr fun x => lintegral_const_mul _ (hρm' x)
      _ ≤ ENNReal.ofReal c ^ (2 : ℝ) * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) *
          (ENNReal.ofReal Cw * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) := by
          gcongr with x
          exact lintegral_euclideanHeatKernel_originBall_le hs hs1 x
      _ = _ := by
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun x => by ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (aestronglyMeasurable_heatDerivativeAverage β s hFm).restrict]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  calc (∫⁻ y in originBall d 1, ‖heatDerivativeAverage β s F y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal c ^ (2 : ℝ) * (ENNReal.ofReal Cw *
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)))) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hCw0 (by norm_num), ← mul_assoc,
          ← Real.sqrt_eq_rpow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
          ← ENNReal.ofReal_mul hc0]
        congr 2
        rw [hc]
        ring

end QSH
