import QuantitativeStochasticHomogenization.Ch04.Sec06.GaussianAverageSquares

/-!
# Section 4.6: Gaussian moments from the Gaussian energy

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6. A field with finite Gaussian energy `∫ |F|² e^{-‖x‖²/32} < ∞` has the Gaussian moments
`∫ |F| Φ(τ)(· - y) < ∞` for `0 < τ ≤ 2` and every center `y`
(`integrable_mul_euclideanHeatKernel_of_energy`), and `∫ |F| e^{-‖x‖²/16} < ∞`
(`integrable_mul_exp_of_energy`), by the Cauchy–Schwarz inequality.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem integrable_exp_neg_mul_norm_sq (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Vec d => Real.exp (-(b * ‖x‖ ^ 2))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : (0 : ℝ) < d / (4 * b) := by positivity
  set c := (4 * Real.pi * (d / (4 * b))) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  refine ((integrable_euclideanHeatKernel (d := d) ht).const_mul c⁻¹).mono'
    (by fun_prop : Continuous fun x : Vec d => Real.exp (-(b * ‖x‖ ^ 2))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold euclideanHeatKernel
  rw [← hc, ← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  refine Real.exp_le_exp.mpr ?_
  have h1 := euclideanSq_le_card_mul_norm_sq x
  have h2 : -(euclideanSq x) / (4 * (d / (4 * b))) = -(b * euclideanSq x / d) := by
    field_simp
  rw [h2, neg_le_neg_iff, div_le_iff₀ hdpos]
  nlinarith

theorem memLp_exp_neg_mul_norm_sq (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    MemLp (fun x : Vec d => Real.exp (-(b * ‖x‖ ^ 2))) 2 := by
  refine (memLp_two_iff_integrable_sq (by fun_prop : Continuous fun x : Vec d =>
    Real.exp (-(b * ‖x‖ ^ 2))).aestronglyMeasurable).mpr ?_
  refine (integrable_exp_neg_mul_norm_sq hd (by positivity : (0 : ℝ) < 2 * b)).congr
    (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem euclideanSq_sub_ge (x y : Vec d) :
    euclideanSq x / 2 - euclideanSq y ≤ euclideanSq (x - y) := by
  unfold euclideanSq dot
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (x i - 2 * y i)]

/-- The weighted field `F e^{-‖x‖²/64}` is square integrable when the Gaussian energy is finite. -/
theorem memLp_mul_exp_of_energy {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) < ⊤) :
    MemLp (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 64)) 2 := by
  have hm : AEStronglyMeasurable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 64)) volume :=
    hFm.mul (by fun_prop : Continuous fun x : Vec d =>
      Real.exp (-(‖x‖ ^ 2) / 64)).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  refine lt_of_eq_of_lt (lintegral_congr fun x => ?_) hF
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal_abs (Real.exp _), abs_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  ring

theorem integrable_mul_of_energy {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) < ⊤)
    {g : Vec d → ℝ} (hg : MemLp (fun x => g x * Real.exp (‖x‖ ^ 2 / 64)) 2) :
    Integrable (fun x => F x * g x) := by
  have h := (memLp_mul_exp_of_energy hFm hF).integrable_mul hg
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  have : Real.exp (-(‖x‖ ^ 2) / 64) * Real.exp (‖x‖ ^ 2 / 64) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc F x * Real.exp (-(‖x‖ ^ 2) / 64) * (g x * Real.exp (‖x‖ ^ 2 / 64))
      = F x * g x * (Real.exp (-(‖x‖ ^ 2) / 64) * Real.exp (‖x‖ ^ 2 / 64)) := by ring
    _ = F x * g x := by rw [this, mul_one]

/-- **Gaussian moments from the Gaussian energy**: `∫ |F| Φ(τ)(· - y) < ∞` for `0 < τ ≤ 2`. -/
theorem integrable_mul_euclideanHeatKernel_of_energy (hd : 1 ≤ d) {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) < ⊤)
    {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 2) (y : Vec d) :
    Integrable (fun x => F x * euclideanHeatKernel τ (x - y)) := by
  refine integrable_mul_of_energy hFm hF ?_
  set c := (4 * Real.pi * τ) ^ (-(d : ℝ) / 2) * Real.exp (euclideanSq y / 8) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ((memLp_exp_neg_mul_norm_sq hd (by norm_num : (0 : ℝ) < 3 / 64)).const_mul c).of_le
    (((contDiff_euclideanHeatKernel τ).continuous.comp (continuous_id.sub continuous_const)).mul
      (by fun_prop : Continuous fun x : Vec d => Real.exp (‖x‖ ^ 2 / 64))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (euclideanHeatKernel_nonneg hτ.le _), abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hc0, abs_of_pos (Real.exp_pos _)]
  unfold euclideanHeatKernel
  have hn := norm_sq_le_euclideanSq x
  have hs := euclideanSq_sub_ge x y
  have hy0 : 0 ≤ euclideanSq y := le_trans (sq_nonneg ‖y‖) (norm_sq_le_euclideanSq y)
  have hxy : 0 ≤ euclideanSq (x - y) := le_trans (sq_nonneg _) (norm_sq_le_euclideanSq _)
  have he : -(euclideanSq (x - y)) / (4 * τ) + ‖x‖ ^ 2 / 64 ≤
      euclideanSq y / 8 + -(3 / 64 * ‖x‖ ^ 2) := by
    have h1 : -(euclideanSq (x - y)) / (4 * τ) ≤ -(euclideanSq (x - y)) / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  calc (4 * Real.pi * τ) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq (x - y)) / (4 * τ)) *
        Real.exp (‖x‖ ^ 2 / 64)
      = (4 * Real.pi * τ) ^ (-(d : ℝ) / 2) *
        Real.exp (-(euclideanSq (x - y)) / (4 * τ) + ‖x‖ ^ 2 / 64) := by
        rw [Real.exp_add]; ring
    _ ≤ (4 * Real.pi * τ) ^ (-(d : ℝ) / 2) *
        Real.exp (euclideanSq y / 8 + -(3 / 64 * ‖x‖ ^ 2)) := by gcongr
    _ = c * Real.exp (-(3 / 64 * ‖x‖ ^ 2)) := by rw [Real.exp_add, hc]; ring

/-- **The moment of `HasGaussianMoment` from the Gaussian energy.** -/
theorem integrable_mul_exp_of_energy (hd : 1 ≤ d) {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32)) < ⊤) :
    Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16)) := by
  refine integrable_mul_of_energy hFm hF ?_
  refine (memLp_exp_neg_mul_norm_sq hd (by norm_num : (0 : ℝ) < 3 / 64)).congr_norm
    (by fun_prop : Continuous fun x : Vec d =>
      Real.exp (-(‖x‖ ^ 2) / 16) * Real.exp (‖x‖ ^ 2 / 64)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [← Real.exp_add]
  congr 2
  ring

end QSH
