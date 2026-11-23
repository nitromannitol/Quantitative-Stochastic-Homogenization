import QuantitativeStochasticHomogenization.Ch06.Sec01.GaussianWeightedEnergy
import QuantitativeStochasticHomogenization.Ch03.Sec04.UncenteredSublinearity
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallMeanSquareScaling
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialBallVolume
import QuantitativeStochasticHomogenization.Ch03.Sec04.HeatKernelConvolution
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianL2
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses

/-!
# Gaussian averages of a sublinear function

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the terminal value of the heat identity (H) of the route of Proposition 4.10.

If `∫_{B_R} f ≤ M R^{d+2}` for `R ≥ R₀`, then `∫ f Φ_s(· - x) ≤ C_d M s` for `s ≥ R₀²` and
`|x| ≤ √s`, by the decomposition of space into the shells of `lintegral_mul_heatKernel_le`
(`lintegral_mul_heatKernel_le_of_quadratic`). For a function `φ` with sublinear mean-square
oscillation on the balls `B_R` (the sublinearity of a corrector), `∫_{B_R} φ² = o(R^{d+2})`, hence
`∫ Φ_s(x - y) |φ(y)| dy = o(√s)` uniformly for `|x| ≤ √s`
(`exists_integral_heatKernel_mul_abs_le_of_sublinear`), and `Φ_s(x - ·) |φ|` is integrable for every
`s > 0` and `x` (`integrable_heatKernel_mul_abs_of_sublinear`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Gaussian-weighted integrals under quadratic growth.** If `∫_{B_R} f ≤ M R^{d+2}` for every
`R ≥ R₀`, then for `s ≥ R₀²` and `|x| ≤ √s`,
`∫ f(y) Φ_s(y - x) dy ≤ (4π)^(-d/2) (2^(d+2) + Σ_k e^(-(k+1)²/4)(k+3)^(d+2)) M s`. -/
theorem lintegral_mul_heatKernel_le_of_quadratic {f : Vec d → ℝ≥0∞} (hf : AEMeasurable f volume)
    {M R₀ : ℝ} (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, f y ≤ ENNReal.ofReal (M * R ^ (d + 2)))
    {s : ℝ} (hs : R₀ ^ 2 ≤ s) {x : Vec d} (hx : euclideanNorm x ≤ Real.sqrt s) :
    ∫⁻ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x)) ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ (d + 2) + gaussianShellSum (d + 2)) *
        M * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  set ρ := Real.sqrt s with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hs0
  have hρR : R₀ ≤ ρ := Real.le_sqrt_of_sq_le hs
  set c := (4 * Real.pi * s) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set e : ℕ → ℝ := fun k => Real.exp (-((k : ℝ) + 1) ^ 2 / 4) with he
  have hdom : ∀ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x)) ≤
      ENNReal.ofReal c * ((ball (0 : Vec d) (2 * ρ)).indicator f y +
        ∑' k : ℕ, ENNReal.ofReal (e k) * (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y) := by
    intro y
    have hK : euclideanHeatKernel s (y - x) = c * Real.exp (-euclideanSq (y - x) / (4 * s)) :=
      rfl
    have hsh := ofReal_exp_le_shells (d := d) hs0 (y := y) hx
    rw [hK, ENNReal.ofReal_mul hc0]
    have hind : ∀ (A : Set (Vec d)), f y * A.indicator 1 y = A.indicator f y := by
      intro A
      by_cases hyA : y ∈ A
      · rw [Set.indicator_of_mem hyA, Set.indicator_of_mem hyA, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hyA, Set.indicator_of_notMem hyA, mul_zero]
    calc f y * (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s))))
        = ENNReal.ofReal c * (f y * ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s)))) :=
          by ring
      _ ≤ ENNReal.ofReal c * (f y * ((ball (0 : Vec d) (2 * ρ)).indicator 1 y +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator 1 y)) := by
          gcongr
      _ = _ := by
          rw [mul_add, hind, ← ENNReal.tsum_mul_left]
          congr 2
          refine tsum_congr fun k => ?_
          rw [← hind]
          ring
  have hmeasI : ∀ R : ℝ, AEMeasurable ((ball (0 : Vec d) R).indicator f) volume :=
    fun R => hf.indicator (measurableSet_ball_zero R)
  have hball' : ∀ R : ℝ, R₀ ≤ R →
      ∫⁻ y, (ball (0 : Vec d) R).indicator f y ≤ ENNReal.ofReal (M * R ^ (d + 2)) := by
    intro R hR
    rw [lintegral_indicator (measurableSet_ball_zero R)]
    exact hball R hR
  have hsum : Summable fun k => e k * ((k : ℝ) + 3) ^ (d + 2) := summable_gaussianShell (d + 2)
  calc ∫⁻ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x))
      ≤ ∫⁻ y, ENNReal.ofReal c * ((ball (0 : Vec d) (2 * ρ)).indicator f y +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y) := lintegral_mono hdom
    _ = ENNReal.ofReal c * ((∫⁻ y, (ball (0 : Vec d) (2 * ρ)).indicator f y) +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            ∫⁻ y, (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y) := by
        have htsum : ∫⁻ y, ∑' k : ℕ, ENNReal.ofReal (e k) *
              (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y =
            ∑' k : ℕ, ENNReal.ofReal (e k) *
              ∫⁻ y, (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y := by
          rw [lintegral_tsum fun k => ((hmeasI _).const_mul _)]
          exact tsum_congr fun k => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' (hmeasI _), htsum]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (M * (2 * ρ) ^ (d + 2)) +
          ∑' k : ℕ, ENNReal.ofReal (e k) * ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ (d + 2))) := by
        gcongr with k
        all_goals first
          | exact hball' _ (by linarith)
          | exact hball' _ (le_trans hρR (le_mul_of_one_le_left hρ0.le (one_le_natCast_add_three _)))
    _ = ENNReal.ofReal ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ (d + 2) + gaussianShellSum (d + 2)) *
          M * s) := by
        have he0 : ∀ k, 0 ≤ e k := fun k => (Real.exp_pos _).le
        have hterm : ∀ k : ℕ, ENNReal.ofReal (e k) *
            ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ (d + 2)) =
            ENNReal.ofReal (M * ρ ^ (d + 2) * (e k * ((k : ℝ) + 3) ^ (d + 2))) := by
          intro k
          rw [← ENNReal.ofReal_mul (he0 k)]
          congr 1
          rw [mul_pow]
          ring
        have h1 : ∑' k : ℕ, ENNReal.ofReal (e k) *
            ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ (d + 2)) =
            ENNReal.ofReal (M * ρ ^ (d + 2) * gaussianShellSum (d + 2)) := by
          simp_rw [hterm]
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun k => mul_nonneg (by positivity) (mul_nonneg (he0 k) (by positivity)))
            (hsum.mul_left _), tsum_mul_left]
          rfl
        rw [h1, ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg (by positivity) (gaussianShellSum_nonneg (d + 2))),
          ← ENNReal.ofReal_mul hc0]
        congr 1
        have h := rpow_mul_sqrt_pow (d := d) hs0
        rw [← hρ, ← hc] at h
        have hρ2 : ρ ^ 2 = s := Real.sq_sqrt hs0.le
        calc c * (M * (2 * ρ) ^ (d + 2) + M * ρ ^ (d + 2) * gaussianShellSum (d + 2))
            = (c * ρ ^ d) * ρ ^ 2 * (2 ^ (d + 2) + gaussianShellSum (d + 2)) * M := by
              rw [mul_pow]
              ring
          _ = _ := by rw [h, hρ2]; ring

/-- `∫_{B_R} φ² ≤ δ² |B_1| R^{d+2}` from `R⁻¹ (⨍_{B_R} φ²)^{1/2} ≤ δ`. -/
theorem lintegral_ball_sq_le_of_rms {φ : Vec d → ℝ} {R δ : ℝ} (hR : 0 < R)
    (hmem : MemLp φ 2 (volume.restrict (ball 0 R)))
    (hrms : R⁻¹ * Real.sqrt (⨍ x in ball (0 : Vec d) R, φ x ^ 2) ≤ δ) :
    ∫⁻ y in ball 0 R, ‖φ y‖ₑ ^ 2 ≤
      ENNReal.ofReal (δ ^ 2 * volume.real (ball (0 : Vec d) 1) * R ^ (d + 2)) := by
  have hVpos : 0 < volume.real (ball (0 : Vec d) R) := ball_volume_pos_finite d R hR
  have hV := volume_real_euclideanBall (d := d) R hR
  have hint : Integrable (fun y => φ y ^ 2) (volume.restrict (ball 0 R)) := hmem.integrable_sq
  have h0 : 0 ≤ ⨍ x in ball (0 : Vec d) R, φ x ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hVpos.le) (integral_nonneg fun x => sq_nonneg _)
  have hsq : Real.sqrt (⨍ x in ball (0 : Vec d) R, φ x ^ 2) ≤ δ * R := by
    rw [inv_mul_le_iff₀ hR] at hrms
    linarith
  have havg : ⨍ x in ball (0 : Vec d) R, φ x ^ 2 ≤ (δ * R) ^ 2 := by
    calc ⨍ x in ball (0 : Vec d) R, φ x ^ 2
        = (Real.sqrt (⨍ x in ball (0 : Vec d) R, φ x ^ 2)) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (δ * R) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  have hintR : ∫ x in ball (0 : Vec d) R, φ x ^ 2 =
      volume.real (ball (0 : Vec d) R) * ⨍ x in ball (0 : Vec d) R, φ x ^ 2 := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]
  have hconv : ∫⁻ y in ball 0 R, ‖φ y‖ₑ ^ 2 = ENNReal.ofReal (∫ y in ball (0 : Vec d) R, φ y ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← Real.enorm_eq_ofReal (sq_nonneg _), enorm_pow]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hintR, hV]
  calc R ^ d * volume.real (ball (0 : Vec d) 1) * ⨍ x in ball (0 : Vec d) R, φ x ^ 2
      ≤ R ^ d * volume.real (ball (0 : Vec d) 1) * (δ * R) ^ 2 := by
        gcongr
    _ = _ := by ring

/-- **The Gaussian averages of a sublinear function are `o(√s)`**: for every `ε > 0` there is `S`
such that `∫ Φ_s(x - y) |φ(y)| dy ≤ ε √s` for `s ≥ S` and `|x| ≤ √s`. -/
theorem exists_integral_heatKernel_mul_abs_le_of_sublinear {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ volume)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (φ x - ⨍ y in ball 0 R, φ y) ^ 2)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, S ≤ s → ∀ x : Vec d, euclideanNorm x ≤ Real.sqrt s →
      Integrable (fun y => euclideanHeatKernel s (x - y) * |φ y|) ∧
      ∫ y, euclideanHeatKernel s (x - y) * |φ y| ≤ ε * Real.sqrt s := by
  have hun := sublinear_uncentered_of_centered φ hloc hsub
  set V₁ := volume.real (ball (0 : Vec d) 1) with hV₁
  have hV₁0 : 0 < V₁ := ball_volume_pos_finite d 1 one_pos
  set K := (4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ (d + 2) + gaussianShellSum (d + 2)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (add_nonneg (by positivity) (gaussianShellSum_nonneg _))
  set δ := ε / Real.sqrt (K * V₁ + 1) with hδ
  have hq : 0 < Real.sqrt (K * V₁ + 1) := Real.sqrt_pos.mpr (by positivity)
  have hδ0 : 0 < δ := div_pos hε hq
  have hδK : K * (δ ^ 2 * V₁) ≤ ε ^ 2 := by
    have h1 : δ ^ 2 * (K * V₁ + 1) = ε ^ 2 := by
      rw [hδ, div_pow, Real.sq_sqrt (by positivity)]
      field_simp
    nlinarith [sq_nonneg δ]
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (hun.eventually (Iic_mem_nhds hδ0))
  set R₀ := max R₁ 1 with hR₀
  have hR₀0 : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ‖φ y‖ₑ ^ 2 ≤
      ENNReal.ofReal (δ ^ 2 * V₁ * R ^ (d + 2)) := fun R hR =>
    lintegral_ball_sq_le_of_rms (hR₀0.trans_le hR) (hloc R (hR₀0.trans_le hR))
      (hR₁ R ((le_max_left _ _).trans hR))
  refine ⟨R₀ ^ 2, by positivity, fun s hs x hx => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hshell := lintegral_mul_heatKernel_le_of_quadratic (f := fun y => ‖φ y‖ₑ ^ 2)
    (hφm.enorm.pow_const 2) (by positivity) hR₀0 hball hs hx
  have hΦm : Measurable fun y => euclideanHeatKernel s (x - y) :=
    (continuous_euclideanHeatKernel s |>.comp (continuous_const.sub continuous_id)).measurable
  have hΦ0 : ∀ y, 0 ≤ euclideanHeatKernel s (x - y) := fun y => euclideanHeatKernel_nonneg hs0.le _
  have hmeas2 : AEStronglyMeasurable (fun y => euclideanHeatKernel s (x - y) * φ y ^ 2) volume :=
    hΦm.aestronglyMeasurable.mul (hφm.pow 2)
  have heq : ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel s (x - y) * φ y ^ 2) =
      ∫⁻ y, ‖φ y‖ₑ ^ 2 * ENNReal.ofReal (euclideanHeatKernel s (y - x)) := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (hΦ0 y), mul_comm, show y - x = -(x - y) by abel,
      euclideanHeatKernel_neg, ← Real.enorm_eq_ofReal (sq_nonneg _), enorm_pow]
  set A := (4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ (d + 2) + gaussianShellSum (d + 2)) *
    (δ ^ 2 * V₁) * s with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg (mul_nonneg hK0 (by positivity)) hs0.le
  have hsqint : Integrable (fun y => euclideanHeatKernel s (x - y) * φ y ^ 2) := by
    refine ⟨hmeas2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
      mul_nonneg (hΦ0 y) (sq_nonneg _)), heq]
    exact lt_of_le_of_lt hshell ENNReal.ofReal_lt_top
  have hsqle : ∫ y, euclideanHeatKernel s (x - y) * φ y ^ 2 ≤ A := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y =>
      mul_nonneg (hΦ0 y) (sq_nonneg _)) hmeas2, heq]
    exact ENNReal.toReal_le_of_le_ofReal hA0 hshell
  have hAε : A ≤ ε ^ 2 * s := by
    rw [hA]
    calc (4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ (d + 2) + gaussianShellSum (d + 2)) *
          (δ ^ 2 * V₁) * s = K * (δ ^ 2 * V₁) * s := by rw [hK]
      _ ≤ ε ^ 2 * s := mul_le_mul_of_nonneg_right hδK hs0.le
  have hΦi : Integrable (fun y => euclideanHeatKernel s (x - y)) :=
    (integrable_euclideanHeatKernel hs0).comp_sub_left x
  have hΦ1 : ∫ y, euclideanHeatKernel s (x - y) = 1 := by
    rw [integral_sub_left_eq_self (fun y => euclideanHeatKernel s y) volume x]
    exact integral_euclideanHeatKernel hs0
  set q := ε * Real.sqrt s with hq'
  have hq0 : 0 < q := mul_pos hε (Real.sqrt_pos.mpr hs0)
  have hq2 : q ^ 2 = ε ^ 2 * s := by rw [hq', mul_pow, Real.sq_sqrt hs0.le]
  have hdom : ∀ y, euclideanHeatKernel s (x - y) * |φ y| ≤
      (euclideanHeatKernel s (x - y) * φ y ^ 2) / (2 * q) + q / 2 * euclideanHeatKernel s (x - y) := by
    intro y
    have h1 : |φ y| ≤ φ y ^ 2 / (2 * q) + q / 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|φ y| - q), sq_abs (φ y)]
    calc euclideanHeatKernel s (x - y) * |φ y| ≤
          euclideanHeatKernel s (x - y) * (φ y ^ 2 / (2 * q) + q / 2) :=
          mul_le_mul_of_nonneg_left h1 (hΦ0 y)
      _ = _ := by ring
  have hint : Integrable (fun y => euclideanHeatKernel s (x - y) * |φ y|) := by
    refine ((hsqint.div_const (2 * q)).add (hΦi.const_mul (q / 2))).mono'
      (hΦm.aestronglyMeasurable.mul (continuous_abs.comp_aestronglyMeasurable hφm)) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hΦ0 y) (abs_nonneg _))]
    exact hdom y
  refine ⟨hint, ?_⟩
  calc ∫ y, euclideanHeatKernel s (x - y) * |φ y|
      ≤ ∫ y, ((euclideanHeatKernel s (x - y) * φ y ^ 2) / (2 * q) +
          q / 2 * euclideanHeatKernel s (x - y)) :=
        integral_mono hint ((hsqint.div_const (2 * q)).add (hΦi.const_mul (q / 2))) hdom
    _ = (∫ y, euclideanHeatKernel s (x - y) * φ y ^ 2) / (2 * q) + q / 2 := by
        rw [integral_add (hsqint.div_const _) (hΦi.const_mul _), integral_div, integral_const_mul,
          hΦ1, mul_one]
    _ ≤ (ε ^ 2 * s) / (2 * q) + q / 2 := by
        gcongr
        exact hsqle.trans hAε
    _ = q := by
        rw [← hq2]
        field_simp
        ring

/-- **Gaussian integrability of a sublinear function**: `Φ_s(x - ·) |φ|` is integrable for every
`s > 0` and `x`. -/
theorem integrable_heatKernel_mul_abs_of_sublinear {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ volume)
    (hloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (φ x - ⨍ y in ball 0 R, φ y) ^ 2)) atTop (𝓝 0)) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    Integrable (fun y => euclideanHeatKernel s (x - y) * |φ y|) := by
  obtain ⟨S, hS0, hS⟩ := exists_integral_heatKernel_mul_abs_le_of_sublinear hφm hloc hsub one_pos
  set S' := max S (max s (euclideanNorm x ^ 2)) with hS'
  have hSS : S ≤ S' := le_max_left _ _
  have hsS : s ≤ S' := (le_max_left _ _).trans (le_max_right _ _)
  have hxS : euclideanNorm x ≤ Real.sqrt S' :=
    Real.le_sqrt_of_sq_le ((le_max_right _ _).trans (le_max_right _ _))
  have hi := (hS S' hSS x hxS).1
  refine (hi.const_mul ((S' / s) ^ ((d : ℝ) / 2))).mono'
    (((continuous_euclideanHeatKernel s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      (continuous_abs.comp_aestronglyMeasurable hφm)) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (euclideanHeatKernel_nonneg hs.le _)
    (abs_nonneg _)), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (euclideanHeatKernel_le_mul hs hsS _) (abs_nonneg _)

end QSH
