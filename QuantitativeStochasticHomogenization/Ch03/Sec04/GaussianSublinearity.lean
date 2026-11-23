import QuantitativeStochasticHomogenization.Ch06.Sec01.GaussianWeightedEnergy
import QuantitativeStochasticHomogenization.Ch06.Sec01.HighContrastEnergyBounds
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyBounds
import QuantitativeStochasticHomogenization.Ch03.Sec03.KernelSmoothing

/-!
# Gaussian averages of sublinear functions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 3.21: the Gaussian averages of the squared oscillation of a corrector.

* `lintegral_mul_heatKernel_le_of_growth`: if `∫_{B_R} f ≤ M R^{d+m}` for `R ≥ R₀`, then for
  `s ≥ R₀²` and `|x| ≤ √s` the Gaussian average `∫ f Φ_s(· - x)` is at most a dimensional
  constant times `M s^{m/2}` (the shell decomposition of `lintegral_mul_heatKernel_le`).
* `integral_sq_sub_mean_le_of_osc`: if the normalized squared oscillation of `u` on `B_ρ` is at
  most `B ρ²` for every `ρ ≥ r`, then `∫_{B_R} (u - (u)_{B_r})² ≤ C_d B |B_1| R^{d+2}` for
  `R ≥ r`, by telescoping the means on the dyadic balls `B_{2^k r}`.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Gaussian averages under polynomial growth -/

/-- **Gaussian average under polynomial growth.** If `∫_{B_R} f ≤ M R^{d+m}` for every `R ≥ R₀`,
then for `s ≥ R₀²` and `|x| ≤ √s`,
`∫ f(y) Φ_s(y - x) dy ≤ (4π)^(-d/2) (2^{d+m} + Σ_k e^(-(k+1)²/4)(k+3)^{d+m}) M (√s)^m`. -/
theorem lintegral_mul_heatKernel_le_of_growth (m : ℕ) {f : Vec d → ℝ≥0∞} (hf : AEMeasurable f)
    {M R₀ : ℝ} (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, f y ≤ ENNReal.ofReal (M * R ^ (d + m)))
    {s : ℝ} (hs : R₀ ^ 2 ≤ s) {x : Vec d} (hx : euclideanNorm x ≤ Real.sqrt s) :
    ∫⁻ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x)) ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(d : ℝ) / 2) *
        (2 ^ (d + m) + gaussianShellSum (d + m)) * M * Real.sqrt s ^ m) := by
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
  have hmeasI : ∀ R : ℝ, AEMeasurable ((ball (0 : Vec d) R).indicator f) :=
    fun R => hf.indicator (measurableSet_ball_zero R)
  have hball' : ∀ R : ℝ, R₀ ≤ R →
      ∫⁻ y, (ball (0 : Vec d) R).indicator f y ≤ ENNReal.ofReal (M * R ^ (d + m)) := by
    intro R hR
    rw [lintegral_indicator (measurableSet_ball_zero R)]
    exact hball R hR
  have hsum : Summable fun k => e k * ((k : ℝ) + 3) ^ (d + m) := summable_gaussianShell (d + m)
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
          rw [lintegral_tsum fun k => (hmeasI _).const_mul _]
          exact tsum_congr fun k => lintegral_const_mul'' _ (hmeasI _)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' (hmeasI _), htsum]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (M * (2 * ρ) ^ (d + m)) +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ (d + m))) := by
        gcongr with k
        all_goals first
          | exact hball' _ (by linarith)
          | exact hball' _ (le_trans hρR (le_mul_of_one_le_left hρ0.le (one_le_natCast_add_three _)))
    _ = ENNReal.ofReal ((4 * Real.pi) ^ (-(d : ℝ) / 2) *
          (2 ^ (d + m) + gaussianShellSum (d + m)) * M * Real.sqrt s ^ m) := by
        have he0 : ∀ k, 0 ≤ e k := fun k => (Real.exp_pos _).le
        have hterm : ∀ k : ℕ, ENNReal.ofReal (e k) *
            ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ (d + m)) =
            ENNReal.ofReal (M * ρ ^ (d + m) * (e k * ((k : ℝ) + 3) ^ (d + m))) := by
          intro k
          rw [← ENNReal.ofReal_mul (he0 k)]
          congr 1
          rw [mul_pow]
          ring
        have h1 : ∑' k : ℕ, ENNReal.ofReal (e k) *
            ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ (d + m)) =
            ENNReal.ofReal (M * ρ ^ (d + m) * gaussianShellSum (d + m)) := by
          simp_rw [hterm]
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun k => mul_nonneg (by positivity) (mul_nonneg (he0 k) (by positivity)))
            (hsum.mul_left _), tsum_mul_left]
          rfl
        rw [h1, ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg (by positivity) (gaussianShellSum_nonneg (d + m))),
          ← ENNReal.ofReal_mul hc0]
        congr 1
        have h := rpow_mul_sqrt_pow (d := d) hs0
        rw [← hρ, ← hc] at h
        calc c * (M * (2 * ρ) ^ (d + m) + M * ρ ^ (d + m) * gaussianShellSum (d + m))
            = (c * ρ ^ d) * (2 ^ (d + m) + gaussianShellSum (d + m)) * M * ρ ^ m := by
              rw [mul_pow, pow_add, pow_add]; ring
          _ = _ := by rw [h]

/-! ## Real-valued Gaussian averages -/

/-- The constant `(4π)^(-d/2) (2^{d+m} + Σ_k e^(-(k+1)²/4)(k+3)^{d+m})` of the Gaussian averages
under polynomial growth. -/
def gaussianGrowthConst (d m : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ (d + m) + gaussianShellSum (d + m))

theorem gaussianGrowthConst_nonneg (d m : ℕ) : 0 ≤ gaussianGrowthConst d m := by
  unfold gaussianGrowthConst
  have := gaussianShellSum_nonneg (d + m)
  positivity

/-- **Gaussian averages of squares under polynomial growth.** If `∫_{B_R} f² ≤ M R^{d+m}` for every
`R ≥ R₀`, then for `s ≥ R₀²` and `|x| ≤ √s` the function `Φ_s(· - x) f²` is integrable with integral
at most `gaussianGrowthConst d m · M (√s)^m`. -/
theorem integral_heatKernel_mul_sq_le_of_growth (m : ℕ) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) {M R₀ : ℝ} (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → IntegrableOn (fun y => f y ^ 2) (ball 0 R) ∧
      ∫ y in ball 0 R, f y ^ 2 ≤ M * R ^ (d + m))
    {s : ℝ} (hs : R₀ ^ 2 ≤ s) {x : Vec d} (hx : euclideanNorm x ≤ Real.sqrt s) :
    Integrable (fun y => euclideanHeatKernel s (y - x) * f y ^ 2) ∧
      ∫ y, euclideanHeatKernel s (y - x) * f y ^ 2 ≤
        gaussianGrowthConst d m * M * Real.sqrt s ^ m := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  set F : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal (f y ^ 2) with hF
  have hFm : AEMeasurable F := (hf.aemeasurable.pow_const 2).ennreal_ofReal
  have hballF : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, F y ≤ ENNReal.ofReal (M * R ^ (d + m)) := by
    intro R hR
    obtain ⟨hi, hle⟩ := hball R hR
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  have hL := lintegral_mul_heatKernel_le_of_growth m hFm hM hR₀ hballF hs hx
  have hK0 : ∀ y, 0 ≤ euclideanHeatKernel s (y - x) := fun y =>
    euclideanHeatKernel_nonneg hs0.le _
  have hpt : ∀ y, F y * ENNReal.ofReal (euclideanHeatKernel s (y - x)) =
      ENNReal.ofReal (euclideanHeatKernel s (y - x) * f y ^ 2) := by
    intro y
    rw [hF, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  simp_rw [hpt] at hL
  have hcont : Continuous fun y => euclideanHeatKernel s (y - x) :=
    (continuous_euclideanHeatKernel s).comp (continuous_id.sub continuous_const)
  have hmeas : AEStronglyMeasurable (fun y => euclideanHeatKernel s (y - x) * f y ^ 2) volume :=
    hcont.aestronglyMeasurable.mul (hf.pow 2)
  have hnn : ∀ y, 0 ≤ euclideanHeatKernel s (y - x) * f y ^ 2 := fun y =>
    mul_nonneg (hK0 y) (sq_nonneg _)
  have hint : Integrable (fun y => euclideanHeatKernel s (y - x) * f y ^ 2) := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ y, ‖euclideanHeatKernel s (y - x) * f y ^ 2‖ₑ
        = ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel s (y - x) * f y ^ 2) :=
          lintegral_congr fun y => Real.enorm_of_nonneg (hnn y)
      _ ≤ _ := hL
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas]
  have hC0 : 0 ≤ gaussianGrowthConst d m * M * Real.sqrt s ^ m := by
    have := gaussianGrowthConst_nonneg d m
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hC0 (by simpa [gaussianGrowthConst, mul_assoc] using hL)

/-- **Weighted Cauchy–Schwarz.** For a nonnegative weight `w` with `w f²` and `w h²` integrable,
`w f h` is integrable and `|∫ w f h| ≤ (∫ w f²)^{1/2} (∫ w h²)^{1/2}`. -/
theorem integrable_and_abs_integral_weight_mul_le {w f h : Vec d → ℝ} (hw0 : ∀ y, 0 ≤ w y)
    (hwm : AEStronglyMeasurable w volume) (hf : AEStronglyMeasurable f volume)
    (hh : AEStronglyMeasurable h volume) (hf2 : Integrable fun y => w y * f y ^ 2)
    (hh2 : Integrable fun y => w y * h y ^ 2) :
    Integrable (fun y => w y * (f y * h y)) ∧
      |∫ y, w y * (f y * h y)| ≤
        Real.sqrt (∫ y, w y * f y ^ 2) * Real.sqrt (∫ y, w y * h y ^ 2) := by
  have hsq : ∀ y, Real.sqrt (w y) ^ 2 = w y := fun y => Real.sq_sqrt (hw0 y)
  have hsm : AEStronglyMeasurable (fun y => Real.sqrt (w y)) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hwm
  have hf' : MemLp (fun y => Real.sqrt (w y) * f y) 2 volume := by
    refine (memLp_two_iff_integrable_sq (hsm.mul hf)).mpr ?_
    refine hf2.congr (Eventually.of_forall fun y => ?_)
    show w y * f y ^ 2 = (Real.sqrt (w y) * f y) ^ 2
    rw [mul_pow, hsq]
  have hh' : MemLp (fun y => Real.sqrt (w y) * h y) 2 volume := by
    refine (memLp_two_iff_integrable_sq (hsm.mul hh)).mpr ?_
    refine hh2.congr (Eventually.of_forall fun y => ?_)
    show w y * h y ^ 2 = (Real.sqrt (w y) * h y) ^ 2
    rw [mul_pow, hsq]
  have hprod : ∀ y, (Real.sqrt (w y) * f y) * (Real.sqrt (w y) * h y) = w y * (f y * h y) := by
    intro y
    have := hsq y
    rw [sq] at this
    calc (Real.sqrt (w y) * f y) * (Real.sqrt (w y) * h y)
        = (Real.sqrt (w y) * Real.sqrt (w y)) * (f y * h y) := by ring
      _ = w y * (f y * h y) := by rw [this]
  have hsq' : ∀ (k : Vec d → ℝ) y, (Real.sqrt (w y) * k y) ^ 2 = w y * k y ^ 2 := by
    intro k y
    rw [mul_pow, hsq]
  refine ⟨(integrable_mul_of_memLp_two hf' hh').congr (Eventually.of_forall hprod), ?_⟩
  have h := abs_integral_mul_le_sqrt_mul_sqrt hf' hh'
  simp only [hprod, hsq'] at h
  exact h

/-! ## Telescoping the dyadic means -/

/-- The dyadic oscillation constant `2 (1 + 4·2^d) 2^{d+2}`. -/
def dyadicOscConst (d : ℕ) : ℝ := 2 * (1 + 4 * 2 ^ d) * 2 ^ (d + 2)

theorem dyadicOscConst_pos (d : ℕ) : 0 < dyadicOscConst d := by
  unfold dyadicOscConst; positivity

/-- **Growth from small oscillations.** If `⨍_{B_ρ} (u - (u)_{B_ρ})² ≤ B ρ²` for every `ρ ≥ r`,
then `∫_{B_R} (u - (u)_{B_r})² ≤ C_d B |B_1| R^{d+2}` for every `R ≥ r`. -/
theorem integral_sq_sub_mean_le_of_osc {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) {r B : ℝ} (hr : 0 < r)
    (hB : 0 ≤ B)
    (hosc : ∀ ρ : ℝ, r ≤ ρ → ⨍ x in ball 0 ρ, (u x - ⨍ y in ball 0 ρ, u y) ^ 2 ≤ B * ρ ^ 2)
    {R : ℝ} (hR : r ≤ R) :
    ∫ x in ball 0 R, (u x - ⨍ y in ball 0 r, u y) ^ 2 ≤
      dyadicOscConst d * B * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal *
        R ^ (d + 2) := by
  set ω := (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal with hω
  have hω0 : 0 < ω :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  set ρ : ℕ → ℝ := fun k => 2 ^ k * r with hρdef
  have hρ0 : ∀ k, 0 < ρ k := fun k => by positivity
  set m : ℕ → ℝ := fun k => ⨍ y in ball 0 (ρ k), u y with hmdef
  have hvol : ∀ t : ℝ, 0 < t → volume.real (ball (0 : Vec d) t) = t ^ d * ω := fun t ht =>
    volume_real_ball ht
  have hfin : ∀ t : ℝ, 0 < t → IsFiniteMeasure (volume.restrict (ball (0 : Vec d) t)) :=
    fun t ht => isFiniteMeasure_restrict.mpr (volume_ball_ne_top ht)
  -- one dyadic step of the means
  have hstep : ∀ k, (m (k + 1) - m k) ^ 2 ≤ 2 ^ d * B * ρ (k + 1) ^ 2 := by
    intro k
    have hk0 := hρ0 k
    have hk1 := hρ0 (k + 1)
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (ρ k))) := hfin _ hk0
    have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (ρ (k + 1)))) := hfin _ hk1
    have hρs : ρ (k + 1) = 2 * ρ k := by simp only [hρdef, pow_succ]; ring
    have hsub : ball (0 : Vec d) (ρ k) ⊆ ball 0 (ρ (k + 1)) := by
      intro x hx
      have hx' : euclideanNorm (x - 0) < ρ k := hx
      show euclideanNorm (x - 0) < ρ (k + 1)
      rw [hρs]
      linarith
    have hmem : MemLp (fun x => u x - m (k + 1)) 2 (volume.restrict (ball 0 (ρ k))) :=
      (hu _ hk0).sub (memLp_const _)
    have hJ := sq_setAverage_le (volume_ball_ne_zero hk0) (volume_ball_ne_top hk0)
      (hmem.integrable one_le_two) hmem.integrable_sq
    have hV : volume.real (ball (0 : Vec d) (ρ k)) ≠ 0 :=
      (ENNReal.toReal_pos (volume_ball_ne_zero hk0) (volume_ball_ne_top hk0)).ne'
    have hmean : ⨍ x in ball 0 (ρ k), (u x - m (k + 1)) = m k - m (k + 1) := by
      have hI : ∫ x in ball (0 : Vec d) (ρ k), (u x - m (k + 1)) =
          (∫ x in ball (0 : Vec d) (ρ k), u x) - volume.real (ball (0 : Vec d) (ρ k)) *
            m (k + 1) := by
        rw [integral_sub ((hu _ hk0).integrable one_le_two) (integrable_const _),
          setIntegral_const, smul_eq_mul]
      rw [setAverage_eq, smul_eq_mul, hI]
      have hmk : m k = (volume.real (ball (0 : Vec d) (ρ k)))⁻¹ *
          ∫ x in ball (0 : Vec d) (ρ k), u x := by
        simp only [hmdef]
        rw [setAverage_eq, smul_eq_mul]
      rw [hmk]
      field_simp
    rw [hmean] at hJ
    have hmono : ∫ x in ball (0 : Vec d) (ρ k), (u x - m (k + 1)) ^ 2 ≤
        ∫ x in ball (0 : Vec d) (ρ (k + 1)), (u x - m (k + 1)) ^ 2 :=
      setIntegral_mono_set (((hu _ hk1).sub (memLp_const _)).integrable_sq)
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hsub)
    have hrk1 : r ≤ ρ (k + 1) := by
      have h1 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      simp only [hρdef]
      nlinarith
    have hosc' := hosc (ρ (k + 1)) hrk1
    rw [setAverage_eq, smul_eq_mul, hvol _ hk1] at hosc'
    rw [setAverage_eq, smul_eq_mul, hvol _ hk0] at hJ
    have hratio : (ρ (k + 1)) ^ d * ω = 2 ^ d * (ρ k ^ d * ω) := by rw [hρs, mul_pow]; ring
    have hpos0 : 0 < ρ k ^ d * ω := by positivity
    have hpos1 : 0 < ρ (k + 1) ^ d * ω := by positivity
    rw [show (m k - m (k + 1)) ^ 2 = (m (k + 1) - m k) ^ 2 by ring] at hJ
    calc (m (k + 1) - m k) ^ 2
        ≤ (ρ k ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) (ρ k), (u x - m (k + 1)) ^ 2 := hJ
      _ ≤ (ρ k ^ d * ω)⁻¹ * ∫ x in ball (0 : Vec d) (ρ (k + 1)), (u x - m (k + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hpos0.le)
      _ = 2 ^ d * ((ρ (k + 1) ^ d * ω)⁻¹ *
            ∫ x in ball (0 : Vec d) (ρ (k + 1)), (u x - m (k + 1)) ^ 2) := by
          rw [hratio]
          field_simp
      _ ≤ 2 ^ d * (B * ρ (k + 1) ^ 2) := mul_le_mul_of_nonneg_left hosc' (by positivity)
      _ = 2 ^ d * B * ρ (k + 1) ^ 2 := by ring
  -- the telescoped means
  have htel : ∀ k, |m k - m 0| ≤ Real.sqrt (2 ^ d * B) * (2 * ρ k) := by
    intro k
    induction k with
    | zero => simp; positivity
    | succ k ih =>
      have h1 : |m (k + 1) - m k| ≤ Real.sqrt (2 ^ d * B) * ρ (k + 1) := by
        have h2 : Real.sqrt (2 ^ d * B * ρ (k + 1) ^ 2) = Real.sqrt (2 ^ d * B) * ρ (k + 1) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hρ0 _).le]
        rw [← h2]
        exact Real.abs_le_sqrt (hstep k)
      have hρs : ρ (k + 1) = 2 * ρ k := by simp only [hρdef, pow_succ]; ring
      calc |m (k + 1) - m 0| ≤ |m (k + 1) - m k| + |m k - m 0| := abs_sub_le _ _ _
        _ ≤ Real.sqrt (2 ^ d * B) * ρ (k + 1) + Real.sqrt (2 ^ d * B) * (2 * ρ k) :=
            add_le_add h1 ih
        _ = Real.sqrt (2 ^ d * B) * (2 * ρ (k + 1)) := by rw [hρs]; ring
  -- choose the dyadic radius above `R`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, R ≤ ρ k ∧ ρ k ≤ 2 * R := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / r) (by norm_num : (1 : ℝ) < 2)
    classical
    let k := Nat.find (⟨n, hn.le⟩ : ∃ n : ℕ, R / r ≤ 2 ^ n)
    have hk1 : R / r ≤ 2 ^ k := Nat.find_spec (⟨n, hn.le⟩ : ∃ n : ℕ, R / r ≤ 2 ^ n)
    refine ⟨k, ?_, ?_⟩
    · show R ≤ 2 ^ k * r
      rwa [div_le_iff₀ hr] at hk1
    · show 2 ^ k * r ≤ 2 * R
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero, one_mul]; linarith
      · have hmin := Nat.find_min (⟨n, hn.le⟩ : ∃ n : ℕ, R / r ≤ 2 ^ n) (Nat.sub_lt hpos one_pos)
        push Not at hmin
        rw [lt_div_iff₀ hr] at hmin
        have : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        linarith
  obtain ⟨hRk, hkR⟩ := hk
  have hk0 := hρ0 k
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (ρ k))) := hfin _ hk0
  have hsubR : ball (0 : Vec d) R ⊆ ball 0 (ρ k) := by
    intro x hx
    have hx' : euclideanNorm (x - 0) < R := hx
    show euclideanNorm (x - 0) < ρ k
    linarith
  have hmemk : MemLp (fun x => u x - m 0) 2 (volume.restrict (ball 0 (ρ k))) :=
    (hu _ hk0).sub (memLp_const _)
  have hmono : ∫ x in ball (0 : Vec d) R, (u x - m 0) ^ 2 ≤
      ∫ x in ball (0 : Vec d) (ρ k), (u x - m 0) ^ 2 :=
    setIntegral_mono_set hmemk.integrable_sq (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall hsubR)
  have hsplit : ∀ x, (u x - m 0) ^ 2 ≤ 2 * (u x - m k) ^ 2 + 2 * (m k - m 0) ^ 2 := by
    intro x; nlinarith [sq_nonneg (u x - m k - (m k - m 0))]
  have hi1 : Integrable (fun x => 2 * (u x - m k) ^ 2) (volume.restrict (ball 0 (ρ k))) :=
    (((hu _ hk0).sub (memLp_const (m k))).integrable_sq).const_mul 2
  have hi2 : Integrable (fun _ : Vec d => 2 * (m k - m 0) ^ 2) (volume.restrict (ball 0 (ρ k))) :=
    integrable_const _
  have hbig : ∫ x in ball (0 : Vec d) (ρ k), (u x - m 0) ^ 2 ≤
      2 * (∫ x in ball (0 : Vec d) (ρ k), (u x - m k) ^ 2) +
        2 * (m k - m 0) ^ 2 * volume.real (ball (0 : Vec d) (ρ k)) := by
    have h := integral_mono hmemk.integrable_sq (hi1.add hi2) hsplit
    have heq : ∫ x in ball (0 : Vec d) (ρ k), (2 * (u x - m k) ^ 2 + 2 * (m k - m 0) ^ 2) =
        2 * (∫ x in ball (0 : Vec d) (ρ k), (u x - m k) ^ 2) +
          2 * (m k - m 0) ^ 2 * volume.real (ball (0 : Vec d) (ρ k)) := by
      rw [integral_add hi1 hi2, integral_const_mul (2 : ℝ) (fun x => (u x - m k) ^ 2),
        setIntegral_const, smul_eq_mul]
      ring
    exact h.trans (le_of_eq heq)
  have hosck := hosc (ρ k) (hR.trans hRk)
  rw [setAverage_eq, smul_eq_mul, hvol _ hk0] at hosck
  have hpos : 0 < ρ k ^ d * ω := by positivity
  have hI : ∫ x in ball (0 : Vec d) (ρ k), (u x - m k) ^ 2 ≤ B * ρ k ^ 2 * (ρ k ^ d * ω) := by
    rw [inv_mul_le_iff₀ hpos] at hosck
    linarith
  have htk := htel k
  have hsqk : (m k - m 0) ^ 2 ≤ 2 ^ d * B * (2 * ρ k) ^ 2 := by
    have h1 := Real.sqrt_le_sqrt (sq_nonneg (m k - m 0))
    rw [Real.sqrt_sq_eq_abs] at h1
    have h2 := pow_le_pow_left₀ (abs_nonneg _) htk 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at h2
    exact h2
  have hprod : (m k - m 0) ^ 2 * (ρ k ^ d * ω) ≤ 2 ^ d * B * (2 * ρ k) ^ 2 * (ρ k ^ d * ω) :=
    mul_le_mul_of_nonneg_right hsqk hpos.le
  have hρkR : ρ k ^ (d + 2) ≤ (2 * R) ^ (d + 2) := pow_le_pow_left₀ hk0.le hkR _
  have hstart : ∫ x in ball (0 : Vec d) R, (u x - ⨍ y in ball 0 r, u y) ^ 2 =
      ∫ x in ball (0 : Vec d) R, (u x - m 0) ^ 2 := by
    simp only [hmdef, hρdef, pow_zero, one_mul]
  have hvk := hvol _ hk0
  calc ∫ x in ball (0 : Vec d) R, (u x - ⨍ y in ball 0 r, u y) ^ 2
      = ∫ x in ball (0 : Vec d) R, (u x - m 0) ^ 2 := hstart
    _ ≤ ∫ x in ball (0 : Vec d) (ρ k), (u x - m 0) ^ 2 := hmono
    _ ≤ 2 * (∫ x in ball (0 : Vec d) (ρ k), (u x - m k) ^ 2) +
          2 * (m k - m 0) ^ 2 * volume.real (ball (0 : Vec d) (ρ k)) := hbig
    _ ≤ 2 * (B * ρ k ^ 2 * (ρ k ^ d * ω)) + 2 * (2 ^ d * B * (2 * ρ k) ^ 2) * (ρ k ^ d * ω) := by
        rw [hvk]
        have h1 := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 2)
        have h2 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
        have e1 : 2 * (∫ x in ball (0 : Vec d) (ρ k), (u x - m k) ^ 2) +
            2 * (m k - m 0) ^ 2 * (ρ k ^ d * ω) =
            2 * (∫ x in ball (0 : Vec d) (ρ k), (u x - m k) ^ 2) +
              2 * ((m k - m 0) ^ 2 * (ρ k ^ d * ω)) := by ring
        have e2 : 2 * (B * ρ k ^ 2 * (ρ k ^ d * ω)) +
            2 * (2 ^ d * B * (2 * ρ k) ^ 2) * (ρ k ^ d * ω) =
            2 * (B * ρ k ^ 2 * (ρ k ^ d * ω)) +
              2 * (2 ^ d * B * (2 * ρ k) ^ 2 * (ρ k ^ d * ω)) := by ring
        rw [e1, e2]
        exact add_le_add h1 h2
    _ = 2 * (1 + 4 * 2 ^ d) * B * ω * ρ k ^ (d + 2) := by ring
    _ ≤ 2 * (1 + 4 * 2 ^ d) * B * ω * (2 * R) ^ (d + 2) := by gcongr
    _ = dyadicOscConst d * B * ω * R ^ (d + 2) := by
        unfold dyadicOscConst
        rw [mul_pow]
        ring

end QSH
