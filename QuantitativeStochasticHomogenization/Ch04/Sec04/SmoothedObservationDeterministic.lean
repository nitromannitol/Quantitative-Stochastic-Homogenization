import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationOs
import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification

/-!
# The error terms of the cut-off Gaussian observations

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the deterministic part of the observation of the smoothed correctors. Let `χ` be a cutoff of
`B_R(z)` (equal to one on `B_{R/2}(z)`, with gradient at most `D/R`) and let the centers `q` lie
in `B_{R/4}(z)`. Then:

* the derivative of `χ` vanishes on `B_{R/2}(z)` and outside `B_R(z)`;
* `|∫_{B_T} (1 - χ) Φ_{q,ρ} (φ - c)| ≤ Φ̂_ρ e^{-R²/(64ρ²)} (|B_T| ∫_{B_T} (φ - c)²)^{1/2}`;
* `|∫ ∂_jχ Φ_{q,ρ} (φ - c)| ≤ (D/R) Φ̂_ρ e^{-R²/(64ρ²)} (|B_R| ∫_{B_R} (φ - c)²)^{1/2}`;
* `|∫ (1 - χ) Φ_{q,ρ} g_j| ≤ 2^{d/2} e^{-R²/(128ρ²)} (∫ Φ_{q,√2ρ} |g|²)^{1/2}`;
* the mass `∫ χ Φ_{z,ρ}` is at least `1/2` when `2^{d/2} e^{-R²/(32ρ²)} ≤ 1/2`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- A smooth function at most one has vanishing derivative where it equals one. -/
theorem coordinateDerivative_eq_zero_of_le_one_of_eq_one {χ : Vec d → ℝ}
    (h1 : ∀ x, χ x ≤ 1) {x : Vec d} (hx : χ x = 1) (j : Fin d) :
    coordinateDerivative j χ x = 0 := by
  have hmax : IsLocalMax χ x := Eventually.of_forall fun y => by rw [hx]; exact h1 y
  rw [coordinateDerivative, hmax.fderiv_eq_zero]
  rfl

/-- **The potential term outside the cutoff.** -/
theorem abs_setIntegral_one_sub_cutoff_le {χ φ : Vec d → ℝ} {z q : Vec d} {R T ρ c : ℝ}
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1) (hq : euclideanNorm (q - z) ≤ R / 4)
    (hφT : MemLp φ 2 (volume.restrict (ball z T))) :
    |∫ x in ball z T, (1 - χ x) * heatKernel q ρ x * (φ x - c)| ≤
      heatKernelPeak d ρ * Real.exp (-((R / 2) ^ 2) / (16 * ρ ^ 2)) *
        Real.sqrt (volume.real (ball z T) * ∫ x in ball z T, (φ x - c) ^ 2) := by
  set K := heatKernelPeak d ρ * Real.exp (-((R / 2) ^ 2) / (16 * ρ ^ 2)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (heatKernelPeak_pos hρ.ne').le (Real.exp_pos _).le
  have hq' : euclideanNorm (q - z) ≤ R / 2 / 2 := by linarith
  have hpt : ∀ x, |(1 - χ x) * heatKernel q ρ x * (φ x - c)| ≤ K * |φ x - c| := fun x => by
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 (hχ01 x).2),
      abs_of_nonneg (heatKernel_pos q hρ x).le]
    by_cases hx : x ∈ ball z (R / 2)
    · rw [hχ1 x hx, sub_self, zero_mul, zero_mul]
      exact mul_nonneg hK0 (abs_nonneg _)
    · have h1 := heatKernel_le_peak_mul_exp_of_far (by linarith) hρ hx hq'
      have h2 : (1 - χ x) * heatKernel q ρ x ≤ K := by
        calc (1 - χ x) * heatKernel q ρ x ≤ 1 * heatKernel q ρ x :=
              mul_le_mul_of_nonneg_right (by linarith [(hχ01 x).1])
                (heatKernel_pos q hρ x).le
          _ ≤ K := by rw [one_mul]; exact h1
      exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have hfT : MemLp (fun x => φ x - c) 2 (volume.restrict (ball z T)) := hφT.sub (memLp_const c)
  have : IsFiniteMeasure (volume.restrict (ball z T)) :=
    isFiniteMeasure_restrict.2 (volume_ball_lt_top z T).ne
  have hb : ‖∫ x in ball z T, (1 - χ x) * heatKernel q ρ x * (φ x - c)‖ ≤
      ∫ x in ball z T, K * |φ x - c| :=
    norm_integral_le_of_norm_le (((hfT.integrable one_le_two).abs).const_mul K)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
  rw [integral_const_mul, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (setIntegral_abs_le_sqrt (volume_ball_lt_top z T) hfT) hK0)

/-- **The term of the derivative of the cutoff.** -/
theorem abs_integral_cutoff_derivative_le {χ φ : Vec d → ℝ} {z q : Vec d} {R D ρ c : ℝ}
    (hR : 0 < R) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0) (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2)
    (hq : euclideanNorm (q - z) ≤ R / 4) (hφR : MemLp φ 2 (volume.restrict (ball z R)))
    (j : Fin d) :
    |∫ x, coordinateDerivative j χ x * heatKernel q ρ x * (φ x - c)| ≤
      D / R * (heatKernelPeak d ρ * Real.exp (-((R / 2) ^ 2) / (16 * ρ ^ 2))) *
        Real.sqrt (volume.real (ball z R) * ∫ x in ball z R, (φ x - c) ^ 2) := by
  set K := D / R * (heatKernelPeak d ρ * Real.exp (-((R / 2) ^ 2) / (16 * ρ ^ 2))) with hK
  have hK0 : 0 ≤ K := by
    have := (heatKernelPeak_pos (d := d) hρ.ne').le
    positivity
  have hq' : euclideanNorm (q - z) ≤ R / 2 / 2 := by linarith
  have hout : ∀ x, x ∉ ball z R → coordinateDerivative j χ x * heatKernel q ρ x * (φ x - c) = 0 :=
    fun x hx => by
      rw [coordinateDerivative_eq_zero_of_nonneg_of_eq_zero (fun y => (hχ01 y).1)
        (hχR x hx) j]
      ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  have hpt : ∀ x, |coordinateDerivative j χ x * heatKernel q ρ x * (φ x - c)| ≤ K * |φ x - c| :=
    fun x => by
      rw [abs_mul, abs_mul, abs_of_nonneg (heatKernel_pos q hρ x).le]
      by_cases hx : x ∈ ball z (R / 2)
      · rw [coordinateDerivative_eq_zero_of_le_one_of_eq_one (fun y => (hχ01 y).2)
          (hχ1 x hx) j, abs_zero, zero_mul, zero_mul]
        exact mul_nonneg hK0 (abs_nonneg _)
      · have h1 := heatKernel_le_peak_mul_exp_of_far (by linarith) hρ hx hq'
        have h2 : |coordinateDerivative j χ x| ≤ D / R := by
          have := abs_coord_le_euclideanNorm (gradient χ x) j
          have hn : euclideanNorm (gradient χ x) ≤ D / R := by
            rw [euclideanNorm]
            calc Real.sqrt (euclideanSq (gradient χ x)) ≤ Real.sqrt ((D / R) ^ 2) :=
                  Real.sqrt_le_sqrt (hχD x)
              _ = D / R := Real.sqrt_sq (by positivity)
          exact this.trans hn
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h2 h1 (heatKernel_pos q hρ x).le (by positivity)) (abs_nonneg _)
  have hfR : MemLp (fun x => φ x - c) 2 (volume.restrict (ball z R)) := hφR.sub (memLp_const c)
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    isFiniteMeasure_restrict.2 (volume_ball_lt_top z R).ne
  have hb : ‖∫ x in ball z R, coordinateDerivative j χ x * heatKernel q ρ x * (φ x - c)‖ ≤
      ∫ x in ball z R, K * |φ x - c| :=
    norm_integral_le_of_norm_le (((hfR.integrable one_le_two).abs).const_mul K)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
  rw [integral_const_mul, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (setIntegral_abs_le_sqrt (volume_ball_lt_top z R) hfR) hK0)

/-- **The gradient term outside the cutoff**, by the Gaussian energy at the scale `√2 ρ`. -/
theorem abs_integral_one_sub_cutoff_grad_le {χ : Vec d → ℝ} {g : Vec d → Vec d} {z q : Vec d}
    {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1) (hq : euclideanNorm (q - z) ≤ R / 4)
    (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun x => heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x)))
    (j : Fin d) :
    |∫ x, (1 - χ x) * heatKernel q ρ x * g x j| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (32 * ρ ^ 2)) *
        Real.sqrt (∫ x, heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x)) := by
  set A := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (32 * ρ ^ 2)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hρ' : 0 < Real.sqrt 2 * ρ := by positivity
  set w : Vec d → ℝ := heatKernel q (Real.sqrt 2 * ρ) with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => (heatKernel_pos q hρ' x).le
  have hq' : euclideanNorm (q - z) ≤ R / 2 / 2 := by linarith
  have hpt : ∀ x, |(1 - χ x) * heatKernel q ρ x * g x j| ≤ A * (w x * |g x j|) := fun x => by
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 (hχ01 x).2),
      abs_of_nonneg (heatKernel_pos q hρ x).le]
    by_cases hx : x ∈ ball z (R / 2)
    · rw [hχ1 x hx, sub_self, zero_mul, zero_mul]
      exact mul_nonneg hA0 (mul_nonneg (hw0 x) (abs_nonneg _))
    · have h1 := heatKernel_le_exp_mul_heatKernel_of_far (by linarith) hρ hx hq'
      calc (1 - χ x) * heatKernel q ρ x * |g x j| ≤ 1 * heatKernel q ρ x * |g x j| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [(hχ01 x).1])
              (heatKernel_pos q hρ x).le) (abs_nonneg _)
        _ ≤ (A * w x) * |g x j| := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = A * (w x * |g x j|) := by ring
  have hgj : AEStronglyMeasurable (fun x => g x j) volume :=
    (continuous_apply j).comp_aestronglyMeasurable hgm
  have hwi : Integrable w := integrable_heatKernel q hρ'
  have hbd1 : ∀ x, |g x j| ≤ 1 + euclideanSq (g x) := fun x =>
    (abs_coord_le_euclideanNorm (g x) j).trans (by
      rw [← sq_euclideanNorm]; nlinarith [sq_nonneg (euclideanNorm (g x) - 1)])
  have hbd2 : ∀ x, |g x j| ^ 2 ≤ euclideanSq (g x) := fun x => by
    rw [← sq_euclideanNorm]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_coord_le_euclideanNorm (g x) j) 2
  have hi1 : Integrable (fun x => w x * |g x j|) := by
    refine (hwi.add hgi).mono' ((hwi.aestronglyMeasurable.mul (continuous_abs.comp_aestronglyMeasurable hgj))) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (abs_nonneg _))]
    calc w x * |g x j| ≤ w x * (1 + euclideanSq (g x)) := mul_le_mul_of_nonneg_left (hbd1 x) (hw0 x)
      _ = w x + w x * euclideanSq (g x) := by ring
  have hi2 : Integrable (fun x => w x * |g x j| ^ 2) := by
    refine hgi.mono' ((hwi.aestronglyMeasurable.mul ((continuous_abs.comp_aestronglyMeasurable hgj).pow 2))) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hbd2 x) (hw0 x)
  have hcs := sq_integral_weight_mul_le hw0 hwi hi1 hi2
  rw [show ∫ x, w x = 1 from integral_heatKernel_mask q hρ'.ne', mul_one] at hcs
  have hle2 : ∫ x, w x * |g x j| ^ 2 ≤ ∫ x, w x * euclideanSq (g x) :=
    integral_mono hi2 hgi fun x => mul_le_mul_of_nonneg_left (hbd2 x) (hw0 x)
  have hsq : ∫ x, w x * |g x j| ≤ Real.sqrt (∫ x, w x * euclideanSq (g x)) :=
    Real.le_sqrt_of_sq_le (hcs.trans hle2)
  have hb : ‖∫ x, (1 - χ x) * heatKernel q ρ x * g x j‖ ≤ ∫ x, A * (w x * |g x j|) :=
    norm_integral_le_of_norm_le (hi1.const_mul A)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
  rw [integral_const_mul, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hsq hA0)

/-- **The mass of the cut-off Gaussian** is at least `1/2`. -/
theorem half_le_integral_cutoff_heatKernel {χ : Vec d → ℝ} {z : Vec d} {R ρ : ℝ} (hR : 0 ≤ R)
    (hρ : 0 < ρ) (hχc : Continuous χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hsmall : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (8 * ρ ^ 2)) ≤ 1 / 2) :
    1 / 2 ≤ ∫ x, χ x * heatKernel z ρ x := by
  have hΦi : Integrable (heatKernel z ρ) := integrable_heatKernel_mask z hρ.ne'
  have hmeas : MeasurableSet (ball z (R / 2)) := measurableSet_ball z (R / 2)
  have hsplit := integral_add_compl hmeas hΦi
  rw [integral_heatKernel_mask z hρ.ne'] at hsplit
  have htail := setIntegral_compl_ball_heatKernel_le z hρ.ne' (R / 2) (by linarith)
  have hin : ∫ x in ball z (R / 2), heatKernel z ρ x ≤ ∫ x, χ x * heatKernel z ρ x := by
    have hi : Integrable (fun x => χ x * heatKernel z ρ x) :=
      hΦi.mono' (hχc.aestronglyMeasurable.mul hΦi.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ01 x).1,
            abs_of_nonneg (heatKernel_pos z hρ x).le]
          exact mul_le_of_le_one_left (heatKernel_pos z hρ x).le (hχ01 x).2)
    calc ∫ x in ball z (R / 2), heatKernel z ρ x
        = ∫ x in ball z (R / 2), χ x * heatKernel z ρ x :=
          setIntegral_congr_fun hmeas fun x hx => by simp only [hχ1 x hx, one_mul]
      _ ≤ ∫ x, χ x * heatKernel z ρ x :=
          setIntegral_le_integral hi (Eventually.of_forall fun x =>
            mul_nonneg (hχ01 x).1 (heatKernel_pos z hρ x).le)
  linarith

/-- **The cut-off Gaussian average of a gradient** differs from the Gaussian average by the term
outside the cutoff. -/
theorem abs_integral_cutoff_grad_le_whole {χ : Vec d → ℝ} {g : Vec d → Vec d} {z q : Vec d}
    {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) (hχc : Continuous χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1) (hq : euclideanNorm (q - z) ≤ R / 4)
    (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun x => heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x)))
    (hgv : Integrable (fun x => heatKernel q ρ x • g x)) (j : Fin d) :
    |∫ x, χ x * heatKernel q ρ x * g x j| ≤
      |(∫ x, heatKernel q ρ x • g x) j| +
        (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (32 * ρ ^ 2)) *
          Real.sqrt (∫ x, heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x)) := by
  have hev : (∫ x, heatKernel q ρ x • g x) j = ∫ x, heatKernel q ρ x * g x j := by
    rw [eval_integral (fun k => hgv.eval k)]
    rfl
  have hj : Integrable (fun x => heatKernel q ρ x * g x j) := hgv.eval j
  have h1 : Integrable (fun x => χ x * heatKernel q ρ x * g x j) := by
    refine hj.norm.mono' ((hχc.aestronglyMeasurable).mul hj.aestronglyMeasurable |>.congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hχ01 x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 x).2
  have h2 : Integrable (fun x => (1 - χ x) * heatKernel q ρ x * g x j) :=
    (hj.sub h1).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ x, heatKernel q ρ x * g x j =
      (∫ x, χ x * heatKernel q ρ x * g x j) + ∫ x, (1 - χ x) * heatKernel q ρ x * g x j := by
    rw [← integral_add h1 h2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have ht := abs_integral_one_sub_cutoff_grad_le hR hρ hχ01 hχ1 hq hgm hgi j
  rw [hev]
  have : |∫ x, χ x * heatKernel q ρ x * g x j| ≤ |∫ x, heatKernel q ρ x * g x j| +
      |∫ x, (1 - χ x) * heatKernel q ρ x * g x j| := by
    rw [hsplit]
    have := abs_sub_abs_le_abs_sub (∫ x, χ x * heatKernel q ρ x * g x j)
      (-∫ x, (1 - χ x) * heatKernel q ρ x * g x j)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  linarith

/-- The Gaussian factor `Φ̂_ρ e^{-(R/2)²/(16ρ²)}` of the potential error terms. -/
def gaussTail (d : ℕ) (R ρ : ℝ) : ℝ := heatKernelPeak d ρ * Real.exp (-((R / 2) ^ 2) / (16 * ρ ^ 2))

/-- The Gaussian factor `2^{d/2} e^{-(R/2)²/(32ρ²)}` of the gradient error term. -/
def gaussTail' (d : ℕ) (R ρ : ℝ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (32 * ρ ^ 2))

theorem gaussTail_nonneg (d : ℕ) (R : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ gaussTail d R ρ :=
  mul_nonneg (heatKernelPeak_pos hρ.ne').le (Real.exp_pos _).le

theorem gaussTail'_nonneg (d : ℕ) (R ρ : ℝ) : 0 ≤ gaussTail' d R ρ := by
  unfold gaussTail'
  positivity

/-- `(∫_0^1 f)² ≤ ∫_0^1 f²` for a continuous `f`. -/
theorem sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, f t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, f t ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have h1 : ∫ _ in Set.Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal zero_le_one]
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) :=
    integrableOn_const (by simp) (by simp)
  have h := sq_integral_mul_le (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)) (g := f)
    (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) h1 hi
    ((hf.integrableOn_Ioc).congr_fun (fun t _ => by simp) measurableSet_Ioc)
    (((hf.pow 2).integrableOn_Ioc).congr_fun (fun t _ => by simp) measurableSet_Ioc)
  simpa using h

/-- **The squared truncated observation at a point of `B_{R₁}(z)`** by the segment integral of the
squared Gaussian gradient averages and the error terms. -/
theorem sq_truncated_observation_le {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hφl : LocallyIntegrable φ volume) (hφg : HasWeakGradient Set.univ φ g)
    (hgm : AEStronglyMeasurable g volume)
    (hgi : ∀ (q : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel q r x * euclideanSq (g x)))
    {z : Vec d} {R₁ R T ρ D c Eg W : ℝ} (hR₁ : 0 < R₁) (h4 : 4 * R₁ ≤ R) (hRT : R ≤ T)
    (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hgv : ∀ q : Vec d, Integrable (fun x => heatKernel q ρ x • g x))
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0) (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2)
    (hφT : MemLp φ 2 (volume.restrict (ball z T)))
    (hc : ∫ x, χ x * heatKernel z ρ x * (φ x - c) = 0)
    (hEg : ∀ q, euclideanNorm (q - z) ≤ R₁ →
      ∫ x, heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x) ≤ Eg)
    (hW : ∫ x in ball z T, (φ x - c) ^ 2 ≤ W) {y : Vec d} (hy : y ∈ ball z R₁) :
    (∫ x in ball z T, heatKernel y ρ x * (φ x - c)) ^ 2 ≤
      2 * R₁ ^ 2 * d * (∫ t in (0 : ℝ)..1,
          euclideanSq (∫ x, heatKernel (z + t • (y - z)) ρ x • g x)) +
        2 * (R₁ * (d * (gaussTail' d R ρ * Real.sqrt Eg +
          D / R * gaussTail d R ρ * Real.sqrt (volume.real (ball z R) * W))) +
          gaussTail d R ρ * Real.sqrt (volume.real (ball z T) * W)) ^ 2 := by
  have hR : 0 < R := by linarith
  set h := y - z with hh
  have hyh : z + h = y := by rw [hh]; abel
  have hhn : euclideanNorm h < R₁ := hy
  have hρ' : 0 < Real.sqrt 2 * ρ := by positivity
  set τ₁ := gaussTail' d R ρ * Real.sqrt Eg with hτ₁
  set τ₂ := D / R * gaussTail d R ρ * Real.sqrt (volume.real (ball z R) * W) with hτ₂
  set τ₃ := gaussTail d R ρ * Real.sqrt (volume.real (ball z T) * W) with hτ₃
  have hτ₁0 : 0 ≤ τ₁ := mul_nonneg (gaussTail'_nonneg d R ρ) (Real.sqrt_nonneg _)
  have hτ₂0 : 0 ≤ τ₂ :=
    mul_nonneg (mul_nonneg (by positivity) (gaussTail_nonneg d R hρ)) (Real.sqrt_nonneg _)
  have hτ₃0 : 0 ≤ τ₃ := mul_nonneg (gaussTail_nonneg d R hρ) (Real.sqrt_nonneg _)
  set G : ℝ → Vec d := fun t => ∫ x, heatKernel (z + t • h) ρ x • g x with hG
  have hGc : Continuous G :=
    (continuous_heatKernel_average hgm hρ fun p => hgi p _ hρ').comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hNc : Continuous fun t => euclideanNorm (G t) := euclideanNorm_continuous.comp hGc
  have hq : ∀ t ∈ Set.Icc (0 : ℝ) 1, euclideanNorm (z + t • h - z) ≤ R / 4 := fun t ht => by
    rw [add_sub_cancel_left, euclideanNorm_smul_of_zero_le t ht.1]
    have : t * euclideanNorm h ≤ 1 * euclideanNorm h :=
      mul_le_mul_of_nonneg_right ht.2 (zero_le_euclideanNorm h)
    linarith
  have hq₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, euclideanNorm (z + t • h - z) ≤ R₁ := fun t ht => by
    rw [add_sub_cancel_left, euclideanNorm_smul_of_zero_le t ht.1]
    have : t * euclideanNorm h ≤ 1 * euclideanNorm h :=
      mul_le_mul_of_nonneg_right ht.2 (zero_le_euclideanNorm h)
    linarith
  have hBT : ∫ x in ball z R, (φ x - c) ^ 2 ≤ W := by
    refine le_trans ?_ hW
    exact setIntegral_mono_set ((hφT.sub (memLp_const c)).integrable_sq)
      (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall fun x hx => lt_of_lt_of_le hx hRT)
  have hφR : MemLp φ 2 (volume.restrict (ball z R)) :=
    hφT.mono_measure (Measure.restrict_mono (fun x hx => lt_of_lt_of_le hx hRT) le_rfl)
  have hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      |∫ x, χ x * heatKernel (z + t • h) ρ x * g x j| ≤ |G t j| + τ₁ := fun t ht j => by
    have h1 := abs_integral_cutoff_grad_le_whole hR.le hρ hχ.continuous hχ01 hχ1 (hq t ht) hgm
      (hgi _ _ hρ') (hgv _) j
    have h2 : Real.sqrt (∫ x, heatKernel (z + t • h) (Real.sqrt 2 * ρ) x * euclideanSq (g x)) ≤
        Real.sqrt Eg := Real.sqrt_le_sqrt (hEg _ (hq₁ t ht))
    have h3 := mul_le_mul_of_nonneg_left h2 (gaussTail'_nonneg d R ρ)
    unfold gaussTail' at h3
    rw [hτ₁]
    unfold gaussTail'
    linarith
  have hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      |∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c)| ≤ τ₂ :=
    fun t ht j => by
      have h1 := abs_integral_cutoff_derivative_le (c := c) hR hD hρ hχ01 hχ1 hχR hχD
        (hq t ht) hφR j
      refine h1.trans ?_
      rw [hτ₂]
      unfold gaussTail
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) ?_
      · exact mul_le_mul_of_nonneg_left hBT measureReal_nonneg
      · have := (heatKernelPeak_pos (d := d) hρ.ne').le
        positivity
  have hy4 : euclideanNorm (z + h - z) ≤ R / 4 := by
    rw [add_sub_cancel_left]; linarith
  have h3 : |∫ x in ball z T, (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c)| ≤ τ₃ := by
    have h1 := abs_setIntegral_one_sub_cutoff_le (c := c) hR.le hρ hχ01 hχ1 hy4 hφT
    refine h1.trans ?_
    rw [hτ₃]
    unfold gaussTail
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hW measureReal_nonneg))
      (mul_nonneg (heatKernelPeak_pos hρ.ne').le (Real.exp_pos _).le)
  have hχT : ∀ x, x ∉ ball z T → χ x = 0 := fun x hx =>
    hχR x fun hxR => hx (lt_of_lt_of_le hxR hRT)
  have hmain := abs_truncated_observation_le hφl hφg hχ hχc hρ hχT hc G
    (hNc.intervalIntegrable 0 1) hA hB h3
  rw [hyh] at hmain
  -- Jensen on the segment
  have hJ := sq_intervalIntegral_le hNc
  have hJ' : ∫ t in (0 : ℝ)..1, euclideanNorm (G t) ^ 2 =
      ∫ t in (0 : ℝ)..1, euclideanSq (∫ x, heatKernel (z + t • h) ρ x • g x) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    show euclideanNorm (G t) ^ 2 = _
    rw [sq_euclideanNorm]
  rw [hJ'] at hJ
  set I := ∫ t in (0 : ℝ)..1, euclideanNorm (G t) with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg zero_le_one fun t _ =>
    zero_le_euclideanNorm _
  have hsd : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hn0 := zero_le_euclideanNorm h
  set A := Real.sqrt d * I with hA'
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) hI0
  set B := (d : ℝ) * (τ₁ + τ₂) with hB'
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg d) (add_nonneg hτ₁0 hτ₂0)
  set X := ∫ x in ball z T, heatKernel y ρ x * (φ x - c) with hX
  have hX1 : |X| ≤ R₁ * A + (R₁ * B + τ₃) := by
    have e1 : euclideanNorm h * A ≤ R₁ * A := mul_le_mul_of_nonneg_right hhn.le hA0
    have e2 : euclideanNorm h * B ≤ R₁ * B := mul_le_mul_of_nonneg_right hhn.le hB0
    linarith
  have hX2 : X ^ 2 ≤ (R₁ * A + (R₁ * B + τ₃)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hX1 2
  have hA2 : A ^ 2 ≤ d * ∫ t in (0 : ℝ)..1,
      euclideanSq (∫ x, heatKernel (z + t • h) ρ x • g x) := by
    rw [hA', mul_pow, hsd]
    exact mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg d)
  have hsq : (R₁ * A + (R₁ * B + τ₃)) ^ 2 ≤ 2 * (R₁ * A) ^ 2 + 2 * (R₁ * B + τ₃) ^ 2 := by
    nlinarith [sq_nonneg (R₁ * A - (R₁ * B + τ₃))]
  have hfin : 2 * (R₁ * A) ^ 2 ≤ 2 * R₁ ^ 2 * d * ∫ t in (0 : ℝ)..1,
      euclideanSq (∫ x, heatKernel (z + t • h) ρ x • g x) := by
    calc 2 * (R₁ * A) ^ 2 = 2 * R₁ ^ 2 * A ^ 2 := by ring
      _ ≤ 2 * R₁ ^ 2 * (d * ∫ t in (0 : ℝ)..1,
          euclideanSq (∫ x, heatKernel (z + t • h) ρ x • g x)) :=
          mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = _ := by ring
  exact hX2.trans (hsq.trans (add_le_add hfin le_rfl))

/-- **The Gaussian average of a gradient** differs from the cut-off average by the term outside
the cutoff. -/
theorem abs_integral_grad_le_cutoff {χ : Vec d → ℝ} {g : Vec d → Vec d} {z q : Vec d}
    {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) (hχc : Continuous χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1) (hq : euclideanNorm (q - z) ≤ R / 4)
    (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun x => heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x)))
    (hgv : Integrable (fun x => heatKernel q ρ x • g x)) (j : Fin d) :
    |(∫ x, heatKernel q ρ x • g x) j| ≤
      |∫ x, χ x * heatKernel q ρ x * g x j| +
        gaussTail' d R ρ * Real.sqrt (∫ x, heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x)) := by
  have hev : (∫ x, heatKernel q ρ x • g x) j = ∫ x, heatKernel q ρ x * g x j := by
    rw [eval_integral (fun k => hgv.eval k)]
    rfl
  have hj : Integrable (fun x => heatKernel q ρ x * g x j) := hgv.eval j
  have h1 : Integrable (fun x => χ x * heatKernel q ρ x * g x j) := by
    refine hj.norm.mono' ((hχc.aestronglyMeasurable).mul hj.aestronglyMeasurable |>.congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hχ01 x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 x).2
  have h2 : Integrable (fun x => (1 - χ x) * heatKernel q ρ x * g x j) :=
    (hj.sub h1).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ x, heatKernel q ρ x * g x j =
      (∫ x, χ x * heatKernel q ρ x * g x j) + ∫ x, (1 - χ x) * heatKernel q ρ x * g x j := by
    rw [← integral_add h1 h2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have ht := abs_integral_one_sub_cutoff_grad_le hR hρ hχ01 hχ1 hq hgm hgi j
  rw [hev, hsplit]
  unfold gaussTail'
  exact (abs_add_le _ _).trans (by linarith)

end QSH
