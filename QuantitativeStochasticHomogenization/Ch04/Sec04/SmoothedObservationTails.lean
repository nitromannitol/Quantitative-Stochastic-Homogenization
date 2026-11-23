import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationBound
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectorIndependence

/-!
# Deterministic bounds for the cut-off Gaussian observations

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the deterministic part of the observation of the smoothed correctors. Away from `B_R(z)` the
Gaussian `Φ_{p,ρ}` with `|p - z| ≤ R/2` is at most `e^{-R²/(16ρ²)}` times its peak, and at most
`2^{d/2} e^{-R²/(32ρ²)} Φ_{p,√2ρ}`. A cutoff `χ` of `B_R(z)` has vanishing derivative outside
`B_R(z)`, so by the weak gradient `∫ χ Φ_{p,ρ} ∂_jφ = -∫ (χ ∂_jΦ_{p,ρ} + ∂_jχ Φ_{p,ρ}) (φ - c)` is at
most `(sup |∂_jΦ_{p,ρ}| + (D/R) sup Φ_{p,ρ}) (|B_R| ∫_{B_R} (φ - c)²)^{1/2}`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `|x - p| ≥ R/2` for `x ∉ B_R(z)` and `|p - z| ≤ R/2`. -/
theorem half_le_euclideanNorm_sub_of_far {z p x : Vec d} {R : ℝ} (hx : x ∉ ball z R)
    (hp : euclideanNorm (p - z) ≤ R / 2) : R / 2 ≤ euclideanNorm (x - p) := by
  have hx' : R ≤ euclideanNorm (x - z) := not_lt.1 hx
  have h := euclideanNorm_sub_le_sub_add x z p
  linarith

theorem sq_le_euclideanSq_sub_of_far {z p x : Vec d} {R : ℝ} (hR : 0 ≤ R) (hx : x ∉ ball z R)
    (hp : euclideanNorm (p - z) ≤ R / 2) : R ^ 2 / 4 ≤ euclideanSq (x - p) := by
  have h := half_le_euclideanNorm_sub_of_far hx hp
  rw [← sq_euclideanNorm]
  have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / 2) h 2
  linarith [show (R / 2) ^ 2 = R ^ 2 / 4 by ring]

/-- **The Gaussian away from the ball** is at most `e^{-R²/(16ρ²)}` times its peak. -/
theorem heatKernel_le_peak_mul_exp_of_far {z p x : Vec d} {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hx : x ∉ ball z R) (hp : euclideanNorm (p - z) ≤ R / 2) :
    heatKernel p ρ x ≤ heatKernelPeak d ρ * Real.exp (-(R ^ 2) / (16 * ρ ^ 2)) := by
  rw [heatKernel_eq]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (heatKernelPeak_pos hρ.ne').le
  have h := sq_le_euclideanSq_sub_of_far hR hx hp
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The Gaussian away from the ball** is at most `2^{d/2} e^{-R²/(32ρ²)} Φ_{p,√2ρ}`. -/
theorem heatKernel_le_exp_mul_heatKernel_of_far {z p x : Vec d} {R ρ : ℝ} (hR : 0 ≤ R)
    (hρ : 0 < ρ) (hx : x ∉ ball z R) (hp : euclideanNorm (p - z) ≤ R / 2) :
    heatKernel p ρ x ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(R ^ 2) / (32 * ρ ^ 2)) *
        heatKernel p (Real.sqrt 2 * ρ) x := by
  have h := sq_le_euclideanSq_sub_of_far hR hx hp
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [heatKernel_eq, heatKernel_eq, heatKernelPeak_eq_mul_sqrt_two d ρ]
  have hs : (Real.sqrt 2 * ρ) ^ 2 = 2 * ρ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs]
  have e : Real.exp (-euclideanSq (x - p) / (4 * ρ ^ 2)) =
      Real.exp (-euclideanSq (x - p) / (8 * ρ ^ 2)) *
        Real.exp (-euclideanSq (x - p) / (4 * (2 * ρ ^ 2))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h1 : Real.exp (-euclideanSq (x - p) / (8 * ρ ^ 2)) ≤
      Real.exp (-(R ^ 2) / (32 * ρ ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [e]
  have hP : 0 ≤ heatKernelPeak d (Real.sqrt 2 * ρ) :=
    (heatKernelPeak_pos (by positivity : Real.sqrt 2 * ρ ≠ 0)).le
  have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := by positivity
  have h3 : 0 ≤ Real.exp (-euclideanSq (x - p) / (4 * (2 * ρ ^ 2))) := (Real.exp_pos _).le
  calc 2 ^ ((d : ℝ) / 2) * heatKernelPeak d (Real.sqrt 2 * ρ) *
        (Real.exp (-euclideanSq (x - p) / (8 * ρ ^ 2)) *
          Real.exp (-euclideanSq (x - p) / (4 * (2 * ρ ^ 2))))
      ≤ 2 ^ ((d : ℝ) / 2) * heatKernelPeak d (Real.sqrt 2 * ρ) *
        (Real.exp (-(R ^ 2) / (32 * ρ ^ 2)) *
          Real.exp (-euclideanSq (x - p) / (4 * (2 * ρ ^ 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h3) (mul_nonneg h2 hP)
    _ = _ := by ring

/-- A nonnegative smooth function vanishing at `x` has vanishing derivative at `x`. -/
theorem coordinateDerivative_eq_zero_of_nonneg_of_eq_zero {χ : Vec d → ℝ}
    (h0 : ∀ x, 0 ≤ χ x) {x : Vec d} (hx : χ x = 0) (j : Fin d) :
    coordinateDerivative j χ x = 0 := by
  have hmin : IsLocalMin χ x := Eventually.of_forall fun y => by rw [hx]; exact h0 y
  rw [coordinateDerivative, hmin.fderiv_eq_zero]
  rfl

/-- **The cut-off Gaussian average of a gradient** by the oscillation of the potential on the
ball of the cutoff. -/
theorem abs_integral_cutoff_heatKernel_mul_grad_le {χ φ : Vec d → ℝ} {g : Vec d → Vec d}
    {z : Vec d} {R D ρ : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0) (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2)
    (hφl : LocallyIntegrable φ volume) (hφg : HasWeakGradient Set.univ φ g) (c : ℝ)
    (hφ2 : MemLp φ 2 (volume.restrict (ball z R))) (p : Vec d) (j : Fin d) :
    |∫ x, χ x * heatKernel p ρ x * g x j| ≤
      ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) +
        D / R * heatKernelPeak d ρ) *
      Real.sqrt (volume.real (ball z R) * ∫ x in ball z R, (φ x - c) ^ 2) := by
  set K := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) +
    D / R * heatKernelPeak d ρ with hK
  have hfl : LocallyIntegrable (fun x => φ x - c) volume := hφl.sub (locallyIntegrable_const c)
  have hfg : HasWeakGradient Set.univ (fun x => φ x - c) g := hφg.sub_const c
  have hw := neg_integral_cutoff_mul_coordinateDerivative_heatKernel hχ hχc hfg ρ p j
  set F : Vec d → ℝ := fun x => χ x * coordinateDerivative j (heatKernel p ρ) x +
    coordinateDerivative j χ x * heatKernel p ρ x with hF
  have hΦ := contDiff_heatKernel p ρ
  have hi1 : Integrable (fun x => χ x * (φ x - c) * coordinateDerivative j (heatKernel p ρ) x) :=
    (integrable_mul_of_compact hfl
      (hχ.continuous.mul (hΦ.continuous_fderiv (by simp) |>.clm_apply continuous_const))
      hχc.mul_right).congr (Eventually.of_forall fun x =>
        (by ring : χ x * coordinateDerivative j (heatKernel p ρ) x * (φ x - c) =
          χ x * (φ x - c) * coordinateDerivative j (heatKernel p ρ) x))
  have hi2 : Integrable (fun x => coordinateDerivative j χ x * heatKernel p ρ x * (φ x - c)) :=
    integrable_mul_of_compact hfl
      ((hχ.continuous_fderiv (by simp) |>.clm_apply continuous_const).mul hΦ.continuous)
      ((hχc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector j))
        (by simp) |>.mul_right)
  have heq : ∫ x, χ x * heatKernel p ρ x * g x j = -∫ x, F x * (φ x - c) := by
    have e1 : ∫ x, F x * (φ x - c) =
        (∫ x, χ x * (φ x - c) * coordinateDerivative j (heatKernel p ρ) x) +
          ∫ x, coordinateDerivative j χ x * heatKernel p ρ x * (φ x - c) := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hF]; ring)
    rw [e1]
    linarith
  -- the integrand vanishes outside the ball
  have hout : ∀ x, x ∉ ball z R → F x * (φ x - c) = 0 := fun x hx => by
    have h0 := hχR x hx
    have h1 := coordinateDerivative_eq_zero_of_nonneg_of_eq_zero (fun y => (hχ01 y).1) h0 j
    simp only [hF, h0, h1]
    ring
  have hset : ∫ x, F x * (φ x - c) = ∫ x in ball z R, F x * (φ x - c) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
  -- the pointwise bound of `F`
  have hFb : ∀ x, |F x| ≤ K := fun x => by
    have h1 := abs_coordinateDerivative_heatKernel_le hρ p j x
    have h2 : |coordinateDerivative j χ x| ≤ D / R := by
      have := abs_coord_le_euclideanNorm (gradient χ x) j
      have hn : euclideanNorm (gradient χ x) ≤ D / R := by
        rw [euclideanNorm]
        calc Real.sqrt (euclideanSq (gradient χ x)) ≤ Real.sqrt ((D / R) ^ 2) :=
              Real.sqrt_le_sqrt (hχD x)
          _ = D / R := Real.sqrt_sq (by positivity)
      exact this.trans hn
    have h3 : heatKernel p ρ x ≤ heatKernelPeak d ρ := by
      rw [heatKernel_eq]
      have : Real.exp (-euclideanSq (x - p) / (4 * ρ ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (zero_le_euclideanSq _)) (by positivity)
      calc heatKernelPeak d ρ * Real.exp (-euclideanSq (x - p) / (4 * ρ ^ 2))
          ≤ heatKernelPeak d ρ * 1 :=
            mul_le_mul_of_nonneg_left this (heatKernelPeak_pos hρ.ne').le
        _ = _ := mul_one _
    have h4 : 0 ≤ heatKernel p ρ x := (heatKernel_pos p hρ x).le
    simp only [hF]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hχ01 x).1, abs_of_nonneg h4]
    have hc1 : χ x * |coordinateDerivative j (heatKernel p ρ) x| ≤
        (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) :=
      (mul_le_mul_of_nonneg_right (hχ01 x).2 (abs_nonneg _)).trans (by rw [one_mul]; exact h1)
    have hc2 : |coordinateDerivative j χ x| * heatKernel p ρ x ≤ D / R * heatKernelPeak d ρ :=
      mul_le_mul h2 h3 h4 (by positivity)
    linarith
  have hfB : MemLp (fun x => φ x - c) 2 (volume.restrict (ball z R)) := hφ2.sub (memLp_const c)
  have hBf : volume (ball z R) < ⊤ := volume_ball_lt_top z R
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBf⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hFb 0)
  have hbound : ‖∫ x in ball z R, F x * (φ x - c)‖ ≤ ∫ x in ball z R, K * |φ x - c| :=
    norm_integral_le_of_norm_le (((hfB.integrable one_le_two).abs).const_mul K)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hFb x) (abs_nonneg _))
  rw [integral_const_mul, Real.norm_eq_abs] at hbound
  rw [heq, abs_neg, hset]
  exact hbound.trans (mul_le_mul_of_nonneg_left (setIntegral_abs_le_sqrt hBf hfB) hK0)

end QSH
