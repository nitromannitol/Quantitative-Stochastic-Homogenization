import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationDeterministic
import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevSublinear

/-!
# Gaussian energies from energies on balls around a center

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (SCOTT-localization (5)). The shell decomposition of the heat kernel
(`integral_heatKernel_mul_le_of_ball`) at the center `z`: if `∫_{B_R(z)} f ≤ M R^d` for `R ≥ X ≥ 1`,
then `∫ Φ_{z,ρ} f ≤ K_d M X^d` for `ρ ≥ 1`. With the moving of the center, for `|q - z| ≤ R₁`,
`∫ Φ_{q,ρ} f ≤ 2^{d/2} e^{R₁²/(4ρ²)} K_d M X^d` for `ρ ≥ 1`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem heatKernel_add_right (z : Vec d) (ρ : ℝ) (x : Vec d) :
    heatKernel z ρ (x + z) = heatKernel 0 ρ x := by
  simp only [heatKernel_eq_comp_sub, add_sub_cancel_right, sub_zero]

/-- **Gaussian averages at the center `z`** from energies on the balls centered at `z`. -/
theorem integral_heatKernel_mul_le_of_ball_center {f : Vec d → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {M X : ℝ} (hM0 : 0 ≤ M) (hX : 1 ≤ X) (z : Vec d)
    (hball : ∀ R : ℝ, X ≤ R →
      ∫⁻ y in ball z R, ENNReal.ofReal (f y) ≤ ENNReal.ofReal (M * R ^ d))
    {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∫ x, heatKernel z ρ x * f x ≤ gaussianBallConstant d * M * X ^ d := by
  have hball' : ∀ R : ℝ, X ≤ R →
      ∫⁻ y in ball 0 R, ENNReal.ofReal (f (y + z)) ≤ ENNReal.ofReal (M * R ^ d) := by
    intro R hR
    have hpre : ball (0 : Vec d) R = (fun x => x + z) ⁻¹' ball z R := by
      ext x
      simp only [ball, Set.mem_setOf_eq, Set.mem_preimage, add_sub_cancel_right, sub_zero]
    rw [hpre]
    calc ∫⁻ y in (fun x => x + z) ⁻¹' ball z R, ENNReal.ofReal (f (y + z))
        = ∫⁻ y in ball z R, ENNReal.ofReal (f y) :=
          (measurePreserving_add_right volume z).setLIntegral_comp_preimage
            (measurableSet_ball z R) (ENNReal.measurable_ofReal.comp hfm)
      _ ≤ _ := hball R hR
  have h := integral_heatKernel_mul_le_of_ball (f := fun x => f (x + z))
    (hfm.comp (measurable_id.add_const z)) (fun x => hf0 _) hM0 hX hball' hρ
  have e : ∫ x, heatKernel 0 ρ x * f (x + z) = ∫ x, heatKernel z ρ x * f x := by
    rw [← integral_add_right_eq_self (μ := volume) (fun x => heatKernel z ρ x * f x) z]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [heatKernel_add_right]
  rw [← e]
  exact h

/-- **Gaussian averages near the center `z`** from energies on the balls centered at `z`. -/
theorem integral_heatKernel_mul_le_of_ball_near {f : Vec d → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {M X : ℝ} (hM0 : 0 ≤ M) (hX : 1 ≤ X) (z : Vec d)
    (hball : ∀ R : ℝ, X ≤ R →
      ∫⁻ y in ball z R, ENNReal.ofReal (f y) ≤ ENNReal.ofReal (M * R ^ d))
    {ρ R₁ : ℝ} (hρ : 1 ≤ ρ) {q : Vec d} (hq : euclideanNorm (q - z) ≤ R₁)
    (hfi : Integrable (fun x => heatKernel q ρ x * f x))
    (hzi : Integrable (fun x => heatKernel z (Real.sqrt 2 * ρ) x * f x)) :
    ∫ x, heatKernel q ρ x * f x ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (R₁ ^ 2 / (4 * ρ ^ 2)) *
        (gaussianBallConstant d * M * X ^ d) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hρ' : 1 ≤ Real.sqrt 2 * ρ := by
    have : 1 ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  set A : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (R₁ ^ 2 / (4 * ρ ^ 2)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hle : ∀ x, heatKernel q ρ x * f x ≤ A * (heatKernel z (Real.sqrt 2 * ρ) x * f x) := by
    intro x
    have h1 := heatKernel_le_shift q z x hρ0
    have hsq : euclideanSq (q - z) ≤ R₁ ^ 2 := by
      rw [← sq_euclideanNorm]
      exact pow_le_pow_left₀ (zero_le_euclideanNorm _) hq 2
    have h2 : Real.exp (euclideanSq (q - z) / (4 * ρ ^ 2)) ≤ Real.exp (R₁ ^ 2 / (4 * ρ ^ 2)) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right hsq (by positivity))
    have h3 : heatKernel q ρ x ≤ A * heatKernel z (Real.sqrt 2 * ρ) x := by
      refine h1.trans ?_
      rw [hA]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity))
        (heatKernel_pos z (mul_pos (Real.sqrt_pos.2 two_pos) hρ0) x).le
    calc heatKernel q ρ x * f x ≤ (A * heatKernel z (Real.sqrt 2 * ρ) x) * f x :=
          mul_le_mul_of_nonneg_right h3 (hf0 x)
      _ = _ := by ring
  have hz := integral_heatKernel_mul_le_of_ball_center hfm hf0 hM0 hX z hball hρ'
  calc ∫ x, heatKernel q ρ x * f x ≤ ∫ x, A * (heatKernel z (Real.sqrt 2 * ρ) x * f x) :=
        integral_mono hfi (hzi.const_mul A) hle
    _ = A * ∫ x, heatKernel z (Real.sqrt 2 * ρ) x * f x := integral_const_mul _ _
    _ ≤ A * (gaussianBallConstant d * M * X ^ d) := mul_le_mul_of_nonneg_left hz hA0

theorem euclideanNorm_le_sqrt_mul_of_coord_le {v : Vec d} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j, |v j| ≤ M) : euclideanNorm v ≤ Real.sqrt d * M := by
  have hs : euclideanSq v ≤ d * M ^ 2 := by
    have : euclideanSq v = ∑ j, v j ^ 2 := by simp [euclideanSq, dot, sq]
    rw [this]
    calc ∑ j, v j ^ 2 ≤ ∑ _j : Fin d, M ^ 2 := Finset.sum_le_sum fun j _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
      _ = d * M ^ 2 := by simp
  rw [euclideanNorm]
  calc Real.sqrt (euclideanSq v) ≤ Real.sqrt (d * M ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt d * M := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hM]

/-- **The oscillation around the cut-off Gaussian mean** on `B_T(z)` from the oscillation around
any constant: `∫_{B_T} (φ - c)² ≤ 2 V + 8 Φ̂_ρ² |B_T|² V`. -/
theorem integral_sub_cutoffMean_sq_le {φ χ : Vec d → ℝ} {z : Vec d} {R T ρ c₀ V : ℝ}
    (hR : 0 ≤ R) (hRT : R ≤ T) (hρ : 0 < ρ) (hχc : Continuous χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0)
    (hsmall : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (8 * ρ ^ 2)) ≤ 1 / 2)
    (hφT : MemLp φ 2 (volume.restrict (ball z T)))
    (hV : ∫ x in ball z T, (φ x - c₀) ^ 2 ≤ V) :
    ∫ x in ball z T,
        (φ x - (∫ y, χ y * heatKernel z ρ y * φ y) / ∫ y, χ y * heatKernel z ρ y) ^ 2 ≤
      2 * V + 8 * heatKernelPeak d ρ ^ 2 * volume.real (ball z T) ^ 2 * V := by
  set m := ∫ y, χ y * heatKernel z ρ y with hm
  set c := (∫ y, χ y * heatKernel z ρ y * φ y) / m with hc
  have hm2 : 1 / 2 ≤ m := half_le_integral_cutoff_heatKernel hR hρ hχc hχ01 hχ1 hsmall
  have hm0 : 0 < m := by linarith
  have hP := (heatKernelPeak_pos (d := d) hρ.ne').le
  have hBT := (measureReal_nonneg : 0 ≤ volume.real (ball z T))
  have hV0 : 0 ≤ V := (integral_nonneg fun x => sq_nonneg _).trans hV
  have hf0 : MemLp (fun x => φ x - c₀) 2 (volume.restrict (ball z T)) := hφT.sub (memLp_const c₀)
  -- the cut-off integral against `φ - c₀`
  have hout : ∀ x, x ∉ ball z T → χ x * heatKernel z ρ x * (φ x - c₀) = 0 := fun x hx => by
    rw [hχR x fun h => hx (lt_of_lt_of_le h hRT)]; ring
  have hχΦ : ∀ x, |χ x * heatKernel z ρ x| ≤ heatKernelPeak d ρ := fun x => by
    rw [abs_mul, abs_of_nonneg (hχ01 x).1, abs_of_nonneg (heatKernel_pos z hρ x).le]
    calc χ x * heatKernel z ρ x ≤ 1 * heatKernel z ρ x :=
          mul_le_mul_of_nonneg_right (hχ01 x).2 (heatKernel_pos z hρ x).le
      _ ≤ heatKernelPeak d ρ := by
          rw [one_mul, heatKernel_eq]
          have : Real.exp (-euclideanSq (x - z) / (4 * ρ ^ 2)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (zero_le_euclideanSq _))
              (by positivity)
          nlinarith
  haveI : IsFiniteMeasure (volume.restrict (ball z T)) :=
    isFiniteMeasure_restrict.2 (volume_ball_lt_top z T).ne
  have hI : |∫ x, χ x * heatKernel z ρ x * (φ x - c₀)| ≤
      heatKernelPeak d ρ * Real.sqrt (volume.real (ball z T) * V) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    have hb : ‖∫ x in ball z T, χ x * heatKernel z ρ x * (φ x - c₀)‖ ≤
        ∫ x in ball z T, heatKernelPeak d ρ * |φ x - c₀| :=
      norm_integral_le_of_norm_le (((hf0.integrable one_le_two).abs).const_mul _)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hχΦ x) (abs_nonneg _))
    rw [integral_const_mul, Real.norm_eq_abs] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hP)
    exact (setIntegral_abs_le_sqrt (volume_ball_lt_top z T) hf0).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hV hBT))
  -- `c - c₀` from the cut-off integral
  have hφl : Integrable (fun x => χ x * heatKernel z ρ x * φ x) := by
    have hi : IntegrableOn (fun x => χ x * heatKernel z ρ x * φ x) (ball z T) := by
      refine (((hφT.integrable one_le_two).norm).const_mul (heatKernelPeak d ρ)).mono' ?_ ?_
      · exact ((hχc.mul (contDiff_heatKernel z ρ).continuous).aestronglyMeasurable).mul
          (hφT.integrable one_le_two).aestronglyMeasurable
      · exact Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hχΦ x) (abs_nonneg _)
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hi
    intro x hx
    by_contra hxT
    have h0 : χ x = 0 := hχR x fun h => hxT (lt_of_lt_of_le h hRT)
    exact hx (show χ x * heatKernel z ρ x * φ x = 0 by rw [h0]; ring)
  have hΦi : Integrable (fun x => χ x * heatKernel z ρ x) :=
    (integrable_heatKernel_mask z hρ.ne').mono'
      (hχc.aestronglyMeasurable.mul (contDiff_heatKernel z ρ).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ01 x).1,
          abs_of_nonneg (heatKernel_pos z hρ x).le]
        exact mul_le_of_le_one_left (heatKernel_pos z hρ x).le (hχ01 x).2)
  have hdiff : ∫ x, χ x * heatKernel z ρ x * (φ x - c₀) = (c - c₀) * m := by
    have e : (fun x => χ x * heatKernel z ρ x * (φ x - c₀)) =
        fun x => χ x * heatKernel z ρ x * φ x - c₀ * (χ x * heatKernel z ρ x) := by
      funext x; ring
    rw [e, integral_sub hφl (hΦi.const_mul c₀), integral_const_mul, hc, sub_mul,
      div_mul_cancel₀ _ hm0.ne']
  have hcc : |c - c₀| ≤ 2 * (heatKernelPeak d ρ * Real.sqrt (volume.real (ball z T) * V)) := by
    have h1 : |c - c₀| * m ≤ heatKernelPeak d ρ * Real.sqrt (volume.real (ball z T) * V) := by
      have h := hI
      rw [hdiff, abs_mul, abs_of_pos hm0] at h
      exact h
    have h2 : |c - c₀| * (1 / 2) ≤ |c - c₀| * m := mul_le_mul_of_nonneg_left hm2 (abs_nonneg _)
    linarith
  -- the oscillation around `c`
  have hpt : ∀ x, (φ x - c) ^ 2 ≤ 2 * (φ x - c₀) ^ 2 + 2 * (c - c₀) ^ 2 := fun x => by
    nlinarith [sq_nonneg (φ x - c₀ + (c - c₀))]
  have hi1 : Integrable (fun x => (φ x - c) ^ 2) (volume.restrict (ball z T)) :=
    (hφT.sub (memLp_const c)).integrable_sq
  have hi2 : Integrable (fun x => 2 * (φ x - c₀) ^ 2 + 2 * (c - c₀) ^ 2)
      (volume.restrict (ball z T)) := (hf0.integrable_sq.const_mul 2).add (integrable_const _)
  have hmono := integral_mono hi1 hi2 hpt
  rw [integral_add (hf0.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul,
    setIntegral_const, smul_eq_mul] at hmono
  have hsq : (c - c₀) ^ 2 ≤ 4 * (heatKernelPeak d ρ ^ 2 * (volume.real (ball z T) * V)) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hcc 2
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hBT hV0)] at h
    linarith
  have e1 : 2 * (∫ x in ball z T, (φ x - c₀) ^ 2) ≤ 2 * V := by linarith
  have e2 : volume.real (ball z T) * (2 * (c - c₀) ^ 2) ≤
      volume.real (ball z T) * (2 * (4 * (heatKernelPeak d ρ ^ 2 * (volume.real (ball z T) * V)))) :=
    mul_le_mul_of_nonneg_left (by linarith) hBT
  calc ∫ x in ball z T, (φ x - c) ^ 2
      ≤ 2 * (∫ x in ball z T, (φ x - c₀) ^ 2) + volume.real (ball z T) * (2 * (c - c₀) ^ 2) :=
        hmono
    _ ≤ 2 * V + volume.real (ball z T) *
        (2 * (4 * (heatKernelPeak d ρ ^ 2 * (volume.real (ball z T) * V)))) := by linarith
    _ = 2 * V + 8 * heatKernelPeak d ρ ^ 2 * volume.real (ball z T) ^ 2 * V := by ring

/-- **The Gaussian average of a gradient near `z`** by the oscillation of the potential on the ball
of the cutoff and the Gaussian energy. -/
theorem euclideanNorm_heatKernel_average_le {φ χ : Vec d → ℝ} {g : Vec d → Vec d} {z p : Vec d}
    {R ρ D c₀ V Eg : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (hρ : 0 < ρ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1) (hχR : ∀ x, x ∉ ball z R → χ x = 0)
    (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2)
    (hφl : LocallyIntegrable φ volume) (hφg : HasWeakGradient Set.univ φ g)
    (hφR : MemLp φ 2 (volume.restrict (ball z R))) (hV : ∫ x in ball z R, (φ x - c₀) ^ 2 ≤ V)
    (hgm : AEStronglyMeasurable g volume) (hp : euclideanNorm (p - z) ≤ R / 4)
    (hgi : Integrable (fun x => heatKernel p (Real.sqrt 2 * ρ) x * euclideanSq (g x)))
    (hEg : ∫ x, heatKernel p (Real.sqrt 2 * ρ) x * euclideanSq (g x) ≤ Eg)
    (hgv : Integrable (fun x => heatKernel p ρ x • g x)) :
    euclideanNorm (∫ x, heatKernel p ρ x • g x) ≤
      Real.sqrt d * (((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) +
        D / R * heatKernelPeak d ρ) * Real.sqrt (volume.real (ball z R) * V) +
          gaussTail' d R ρ * Real.sqrt Eg) := by
  have hK0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) +
      D / R * heatKernelPeak d ρ :=
    add_nonneg (mul_nonneg (mul_nonneg (by positivity) (div_nonneg (by norm_num) hρ.le))
      (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg (div_nonneg hD hR.le) (heatKernelPeak_pos (d := d) hρ.ne').le)
  refine euclideanNorm_le_sqrt_mul_of_coord_le (add_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg _))
    (mul_nonneg (gaussTail'_nonneg d R ρ) (Real.sqrt_nonneg _))) fun j => ?_
  have h1 := abs_integral_grad_le_cutoff hR.le hρ hχ.continuous hχ01 hχ1 hp hgm hgi hgv j
  have h2 := abs_integral_cutoff_heatKernel_mul_grad_le hR hD hρ hχ hχc hχ01 hχR hχD hφl hφg c₀
    hφR p j
  have h3 : Real.sqrt (volume.real (ball z R) * ∫ x in ball z R, (φ x - c₀) ^ 2) ≤
      Real.sqrt (volume.real (ball z R) * V) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hV measureReal_nonneg)
  have h4 : Real.sqrt (∫ x, heatKernel p (Real.sqrt 2 * ρ) x * euclideanSq (g x)) ≤
      Real.sqrt Eg := Real.sqrt_le_sqrt hEg
  have h5 := mul_le_mul_of_nonneg_left h3 hK0
  have h6 := mul_le_mul_of_nonneg_left h4 (gaussTail'_nonneg d R ρ)
  linarith

end QSH
