import QuantitativeStochasticHomogenization.Ch03.Sec04.GaussianSublinearity
import QuantitativeStochasticHomogenization.Ch03.Sec04.GaussianTestExtension
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientCentering
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatAverageDecay
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatGradientWindow
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianL2

/-!
# Gaussian averages of a sublinear corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 3.21, the deterministic part. Let `u` have weak gradient `g`, and suppose that above a
scale `Y` the normalized `L²` oscillation of `u` on `B_ρ` is at most `C ρ^{1-θ} Y^θ` and the
normalized energy of `g` is at most `C²`. Then for `r ≥ Y` and `|x₀| ≤ r`:

* `abs_integral_heatKernel_grad_le`: `|∫ Φ_{x₀,r} ∂ₖu| ≤ C_d C (Y/r)^θ`, writing
  `∫ Φ ∂ₖu = -∫ (u - c) ∂ₖΦ` with `c = (u)_{B_r}`;
* `abs_integral_heatKernel_dot_le`: for a weakly divergence-free field `q` with
  `∫_{B_R} |q|² ≤ M_q R^d` (`R ≥ r`), `|∫ Φ_{x₀,r} q · ∇u| ≤ C_d √M_q C (Y/r)^θ`, writing
  `∫ Φ q · ∇u = -∫ (u - c) q · ∇Φ`;
* `abs_integral_heatKernel_le_of_pairing`: a field with a pairing bound above `R₀` has Gaussian
  averages at most `C A (R₀/r)^κ` (`exists_heatConv_le`).
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Elementary facts -/

theorem aestronglyMeasurable_of_forall_ball {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] {f : Vec d → E}
    (hf : ∀ R : ℝ, 0 < R → AEStronglyMeasurable f (volume.restrict (ball 0 R))) :
    AEStronglyMeasurable f volume := by
  have hU : (⋃ n : ℕ, ball (0 : Vec d) ((n : ℝ) + 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm (x - 0))
    exact ⟨n, show euclideanNorm (x - 0) < (n : ℝ) + 1 by linarith⟩
  have h := aestronglyMeasurable_iUnion_iff.mpr fun n : ℕ => hf ((n : ℝ) + 1) (by positivity)
  rwa [hU, Measure.restrict_univ] at h

theorem contDiff_heatKernel (x₀ : Vec d) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (heatKernel x₀ r) :=
  (contDiff_euclideanHeatKernel_top (r ^ 2)).comp (contDiff_id.sub contDiff_const)

theorem coordinateDerivative_heatKernel (x₀ : Vec d) (r : ℝ) (k : Fin d) (x : Vec d) :
    coordinateDerivative k (heatKernel x₀ r) x =
      coordinateDerivative k (euclideanHeatKernel (r ^ 2)) (x - x₀) := by
  unfold coordinateDerivative heatKernel
  rw [fderiv_comp_sub]

theorem abs_coordinateDerivative_heatKernel_le {r : ℝ} (hr : 0 < r) (x₀ : Vec d) (k : Fin d)
    (x : Vec d) :
    |coordinateDerivative k (heatKernel x₀ r) x| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / r) * euclideanHeatKernel (2 * r ^ 2) (x - x₀) := by
  rw [coordinateDerivative_heatKernel]
  have h := abs_heatGrad_le (d := d) (by positivity : 0 < r ^ 2) k (x - x₀)
  rwa [Real.sqrt_sq hr.le] at h

theorem heatKernel_le_two_mul {r : ℝ} (hr : 0 < r) (x₀ x : Vec d) :
    heatKernel x₀ r x ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * r ^ 2) (x - x₀) := by
  have h := euclideanHeatKernel_le_mul (d := d) (by positivity : 0 < r ^ 2)
    (by nlinarith : r ^ 2 ≤ 2 * r ^ 2) (x - x₀)
  rwa [show 2 * r ^ 2 / r ^ 2 = 2 by field_simp] at h

theorem integrable_euclideanHeatKernel_sub_right {s : ℝ} (hs : 0 < s) (x₀ : Vec d) :
    Integrable fun y => euclideanHeatKernel s (y - x₀) :=
  (integrable_euclideanHeatKernel hs).comp_sub_right x₀

theorem integral_euclideanHeatKernel_sub' {s : ℝ} (hs : 0 < s) (x₀ : Vec d) :
    ∫ y, euclideanHeatKernel s (y - x₀) = 1 := by
  rw [integral_sub_right_eq_self (fun z => euclideanHeatKernel s z) x₀]
  exact integral_euclideanHeatKernel hs

/-- **Jensen against a Gaussian**: `Φ f` is integrable and `|∫ Φ f| ≤ (∫ Φ f²)^{1/2}`. -/
theorem integrable_and_abs_integral_heat_le {s : ℝ} (hs : 0 < s) (x₀ : Vec d) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hf2 : Integrable fun y => euclideanHeatKernel s (y - x₀) * f y ^ 2) :
    Integrable (fun y => euclideanHeatKernel s (y - x₀) * f y) ∧
      ∫ y, euclideanHeatKernel s (y - x₀) * |f y| ≤
        Real.sqrt (∫ y, euclideanHeatKernel s (y - x₀) * f y ^ 2) := by
  have hw0 : ∀ y, 0 ≤ euclideanHeatKernel s (y - x₀) := fun y =>
    euclideanHeatKernel_nonneg hs.le _
  have hwm : AEStronglyMeasurable (fun y => euclideanHeatKernel s (y - x₀)) volume :=
    (integrable_euclideanHeatKernel_sub_right hs x₀).aestronglyMeasurable
  have h1 : Integrable fun y => euclideanHeatKernel s (y - x₀) * (1 : ℝ) ^ 2 := by
    simpa using integrable_euclideanHeatKernel_sub_right hs x₀
  have hA := integrable_and_abs_integral_weight_mul_le hw0 hwm hf aestronglyMeasurable_const
    hf2 h1
  have hB := integrable_and_abs_integral_weight_mul_le hw0 hwm hf.norm aestronglyMeasurable_const
    (hf2.congr (Eventually.of_forall fun y => by simp [sq_abs])) h1
  simp only [mul_one, one_pow, Real.norm_eq_abs] at hA hB
  rw [integral_euclideanHeatKernel_sub' hs x₀, Real.sqrt_one, mul_one] at hB
  refine ⟨hA.1, (le_abs_self _).trans (hB.2.trans (le_of_eq ?_))⟩
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y => by simp [sq_abs])

theorem rpow_one_sub_mul_rpow_eq {ρ Y θ : ℝ} (hρ : 0 < ρ) (hY : 0 ≤ Y) :
    ρ ^ (1 - θ) * Y ^ θ = ρ * (Y / ρ) ^ θ := by
  rw [Real.rpow_sub hρ, Real.rpow_one, Real.div_rpow hY hρ.le]
  have : 0 < ρ ^ θ := Real.rpow_pos_of_pos hρ θ
  field_simp

/-! ## Growth of the centered corrector -/

/-- **Growth of the centered corrector.** Under the oscillation bound above `Y`, for `r ≥ Y` and
`c = (u)_{B_r}`, `∫_{B_R} (u - c)² ≤ C_d C² ((Y/r)^θ)² |B_1| R^{d+2}` for `R ≥ r`. -/
theorem growth_sub_mean_of_osc {u : Vec d → ℝ}
    (huL : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) {Y Cφ θ : ℝ} (hY : 0 < Y)
    (hθ : 0 ≤ θ)
    (hosc : ∀ ρ : ℝ, Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ,
      |u x - ⨍ y in ball 0 ρ, u y| ^ 2) ≤ Cφ * ρ ^ (1 - θ) * Y ^ θ)
    (hCφ : 0 ≤ Cφ) {r : ℝ} (hr : Y ≤ r) (R : ℝ) (hR : r ≤ R) :
    IntegrableOn (fun y => (u y - ⨍ x in ball 0 r, u x) ^ 2) (ball 0 R) ∧
      ∫ y in ball 0 R, (u y - ⨍ x in ball 0 r, u x) ^ 2 ≤
        dyadicOscConst d * (Cφ ^ 2 * ((Y / r) ^ θ) ^ 2) * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal * R ^ (d + 2) := by
  have hr0 : 0 < r := hY.trans_le hr
  have hR0 : 0 < R := hr0.trans_le hR
  refine ⟨((huL R hR0).sub (memLp_const _)).integrable_sq, ?_⟩
  refine integral_sq_sub_mean_le_of_osc huL hr0 (by positivity) (fun ρ hρ => ?_) hR
  have hρ0 : 0 < ρ := hr0.trans_le hρ
  have h := hosc ρ (hr.trans hρ)
  have hA0 : 0 ≤ ⨍ x in ball 0 ρ, (u x - ⨍ y in ball 0 ρ, u y) ^ 2 :=
    setAverage_nonneg_of_nonneg fun x => sq_nonneg _
  have heq : ⨍ x in ball 0 ρ, |u x - ⨍ y in ball 0 ρ, u y| ^ 2 =
      ⨍ x in ball 0 ρ, (u x - ⨍ y in ball 0 ρ, u y) ^ 2 := by
    simp only [sq_abs]
  rw [heq, mul_assoc, rpow_one_sub_mul_rpow_eq hρ0 hY.le] at h
  have hb0 : 0 ≤ Cφ * (ρ * (Y / ρ) ^ θ) := by positivity
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt hA0] at h2
  refine h2.trans ?_
  have hYρ : (Y / ρ) ^ θ ≤ (Y / r) ^ θ :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hY.le hr0 hρ) hθ
  have h3 : ((Y / ρ) ^ θ) ^ 2 ≤ ((Y / r) ^ θ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hYρ 2
  calc (Cφ * (ρ * (Y / ρ) ^ θ)) ^ 2 = Cφ ^ 2 * ((Y / ρ) ^ θ) ^ 2 * ρ ^ 2 := by ring
    _ ≤ Cφ ^ 2 * ((Y / r) ^ θ) ^ 2 * ρ ^ 2 := by gcongr

/-- **Growth of a square integrable field with bounded normalized energy.** -/
theorem growth_of_energy {f : Vec d → ℝ} {Y C : ℝ} (hY : 0 < Y)
    (hfL : ∀ R : ℝ, 0 < R → IntegrableOn (fun y => f y ^ 2) (ball 0 R))
    (hen : ∀ ρ : ℝ, Y ≤ ρ → ⨍ x in ball 0 ρ, f x ^ 2 ≤ C) (R : ℝ) (hR : Y ≤ R) :
    IntegrableOn (fun y => f y ^ 2) (ball 0 R) ∧
      ∫ y in ball 0 R, f y ^ 2 ≤ C * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal * R ^ (d + 0) := by
  have hR0 : 0 < R := hY.trans_le hR
  refine ⟨hfL R hR0, ?_⟩
  have h := hen R hR
  rw [setAverage_eq, smul_eq_mul, volume_real_ball hR0] at h
  have hpos : 0 < R ^ d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal :=
    mul_pos (pow_pos hR0 d)
      (ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1))
  rw [inv_mul_le_iff₀ hpos] at h
  rw [add_zero]
  linarith

/-! ## The gradient -/

/-- The constant of the Gaussian bound on the corrector gradient. -/
def gaussianGradConst (d : ℕ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) / 2) * 2 * Real.sqrt (2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal)

theorem gaussianGradConst_nonneg (d : ℕ) : 0 ≤ gaussianGradConst d := by
  unfold gaussianGradConst
  positivity

/-- Gaussian bounds on the centered corrector at the doubled time `2r²`. -/
theorem integrable_heat_sq_sub_mean {u : Vec d → ℝ}
    (huL : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) {Y Cφ θ : ℝ} (hY : 0 < Y)
    (hθ : 0 ≤ θ)
    (hosc : ∀ ρ : ℝ, Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ,
      |u x - ⨍ y in ball 0 ρ, u y| ^ 2) ≤ Cφ * ρ ^ (1 - θ) * Y ^ θ)
    (hCφ : 0 ≤ Cφ) {r : ℝ} (hr : Y ≤ r) {x₀ : Vec d} (hx₀ : euclideanNorm x₀ ≤ r) :
    Integrable (fun y => euclideanHeatKernel (2 * r ^ 2) (y - x₀) *
        (u y - ⨍ x in ball 0 r, u x) ^ 2) ∧
      ∫ y, euclideanHeatKernel (2 * r ^ 2) (y - x₀) * (u y - ⨍ x in ball 0 r, u x) ^ 2 ≤
        (2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal) * (Cφ * (Y / r) ^ θ) ^ 2 *
          r ^ 2 := by
  have hr0 : 0 < r := hY.trans_le hr
  have hvm : AEStronglyMeasurable (fun y => u y - ⨍ x in ball 0 r, u x) volume :=
    aestronglyMeasurable_of_forall_ball fun R hR =>
      ((huL R hR).sub (memLp_const _)).aestronglyMeasurable
  have hω : 0 ≤ (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal := ENNReal.toReal_nonneg
  have hM : 0 ≤ dyadicOscConst d * (Cφ ^ 2 * ((Y / r) ^ θ) ^ 2) * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal :=
    mul_nonneg (mul_nonneg (dyadicOscConst_pos d).le (by positivity)) hω
  have hs : r ^ 2 ≤ 2 * r ^ 2 := by nlinarith
  have hx : euclideanNorm x₀ ≤ Real.sqrt (2 * r ^ 2) := by
    refine hx₀.trans (Real.le_sqrt_of_sq_le ?_)
    nlinarith
  have h := integral_heatKernel_mul_sq_le_of_growth 2 hvm hM hr0
    (fun R hR => growth_sub_mean_of_osc huL hY hθ hosc hCφ hr R hR) hs hx
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- **Gaussian averages of the corrector gradient.** -/
theorem abs_integral_heatKernel_grad_le {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g)
    (huL : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    {Y Cφ θ : ℝ} (hY : 0 < Y) (hθ : 0 ≤ θ) (hCφ : 0 ≤ Cφ)
    (hosc : ∀ ρ : ℝ, Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ,
      |u x - ⨍ y in ball 0 ρ, u y| ^ 2) ≤ Cφ * ρ ^ (1 - θ) * Y ^ θ)
    {r : ℝ} (hr : Y ≤ r) {x₀ : Vec d} (hx₀ : euclideanNorm x₀ ≤ r) (k : Fin d)
    (hgk : Integrable fun x => heatKernel x₀ r x * g x k) :
    |∫ x, heatKernel x₀ r x * g x k| ≤ gaussianGradConst d * Cφ * (Y / r) ^ θ := by
  have hr0 : 0 < r := hY.trans_le hr
  set c := ⨍ x in ball 0 r, u x with hc
  set v : Vec d → ℝ := fun y => u y - c with hv
  set W : Vec d → ℝ := fun y => euclideanHeatKernel (2 * r ^ 2) (y - x₀) with hW
  have hs2 : 0 < 2 * r ^ 2 := by positivity
  have hW0 : ∀ y, 0 ≤ W y := fun y => euclideanHeatKernel_nonneg hs2.le _
  have hvw : HasWeakGradient Set.univ v g := hasWeakGradient_sub_const Set.univ hw c
  have hvm : AEStronglyMeasurable v volume :=
    aestronglyMeasurable_of_forall_ball fun R hR =>
      ((huL R hR).sub (memLp_const _)).aestronglyMeasurable
  obtain ⟨hint2, hbound2⟩ := integrable_heat_sq_sub_mean huL hY hθ hosc hCφ hr hx₀
  obtain ⟨hWv, hWv'⟩ := integrable_and_abs_integral_heat_le hs2 x₀ hvm hint2
  set Cg := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / r) with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  have hdom : ∀ x, ‖v x * coordinateDerivative k (heatKernel x₀ r) x‖ ≤ Cg * (W x * |v x|) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    have := abs_coordinateDerivative_heatKernel_le hr0 x₀ k x
    calc |v x| * |coordinateDerivative k (heatKernel x₀ r) x| ≤ |v x| * (Cg * W x) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = Cg * (W x * |v x|) := by ring
  have hWva : Integrable fun x => W x * |v x| := by
    refine hWv.abs.congr (Eventually.of_forall fun x => ?_)
    show |W x * v x| = W x * |v x|
    rw [abs_mul, abs_of_nonneg (hW0 x)]
  have hF : Integrable fun x => v x * coordinateDerivative k (heatKernel x₀ r) x := by
    refine (hWva.const_mul Cg).mono' ?_ (Eventually.of_forall hdom)
    have hcd : Continuous fun x => coordinateDerivative k (heatKernel x₀ r) x :=
      (contDiff_coordinateDerivative_top (contDiff_heatKernel x₀ r) k).continuous
    exact hvm.mul hcd.aestronglyMeasurable
  have hF' : Integrable fun x => heatKernel x₀ r x * v x := by
    refine (hWva.const_mul ((2 : ℝ) ^ ((d : ℝ) / 2))).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (contDiff_heatKernel x₀ r).continuous.aestronglyMeasurable.mul hvm
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _ _)]
      have := heatKernel_le_two_mul hr0 x₀ x
      calc heatKernel x₀ r x * |v x| ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * W x * |v x| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = _ := by ring
  have hibp := integral_mul_grad_eq_neg hvw k (contDiff_heatKernel x₀ r) hgk hF hF'
  rw [hibp, abs_neg]
  have hK : 0 ≤ 2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (gaussianGrowthConst_nonneg d 2))
      (dyadicOscConst_pos d).le) ENNReal.toReal_nonneg
  calc |∫ x, v x * coordinateDerivative k (heatKernel x₀ r) x|
      ≤ ∫ x, ‖v x * coordinateDerivative k (heatKernel x₀ r) x‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, Cg * (W x * |v x|) := integral_mono hF.norm (hWva.const_mul Cg) hdom
    _ = Cg * ∫ x, W x * |v x| := integral_const_mul _ _
    _ ≤ Cg * Real.sqrt ((2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal) *
          (Cφ * (Y / r) ^ θ) ^ 2 * r ^ 2) :=
        mul_le_mul_of_nonneg_left (hWv'.trans (Real.sqrt_le_sqrt hbound2)) hCg0
    _ = gaussianGradConst d * Cφ * (Y / r) ^ θ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hr0.le, hCg, gaussianGradConst]
        field_simp

/-! ## The energy cross term -/

theorem continuous_euclideanNorm_vec : Continuous fun x : Vec d => euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem aestronglyMeasurable_vec_of_forall_ball {q : Vec d → Vec d}
    (hqL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => q x i) 2 (volume.restrict (ball 0 R))) :
    AEStronglyMeasurable q volume :=
  aestronglyMeasurable_of_forall_ball fun R hR => (memLp_pi_iff.mpr (hqL R hR)).aestronglyMeasurable

/-- The constant of the Gaussian bound on the energy cross term. -/
def gaussianCrossConst (d : ℕ) : ℝ :=
  d * ((2 : ℝ) ^ ((d : ℝ) / 2) * 2) *
    Real.sqrt (2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal) *
      Real.sqrt (gaussianGrowthConst d 0)

theorem gaussianCrossConst_nonneg (d : ℕ) : 0 ≤ gaussianCrossConst d := by
  unfold gaussianCrossConst
  positivity

/-- **Gaussian averages of the energy cross term.** For `q` weakly divergence-free with
`∫_{B_R} |q|² ≤ M_q R^d` for `R ≥ r`, `|∫ Φ_{x₀,r} q · ∇u| ≤ C_d √M_q C (Y/r)^θ`. -/
theorem abs_integral_heatKernel_dot_le {q : Vec d → Vec d}
    (hq : HasWeakDivergence Set.univ q (fun _ => 0))
    (hqL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => q x i) 2 (volume.restrict (ball 0 R)))
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hw : HasWeakGradient Set.univ u g)
    (huL : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hgL : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R)))
    {Y Cφ θ Mq : ℝ} (hY : 0 < Y) (hθ : 0 ≤ θ) (hCφ : 0 ≤ Cφ) (hMq : 0 ≤ Mq)
    (hosc : ∀ ρ : ℝ, Y ≤ ρ → Real.sqrt (⨍ x in ball 0 ρ,
      |u x - ⨍ y in ball 0 ρ, u y| ^ 2) ≤ Cφ * ρ ^ (1 - θ) * Y ^ θ)
    {r : ℝ} (hr : Y ≤ r) {x₀ : Vec d} (hx₀ : euclideanNorm x₀ ≤ r)
    (hqg : ∀ R : ℝ, r ≤ R → IntegrableOn (fun y => euclideanNorm (q y) ^ 2) (ball 0 R) ∧
      ∫ y in ball 0 R, euclideanNorm (q y) ^ 2 ≤ Mq * R ^ (d + 0))
    (hA : Integrable fun x => heatKernel x₀ r x * dot (q x) (g x)) :
    |∫ x, heatKernel x₀ r x * dot (q x) (g x)| ≤
      gaussianCrossConst d * Real.sqrt Mq * Cφ * (Y / r) ^ θ := by
  have hr0 : 0 < r := hY.trans_le hr
  set c := ⨍ x in ball 0 r, u x with hc
  set v : Vec d → ℝ := fun y => u y - c with hv
  set W : Vec d → ℝ := fun y => euclideanHeatKernel (2 * r ^ 2) (y - x₀) with hW
  have hs2 : 0 < 2 * r ^ 2 := by positivity
  have hW0 : ∀ y, 0 ≤ W y := fun y => euclideanHeatKernel_nonneg hs2.le _
  have hWm : AEStronglyMeasurable W volume :=
    (integrable_euclideanHeatKernel_sub_right hs2 x₀).aestronglyMeasurable
  have hvw : HasWeakGradient Set.univ v g := hasWeakGradient_sub_const Set.univ hw c
  have hvL : ∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (ball 0 R)) := fun R hR =>
    (huL R hR).sub (memLp_const _)
  have hvm : AEStronglyMeasurable v volume :=
    aestronglyMeasurable_of_forall_ball fun R hR => (hvL R hR).aestronglyMeasurable
  have hqm : AEStronglyMeasurable q volume := aestronglyMeasurable_vec_of_forall_ball hqL
  have hqnm : AEStronglyMeasurable (fun y => euclideanNorm (q y)) volume :=
    continuous_euclideanNorm_vec.comp_aestronglyMeasurable hqm
  obtain ⟨hint2, hbound2⟩ := integrable_heat_sq_sub_mean huL hY hθ hosc hCφ hr hx₀
  -- the Gaussian energy of `q` at time `2r²`
  have hs : r ^ 2 ≤ 2 * r ^ 2 := by nlinarith
  have hx : euclideanNorm x₀ ≤ Real.sqrt (2 * r ^ 2) := by
    refine hx₀.trans (Real.le_sqrt_of_sq_le ?_)
    nlinarith
  obtain ⟨hq2, hq2'⟩ := integral_heatKernel_mul_sq_le_of_growth 0 hqnm hMq hr0 hqg hs hx
  rw [pow_zero, mul_one] at hq2'
  -- the weighted product `W |v| |q|`
  obtain ⟨hprod, hprod'⟩ := integrable_and_abs_integral_weight_mul_le hW0 hWm hvm.norm hqnm
    (hint2.congr (Eventually.of_forall fun y => by
      show W y * v y ^ 2 = W y * ‖v y‖ ^ 2
      rw [Real.norm_eq_abs, sq_abs])) hq2
  have hprod2 : Integrable fun y => W y * (|v y| * euclideanNorm (q y)) := by
    simpa [Real.norm_eq_abs] using hprod
  have hprodeq : ∫ y, W y * (|v y| * euclideanNorm (q y)) ≤
      Real.sqrt (∫ y, W y * v y ^ 2) * Real.sqrt (∫ y, W y * euclideanNorm (q y) ^ 2) := by
    have h := (le_abs_self _).trans hprod'
    simpa [Real.norm_eq_abs, sq_abs] using h
  set Cg := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / r) with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  have hdot : ∀ x, |dot (q x) (gradient (heatKernel x₀ r) x)| ≤
      d * Cg * (W x * euclideanNorm (q x)) := by
    intro x
    refine (abs_dot_le_sum_abs_mul_abs _ _).trans ?_
    calc ∑ k, |q x k| * |gradient (heatKernel x₀ r) x k|
        ≤ ∑ _k : Fin d, euclideanNorm (q x) * (Cg * W x) := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (abs_apply_le_euclideanNorm _ k)
            (abs_coordinateDerivative_heatKernel_le hr0 x₀ k x) (abs_nonneg _)
            (Real.sqrt_nonneg _)
      _ = d * Cg * (W x * euclideanNorm (q x)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hdom : ∀ x, ‖v x * dot (q x) (gradient (heatKernel x₀ r) x)‖ ≤
      d * Cg * (W x * (|v x| * euclideanNorm (q x))) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    calc |v x| * |dot (q x) (gradient (heatKernel x₀ r) x)|
        ≤ |v x| * (d * Cg * (W x * euclideanNorm (q x))) :=
          mul_le_mul_of_nonneg_left (hdot x) (abs_nonneg _)
      _ = d * Cg * (W x * (|v x| * euclideanNorm (q x))) := by ring
  have hgradc : ∀ k, Continuous fun x => gradient (heatKernel x₀ r) x k := fun k =>
    (contDiff_coordinateDerivative_top (contDiff_heatKernel x₀ r) k).continuous
  have hqk : ∀ k, AEStronglyMeasurable (fun x => q x k) volume := fun k =>
    (continuous_apply k).comp_aestronglyMeasurable hqm
  have hdotm : AEStronglyMeasurable
      (fun x => dot (q x) (gradient (heatKernel x₀ r) x)) volume := by
    unfold dot
    exact (Finset.aestronglyMeasurable_sum (f := fun k x => q x k * gradient (heatKernel x₀ r) x k)
      Finset.univ fun k _ => (hqk k).mul (hgradc k).aestronglyMeasurable).congr
      (Eventually.of_forall fun x => by simp only [Finset.sum_apply])
  have hF : Integrable fun x => v x * dot (q x) (gradient (heatKernel x₀ r) x) :=
    (hprod2.const_mul _).mono' (hvm.mul hdotm) (Eventually.of_forall hdom)
  have hF' : ∀ k, Integrable fun x => heatKernel x₀ r x * (v x * q x k) := by
    intro k
    refine (hprod2.const_mul ((2 : ℝ) ^ ((d : ℝ) / 2))).mono'
      ((contDiff_heatKernel x₀ r).continuous.aestronglyMeasurable.mul
        (hvm.mul (hqk k))) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _ _)]
    have h1 := heatKernel_le_two_mul hr0 x₀ x
    have h2 := abs_apply_le_euclideanNorm (q x) k
    calc heatKernel x₀ r x * (|v x| * |q x k|)
        ≤ ((2 : ℝ) ^ ((d : ℝ) / 2) * W x) * (|v x| * euclideanNorm (q x)) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (by positivity) (hW0 x))
      _ = _ := by ring
  have hibp := integral_mul_dot_grad_eq_neg hq hqL hvw hvL hgL (contDiff_heatKernel x₀ r) hA hF hF'
  rw [hibp, abs_neg]
  have hK : 0 ≤ 2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (gaussianGrowthConst_nonneg d 2))
      (dyadicOscConst_pos d).le) ENNReal.toReal_nonneg
  have hK0 := gaussianGrowthConst_nonneg d 0
  calc |∫ x, v x * dot (q x) (gradient (heatKernel x₀ r) x)|
      ≤ ∫ x, ‖v x * dot (q x) (gradient (heatKernel x₀ r) x)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, d * Cg * (W x * (|v x| * euclideanNorm (q x))) :=
        integral_mono hF.norm (hprod2.const_mul _) hdom
    _ = d * Cg * ∫ x, W x * (|v x| * euclideanNorm (q x)) := integral_const_mul _ _
    _ ≤ d * Cg * (Real.sqrt ((2 * gaussianGrowthConst d 2 * dyadicOscConst d * (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal) *
          (Cφ * (Y / r) ^ θ) ^ 2 * r ^ 2) * Real.sqrt (gaussianGrowthConst d 0 * Mq)) := by
        refine mul_le_mul_of_nonneg_left (hprodeq.trans ?_) (by positivity)
        exact mul_le_mul (Real.sqrt_le_sqrt hbound2) (Real.sqrt_le_sqrt hq2')
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = gaussianCrossConst d * Real.sqrt Mq * Cφ * (Y / r) ^ θ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hr0.le, Real.sqrt_mul hK0, hCg, gaussianCrossConst]
        field_simp

/-! ## Fields with a pairing bound -/

/-- **Gaussian averages of a field with a pairing bound above `R₀`.** -/
theorem exists_abs_integral_heatKernel_le_of_pairing (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 ≤ κ → Measurable F → HasGaussianMoments F →
      ∀ (r : ℝ) (x₀ : Vec d), R₀ ≤ r → euclideanNorm x₀ ≤ r →
        |∫ y, heatKernel x₀ r y * F y| ≤ C * A * (R₀ / r) ^ κ := by
  obtain ⟨C, hC, h⟩ := exists_heatConv_le d
  refine ⟨C, hC, ?_⟩
  intro F R₀ A κ hF hR₀ hA hκ hFm hmom r x₀ hr hx₀
  have hr0 : 0 < r := hR₀.trans_le hr
  have hsq : R₀ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hR₀.le hr 2
  have hx2 : euclideanNorm x₀ ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hx₀ 2
  have h1 := h hF hR₀ hA hκ hFm hmom (r ^ 2) x₀ hsq hx2
  have heq : ∀ y, heatKernel x₀ r y = euclideanHeatKernel (r ^ 2) (x₀ - y) := by
    intro y
    unfold heatKernel
    rw [← euclideanHeatKernel_neg, neg_sub]
  simp_rw [heq]
  refine h1.trans (le_of_eq ?_)
  have hr2 : (r ^ 2) ^ (-(κ / 2)) = r ^ (-κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 1
    push_cast
    ring
  rw [hr2, Real.div_rpow hR₀.le hr0.le, Real.rpow_neg hr0.le, div_eq_mul_inv]
  ring

end QSH
