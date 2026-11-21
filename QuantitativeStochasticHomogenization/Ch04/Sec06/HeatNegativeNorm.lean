import QuantitativeStochasticHomogenization.AppD.HeatTaylorPairing
import QuantitativeStochasticHomogenization.Ch04.Sec06.RescaledAverages

/-!
# Section 4.6: negative Sobolev norms on the unit ball by the heat semigroup

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.6 and Appendix D. For a field `F` with `F exp(-‖x‖²/16)` integrable, write
`Y_{β,s}(y) = ∫ F(x) ∂^β Φ(s)(x - y) dx` (`heatDerivativeAverage`). The Taylor formula of the heat
semigroup, with half of the derivatives of `Δ^k` moved onto the kernel, gives for every test
function `ψ` of the unit ball of `H^{n+1}(B_1)`
`|∫ F ψ| ≤ C (∑_{k ≤ n} ∑_{|β| = k} ‖Y_{β,1}‖_{L²(B_1)} + ∫₀¹ s^n ∑_{|β| = n+1} ‖Y_{β,s}‖_{L²(B_1)} ds)`
(`ofReal_abs_integral_mul_le_heatBracket`), hence the same bound for the normalized `H^{-(n+1)}(B_1)`
norm (`negativeIntegerSobolevNorm_le_heatBracket`).
-/

open MeasureTheory Filter Set
open scoped ContDiff Convolution Nat ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The unit ball -/

theorem isOpen_originBall_one : IsOpen (originBall d 1) := by
  refine isOpen_lt ?_ continuous_const
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem norm_lt_one_of_mem_originBall {x : Vec d} (hx : x ∈ originBall d 1) : ‖x‖ < 1 := by
  have h1 : euclideanNorm x < 1 := hx
  have h2 : ‖x‖ ^ 2 ≤ euclideanSq x := norm_sq_le_euclideanSq x
  have h4 : euclideanSq x < 1 ^ 2 := by
    unfold euclideanNorm at h1
    exact (Real.sqrt_lt' one_pos).mp h1
  nlinarith [norm_nonneg x]

theorem volume_originBall_pos : 0 < volume (originBall d 1) := by
  refine isOpen_originBall_one.measure_pos volume ⟨0, ?_⟩
  show euclideanNorm (0 : Vec d) < 1
  simp [euclideanNorm, euclideanSq, dot]

theorem volume_originBall_lt_top : volume (originBall d 1) < ⊤ := by
  refine (measure_mono fun x hx => ?_).trans_lt (measure_ball_lt_top (x := (0 : Vec d)) (r := 1))
  simpa [Metric.mem_ball, dist_zero_right] using norm_lt_one_of_mem_originBall hx

/-- The constant `|B_1|^{1/2} (1 + |B_1|)^m` bounding the `L²(B_1)` norms of the derivatives of
order at most `m` of the tests in the unit ball of `H^m(B_1)`. -/
def unitBallTestConstant (d m : ℕ) : ℝ :=
  Real.sqrt (volume (originBall d 1)).toReal * (1 + (volume (originBall d 1)).toReal) ^ m

theorem unitBallTestConstant_pos (d m : ℕ) : 0 < unitBallTestConstant d m := by
  have hv : 0 < (volume (originBall d 1)).toReal :=
    ENNReal.toReal_pos volume_originBall_pos.ne' volume_originBall_lt_top.ne
  unfold unitBallTestConstant
  positivity

/-! ## `L²(B_1)` norms of tests -/

theorem eLpNorm_eq_sqrt_mul_scalarRms {g : Vec d → ℝ} (hg : Continuous g)
    (hcg : HasCompactSupport g) {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤) :
    eLpNorm g 2 (volume.restrict U) =
      ENNReal.ofReal (Real.sqrt (volume U).toReal * scalarRms volume U g) := by
  have hm : MemLp g 2 (volume.restrict U) := (hg.memLp_of_hasCompactSupport hcg).restrict U
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  have hv : (volume U).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hU0, hUt⟩
  unfold scalarRms
  rw [setAverage_eq, smul_eq_mul, measureReal_def, ← Real.sqrt_mul ENNReal.toReal_nonneg, ← mul_assoc,
    mul_inv_cancel₀ hv, one_mul, Real.sqrt_eq_rpow]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_two, sq_abs]
  · norm_num

theorem multiIndexDerivative_eq_of_val {k m : ℕ} (β : Fin d → Fin (k + 1))
    (β' : Fin d → Fin (m + 1)) (h : ∀ j, (β j).val = (β' j).val) (ψ : Vec d → ℝ) :
    multiIndexDerivative β ψ = multiIndexDerivative β' ψ := by
  unfold multiIndexDerivative
  simp only [h]

theorem tsupport_foldr_coordinateDerivative_subset (f : Vec d → ℝ) (l : List (Fin d)) :
    tsupport (l.foldr coordinateDerivative f) ⊆ tsupport f := by
  induction l with
  | nil => exact subset_rfl
  | cons a l ih =>
    rw [List.foldr_cons]
    exact (tsupport_coordinateDerivative_subset _ a).trans ih

theorem tsupport_multiIndexDerivative_subset {k : ℕ} (β : Fin d → Fin (k + 1)) (f : Vec d → ℝ) :
    tsupport (multiIndexDerivative β f) ⊆ tsupport f :=
  tsupport_foldr_coordinateDerivative_subset f _

/-- **The test side**: the derivatives of order at most `m` of a test in the unit ball of
`H^m(B_1)` have `L²(B_1)` norm at most `unitBallTestConstant d m`. -/
theorem eLpNorm_multiIndexDerivative_le (hd : 1 ≤ d) {m : ℕ} {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest (originBall d 1) ψ)
    (hψn : integerSobolevTestNorm m (originBall d 1) ψ ≤ 1) {k : ℕ} (β : Fin d → Fin (k + 1))
    (hβ : ∑ j, (β j).val ≤ m) :
    eLpNorm (multiIndexDerivative β ψ) 2 (volume.restrict (originBall d 1)) ≤
      ENNReal.ofReal (unitBallTestConstant d m) := by
  set v := (volume (originBall d 1)).toReal with hvdef
  have hv : 0 < v := ENNReal.toReal_pos volume_originBall_pos.ne' volume_originBall_lt_top.ne
  have hβle : ∀ j, (β j).val < m + 1 := fun j =>
    Nat.lt_succ_of_le ((Finset.single_le_sum (fun i _ => Nat.zero_le (β i).val)
      (Finset.mem_univ j)).trans hβ)
  set β' : Fin d → Fin (m + 1) := fun j => ⟨(β j).val, hβle j⟩ with hβ'
  have heq := multiIndexDerivative_eq_of_val β β' (fun j => rfl) ψ
  have hsum : (∑ j, (β' j).val) = ∑ j, (β j).val := rfl
  have hsm := multiIndexDerivative_smooth hψ.1 hψ.2.1 β
  rw [eLpNorm_eq_sqrt_mul_scalarRms hsm.1.continuous hsm.2 volume_originBall_pos.ne'
    volume_originBall_lt_top.ne, heq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hrms := scalarRms_multiIndexDerivative_le hψn β' (hsum ▸ hβ)
  set e : ℝ := (((∑ j : Fin d, (β' j).val : ℕ) : ℝ) - m) / d with he
  have hr0 : 0 ≤ scalarRms volume (originBall d 1) (multiIndexDerivative β' ψ) :=
    Real.sqrt_nonneg _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hne : 0 ≤ -e := by
    rw [he, neg_nonneg]
    refine div_nonpos_of_nonpos_of_nonneg ?_ hdpos.le
    rw [sub_nonpos]
    exact_mod_cast hsum ▸ hβ
  have hle : -e ≤ m := by
    rw [he, ← neg_div, neg_sub, div_le_iff₀ hdpos]
    have h0 : (0 : ℝ) ≤ ((∑ j : Fin d, (β' j).val : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hrms' : scalarRms volume (originBall d 1) (multiIndexDerivative β' ψ) ≤ v ^ (-e) := by
    calc scalarRms volume (originBall d 1) (multiIndexDerivative β' ψ)
        = v ^ (-e) * (v ^ e * scalarRms volume (originBall d 1) (multiIndexDerivative β' ψ)) := by
          rw [← mul_assoc, ← Real.rpow_add hv, neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ v ^ (-e) * 1 := mul_le_mul_of_nonneg_left hrms (Real.rpow_nonneg hv.le _)
      _ = v ^ (-e) := mul_one _
  have hpow : v ^ (-e) ≤ (1 + v) ^ m := by
    calc v ^ (-e) ≤ (1 + v) ^ (-e) := Real.rpow_le_rpow hv.le (by linarith) hne
      _ ≤ (1 + v) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hle
      _ = (1 + v) ^ m := Real.rpow_natCast _ _
  unfold unitBallTestConstant
  rw [← hvdef]
  exact mul_le_mul_of_nonneg_left (hrms'.trans hpow) (Real.sqrt_nonneg _)

/-! ## The averages `Y_{β,s}` -/

/-- `Y_{β,s}(y) = ∫ F(x) ∂^β Φ(s)(x - y) dx`. -/
def heatDerivativeAverage {k : ℕ} (β : Fin d → Fin (k + 1)) (s : ℝ) (F : Vec d → ℝ)
    (y : Vec d) : ℝ :=
  ∫ x, F x * multiIndexDerivative β (euclideanHeatKernel (d := d) s) (x - y)

theorem aestronglyMeasurable_heatDerivativeAverage {k : ℕ} (β : Fin d → Fin (k + 1)) (s : ℝ)
    {F : Vec d → ℝ} (hFm : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (heatDerivativeAverage β s F) volume := by
  have hKc : Continuous (multiIndexDerivative β (euclideanHeatKernel (d := d) s)) :=
    (foldr_coordinateDerivative_contDiff (contDiff_euclideanHeatKernel s) _).continuous
  have h : AEStronglyMeasurable (fun p : Vec d × Vec d =>
      F p.2 * multiIndexDerivative β (euclideanHeatKernel (d := d) s) (p.2 - p.1))
      ((volume : Measure (Vec d)).prod volume) :=
    (hFm.comp_snd).mul (hKc.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
  exact h.integral_prod_right'

theorem integrable_mul_euclideanHeatKernel_of_exp {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) : Integrable (fun x => F x * euclideanHeatKernel (4 * s) x) := by
  have hc : Continuous (euclideanHeatKernel (d := d) (4 * s)) :=
    (contDiff_euclideanHeatKernel (4 * s)).continuous
  set c := (4 * Real.pi * (4 * s)) ^ (-(d : ℝ) / 2) with hcdef
  refine (hF.norm.const_mul c).mono' (hFm.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hk : euclideanHeatKernel (4 * s) x ≤ c * Real.exp (-(‖x‖ ^ 2) / 16) := by
    unfold euclideanHeatKernel
    rw [hcdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by positivity) _)
    have h1 := norm_sq_le_euclideanSq x
    have h0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) h0]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg (by positivity) x),
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |F x| * euclideanHeatKernel (4 * s) x ≤ |F x| * (c * Real.exp (-(‖x‖ ^ 2) / 16)) :=
        mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = _ := by ring

/-- **Half of the derivatives on the kernel, paired with a field**:
`∫ F Φ(s) ∗ Δ^k χ = ∑_w ∫ ∂^{β_w} χ Y_{β_w,s}`. -/
theorem integral_mul_heatSmooth_iterLaplacian_eq {F : Vec d → ℝ}
    (hFm : AEStronglyMeasurable F volume)
    (hF : Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (k : ℕ) :
    ∫ x, F x * heatSmooth s (iterLaplacian k χ) x = ∑ w : Fin k → Fin d,
      ∫ y, multiIndexDerivative (countIndex w) χ y *
        heatDerivativeAverage (countIndex w) s F y := by
  have hF4 := integrable_mul_euclideanHeatKernel_of_exp hFm hF hs hs1
  have hβ : ∀ w : Fin k → Fin d, ContDiff ℝ ∞ (multiIndexDerivative (countIndex w) χ) ∧
      HasCompactSupport (multiIndexDerivative (countIndex w) χ) := fun w =>
    multiIndexDerivative_smooth hχ hcχ (countIndex w)
  have hint : ∀ w : Fin k → Fin d, Integrable (fun x => F x *
      (multiIndexDerivative (countIndex w) (euclideanHeatKernel (d := d) s) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] multiIndexDerivative (countIndex w) χ) x) :=
    fun w => integrable_mul_convolution hs _ hFm hF4 (hβ w).1.continuous (hβ w).2
  calc ∫ x, F x * heatSmooth s (iterLaplacian k χ) x
      = ∫ x, ∑ w : Fin k → Fin d, F x *
        (multiIndexDerivative (countIndex w) (euclideanHeatKernel (d := d) s) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] multiIndexDerivative (countIndex w) χ) x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [heatSmooth_iterLaplacian s hχ hcχ k x, Finset.mul_sum]
    _ = ∑ w : Fin k → Fin d, ∫ x, F x *
        (multiIndexDerivative (countIndex w) (euclideanHeatKernel (d := d) s) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] multiIndexDerivative (countIndex w) χ) x :=
        integral_finsetSum _ fun w _ => hint w
    _ = _ := Finset.sum_congr rfl fun w _ =>
        integral_mul_convolution_eq hs _ hFm hF4 (hβ w).1.continuous (hβ w).2

/-- **Cauchy–Schwarz on a set containing the support.** -/
theorem ofReal_abs_integral_mul_le {g Y : Vec d → ℝ} (hg : AEStronglyMeasurable g volume)
    (hY : AEStronglyMeasurable Y volume) {U : Set (Vec d)} (hgU : ∀ y ∉ U, g y = 0) :
    ENNReal.ofReal |∫ y, g y * Y y| ≤
      eLpNorm g 2 (volume.restrict U) * eLpNorm Y 2 (volume.restrict U) := by
  have h1 : ∫ y, g y * Y y = ∫ y in U, g y * Y y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hgU y hy, zero_mul]).symm
  rw [h1, ← Real.enorm_eq_ofReal_abs]
  calc ‖∫ y in U, g y * Y y‖ₑ ≤ ∫⁻ y in U, ‖g y * Y y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (g • Y) 1 (volume.restrict U) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        · rfl
        · exact (hg.mul hY).restrict
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm hg.restrict hY.restrict

end QSH
