import QuantitativeStochasticHomogenization.AppC.BallLebesgueDifferentiation
import QuantitativeStochasticHomogenization.AppC.VitaliCovering
import PDEFoundation.Measure.NormalizedLp
import PDEFoundation.Sobolev.Mean

/-!
# Estimates on single balls for Gehring's lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma C.4. This file collects the computations on one ball `B_r(z)`:

* `eLpMeanNormOn_rpow_eq`: `‖h‖_{L̲^s(U)}^s = |U|^{-1} ∫_U |h|^s`;
* `volume_ball_mul`: `|B_{cr}(z)| = c^d |B_r(z)|`;
* `ofReal_setAverage_abs_le_eLpMeanNormOn_two`: `⨍_U |h| ≤ ‖h‖_{L̲²(U)}`;
* `volume_le_of_lt_eLpMeanNormOn`: if `c t < ‖h‖_{L̲^s(B)}` with `c^s ≥ 2`, then
  `|B| ≤ t^{-s} ∫_{B ∩ {|h| > t}} |h|^s`, the step from (C.9) to the display after it in the book.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem eLpMeanNormOn_rpow_eq {U : Set (Vec d)} {s : ℝ} (hs : 0 < s)
    {h : Vec d → ℝ} (hh : AEStronglyMeasurable h (volume.restrict U)) :
    PDE.eLpMeanNormOn U (ENNReal.ofReal s) h ^ s =
      (volume U)⁻¹ * ∫⁻ x in U, ‖h x‖ₑ ^ s := by
  have hs0 : ENNReal.ofReal s ≠ 0 := by simpa using hs
  have hμ : AEStronglyMeasurable h (PDE.normalizedVolumeOn U) := hh.smul_measure _
  rw [PDE.eLpMeanNormOn, eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 ENNReal.ofReal_ne_top hμ,
    ENNReal.toReal_ofReal hs.le, ← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one,
    PDE.normalizedVolumeOn, lintegral_smul_measure, smul_eq_mul]

theorem volume_ball_mul (z : Vec d) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    volume (ball z (c * r)) = ENNReal.ofReal (c ^ d) * volume (ball z r) := by
  rw [ball_eq_euclideanBall z (mul_pos hc hr), ball_eq_euclideanBall z hr,
    PDE.volume_euclideanBall_eq_unit_mul_of_pos z (mul_pos hc hr),
    PDE.volume_euclideanBall_eq_unit_mul_of_pos z hr, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg hc.le d), mul_assoc]

theorem volume_ball_ne_zero' (z : Vec d) {r : ℝ} (hr : 0 < r) : volume (ball z r) ≠ 0 :=
  (volume_ball_pos z hr).ne'

theorem volume_ball_ne_top' (z : Vec d) (r : ℝ) : volume (ball z r) ≠ ⊤ :=
  (volume_ball_lt_top z r).ne

theorem ofReal_setAverage_abs_le_eLpMeanNormOn_two {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {h : Vec d → ℝ} (hint : IntegrableOn h U) :
    ENNReal.ofReal (⨍ x in U, |h x| ∂volume) ≤ PDE.eLpMeanNormOn U 2 h := by
  have hpos : 0 < volume U := pos_iff_ne_zero.mpr hU0
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos hUt.lt_top
  have hintμ : Integrable (fun x => |h x|) (PDE.normalizedVolumeOn U) :=
    PDE.integrable_normalizedVolumeOn_of_integrableOn hint.abs hpos
  have h2 : ⨍ x in U, |h x| ∂volume = ∫ x, |h x| ∂(PDE.normalizedVolumeOn U) := by
    rw [PDE.integral_normalizedVolumeOn_eq_integralAverage, PDE.integralAverage, setAverage_eq,
      smul_eq_mul, measureReal_def]
  have h1 : ENNReal.ofReal (∫ x, |h x| ∂(PDE.normalizedVolumeOn U)) =
      PDE.eLpMeanNormOn U 1 h := by
    rw [ofReal_integral_eq_lintegral_ofReal hintμ (Eventually.of_forall fun x => abs_nonneg _),
      PDE.eLpMeanNormOn, eLpNorm_one_eq_lintegral_enorm]
    · refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal_abs]
    · exact hint.aestronglyMeasurable.smul_measure _
  rw [h2, h1]
  exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two

/-- If `c t < ‖h‖_{L̲^s(B)}` with `c^s ≥ 2`, then `|B| ≤ t^{-s} ∫_{B ∩ {|h| > t}} |h|^s`. -/
theorem volume_le_of_lt_eLpMeanNormOn {B : Set (Vec d)}
    (hBt : volume B ≠ ⊤) {h : Vec d → ℝ} (hhm : Measurable h) {s t c : ℝ} (hs : 0 < s)
    (ht : 0 < t) (hc0 : 0 < c) (hc : 2 ≤ c ^ s)
    (hlt : ENNReal.ofReal (c * t) < PDE.eLpMeanNormOn B (ENNReal.ofReal s) h) :
    volume B ≤ ENNReal.ofReal (t⁻¹ ^ s) * ∫⁻ x in B ∩ {x | t < |h x|}, ‖h x‖ₑ ^ s := by
  set S := {x | t < |h x|} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hhm.abs
  have hN := eLpMeanNormOn_rpow_eq (U := B) hs hhm.aestronglyMeasurable.restrict
  have h1 : ENNReal.ofReal (c * t) ^ s < PDE.eLpMeanNormOn B (ENNReal.ofReal s) h ^ s :=
    ENNReal.rpow_lt_rpow hlt hs
  rw [hN, ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le, ← ENNReal.div_eq_inv_mul] at h1
  have h2 := ENNReal.mul_lt_of_lt_div h1
  rw [← lintegral_inter_add_sdiff _ B hSm] at h2
  set a := ENNReal.ofReal (t ^ s) with ha
  have hdiff : ∫⁻ x in B \ S, ‖h x‖ₑ ^ s ≤ a * volume B := by
    calc ∫⁻ x in B \ S, ‖h x‖ₑ ^ s ≤ ∫⁻ x in B \ S, a := by
          refine setLIntegral_mono measurable_const fun x hx => ?_
          have hx' : |h x| ≤ t := not_lt.mp hx.2
          rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs.le]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) hx' hs.le)
      _ = a * volume (B \ S) := setLIntegral_const _ _
      _ ≤ a * volume B := by gcongr; exact Set.sdiff_subset
  have hct : ENNReal.ofReal ((c * t) ^ s) = ENNReal.ofReal (c ^ s) * a := by
    rw [Real.mul_rpow hc0.le ht.le, ENNReal.ofReal_mul (by positivity)]
  have h2a : (2 : ℝ≥0∞) * (a * volume B) ≤ ENNReal.ofReal ((c * t) ^ s) * volume B := by
    rw [hct, mul_assoc]
    gcongr
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hc
  have hfin : a * volume B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt
  have h3 : a * volume B + a * volume B < (∫⁻ x in B ∩ S, ‖h x‖ₑ ^ s) + a * volume B := by
    calc a * volume B + a * volume B = 2 * (a * volume B) := (two_mul _).symm
      _ ≤ ENNReal.ofReal ((c * t) ^ s) * volume B := h2a
      _ < _ := h2
      _ ≤ _ := add_le_add le_rfl hdiff
  have h4 : a * volume B < ∫⁻ x in B ∩ S, ‖h x‖ₑ ^ s := (ENNReal.add_lt_add_iff_right hfin).mp h3
  have hinv : ENNReal.ofReal (t⁻¹ ^ s) * a = 1 := by
    rw [ha, ← ENNReal.ofReal_mul (by positivity), Real.inv_rpow ht.le,
      inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
  calc volume B = ENNReal.ofReal (t⁻¹ ^ s) * (a * volume B) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (t⁻¹ ^ s) * ∫⁻ x in B ∩ S, ‖h x‖ₑ ^ s := by gcongr

end QSH
