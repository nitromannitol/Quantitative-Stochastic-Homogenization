import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallMeanSquareComparison
import QuantitativeStochasticHomogenization.Ch03.Sec04.DyadicMeanIncrement
import QuantitativeStochasticHomogenization.Ch03.Sec04.DyadicMonotoneEnergy
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Centered and uncentered sublinearity of the actual corrector

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/AKMLocalCanonicalIdentificationSublinearity.lean`.

Source: the application. The centered ball convention of
`Corrector` implies the uncentered convention of `IsFirstOrderCorrector`.
No choice of normalization, quantitative estimate or new source input is used.
-/

open MeasureTheory Filter Topology

namespace QSH

/-- Centered sublinear mean-square oscillation forces uncentered sublinearity
for every locally square-integrable scalar potential. Source: the application. -/
theorem sublinear_uncentered_of_centered {d : ℕ} (u : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y)^2)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x^2)) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun n => 2^n
  let m : ℕ → ℝ := fun n => ⨍ x in ball 0 (r n), u x
  let o : ℝ → ℝ := fun R => ⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y)^2
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have ho (R : ℝ) : 0 ≤ o R := integral_nonneg fun x => sq_nonneg _
  have hr2 (n : ℕ) : r (n+1) = 2*r n := by simp [r, pow_succ, mul_comm]
  have hc : Tendsto (fun n => (r n)⁻¹ * Real.sqrt (o (r n))) atTop (𝓝 0) :=
    hsub.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have hinc : Tendsto (fun n => (m (n+1)-m n)/r n) atTop (𝓝 0) := by
    have hl := (hc.comp (tendsto_add_atTop_nat 1)).const_mul (2 * Real.sqrt ((2:ℝ)^d))
    simp only [mul_zero] at hl
    apply squeeze_zero_norm _ hl
    intro n
    have hn := sq_ball_mean_sub_double_mean_le u (r n) (hr n) (hu _ (by positivity))
    rw [← hr2 n] at hn
    change (m n - m (n+1))^2 ≤ (2:ℝ)^d * o (r (n+1)) at hn
    change ‖(m (n+1)-m n)/r n‖ ≤
      2*Real.sqrt ((2:ℝ)^d)*((r (n+1))⁻¹*Real.sqrt (o (r (n+1))))
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (hr _).le) (Real.sqrt_nonneg _)))).mp
    simp only [sq_abs, div_pow, mul_pow, inv_pow,
      Real.sq_sqrt (by positivity : 0 ≤ (2:ℝ)^d), Real.sq_sqrt (ho _)]
    calc
      _ ≤ ((2:ℝ)^d * o (r (n+1)))/(r n)^2 := by
        apply (div_le_div_iff_of_pos_right (sq_pos_of_pos (hr n))).mpr
        nlinarith only [hn]
      _ = _ := by rw [hr2]; field_simp [ne_of_gt (hr n)]
  have hm : Tendsto (fun n => m n/r n) atTop (𝓝 0) := tendsto_dyadic_scaled_of_small_increments m hinc
  have hsq : Tendsto (fun n => (⨍ x in ball 0 (r n), u x^2)/(r n)^2) atTop (𝓝 0) := by
    have hl := (hc.pow 2).const_mul 2 |>.add ((hm.pow 2).const_mul 2)
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hl
    apply squeeze_zero _ _ hl
    · intro n
      exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)
    · intro n
      have hb := average_sq_le_twice_centered_add_mean u (r n) (hr n) (hu _ (hr n))
      calc
        _ ≤ (2*o (r n)+2*(m n)^2)/(r n)^2 :=
          (div_le_div_iff_of_pos_right (sq_pos_of_pos (hr n))).mpr hb
        _ = _ := by
          rw [mul_pow, Real.sq_sqrt (ho _), div_pow]
          simp only [div_eq_mul_inv, inv_pow]
          ring
  let E : ℝ → ℝ := fun R => ∫ x in ball 0 R, u x^2
  let V : ℝ := volume.real (ball (0 : Vec d) 1)
  have hV : 0 < V := ball_volume_pos_finite d 1 (by norm_num)
  have havg (R : ℝ) (hR : 0 < R) :
      (⨍ x in ball 0 R, u x^2)/R^2 = V⁻¹ * (E R / R^(d+2)) := by
    simp only [setAverage_eq, smul_eq_mul]
    rw [volume_real_euclideanBall R hR]
    dsimp only [V, E]
    rw [pow_add]
    field_simp

  have hed : Tendsto (fun n : ℕ => E ((2:ℝ)^n) / ((2:ℝ)^n)^(d+2)) atTop (𝓝 0) := by
    have hl := hsq.const_mul V
    simp only [mul_zero] at hl
    apply hl.congr
    intro n
    rw [havg (r n) (hr n)]
    simp [V, r, mul_inv_cancel_left₀ hV.ne']
  have he : Tendsto (fun R => E R / R^(d+2)) atTop (𝓝 0) :=
    tendsto_normalized_monotone_of_dyadic E (fun R => integral_nonneg fun _ => sq_nonneg _)
      (monotoneOn_integral_sq_euclideanBall u hu) (d+2) hed
  have hs : Tendsto (fun R => (⨍ x in ball 0 R, u x^2)/R^2) atTop (𝓝 0) := by
    have hl := he.const_mul V⁻¹
    simp only [mul_zero] at hl
    exact hl.congr' ((eventually_gt_atTop (0:ℝ)).mono fun R hR => (havg R hR).symm)
  have hl := hs.sqrt
  simp only [Real.sqrt_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have hnon : 0 ≤ (⨍ x in ball (0 : Vec d) R, u x^2) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Real.sqrt_div hnon, Real.sqrt_sq hR.le]
  ring

end QSH
