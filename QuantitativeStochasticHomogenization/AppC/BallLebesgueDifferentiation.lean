import QuantitativeStochasticHomogenization.Ch04.Sec05.CubeDecomposition
import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity
import Mathlib.MeasureTheory.Covering.DensityTheorem
import PDEFoundation.Measure.BallVolume

/-!
# Lebesgue differentiation on Euclidean balls

The Lebesgue differentiation theorem of Mathlib (`IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`)
is stated for the closed balls of the metric of `Vec d = Fin d → ℝ`, which are cubes. A Euclidean
ball `B_ρ(x)` lies in the cube of half-side `ρ` centered at `x`, whose volume is `2^d/|B_1|` times
that of `B_ρ(x)`, so for almost every `x` the averages `⨍_{B_ρ(x)} |f - f(x)|` tend to `0` as
`ρ → 0⁺`. This gives the Lebesgue points used in the proof of Gehring's lemma (Lemma C.4 of
Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem ball_subset_metric_closedBall (x : Vec d) (ρ : ℝ) :
    ball x ρ ⊆ Metric.closedBall x ρ := by
  intro y hy
  have hy' : euclideanNorm (y - x) < ρ := hy
  rw [Metric.mem_closedBall, dist_pi_le_iff (le_of_lt ((euclideanNorm_nonneg' _).trans_lt hy'))]
  intro i
  rw [Real.dist_eq]
  have := abs_apply_le_euclideanNorm' (y - x) i
  simp only [Pi.sub_apply] at this
  linarith

theorem volume_real_metric_closedBall (x : Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real (Metric.closedBall x ρ) = (2 * ρ) ^ d := by
  rw [measureReal_def, volume_pi_closedBall x hρ]
  simp only [Real.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]

theorem volume_real_ball (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    volume.real (ball x ρ) = ρ ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := by
  rw [measureReal_def, ball_eq_euclideanBall x hρ]
  exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos x hρ

/-- The average of a nonnegative function over `s ⊆ t` is at most `|t|/|s|` times its average
over `t`. -/
theorem setAverage_le_mul_setAverage_of_subset {s t : Set (Vec d)} (hst : s ⊆ t)
    (hs : 0 < volume.real s) (htfin : volume t ≠ ⊤) {h : Vec d → ℝ} (hh : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn h t) :
    ⨍ x in s, h x ∂volume ≤ (volume.real t / volume.real s) * ⨍ x in t, h x ∂volume := by
  have ht : 0 < volume.real t := hs.trans_le (measureReal_mono hst htfin)
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have h1 : ∫ x in s, h x ≤ ∫ x in t, h x :=
    setIntegral_mono_set hint (Eventually.of_forall fun x => hh x) (Eventually.of_forall hst)
  calc (volume.real s)⁻¹ * ∫ x in s, h x ≤ (volume.real s)⁻¹ * ∫ x in t, h x :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs.le)
    _ = volume.real t / volume.real s * ((volume.real t)⁻¹ * ∫ x in t, h x) := by
        field_simp

/-- **Lebesgue differentiation on Euclidean balls**: for a locally integrable `f`, almost every
`x` satisfies `⨍_{B_ρ(x)} |f - f(x)| → 0` as `ρ → 0⁺`. -/
theorem ae_tendsto_ballAverage_abs_sub {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun ρ => ⨍ y in ball x ρ, |f y - f x| ∂volume) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure (Vec d))) hf 1] with x hx
  have hc := hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact Metric.mem_closedBall_self (by simp only [id, one_mul]; linarith))
  set ω := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal with hω
  have hω0 : 0 < ω := PDE.volume_euclideanBall_toReal_pos 0 one_pos
  have hc' := hc.const_mul ((2 : ℝ) ^ d / ω)
  rw [mul_zero] at hc'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc' ?_ ?_
  · filter_upwards with ρ
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun y => abs_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    have : IsFiniteMeasure (volume.restrict (Metric.closedBall x ρ)) :=
      isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
    have hint : IntegrableOn (fun y => |f y - f x|) (Metric.closedBall x ρ) :=
      ((hf.integrableOn_isCompact (isCompact_closedBall x ρ)).sub (integrable_const _)).abs
    have h := setAverage_le_mul_setAverage_of_subset (ball_subset_metric_closedBall x ρ)
      (volume_real_ball_pos x hρ) measure_closedBall_lt_top.ne (fun y => abs_nonneg (f y - f x))
      hint
    have hratio : volume.real (Metric.closedBall x ρ) / volume.real (ball x ρ) =
        (2 : ℝ) ^ d / ω := by
      rw [volume_real_metric_closedBall x hρ.le, volume_real_ball x hρ, mul_pow, ← hω]
      field_simp
    rw [hratio] at h
    simpa only [id, Real.norm_eq_abs] using h

/-- At almost every point `x`, every level `λ < |f(x)|` is exceeded by the averages of `|f|` over
all small balls `B_ρ(x)`. -/
theorem ae_eventually_lt_ballAverage_abs {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, ∀ l : ℝ, l < |f x| → ∀ᶠ ρ in 𝓝[>] 0, l < ⨍ y in ball x ρ, |f y| ∂volume := by
  filter_upwards [ae_tendsto_ballAverage_abs_sub hf] with x hx l hl
  have hev := hx (Iio_mem_nhds (sub_pos.mpr hl))
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ (hρpos : 0 < ρ)
  have hρ' : ⨍ y in ball x ρ, |f y - f x| ∂volume < |f x| - l := hρ
  have hsub := ball_subset_metric_closedBall x ρ
  have hfint : IntegrableOn f (ball x ρ) :=
    (hf.integrableOn_isCompact (isCompact_closedBall x ρ)).mono_set hsub
  have hpos := volume_real_ball_pos x hρpos
  have hfin : volume (ball x ρ) ≠ ⊤ := by
    intro htop
    rw [measureReal_def, htop, ENNReal.toReal_top] at hpos
    exact lt_irrefl 0 hpos
  have : IsFiniteMeasure (volume.restrict (ball x ρ)) := isFiniteMeasure_restrict.mpr hfin
  have hint1 : IntegrableOn (fun y => |f y|) (ball x ρ) := hfint.abs
  have hint2 : IntegrableOn (fun y => |f y - f x|) (ball x ρ) :=
    (hfint.sub (integrable_const _)).abs
  have hmono : ∫ y in ball x ρ, (|f x| - |f y - f x|) ≤ ∫ y in ball x ρ, |f y| := by
    refine integral_mono ((integrable_const _).sub hint2) hint1 fun y => ?_
    have := abs_sub_abs_le_abs_sub (f x) (f y)
    rw [abs_sub_comm (f x) (f y)] at this
    linarith
  rw [integral_sub (integrable_const _) hint2, setIntegral_const, smul_eq_mul] at hmono
  rw [setAverage_eq, smul_eq_mul] at hρ' ⊢
  have h2 : (volume.real (ball x ρ))⁻¹ * (volume.real (ball x ρ) * |f x| -
      ∫ y in ball x ρ, |f y - f x|) ≤ (volume.real (ball x ρ))⁻¹ * ∫ y in ball x ρ, |f y| :=
    mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hpos.le)
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h2
  linarith

end QSH
