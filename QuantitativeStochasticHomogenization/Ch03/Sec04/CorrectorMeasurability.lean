import QuantitativeStochasticHomogenization.Ch03.Sec04.HomogenizationDataExistence
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatMeasurability
import QuantitativeStochasticHomogenization.Ch04.Sec01.AnalyticUpperCuts
import QuantitativeStochasticHomogenization.Ch04.Sec01.EuclideanLipschitz
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoordinateNormBound
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch04.Sec03.AveragesFromEnergy

/-!
# Joint measurability of the corrector gradients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Definition 3.14 and Lemma 3.16: the gradient `∇φ_e` of the first-order corrector is a jointly
measurable function of `(a, x)`, up to a modification on a null set.

The argument is that of `Ch04/Sec01/J1HeatMeasurability.lean`. The coefficient field is encoded
by its entries in `∏ₙ L²(B̄ₙ)`, a Polish space (`coarseGaussian_hencoding`), and the pairs of a
coefficient field and an element of `A₁` form a Borel set `G` whose fibers are exactly the
elements of `A₁` (`coarseGaussian_hgraph`, `coarseGaussian_hfiber`). Adding the Borel condition
that the potential minus `e·x` is sublinear on the balls `B̄ₙ` cuts out, on the event of full
probability of the high-contrast theorem, the corrected affine functions of slope `e`: their
gradients are `e + ∇φ_e` by the uniqueness of correctors. Hence, for every Borel set `B`, the
event `{e + ∇φ_e ∈ B}` agrees up to a null set with the preimage under the encoding of the
projection of a Borel set, an analytic set, which is universally measurable. The corrector
gradient is therefore an almost everywhere measurable map into `∏ₙ L²(B̄ₙ)^d`, and a jointly
measurable representative (`coarseGaussian_hrepresentative`) of a measurable modification is the
version required by Definition 3.14.

* `exists_harmonicA1_of_corrector`: a sublinear corrector of slope `e` gives the element
  `e·x + φ` of `A₁`.
* `tendsto_sublinear_of_closedBall`, `tendsto_closedBall_of_sublinear`: sublinearity on the
  Euclidean balls `B_R` and on the closed sup-norm balls `B̄ₙ`.
* `highContrastCorrectorMeasurable`: the jointly measurable version.
* `homogenizationDataExists`: every law satisfying (0.10)-(0.11) has homogenization data.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Corrected affine functions in `A₁` -/

private theorem measurableSet_ball_zero' (R : ℝ) : MeasurableSet (ball (0 : Vec d) R) := by
  have hc : Continuous fun y : Vec d => euclideanNorm (y - 0) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (by fun_prop)
  exact measurableSet_lt hc.measurable measurable_const

theorem abs_dot_le_mul_of_mem_ball (e : Vec d) {x : Vec d} {R : ℝ}
    (hx : x ∈ ball (0 : Vec d) R) : |dot e x| ≤ (∑ i, |e i|) * R := by
  have hx' : euclideanNorm (x - 0) < R := hx
  rw [sub_zero] at hx'
  calc |dot e x| = |∑ i, e i * x i| := rfl
    _ ≤ ∑ i, |e i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |e i| * R := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((coordinate_abs_le_euclideanNorm x i).trans hx'.le)
          (abs_nonneg _)
    _ = (∑ i, |e i|) * R := by rw [Finset.sum_mul]

/-- The growth condition of `A₁` for `e·x + u` with `u` sublinear. -/
theorem tendsto_growth_dot_add (e : Vec d) {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |dot e x + u x| ^ 2))
      atTop (𝓝 0) := by
  set A := ∑ i, |e i|
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h0 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto (fun R : ℝ => Real.sqrt 2 * A * R⁻¹ +
      Real.sqrt 2 * (R⁻¹ * (R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)))) atTop (𝓝 0) := by
    have := (h0.const_mul (Real.sqrt 2 * A)).add ((h0.mul hsub).const_mul (Real.sqrt 2))
    simpa using this
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact mul_nonneg (zpow_nonneg hR.le _) (Real.sqrt_nonneg _)
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
  have hV : 0 < volume.real (ball (0 : Vec d) R) :=
    ENNReal.toReal_pos (volume_ball_ne_zero hR) (volume_ball_ne_top hR)
  have hint : Integrable (fun x => u x ^ 2) (volume.restrict (ball 0 R)) :=
    (hu R hR).integrable_sq
  have hpt : ∀ x ∈ ball (0 : Vec d) R, |dot e x + u x| ^ 2 ≤ 2 * (A * R) ^ 2 + 2 * u x ^ 2 := by
    intro x hx
    have h1 := abs_dot_le_mul_of_mem_ball e hx
    have h2 : (dot e x) ^ 2 ≤ (A * R) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs]
    nlinarith [sq_nonneg (dot e x - u x)]
  have hmono : ⨍ x in ball 0 R, |dot e x + u x| ^ 2 ≤
      2 * (A * R) ^ 2 + 2 * ⨍ x in ball 0 R, u x ^ 2 := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    have hI : ∫ x in ball (0 : Vec d) R, |dot e x + u x| ^ 2 ≤
        ∫ x in ball (0 : Vec d) R, (2 * (A * R) ^ 2 + 2 * u x ^ 2) :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
        ((integrable_const _).add (hint.const_mul 2))
        ((ae_restrict_iff' (measurableSet_ball_zero' R)).mpr (Eventually.of_forall hpt))
    rw [integral_add (integrable_const _) (hint.const_mul 2), integral_const, integral_const_mul,
      smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hI
    have hV' : (volume (ball (0 : Vec d) R)).toReal = volume.real (ball (0 : Vec d) R) := rfl
    rw [hV'] at hI
    calc (volume.real (ball (0 : Vec d) R))⁻¹ * ∫ x in ball (0 : Vec d) R, |dot e x + u x| ^ 2
        ≤ (volume.real (ball (0 : Vec d) R))⁻¹ * (volume.real (ball (0 : Vec d) R) *
            (2 * (A * R) ^ 2) + 2 * ∫ x in ball (0 : Vec d) R, u x ^ 2) :=
          mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hV.le)
      _ = 2 * (A * R) ^ 2 + 2 * ((volume.real (ball (0 : Vec d) R))⁻¹ *
            ∫ x in ball (0 : Vec d) R, u x ^ 2) := by
          field_simp
  have hm0 : 0 ≤ ⨍ x in ball 0 R, u x ^ 2 :=
    setAverage_nonneg_of_nonneg fun x => sq_nonneg _
  have hsqrt : Real.sqrt (⨍ x in ball 0 R, |dot e x + u x| ^ 2) ≤
      Real.sqrt 2 * (A * R) + Real.sqrt 2 * Real.sqrt (⨍ x in ball 0 R, u x ^ 2) := by
    refine (Real.sqrt_le_sqrt hmono).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs : Real.sqrt (⨍ x in ball 0 R, u x ^ 2) ^ 2 = ⨍ x in ball 0 R, u x ^ 2 :=
      Real.sq_sqrt hm0
    have hp : 0 ≤ Real.sqrt 2 * (A * R) *
        (Real.sqrt 2 * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) := by
      positivity
    nlinarith
  have hR2 : R ^ (-2 : ℤ) = R⁻¹ * R⁻¹ := by
    rw [zpow_neg, zpow_two, mul_inv]
  calc R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |dot e x + u x| ^ 2)
      ≤ R ^ (-2 : ℤ) * (Real.sqrt 2 * (A * R) + Real.sqrt 2 *
          Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) :=
        mul_le_mul_of_nonneg_left hsqrt (zpow_nonneg hR.le _)
    _ = Real.sqrt 2 * A * R⁻¹ +
          Real.sqrt 2 * (R⁻¹ * (R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2))) := by
        rw [hR2]
        field_simp

/-- **A sublinear corrector of slope `e` gives an element `e·x + φ` of `A₁`.** -/
theorem exists_harmonicA1_of_corrector {Λ : ℝ} (a : CoefficientField d Λ) (e : Vec d)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hw : HasWeakGradient Set.univ u g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (hharm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)) atTop (𝓝 0)) :
    ∃ w : HarmonicA1 a, w.potential = (fun x => dot e x + u x) ∧ w.grad = fun x => e + g x := by
  have hwg : HasWeakGradient Set.univ (fun x => dot e x + u x) (fun x => e + g x) :=
    hasWeakGradient_add (hasWeakGradient_dot e) hw
  have hpot : ∀ R : ℝ, 0 < R →
      MemLp (fun x => dot e x + u x) 2 (volume.restrict (ball 0 R)) := by
    intro R hR
    have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
    have hcont : Continuous fun x : Vec d => dot e x := by unfold dot; fun_prop
    have hlin : MemLp (fun x : Vec d => dot e x) 2 (volume.restrict (ball 0 R)) := by
      refine MemLp.of_bound hcont.aestronglyMeasurable ((∑ i, |e i|) * R) ?_
      filter_upwards [ae_restrict_mem (measurableSet_ball_zero' R)] with x hx
      rw [Real.norm_eq_abs]
      exact abs_dot_le_mul_of_mem_ball e hx
    exact hlin.add (hloc R hR).1
  have hgrad : ∀ R : ℝ, 0 < R →
      MemLp (fun x => euclideanNorm (e + g x)) 2 (volume.restrict (ball 0 R)) := by
    intro R hR
    have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
    have hG : MemLp (fun x => e + g x) 2 (volume.restrict (ball 0 R)) :=
      (memLp_const e).add (hloc R hR).2
    have hcont : Continuous fun v : Vec d => euclideanNorm v := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    refine hG.norm.of_le_mul (c := (d : ℝ) + 1)
      (hcont.comp_aestronglyMeasurable hG.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ euclideanNorm (e + g x) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0, norm_norm]
    exact euclideanNorm_le_dimension_mul_norm _
  have hgrowth := tendsto_growth_dot_add e (fun R hR => (hloc R hR).1)
    (sublinear_uncentered_of_centered u (fun R hR => (hloc R hR).1) hsub)
  exact ⟨{ potential := fun x => dot e x + u x
           grad := fun x => e + g x
           weak_gradient := hwg
           local_energy := fun R hR => ⟨hpot R hR, hgrad R hR⟩
           harmonic := hharm
           growth := hgrowth }, rfl, rfl⟩

/-! ## Sublinearity on Euclidean balls and on closed sup-norm balls -/

theorem norm_sq_eq_integral_of_ae_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : Lp ℝ 2 μ} {φ : X → ℝ} (h : f =ᵐ[μ] φ) : ‖f‖ ^ 2 = ∫ x, φ x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem closedBall_subset_ball_dimension (n : ℕ) :
    Metric.closedBall (0 : Vec d) n ⊆ ball 0 (((d : ℝ) + 1) * ((n : ℝ) + 1)) := by
  intro y hy
  change euclideanNorm (y - 0) < _
  rw [sub_zero]
  have hy' : ‖y‖ ≤ (n : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  calc euclideanNorm y ≤ ((d : ℝ) + 1) * ‖y‖ := euclideanNorm_le_dimension_mul_norm y
    _ ≤ ((d : ℝ) + 1) * (n : ℝ) := mul_le_mul_of_nonneg_left hy' (by positivity)
    _ < ((d : ℝ) + 1) * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left (by linarith) (by positivity)

theorem ball_subset_closedBall_zero (R : ℝ) :
    ball (0 : Vec d) R ⊆ Metric.closedBall (0 : Vec d) R := by
  intro y hy
  have hy' : euclideanNorm (y - 0) < R := hy
  rw [sub_zero] at hy'
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_euclideanNorm y).trans hy'.le

theorem memLp_closedBall_of_memLp_ball {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) (n : ℕ) :
    MemLp u 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)) :=
  (hu _ (by positivity)).mono_measure
    (Measure.restrict_mono (closedBall_subset_ball_dimension n) le_rfl)

/-- **Sublinearity on the closed balls `B̄ₙ` gives the centered sublinearity on `B_R`.** -/
theorem tendsto_sublinear_of_closedBall {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hA : Tendsto (fun n : ℕ => (∫ x in Metric.closedBall (0 : Vec d) n, u x ^ 2) /
      (n : ℝ) ^ (d + 2)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)) atTop (𝓝 0) := by
  set c := (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal with hcdef
  have hc : 0 < c :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  set a : ℕ → ℝ := fun n => (∫ x in Metric.closedBall (0 : Vec d) n, u x ^ 2) /
    (n : ℝ) ^ (d + 2) with hadef
  have hlim : Tendsto (fun R : ℝ => Real.sqrt (2 ^ (d + 2) / c * a ⌈R⌉₊)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => a ⌈R⌉₊) atTop (𝓝 0) := hA.comp tendsto_nat_ceil_atTop
    have h2 := (h1.const_mul (2 ^ (d + 2) / c)).sqrt
    simpa using h2
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg (inv_nonneg.mpr hR.le) (Real.sqrt_nonneg _)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
  have hR : 0 < R := by linarith
  set N := ⌈R⌉₊
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 < N := Nat.ceil_pos.mpr hR
    exact_mod_cast this
  have hRN : R ≤ N := Nat.le_ceil R
  have hNR : (N : ℝ) ≤ 2 * R := by
    have := Nat.ceil_lt_add_one hR.le
    linarith
  have hX := setAverage_sq_sub_setAverage_le (volume_ball_ne_zero hR) (volume_ball_ne_top hR)
    (hu R hR) 0
  simp only [sub_zero] at hX
  have hI0 : 0 ≤ ∫ x in Metric.closedBall (0 : Vec d) N, u x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hmono : ∫ x in ball (0 : Vec d) R, u x ^ 2 ≤
      ∫ x in Metric.closedBall (0 : Vec d) N, u x ^ 2 := by
    refine setIntegral_mono_set ((memLp_closedBall_of_memLp_ball hu N).integrable_sq)
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall ?_)
    exact (ball_subset_closedBall_zero R).trans (Metric.closedBall_subset_closedBall hRN)
  have havg : ⨍ x in ball 0 R, u x ^ 2 ≤ (R ^ d * c)⁻¹ *
      ∫ x in Metric.closedBall (0 : Vec d) N, u x ^ 2 := by
    rw [setAverage_eq, smul_eq_mul, volume_real_ball hR]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hm0 : 0 ≤ ⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume :=
    setAverage_nonneg_of_nonneg fun x => sq_nonneg _
  have hpow : (N : ℝ) ^ (d + 2) / 2 ^ (d + 2) ≤ R ^ (d + 2) := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hkey : R⁻¹ ^ 2 * ⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume ≤
      2 ^ (d + 2) / c * a N := by
    have hR0 : R ≠ 0 := hR.ne'
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    calc R⁻¹ ^ 2 * ⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume
        ≤ R⁻¹ ^ 2 * ((R ^ d * c)⁻¹ * ∫ x in Metric.closedBall (0 : Vec d) N, u x ^ 2) :=
          mul_le_mul_of_nonneg_left (hX.trans havg) (by positivity)
      _ = (∫ x in Metric.closedBall (0 : Vec d) N, u x ^ 2) / (c * R ^ (d + 2)) := by
          field_simp
          ring
      _ ≤ (∫ x in Metric.closedBall (0 : Vec d) N, u x ^ 2) /
            (c * ((N : ℝ) ^ (d + 2) / 2 ^ (d + 2))) :=
          div_le_div_of_nonneg_left hI0 (by positivity) (mul_le_mul_of_nonneg_left hpow hc.le)
      _ = 2 ^ (d + 2) / c * a N := by
          simp only [hadef]
          field_simp
  have hsq : R⁻¹ * Real.sqrt (⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume) =
      Real.sqrt (R⁻¹ ^ 2 * ⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq]
  exact Real.sqrt_le_sqrt hkey

/-- **Sublinearity on `B_R` gives sublinearity on the closed balls `B̄ₙ`.** -/
theorem tendsto_closedBall_of_sublinear {φ : Vec d → ℝ}
    (hφ : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, φ x ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ x in Metric.closedBall (0 : Vec d) n, φ x ^ 2) /
      (n : ℝ) ^ (d + 2)) atTop (𝓝 0) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]
    exact ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne'
      (volume_euclideanBall_ne_top' 1)
  have hvol : ∀ ρ : ℝ, 0 < ρ → volume.real (ball (0 : Vec d) ρ) = ρ ^ d * c := fun ρ hρ => by
    rw [volume_real_ball hρ, hcdef]
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = c * (2 * ((d : ℝ) + 1)) ^ (d + 2) := ⟨_, rfl⟩
  have hρ : Tendsto (fun n : ℕ => ((d : ℝ) + 1) * ((n : ℝ) + 1)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.const_mul_atTop (by positivity)
  have hlim : Tendsto (fun n : ℕ => K * ((((d : ℝ) + 1) * ((n : ℝ) + 1))⁻¹ *
      Real.sqrt (⨍ x in ball 0 (((d : ℝ) + 1) * ((n : ℝ) + 1)), φ x ^ 2)) ^ 2) atTop (𝓝 0) := by
    have := ((hsub.comp hρ).pow 2).const_mul K
    simpa using this
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun n =>
      div_nonneg (integral_nonneg fun x => sq_nonneg _) (by positivity)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsubset := closedBall_subset_ball_dimension (d := d) n
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ((d : ℝ) + 1) * ((n : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hRdef] at hsubset ⊢
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hmono : ∫ x in Metric.closedBall (0 : Vec d) n, φ x ^ 2 ≤
      ∫ x in ball (0 : Vec d) R, φ x ^ 2 :=
    setIntegral_mono_set ((hφ _ hR0).integrable_sq) (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall hsubset)
  have hm0 : 0 ≤ ⨍ x in ball 0 R, φ x ^ 2 := setAverage_nonneg_of_nonneg fun x => sq_nonneg _
  have hV : volume.real (ball (0 : Vec d) R) ≠ 0 :=
    (ENNReal.toReal_pos (volume_ball_ne_zero hR0) (volume_ball_ne_top hR0)).ne'
  have hint : ∫ x in ball (0 : Vec d) R, φ x ^ 2 = R ^ d * c * ⨍ x in ball 0 R, φ x ^ 2 := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, ← hvol R hR0, mul_inv_cancel₀ hV, one_mul]
  have hsq : (R⁻¹ * Real.sqrt (⨍ x in ball 0 R, φ x ^ 2)) ^ 2 =
      R⁻¹ ^ 2 * ⨍ x in ball 0 R, φ x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm0]
  have hratio : R ^ (d + 2) ≤ (2 * ((d : ℝ) + 1)) ^ (d + 2) * (n : ℝ) ^ (d + 2) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ hR0.le ?_ _
    rw [hRdef]
    nlinarith
  have hn0 : (0 : ℝ) < (n : ℝ) ^ (d + 2) := by positivity
  rw [div_le_iff₀ hn0, hsq]
  have hR0' : R ≠ 0 := hR0.ne'
  calc ∫ x in Metric.closedBall (0 : Vec d) n, φ x ^ 2 ≤ R ^ d * c * ⨍ x in ball 0 R, φ x ^ 2 :=
        hmono.trans hint.le
    _ = c * R ^ (d + 2) * (R⁻¹ ^ 2 * ⨍ x in ball 0 R, φ x ^ 2) := by
        field_simp
        ring
    _ ≤ c * ((2 * ((d : ℝ) + 1)) ^ (d + 2) * (n : ℝ) ^ (d + 2)) *
          (R⁻¹ ^ 2 * ⨍ x in ball 0 R, φ x ^ 2) := by
        gcongr
    _ = K * (R⁻¹ ^ 2 * ⨍ x in ball 0 R, φ x ^ 2) * (n : ℝ) ^ (d + 2) := by
        rw [hKdef]
        ring

/-! ## Linear functions on balls -/

/-- An element of `A₁` minus the linear function of slope `e`, with locally square integrable
gradient. -/
theorem HarmonicA1.memLp_sub_dot {Λ : ℝ} {a : CoefficientField d Λ} (w : HarmonicA1 a)
    (e : Vec d) {R : ℝ} (hR : 0 < R) :
    MemLp (fun x => w.potential x - dot e x) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (fun x => w.grad x - e) 2 (volume.restrict (ball 0 R)) := by
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top hR)
  refine ⟨(w.local_energy R hR).1.sub (memLp_dot_ball e R), ?_⟩
  have hg : MemLp w.grad 2 (volume.restrict (ball 0 R)) := by
    refine memLp_pi_iff.mpr fun i => ?_
    have hgi : AEStronglyMeasurable (fun x => w.grad x i) volume := by
      simpa only [Measure.restrict_univ] using (w.weak_gradient i).2.1.aestronglyMeasurable
    refine (w.local_energy R hR).2.of_le hgi.restrict (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (coordinate_abs_le_euclideanNorm (w.grad x) i).trans (le_abs_self _)
  exact hg.sub (memLp_const e)

/-! ## The measurability -/

/-- **The corrector gradients have a jointly measurable version**, Definition 3.14. -/
theorem highContrastCorrectorMeasurable : HighContrastCorrectorMeasurable := by
  intro d hd Λ hΛ P hP κ C hκ hC pk e
  classical
  have : NeZero d := ⟨by omega⟩
  have := hP.1
  let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
  let E := ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n)
  let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
  let Fg := ∀ n : ℕ, Fin d → Lp ℝ 2 (μ n)
  let W := ∀ n : ℕ, Lp ℝ 2 (μ n)
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let (n : ℕ) : IsSeparable (μ n) := by dsimp [μ]; infer_instance
  let (n : ℕ) : SecondCountableTopology (Lp ℝ 2 (μ n)) := inferInstance
  let : SecondCountableTopology E := inferInstance
  let : SecondCountableTopology F := inferInstance
  let : SecondCountableTopology Fg := inferInstance
  let : SecondCountableTopology W := inferInstance
  let : MeasurableSpace E := borel E
  let : MeasurableSpace F := borel F
  let : MeasurableSpace Fg := borel Fg
  let : MeasurableSpace W := borel W
  let : BorelSpace E := ⟨rfl⟩
  let : BorelSpace F := ⟨rfl⟩
  let : BorelSpace Fg := ⟨rfl⟩
  let : BorelSpace W := ⟨rfl⟩
  obtain ⟨Cenc, hPolish, hCm, hCa⟩ := coarseGaussian_hencoding (d := d) (K := Λ) (by linarith)
  let : PolishSpace E := hPolish
  let : PolishSpace F := inferInstance
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  let G := {s : E × F |
    (∀ (n : ℕ) (φ : Vec d → ℝ), IsSpatialTest Set.univ φ →
      tsupport φ ⊆ Metric.closedBall (0 : Vec d) n →
      (∀ i : Fin d,
        (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i φ x) =
          -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * φ x)) ∧
      (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
        coordinateDerivative i φ x * s.1 n i j x * (s.2 n).2 j x) = 0) ∧
    (∀ n m : ℕ, ((s.2 n).1 : Vec d → ℝ) =ᵐ[volume.restrict
      (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (s.2 m).1) ∧
    (∀ (n m : ℕ) (i : Fin d), ((s.2 n).2 i : Vec d → ℝ) =ᵐ[volume.restrict
      (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (s.2 m).2 i) ∧
    Tendsto (fun n : ℕ => ‖(s.2 n).1‖ ^ 2 / (n : ℝ) ^ (d + 4)) atTop (𝓝 0)}
  obtain ⟨hG, -⟩ : MeasurableSet G ∧ ∀ A : E, (A, fun _ => (0, fun _ => 0)) ∈ G :=
    coarseGaussian_hgraph d
  have hfiber (a : CoefficientField d Λ) (v : F) : (Cenc a, v) ∈ G ↔
      ∃ w : HarmonicA1 a, ∀ n, (v n).1 =ᵐ[μ n] w.potential ∧
        ∀ i, (v n).2 i =ᵐ[μ n] (fun x => w.grad x i) :=
    coarseGaussian_hfiber (by linarith) a (Cenc a) (hCa a) (fun n => (v n).1) (fun n => (v n).2)
  -- the linear function of slope `e` on the closed balls
  have hℓ (n : ℕ) : MemLp (fun x : Vec d => dot e x) 2 (μ n) :=
    (memLp_dot_ball e (((d : ℝ) + 1) * ((n : ℝ) + 1))).mono_measure
      (Measure.restrict_mono (closedBall_subset_ball_dimension n) le_rfl)
  let ℓ : ∀ n : ℕ, Lp ℝ 2 (μ n) := fun n => (hℓ n).toLp (fun x => dot e x)
  let S := {v : F | Tendsto (fun n : ℕ => ‖(v n).1 - ℓ n‖ ^ 2 / (n : ℝ) ^ (d + 2)) atTop (𝓝 0)}
  have hS : MeasurableSet S := by
    apply measurableSet_tendsto_fun (g := fun _ => (0 : ℝ))
    · intro n
      have hn : Continuous (fun v : F => ‖(v n).1 - ℓ n‖ ^ 2 / (n : ℝ) ^ (d + 2)) := by fun_prop
      exact hn.measurable
    · exact measurable_const
  let Γ := G ∩ Prod.snd ⁻¹' S
  have hΓ : MeasurableSet Γ := hG.inter (hS.preimage measurable_snd)
  -- the full corrected gradient `e + ∇φ_e`
  let gfull (a : CoefficientField d Λ) (x : Vec d) : Vec d :=
    e + undilatedGradient (pk.gradPhi e (toHighContrast hΛ a)) x
  -- the norm of `v n - ℓ n` for a potential `e·x + u`
  have hnorm (n : ℕ) (f : Lp ℝ 2 (μ n)) (u : Vec d → ℝ)
      (hf : f =ᵐ[μ n] fun x => dot e x + u x) :
      ‖f - ℓ n‖ ^ 2 = ∫ x in Metric.closedBall (0 : Vec d) n, u x ^ 2 := by
    refine norm_sq_eq_integral_of_ae_eq ?_
    filter_upwards [Lp.coeFn_sub f (ℓ n), hf, (hℓ n).coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    ring
  -- uniqueness on the fiber
  have hunique (a : CoefficientField d Λ) (hb : toHighContrast hΛ a ∈ pk.Ωend) (v : F)
      (hv : (Cenc a, v) ∈ Γ) :
      ∀ n i, (v n).2 i =ᵐ[μ n] fun x => gfull a x i := by
    obtain ⟨hvG, hvS⟩ := hv
    obtain ⟨w, hw⟩ := (hfiber a v).mp hvG
    set u : Vec d → ℝ := fun x => w.potential x - dot e x
    set g : Vec d → Vec d := fun x => w.grad x - e
    have hwg : HasWeakGradient Set.univ u g := hasWeakGradient_sub w.weak_gradient
      (hasWeakGradient_dot e)
    have hloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
        MemLp g 2 (volume.restrict (ball 0 R)) := fun R hR => w.memLp_sub_dot e hR
    have hharm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0) := by
      have heq : (fun x => (a x).mulVec (e + g x)) = fun x => (a x).mulVec (w.grad x) := by
        funext x
        simp only [g, add_sub_cancel]
      rw [heq]
      exact w.harmonic
    have hA : Tendsto (fun n : ℕ => (∫ x in Metric.closedBall (0 : Vec d) n, u x ^ 2) /
        (n : ℝ) ^ (d + 2)) atTop (𝓝 0) := by
      refine hvS.congr fun n => ?_
      rw [hnorm n (v n).1 u ?_]
      filter_upwards [(hw n).1] with x hx
      rw [hx]
      simp only [u]
      ring
    have hsub := tendsto_sublinear_of_closedBall (fun R hR => (hloc R hR).1) hA
    have hid := dilatedGradient_ae_eq_highContrast hd hκ hC pk hb hwg hloc hharm hsub
    have hq : Measure.QuasiMeasurePreserving (fun x : Vec d => (2 : ℝ)⁻¹ • x) volume volume :=
      Measure.quasiMeasurePreserving_smul volume (inv_ne_zero two_ne_zero)
    have hg_eq : ∀ᵐ x ∂(volume : Measure (Vec d)), w.grad x = gfull a x := by
      filter_upwards [hq.ae hid] with x hx
      simp only [dilatedGradient, smul_inv_smul₀ (two_ne_zero' ℝ)] at hx
      simp only [gfull, undilatedGradient, ← hx, g]
      abel
    intro n i
    filter_upwards [(hw n).2 i, ae_restrict_of_ae hg_eq] with x h1 h2
    rw [h1, h2]
  -- existence on the fiber
  have hexists (a : CoefficientField d Λ) (hb : toHighContrast hΛ a ∈ pk.Ωend) :
      ∃ v : F, (Cenc a, v) ∈ Γ ∧ ∀ n i, (v n).2 i =ᵐ[μ n] fun x => gfull a x i := by
    have hbell := ae_isEllipticMatrix_toHighContrast hΛ a
    set u := undilatedPotential (pk.Phi e (toHighContrast hΛ a))
    set g := undilatedGradient (pk.gradPhi e (toHighContrast hΛ a))
    have hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) :=
      fun R hR => memLp_undilatedPotential_ball pk hb hbell e hR
    have hloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
        MemLp g 2 (volume.restrict (ball 0 R)) :=
      fun R hR => ⟨hu R hR, memLp_undilatedGradient_ball pk hb hbell e hR⟩
    have hsub := tendsto_sublinear_undilatedPotential hd hκ hC pk hb hbell e
    obtain ⟨w, hwp, hwg⟩ := exists_harmonicA1_of_corrector a e
      (hasWeakGradient_undilatedPotential pk hb hbell e) hloc
      (hasWeakDivergence_undilated hΛ a e (pk.equation _ hb e).2
        fun R hR => memLp_undilatedGradient_ball pk hb hbell e hR) hsub
    obtain ⟨U, H, hUH⟩ := coarseGaussian_hclasses w
    let v : F := fun n => (U n, H n)
    have hvG : (Cenc a, v) ∈ G := (hfiber a v).mpr ⟨w, hUH⟩
    have hvS : v ∈ S := by
      have h := tendsto_closedBall_of_sublinear hu (sublinear_uncentered_of_centered u hu hsub)
      refine h.congr fun n => ?_
      rw [hnorm n (U n) u ?_]
      filter_upwards [(hUH n).1] with x hx
      rw [hx, hwp]
    refine ⟨v, ⟨hvG, hvS⟩, fun n i => ?_⟩
    filter_upwards [(hUH n).2 i] with x hx
    rw [hx, hwg]
  -- the gradient as an element of `∏ₙ L²(B̄ₙ)^d`
  let ĝ : CoefficientField d Λ → Fg := fun a =>
    if h : ∀ n i, MemLp (fun x => gfull a x i) 2 (μ n) then
      fun n i => (h n i).toLp (fun x => gfull a x i)
    else 0
  have hĝ (a : CoefficientField d Λ) (hb : toHighContrast hΛ a ∈ pk.Ωend) :
      ∀ n i, ĝ a n i =ᵐ[μ n] fun x => gfull a x i := by
    obtain ⟨v, -, hv⟩ := hexists a hb
    have hm : ∀ n i, MemLp (fun x => gfull a x i) 2 (μ n) := fun n i =>
      (Lp.memLp ((v n).2 i)).ae_eq (hv n i)
    have hĝa : ĝ a = fun n i => (hm n i).toLp (fun x => gfull a x i) :=
      dite_eq_left_of_eq_true (eq_true hm)
    intro n i
    rw [hĝa]
    exact (hm n i).coeFn_toLp
  have hgood : ∀ᵐ a ∂P, toHighContrast hΛ a ∈ pk.Ωend := ae_mem_Ωend hP pk
  -- the events `{ĝ ∈ B}` are null measurable
  have hnull : NullMeasurable ĝ P := by
    intro B hB
    let B' : Set F := {v | (fun n i => (v n).2 i : Fg) ∈ B}
    have hB' : MeasurableSet B' := by
      have hc : Continuous (fun v : F => (fun n i => (v n).2 i : Fg)) := by fun_prop
      exact hc.measurable hB
    let T : Set E := Prod.fst '' (Γ ∩ Prod.snd ⁻¹' B')
    have hT : AnalyticSet T := (hΓ.inter (hB'.preimage measurable_snd)).analyticSet_image
      measurable_fst
    have hTnull : NullMeasurableSet T (P.map Cenc) := by
      let J : E → ℝ := T.indicator fun _ => 1
      have hJ : ∀ t : ℝ, AnalyticSet {x | t < J x} := by
        intro t
        by_cases h0 : t < 0
        · have : {x | t < J x} = Set.univ := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, J]
            by_cases hx : x ∈ T
            · rw [Set.indicator_of_mem hx]; linarith
            · rw [Set.indicator_of_notMem hx]; exact h0
          rw [this]
          exact MeasurableSet.univ.analyticSet
        · by_cases h1 : t < 1
          · have : {x | t < J x} = T := by
              ext x
              simp only [Set.mem_ofPred_eq, J]
              by_cases hx : x ∈ T
              · rw [Set.indicator_of_mem hx]; exact ⟨fun _ => hx, fun _ => h1⟩
              · rw [Set.indicator_of_notMem hx]
                exact ⟨fun h => absurd h (by linarith), fun h => absurd h hx⟩
            rw [this]
            exact hT
          · have : {x | t < J x} = ∅ := by
              ext x
              simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, J]
              by_cases hx : x ∈ T
              · rw [Set.indicator_of_mem hx]; linarith
              · rw [Set.indicator_of_notMem hx]; linarith
            rw [this]
            exact MeasurableSet.empty.analyticSet
      have hJm := aestronglyMeasurable_of_analyticSet_upperCuts (P.map Cenc) J hJ
      have hpre : {x | (1 / 2 : ℝ) < J x} = T := by
        ext x
        simp only [Set.mem_ofPred_eq, J]
        by_cases hx : x ∈ T
        · rw [Set.indicator_of_mem hx]
          exact ⟨fun _ => hx, fun _ => by norm_num⟩
        · rw [Set.indicator_of_notMem hx]
          exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hx⟩
      rw [← hpre]
      exact hJm.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
    have hqmp : Measure.QuasiMeasurePreserving Cenc P (P.map Cenc) :=
      ⟨hCm, Measure.AbsolutelyContinuous.rfl⟩
    refine (hTnull.preimage hqmp).congr ?_
    filter_upwards [hgood] with a hb
    apply propext
    constructor
    · rintro ⟨⟨A, v⟩, ⟨hAv, hvB⟩, hA⟩
      change A = Cenc a at hA
      subst hA
      have hv := hunique a hb v hAv
      change ĝ a ∈ B
      have heq : (fun n i => (v n).2 i : Fg) = ĝ a := by
        funext n i
        exact Lp.ext ((hv n i).trans (hĝ a hb n i).symm)
      change (fun n i => (v n).2 i : Fg) ∈ B at hvB
      rwa [← heq]
    · intro ha
      obtain ⟨v, hvΓ, hv⟩ := hexists a hb
      refine ⟨(Cenc a, v), ⟨hvΓ, ?_⟩, rfl⟩
      change (fun n i => (v n).2 i : Fg) ∈ B
      have heq : (fun n i => (v n).2 i : Fg) = ĝ a := by
        funext n i
        exact Lp.ext ((hv n i).trans (hĝ a hb n i).symm)
      rw [heq]
      exact ha
  have hae : AEMeasurable ĝ P := hnull.aemeasurable
  -- a jointly measurable representative
  obtain ⟨Rep, hRep, hRepa⟩ := coarseGaussian_hrepresentative d
  let Gm : CoefficientField d Λ × Vec d → Vec d := fun p i =>
    Rep (fun n => hae.mk ĝ p.1 n i) p.2 - e i
  refine ⟨Gm, ?_, ?_⟩
  · refine measurable_pi_iff.mpr fun i => ?_
    have hproj : Continuous (fun f : Fg => (fun n => f n i : W)) := by fun_prop
    have hm : Measurable (fun p : CoefficientField d Λ × Vec d =>
        ((fun n => hae.mk ĝ p.1 n i : W), p.2)) :=
      ((hproj.measurable.comp hae.measurable_mk).comp measurable_fst).prodMk measurable_snd
    exact (hRep.comp hm).sub measurable_const
  · filter_upwards [hgood, hae.ae_eq_mk] with a hb hmk
    have hrep : ∀ i, (fun x => Rep (fun n => hae.mk ĝ a n i) x) =ᵐ[volume]
        fun x => gfull a x i := by
      intro i
      refine hRepa _ _ fun n => ?_
      rw [← hmk]
      exact hĝ a hb n i
    filter_upwards [ae_all_iff.mpr hrep] with x hx
    funext i
    simp only [Gm, hx i, gfull, Pi.add_apply]
    ring

/-- **Existence of homogenization data for every law**: correctors in every direction and the
homogenized matrix with the limit (1.22). -/
theorem homogenizationDataExists : HomogenizationDataExists :=
  homogenizationDataExists_of_measurable highContrastCorrectorMeasurable

end QSH
