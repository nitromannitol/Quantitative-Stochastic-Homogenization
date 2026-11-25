import QuantitativeStochasticHomogenization.Ch01.Sec05.BoundaryLayer
import PDEFoundation.PDE.HarmonicConvolution
import PDEFoundation.PDE.HarmonicKernel
import PDEFoundation.PDE.HarmonicApproximation

/-!
# The cutoff function (1.60) on convex domains

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, the cutoff `η_r` of the proof of Theorem 1.17: `0 ≤ η_r ≤ 1`, `η_r = 1` away from a
boundary layer of thickness `C r`, `η_r` vanishes near `∂U`, and `|∇^k η_r| ≤ C r^{-k}` for
`k = 1, 2`, the orders used in (1.65).

The cutoff is the mollified indicator `ρ_t ⋆ 1_A` (`mollifiedIndicator`) of the homothetic copy
`A = x₀ + (1 - r/2)(U - x₀)` of a convex domain `U ⊇ B_ρ(x₀)`, with the radial kernel `ρ_t` of the
elliptic regularity library at scale `t = ρ r / 8`. Its derivatives are `∂^α ρ_t ⋆ 1_A`, bounded by
`‖∂^α ρ_t‖_{L¹} = t^{-|α|} ‖∂^α ρ_1‖_{L¹}`. Every point of the support of `η_r` has the Euclidean
ball of radius `ρ r / 4` inside `U`, and `η_r = 1` on `x₀ + (1 - r)(U - x₀)`, so that
`|{x ∈ U : η_r(x) ≠ 1}| ≤ d r |U|` (`exists_cutoff_of_convex`). The book uses the sets
`U_r = {x ∈ U : dist(x, ∂U) > r}` of a Lipschitz domain instead of the homothetic copies.
-/

open MeasureTheory Set
open scoped Convolution

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ}

/-! ## The scaled kernel -/

theorem euclideanCoordDeriv_const_mul' {f : Vec d → ℝ} {x : Vec d} (j : Fin d) (c : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    PDE.euclideanCoordDeriv j (fun y => c * f y) x = c * PDE.euclideanCoordDeriv j f x := by
  unfold PDE.euclideanCoordDeriv
  rw [fderiv_const_mul hf c]
  simp [smul_eq_mul]

theorem euclideanCoordSecondDeriv_harmonicKernelScaled (i j : Fin d) {s : ℝ} (y : Vec d) :
    PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernelScaled (d := d) s) y =
      (s⁻¹ ^ d * s⁻¹ * s⁻¹) *
        PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) (s⁻¹ • y) := by
  have h1 : PDE.euclideanCoordDeriv i (PDE.harmonicKernelScaled (d := d) s) =
      fun z => (s⁻¹ ^ d * s⁻¹) *
        PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) (s⁻¹ • z) :=
    funext (PDE.harmonicKernelScaled_deriv i)
  have hf : ContDiff ℝ (⊤ : ℕ∞) (PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d))) :=
    PDE.contDiff_euclideanCoordDeriv PDE.harmonicKernel_smooth i
  have hcomp := PDE.euclideanCoordDeriv_comp_smul_add hf s⁻¹ (0 : Vec d) y j
  simp only [add_zero] at hcomp
  have hdiff : DifferentiableAt ℝ
      (fun z : Vec d => PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) (s⁻¹ • z)) y :=
    ((hf.comp (contDiff_id.const_smul s⁻¹)).differentiable (by simp)) y
  unfold PDE.euclideanCoordSecondDeriv
  rw [h1]
  change PDE.euclideanCoordDeriv j (fun z => (s⁻¹ ^ d * s⁻¹) *
      PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) (s⁻¹ • z)) y = _
  rw [euclideanCoordDeriv_const_mul' j _ hdiff, hcomp]
  unfold PDE.euclideanCoordDeriv
  ring

theorem integrable_euclideanCoordSecondDeriv_harmonicKernelScaled (i j : Fin d) {s : ℝ}
    (hs : 0 < s) :
    Integrable (PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernelScaled (d := d) s)) :=
  (PDE.contDiff_euclideanCoordSecondDeriv (PDE.harmonicKernelScaled_smooth s) i j).continuous
    |>.integrable_of_hasCompactSupport
      (PDE.hasCompactSupport_euclideanCoordDeriv
        (PDE.hasCompactSupport_euclideanCoordDeriv
          (PDE.harmonicKernelScaled_hasCompactSupport hs) i) j)

theorem integral_abs_euclideanCoordSecondDeriv_harmonicKernelScaled (i j : Fin d) {s : ℝ}
    (hs : 0 < s) :
    (∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernelScaled (d := d) s) y|) =
      s⁻¹ * s⁻¹ * ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y| := by
  have hcoeff : 0 ≤ s⁻¹ ^ d * s⁻¹ * s⁻¹ := by positivity
  have hpoint : ∀ y : Vec d,
      |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernelScaled (d := d) s) y| =
        (s⁻¹ ^ d * s⁻¹ * s⁻¹) *
          |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) (s⁻¹ • y)| := by
    intro y
    rw [euclideanCoordSecondDeriv_harmonicKernelScaled, abs_mul, abs_of_nonneg hcoeff]
  calc
    _ = (s⁻¹ ^ d * s⁻¹ * s⁻¹) *
        ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) (s⁻¹ • y)| := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul]
    _ = (s⁻¹ ^ d * s⁻¹ * s⁻¹) *
        (s ^ d * ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y|) := by
      rw [Measure.integral_comp_inv_smul_of_nonneg volume
        (fun y => |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y|) hs.le]
      have hdim : Module.finrank ℝ (Vec d) = d := by simp [Vec]
      rw [hdim, smul_eq_mul]
    _ = s⁻¹ * s⁻¹ *
        ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y| := by
      rw [inv_pow]
      field_simp [hs.ne']

/-! ## The mollified indicator -/

/-- The mollified indicator `ρ_t ⋆ 1_A` of a set `A` at scale `t`. -/
def mollifiedIndicator (t : ℝ) (A : Set (Vec d)) : Vec d → ℝ :=
  PDE.harmonicKernelScaled t ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A.indicator (fun _ => 1)

theorem locallyIntegrable_indicator_one {A : Set (Vec d)} (hA : MeasurableSet A) :
    LocallyIntegrable (A.indicator (fun _ => (1 : ℝ))) volume :=
  (locallyIntegrable_const (1 : ℝ)).indicator hA

theorem convolution_indicator_apply (K : Vec d → ℝ) (A : Set (Vec d)) (x : Vec d) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A.indicator (fun _ => (1 : ℝ))) x =
      ∫ y, K y * A.indicator (fun _ => (1 : ℝ)) (x - y) := by
  simp [convolution_def, ContinuousLinearMap.lsmul_apply]

theorem abs_convolution_indicator_le {K : Vec d → ℝ} (hK : Integrable K) (A : Set (Vec d))
    (x : Vec d) :
    |(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A.indicator (fun _ => (1 : ℝ))) x| ≤
      ∫ y, |K y| := by
  rw [convolution_indicator_apply, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hK.abs (Filter.Eventually.of_forall fun y => ?_)
  change ‖K y * A.indicator (fun _ => (1 : ℝ)) (x - y)‖ ≤ |K y|
  rw [Real.norm_eq_abs, abs_mul]
  have : |A.indicator (fun _ => (1 : ℝ)) (x - y)| ≤ 1 := by
    by_cases h : x - y ∈ A <;> simp [h]
  nlinarith [abs_nonneg (K y)]

theorem contDiff_mollifiedIndicator {t : ℝ} (ht : 0 < t) {A : Set (Vec d)}
    (hA : MeasurableSet A) : ContDiff ℝ (⊤ : ℕ∞) (mollifiedIndicator t A) :=
  HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (PDE.harmonicKernelScaled_hasCompactSupport ht) (PDE.harmonicKernelScaled_smooth t)
    (locallyIntegrable_indicator_one hA)

theorem mem_ball_of_harmonicKernelScaled_ne_zero {t : ℝ} (ht : 0 < t) {y : Vec d}
    (hy : PDE.harmonicKernelScaled t y ≠ 0) : euclideanNorm y < t := by
  have h := PDE.harmonicKernelScaled_tsupport_subset ht (subset_tsupport _ hy)
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt ht, sub_zero] at h
  exact h

theorem integrable_harmonicKernelScaled {t : ℝ} (ht : 0 < t) :
    Integrable (PDE.harmonicKernelScaled (d := d) t) :=
  (PDE.harmonicKernelScaled_smooth t).continuous.integrable_of_hasCompactSupport
    (PDE.harmonicKernelScaled_hasCompactSupport ht)

theorem integrable_harmonicKernelScaled_mul_indicator {t : ℝ} (ht : 0 < t) {A : Set (Vec d)}
    (hA : MeasurableSet A) (x : Vec d) :
    Integrable (fun y => PDE.harmonicKernelScaled (d := d) t y *
      A.indicator (fun _ => (1 : ℝ)) (x - y)) := by
  refine (integrable_harmonicKernelScaled ht).mono ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (integrable_harmonicKernelScaled ht).aestronglyMeasurable.mul
      ((measurable_const.indicator hA).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have : |A.indicator (fun _ => (1 : ℝ)) (x - y)| ≤ 1 := by
      by_cases h : x - y ∈ A <;> simp [h]
    nlinarith [abs_nonneg (PDE.harmonicKernelScaled (d := d) t y)]

theorem mollifiedIndicator_nonneg {t : ℝ} (ht : 0 < t) (A : Set (Vec d)) (x : Vec d) :
    0 ≤ mollifiedIndicator t A x := by
  unfold mollifiedIndicator
  rw [convolution_indicator_apply]
  refine integral_nonneg fun y => mul_nonneg (PDE.harmonicKernelScaled_nonneg ht y) ?_
  by_cases h : x - y ∈ A <;> simp [h]

theorem mollifiedIndicator_le_one {t : ℝ} (ht : 0 < t) {A : Set (Vec d)} (hA : MeasurableSet A)
    (x : Vec d) : mollifiedIndicator t A x ≤ 1 := by
  unfold mollifiedIndicator
  rw [convolution_indicator_apply]
  refine le_of_le_of_eq (integral_mono (integrable_harmonicKernelScaled_mul_indicator ht hA x)
    (integrable_harmonicKernelScaled ht) fun y => ?_)
    (PDE.harmonicKernelScaled_integral_eq_one (d := d) ht)
  have h0 := PDE.harmonicKernelScaled_nonneg (d := d) ht y
  by_cases h : x - y ∈ A <;> simp [h, h0]

theorem euclideanNorm_sub_comm (x y : Vec d) : euclideanNorm (x - y) = euclideanNorm (y - x) :=
  PDE.vecEuclideanNorm_sub_comm x y

theorem euclideanNorm_sub_sub_self (x y : Vec d) : euclideanNorm (x - y - x) = euclideanNorm y := by
  rw [sub_sub_cancel_left]
  exact PDE.vecEuclideanNorm_neg y

/-- `ρ_t ⋆ 1_A = 1` at a point whose Euclidean ball of radius `t` lies in `A`. -/
theorem mollifiedIndicator_eq_one {t : ℝ} (ht : 0 < t) {A : Set (Vec d)} {x : Vec d}
    (hx : ∀ y, euclideanNorm (y - x) < t → y ∈ A) : mollifiedIndicator t A x = 1 := by
  unfold mollifiedIndicator
  rw [convolution_indicator_apply]
  have e : (fun y => PDE.harmonicKernelScaled (d := d) t y *
      A.indicator (fun _ => (1 : ℝ)) (x - y)) = PDE.harmonicKernelScaled t := by
    funext y
    by_cases hy : PDE.harmonicKernelScaled (d := d) t y = 0
    · simp [hy]
    · have hxy : x - y ∈ A := hx _ (by
        rw [euclideanNorm_sub_sub_self]
        exact mem_ball_of_harmonicKernelScaled_ne_zero ht hy)
      simp [hxy]
  rw [e, PDE.harmonicKernelScaled_integral_eq_one ht]

/-- `ρ_t ⋆ 1_A = 0` at a point whose Euclidean ball of radius `t` misses `A`. -/
theorem mollifiedIndicator_eq_zero {t : ℝ} (ht : 0 < t) {A : Set (Vec d)} {x : Vec d}
    (hx : ∀ y, euclideanNorm (y - x) < t → y ∉ A) : mollifiedIndicator t A x = 0 := by
  unfold mollifiedIndicator
  rw [convolution_indicator_apply]
  have e : (fun y => PDE.harmonicKernelScaled (d := d) t y *
      A.indicator (fun _ => (1 : ℝ)) (x - y)) = fun _ => 0 := by
    funext y
    by_cases hy : PDE.harmonicKernelScaled (d := d) t y = 0
    · simp [hy]
    · have hxy : x - y ∉ A := hx _ (by
        rw [euclideanNorm_sub_sub_self]
        exact mem_ball_of_harmonicKernelScaled_ne_zero ht hy)
      simp [hxy]
  rw [e, integral_zero]

theorem abs_coordinateDerivative_mollifiedIndicator_le {t : ℝ} (ht : 0 < t) {A : Set (Vec d)}
    (hA : MeasurableSet A) (i : Fin d) (x : Vec d) :
    |coordinateDerivative i (mollifiedIndicator t A) x| ≤
      t⁻¹ * ∫ y, |PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) y| := by
  change |PDE.euclideanCoordDeriv i (mollifiedIndicator t A) x| ≤ _
  unfold mollifiedIndicator
  rw [PDE.euclideanCoordDeriv_convolution_left (PDE.harmonicKernelScaled_hasCompactSupport ht)
    (PDE.harmonicKernelScaled_smooth t) (locallyIntegrable_indicator_one hA) i,
    ← PDE.harmonicKernelScaled_deriv_abs_integral i ht]
  exact abs_convolution_indicator_le (PDE.harmonicKernelScaled_deriv_integrable i ht) A x

theorem abs_coordinateDerivative_coordinateDerivative_mollifiedIndicator_le {t : ℝ} (ht : 0 < t)
    {A : Set (Vec d)} (hA : MeasurableSet A) (i j : Fin d) (x : Vec d) :
    |coordinateDerivative j (coordinateDerivative i (mollifiedIndicator t A)) x| ≤
      t⁻¹ * t⁻¹ * ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y| := by
  change |PDE.euclideanCoordSecondDeriv i j (mollifiedIndicator t A) x| ≤ _
  unfold mollifiedIndicator
  rw [PDE.euclideanCoordSecondDeriv_convolution_left
    (PDE.harmonicKernelScaled_hasCompactSupport ht) (PDE.harmonicKernelScaled_smooth t)
    (locallyIntegrable_indicator_one hA) i j,
    ← integral_abs_euclideanCoordSecondDeriv_harmonicKernelScaled i j ht]
  exact abs_convolution_indicator_le
    (integrable_euclideanCoordSecondDeriv_harmonicKernelScaled i j ht) A x

/-- Every point of the closed support of `ρ_t ⋆ 1_A` is at Euclidean distance less than `2t`
from `A`. -/
theorem exists_mem_of_mem_tsupport_mollifiedIndicator {t : ℝ} (ht : 0 < t) {A : Set (Vec d)}
    {x : Vec d} (hx : x ∈ tsupport (mollifiedIndicator t A)) :
    ∃ y ∈ A, euclideanNorm (x - y) < 2 * t := by
  have hopen : IsOpen {x' : Vec d | euclideanNorm (x' - x) < t} := by
    refine isOpen_lt ?_ continuous_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  obtain ⟨x', hx'U, hx'⟩ := mem_closure_iff.1 hx _ hopen (by
    simp only [mem_setOf_eq, sub_self]
    simpa [euclideanNorm, euclideanSq, dot] using ht)
  have hne : mollifiedIndicator t A x' ≠ 0 := hx'
  by_contra hcon
  push_neg at hcon
  refine hne (mollifiedIndicator_eq_zero ht fun y hy hyA => ?_)
  have h1 := hcon y hyA
  have h2 : euclideanNorm (x - y) ≤ euclideanNorm (x - x') + euclideanNorm (x' - y) := by
    have := PDE.vecEuclideanNorm_add_le (x - x') (x' - y)
    rwa [sub_add_sub_cancel] at this
  have h3 : euclideanNorm (x - x') < t := by
    rw [euclideanNorm_sub_comm]
    exact hx'U
  have h4 : euclideanNorm (x' - y) < t := by
    rw [euclideanNorm_sub_comm]
    exact hy
  linarith

/-! ## The cutoff on convex domains -/

/-- Homothetic copies are nested with a margin: for a convex `U ⊇ B_ρ(x₀)`, `0 ≤ s' < s` and
`y ∈ x₀ + s' (U - x₀)`, every `z` with `|z - y| < (s - s') ρ` lies in `x₀ + s (U - x₀)`. -/
theorem mem_homothety_image_of_mem_homothety_image {U : Set (Vec d)} (hUc : Convex ℝ U)
    {x₀ : Vec d} {ρ : ℝ} (hball : ∀ y, euclideanNorm (y - x₀) < ρ → y ∈ U) {s s' : ℝ}
    (hs' : 0 ≤ s') (hss : s' < s) {y : Vec d} (hy : y ∈ AffineMap.homothety x₀ s' '' U)
    {z : Vec d} (hz : euclideanNorm (z - y) < (s - s') * ρ) :
    z ∈ AffineMap.homothety x₀ s '' U := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hs : 0 < s := hs'.trans_lt hss
  have hd : 0 < s - s' := by linarith
  have hp : x₀ + (s - s')⁻¹ • (z - AffineMap.homothety x₀ s' x) ∈ U := by
    refine hball _ ?_
    rw [add_sub_cancel_left, euclideanNorm_const_smul, abs_of_pos (inv_pos.2 hd),
      inv_mul_lt_iff₀ hd]
    exact hz
  have hcomb := hUc hx hp (div_nonneg hs' hs.le) (by
    rw [sub_nonneg, div_le_one hs]; exact hss.le : (0 : ℝ) ≤ 1 - s' / s) (by ring)
  refine ⟨_, hcomb, ?_⟩
  have hs0 : s ≠ 0 := hs.ne'
  have hd0 : s - s' ≠ 0 := hd.ne'
  ext i
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The cutoff (1.60) on a convex domain.** Let `U` be open, bounded and convex with
`B_ρ(x₀) ⊆ U`. There is `C(d, ρ)` such that for every `r ∈ (0, 1)` there is a smooth compactly
supported `η` with `0 ≤ η ≤ 1`, `|∂_i η| ≤ C r⁻¹`, `|∂_j ∂_i η| ≤ C r⁻²`, every point of the
support of `η` has the Euclidean ball of radius `ρ r / 4` inside `U`, and
`|{x ∈ U : η(x) ≠ 1}| ≤ d r |U|`. -/
theorem exists_cutoff_of_convex {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ y, euclideanNorm (y - x₀) < ρ → y ∈ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < 1 → ∃ η : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ x ∈ tsupport η, ∀ z, euclideanNorm (z - x) < ρ * r / 4 → z ∈ U) ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ i x, |coordinateDerivative i η x| ≤ C / r) ∧
      (∀ i j x, |coordinateDerivative j (coordinateDerivative i η) x| ≤ C / r ^ 2) ∧
      volume.real {x ∈ U | η x ≠ 1} ≤ d * r * volume.real U := by
  set K1 : ℝ := ∑ i : Fin d, ∫ y, |PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) y|
    with hK1
  set K2 : ℝ := ∑ i : Fin d, ∑ j : Fin d,
    ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y| with hK2
  have hK1n : 0 ≤ K1 := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => abs_nonneg _
  have hK2n : 0 ≤ K2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    integral_nonneg fun _ => abs_nonneg _
  refine ⟨8 / ρ * K1 + (8 / ρ) ^ 2 * K2, by positivity, fun r hr hr1 => ?_⟩
  set t : ℝ := ρ * r / 8 with ht
  have ht0 : 0 < t := by positivity
  set A : Set (Vec d) := AffineMap.homothety x₀ (1 - r / 2) '' U with hA
  have hAo : IsOpen A := AffineMap.homothety_isOpenMap x₀ _ (by linarith) U hUo
  have hAm : MeasurableSet A := hAo.measurableSet
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  refine ⟨mollifiedIndicator t A, contDiff_mollifiedIndicator ht0 hAm, ?_, ?_, fun x =>
    ⟨mollifiedIndicator_nonneg ht0 A x, mollifiedIndicator_le_one ht0 hAm x⟩, ?_, ?_, ?_⟩
  · -- compact support
    have hsub : tsupport (mollifiedIndicator t A) ⊆ U := by
      intro x hx
      obtain ⟨y, hyA, hxy⟩ := exists_mem_of_mem_tsupport_mollifiedIndicator ht0 hx
      exact mem_of_mem_homothety_image hUc hball (by linarith) (by linarith) hyA (by
        have : (1 - (1 - r / 2)) * ρ = ρ * r / 2 := by ring
        rw [this]
        linarith)
    exact hUb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
      (hsub.trans subset_closure)
  · intro x hx z hz
    obtain ⟨y, hyA, hxy⟩ := exists_mem_of_mem_tsupport_mollifiedIndicator ht0 hx
    refine mem_of_mem_homothety_image hUc hball (by linarith) (by linarith) hyA ?_
    have h2 : euclideanNorm (z - y) ≤ euclideanNorm (z - x) + euclideanNorm (x - y) := by
      have := PDE.vecEuclideanNorm_add_le (z - x) (x - y)
      rwa [sub_add_sub_cancel] at this
    have : (1 - (1 - r / 2)) * ρ = ρ * r / 2 := by ring
    rw [this]
    linarith
  · intro i x
    refine (abs_coordinateDerivative_mollifiedIndicator_le ht0 hAm i x).trans ?_
    have hle : ∫ y, |PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) y| ≤ K1 :=
      Finset.single_le_sum (f := fun i =>
        ∫ y, |PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) y|)
        (fun i _ => integral_nonneg fun _ => abs_nonneg _) (Finset.mem_univ i)
    have htinv : t⁻¹ = 8 / ρ / r := by rw [ht]; field_simp
    rw [htinv]
    have h2 : 0 ≤ (8 / ρ) ^ 2 * K2 / r := by positivity
    calc 8 / ρ / r * ∫ y, |PDE.euclideanCoordDeriv i (PDE.harmonicKernel (d := d)) y|
        ≤ 8 / ρ / r * K1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ (8 / ρ * K1 + (8 / ρ) ^ 2 * K2) / r := by
        rw [add_div]
        have : 8 / ρ / r * K1 = 8 / ρ * K1 / r := by ring
        linarith
  · intro i j x
    refine (abs_coordinateDerivative_coordinateDerivative_mollifiedIndicator_le ht0 hAm i j x).trans
      ?_
    have hle : ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y| ≤ K2 := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin d,
        ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y|)
        (fun i _ => Finset.sum_nonneg fun j _ => integral_nonneg fun _ => abs_nonneg _)
        (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j =>
        ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y|)
        (fun j _ => integral_nonneg fun _ => abs_nonneg _) (Finset.mem_univ j)
    have htinv : t⁻¹ = 8 / ρ / r := by rw [ht]; field_simp
    rw [htinv]
    have h1 : 0 ≤ 8 / ρ * K1 / r ^ 2 := by positivity
    calc 8 / ρ / r * (8 / ρ / r) *
          ∫ y, |PDE.euclideanCoordSecondDeriv i j (PDE.harmonicKernel (d := d)) y|
        ≤ 8 / ρ / r * (8 / ρ / r) * K2 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ (8 / ρ * K1 + (8 / ρ) ^ 2 * K2) / r ^ 2 := by
        rw [add_div]
        have : 8 / ρ / r * (8 / ρ / r) * K2 = (8 / ρ) ^ 2 * K2 / r ^ 2 := by ring
        linarith
  · -- the boundary layer
    have hr' : 0 < 1 - r := by linarith
    have hmeas := (measureReal_sdiff_homothety_image_le hUo hUt hUc hρ hball (s := 1 - r) hr'
      (by linarith)).2
    have hsub : {x ∈ U | mollifiedIndicator t A x ≠ 1} ⊆
        U \ AffineMap.homothety x₀ (1 - r) '' U := by
      rintro x ⟨hxU, hx1⟩
      refine ⟨hxU, fun hx => hx1 (mollifiedIndicator_eq_one ht0 fun y hy => ?_)⟩
      refine mem_homothety_image_of_mem_homothety_image hUc hball hr'.le
        (by linarith : 1 - r < 1 - r / 2) hx ?_
      have : (1 - r / 2 - (1 - r)) * ρ = ρ * r / 2 := by ring
      rw [this]
      linarith
    have hfin : volume (U \ AffineMap.homothety x₀ (1 - r) '' U) ≠ ⊤ :=
      measure_ne_top_of_subset diff_subset hUt
    calc volume.real {x ∈ U | mollifiedIndicator t A x ≠ 1}
        ≤ volume.real (U \ AffineMap.homothety x₀ (1 - r) '' U) :=
          measureReal_mono hsub hfin
      _ ≤ d * (1 - (1 - r)) * volume.real U := hmeas
      _ = d * r * volume.real U := by ring

end TwoScale

end QSH
