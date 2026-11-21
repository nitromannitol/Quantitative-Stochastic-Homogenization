import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicSecondOrderDecay
import PDEFoundation.Monotonicity.Core.BallDivergence
import PDEFoundation.PDE.HarmonicMeanValueLocal
import PDEFoundation.Monotonicity.Almgren.Shift

/-!
# Orthogonality of harmonic functions vanishing to second order to affine functions

Let `w` be smooth and harmonic on `B_R`. If `∂ᵢw(0) = 0`, then the divergence theorem for the
field `w eᵢ` and the mean value property of the harmonic function `∂ᵢw` give
`∫_{∂B_s} w yᵢ = s ∫_{B_s} ∂ᵢw = 0`, and integration in polar coordinates gives
`∫_{B_r} w yᵢ = 0`. If `w(0) = 0`, the mean value property gives `∫_{B_r} w = 0`.
-/

open MeasureTheory Set Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `∫_{∂B_s} w yᵢ = 0` when `∂ᵢw(0) = 0`. -/
theorem sphereIntegral_mul_coord_eq_zero (hd : 0 < d) {R s : ℝ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (PDE.euclideanBall 0 R))
    (hharm : ∀ y ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian w y = 0)
    (i : Fin d) (hdi : PDE.euclideanCoordDeriv i w 0 = 0) (hs : 0 < s) (hsR : s < R) :
    PDE.sphereIntegral (0 : Vec d) s (fun y => w y * y i) = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hopen := PDE.isOpen_euclideanBall (0 : Vec d) R
  set F : Vec d → Vec d := fun y => w y • PDE.basisVec i with hFdef
  have hF : ContDiffOn ℝ 1 F (PDE.euclideanBall 0 R) :=
    (hw.of_le (by simp)).smul contDiffOn_const
  have hdiv := PDE.integral_euclideanBall_classicalDivergence hF hs hsR
  have hdivF : ∀ y ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.classicalDivergence F y = PDE.euclideanCoordDeriv i w y := by
    intro y hy
    have hdw : DifferentiableAt ℝ w y :=
      (hw.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
    unfold PDE.classicalDivergence
    have hk : ∀ k, PDE.euclideanCoordDeriv k (fun z => F z k) y =
        PDE.basisVec i k * PDE.euclideanCoordDeriv k w y := by
      intro k
      have hfun : (fun z => F z k) = fun z => PDE.basisVec i k * w z := by
        funext z
        simp [hFdef, mul_comm]
      unfold PDE.euclideanCoordDeriv
      rw [hfun, fderiv_const_mul hdw]
      rfl
    simp only [hk]
    rw [Finset.sum_eq_single i]
    · simp [PDE.basisVec]
    · intro k _ hki
      simp [PDE.basisVec, hki]
    · simp
  obtain ⟨hvi, hharmi⟩ := PDE.contDiffOn_euclideanCoordDeriv_and_harmonic hopen hw hharm i
  have hmv := PDE.integralAverage_euclideanBall_eq_center_of_harmonicOn hd hvi hharmi hs hsR
  have hsub : PDE.euclideanBall (0 : Vec d) s ⊆ PDE.euclideanBall 0 R := by
    intro x hx
    rw [PDE.mem_euclideanBall_zero_iff] at hx ⊢
    exact hx.trans (pow_lt_pow_left₀ hsR hs.le two_ne_zero)
  have hint : ∫ x in PDE.euclideanBall (0 : Vec d) s, PDE.classicalDivergence F x =
      ∫ x in PDE.euclideanBall (0 : Vec d) s, PDE.euclideanCoordDeriv i w x :=
    setIntegral_congr_fun (PDE.isOpen_euclideanBall _ _).measurableSet
      fun x hx => hdivF x (hsub hx)
  have hvol : (volume (PDE.euclideanBall (0 : Vec d) s)).toReal ≠ 0 :=
    (PDE.volume_euclideanBall_toReal_pos 0 hs).ne'
  have hzero : ∫ x in PDE.euclideanBall (0 : Vec d) s, PDE.euclideanCoordDeriv i w x = 0 := by
    unfold PDE.integralAverage at hmv
    rw [hdi] at hmv
    rcases mul_eq_zero.mp hmv with h | h
    · exact absurd (inv_eq_zero.mp h) hvol
    · exact h
  rw [hint, hzero] at hdiv
  have hfun : (fun x => PDE.vecDot (F x) x) = fun y => w y * y i := by
    funext y
    simp [hFdef, PDE.vecDot, PDE.basisVec, Pi.single_apply]
  rw [hfun] at hdiv
  rcases mul_eq_zero.mp hdiv.symm with h | h
  · exact absurd (inv_eq_zero.mp h) hs.ne'
  · exact h

theorem euclideanClosedBall_subset_euclideanBall {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    PDE.euclideanClosedBall (0 : Vec d) r ⊆ PDE.euclideanBall 0 R := by
  intro x hx
  change PDE.euclideanSqDist x 0 ≤ r ^ 2 at hx
  rw [PDE.BallDivergence.euclideanSqDist_zero_right] at hx
  rw [PDE.mem_euclideanBall_zero_iff]
  exact hx.trans_lt (pow_lt_pow_left₀ hrR hr two_ne_zero)

theorem integrableOn_euclideanBall_of_continuousOn {g : Vec d → ℝ} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (hg : ContinuousOn g (PDE.euclideanBall 0 R)) :
    IntegrableOn g (PDE.euclideanBall (0 : Vec d) r) :=
  ((hg.mono (euclideanClosedBall_subset_euclideanBall hr hrR)).integrableOn_compact
    (PDE.isCompact_euclideanClosedBall 0 hr)).mono_set
    (PDE.euclideanBall_subset_euclideanClosedBall 0 r)

/-- `∫_{B_r} w yᵢ = 0` when `∂ᵢw(0) = 0`. -/
theorem integral_mul_coord_eq_zero (hd : 0 < d) {R r : ℝ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (PDE.euclideanBall 0 R))
    (hharm : ∀ y ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian w y = 0)
    (i : Fin d) (hdi : PDE.euclideanCoordDeriv i w 0 = 0) (hr : 0 < r) (hrR : r < R) :
    ∫ y in PDE.euclideanBall (0 : Vec d) r, w y * y i = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨ρ', v, hrρ, hρR, hv, hvw⟩ :=
    PDE.exists_contDiff_localization (n := 2) (hw.of_le (by simp)) hr hrR
  have hρ0 : 0 < ρ' := hr.trans hrρ
  have hg : Continuous fun y : Vec d => v y * y i := hv.continuous.mul (continuous_apply i)
  have hsub : PDE.euclideanBall (0 : Vec d) r ⊆ PDE.euclideanBall 0 ρ' := by
    intro x hx
    rw [PDE.mem_euclideanBall_zero_iff] at hx ⊢
    exact hx.trans (pow_lt_pow_left₀ hrρ hr.le two_ne_zero)
  have h1 : ∫ y in PDE.euclideanBall (0 : Vec d) r, w y * y i =
      ∫ y in PDE.euclideanBall (0 : Vec d) r, v y * y i :=
    setIntegral_congr_fun (PDE.isOpen_euclideanBall _ _).measurableSet
      fun x hx => by simp only [hvw (hsub hx)]
  rw [h1, PDE.integral_euclideanBall_eq_intervalIntegral_sphereIntegral hg hr]
  have h2 : ∫ s in (0 : ℝ)..r, PDE.sphereIntegral 0 s (fun y => v y * y i) =
      ∫ s in (0 : ℝ)..r, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le hr.le] at hs
    have hsR : s < R := hs.2.trans_lt hrR
    rw [PDE.sphereIntegral_eq_mul_sphereMean,
      PDE.sphereMean_congr_of_eqOn (g := fun y => w y * y i) hρ0
        (by rw [abs_of_pos hs.1]; exact hs.2.trans_lt hrρ)
        (fun x hx => by simp only [hvw hx]),
      ← PDE.sphereIntegral_eq_mul_sphereMean]
    exact sphereIntegral_mul_coord_eq_zero hd hw hharm i hdi hs.1 hsR
  rw [h2, intervalIntegral.integral_zero]

/-- `∫_{B_r} w = 0` when `w(0) = 0`. -/
theorem integral_eq_zero_of_harmonic (hd : 0 < d) {R r : ℝ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (PDE.euclideanBall 0 R))
    (hharm : ∀ y ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian w y = 0)
    (hw0 : w 0 = 0) (hr : 0 < r) (hrR : r < R) :
    ∫ y in PDE.euclideanBall (0 : Vec d) r, w y = 0 := by
  have hmv := PDE.integralAverage_euclideanBall_eq_center_of_harmonicOn hd hw hharm hr hrR
  have hvol : (volume (PDE.euclideanBall (0 : Vec d) r)).toReal ≠ 0 :=
    (PDE.volume_euclideanBall_toReal_pos 0 hr).ne'
  unfold PDE.integralAverage at hmv
  rw [hw0] at hmv
  rcases mul_eq_zero.mp hmv with h | h
  · exact absurd (inv_eq_zero.mp h) hvol
  · exact h

/-- The first-order Taylor remainder `v - v(0) - Dv(0) y` of a smooth harmonic function is smooth,
harmonic and vanishes to second order. -/
theorem taylorRemainder_props {R : ℝ} (hR : 0 < R) {v : Vec d → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (PDE.euclideanBall 0 R))
    (hharm : ∀ y ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian v y = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => v y - (v 0 + fderiv ℝ v 0 y)) (PDE.euclideanBall 0 R) ∧
    (∀ y ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.euclideanCoordLaplacian (fun y => v y - (v 0 + fderiv ℝ v 0 y)) y = 0) ∧
    (fun y => v y - (v 0 + fderiv ℝ v 0 y)) 0 = 0 ∧
    fderiv ℝ (fun y => v y - (v 0 + fderiv ℝ v 0 y)) 0 = 0 := by
  have hopen := PDE.isOpen_euclideanBall (0 : Vec d) R
  have h0 : (0 : Vec d) ∈ PDE.euclideanBall (0 : Vec d) R := by
    have h : PDE.vecNormSq (0 : Vec d) = 0 := by simp [PDE.vecNormSq, PDE.vecDot]
    rw [PDE.mem_euclideanBall_zero_iff, h]
    positivity
  set L := fderiv ℝ v 0 with hL
  set ℓ : Vec d → ℝ := fun y => v 0 + L y with hℓ
  have hℓs : ContDiff ℝ (⊤ : ℕ∞) ℓ := contDiff_const.add L.contDiff
  have hfd : ∀ y, fderiv ℝ ℓ y = L := fun y => by simp [hℓ]
  have hcd : ∀ j, PDE.euclideanCoordDeriv j ℓ = fun _ => L (PDE.basisVec j) := fun j =>
    funext fun y => by simp [PDE.euclideanCoordDeriv, hfd]
  have hΔℓ : ∀ x, PDE.euclideanCoordLaplacian ℓ x = 0 := by
    intro x
    simp [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv, hcd]
  have hdv : DifferentiableAt ℝ v 0 := PDE.differentiableAt_of_contDiffOn_top hopen hv h0
  refine ⟨hv.sub hℓs.contDiffOn, fun y hy => ?_, by simp, ?_⟩
  · have h := PDE.euclideanCoordLaplacian_sub_const_mul hopen hv hℓs.contDiffOn 1 hy
    have e : (fun z => v z - 1 * ℓ z) = fun z => v z - (v 0 + L z) := by
      funext z
      simp [hℓ]
    rw [e] at h
    rw [h, hharm y hy, hΔℓ y]
    ring
  · have h := fderiv_sub hdv (hℓs.differentiable (by simp) 0)
    change fderiv ℝ (fun y => v y - ℓ y) 0 = 0
    exact h.trans (by rw [hfd, sub_self])

theorem clm_apply_eq_sum (L : Vec d →L[ℝ] ℝ) (y : Vec d) :
    L y = ∑ i, y i * L (PDE.basisVec i) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : Pi.single i (y i) = y i • PDE.basisVec (d := d) i := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [PDE.basisVec]
    · simp [PDE.basisVec, hji]
  rw [hs, map_smul, smul_eq_mul]

/-- **Pythagoras on balls**: `∫_{B_r} (v - v(0) - Dv(0) y)² ≤ ∫_{B_r} v²` for smooth harmonic
`v` on `B_R`, `r < R`. -/
theorem integral_sq_taylorRemainder_le (hd : 0 < d) {R r : ℝ} {v : Vec d → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (PDE.euclideanBall 0 R))
    (hharm : ∀ y ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian v y = 0)
    (hr : 0 < r) (hrR : r < R) :
    ∫ y in PDE.euclideanBall (0 : Vec d) r, (v y - (v 0 + fderiv ℝ v 0 y)) ^ 2 ≤
      ∫ y in PDE.euclideanBall (0 : Vec d) r, v y ^ 2 := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨hws, hwh, hw0, hdw0⟩ := taylorRemainder_props hR hv hharm
  set L := fderiv ℝ v 0 with hL
  set w : Vec d → ℝ := fun y => v y - (v 0 + L y) with hw
  have hdi : ∀ i, PDE.euclideanCoordDeriv i w 0 = 0 := fun i => by
    simp [PDE.euclideanCoordDeriv, hdw0]
  have hco : ∀ i, ∫ y in PDE.euclideanBall (0 : Vec d) r, w y * y i = 0 := fun i =>
    integral_mul_coord_eq_zero hd hws hwh i (hdi i) hr hrR
  have hc0 : ∫ y in PDE.euclideanBall (0 : Vec d) r, w y = 0 :=
    integral_eq_zero_of_harmonic hd hws hwh hw0 hr hrR
  have hwc : ContinuousOn w (PDE.euclideanBall 0 R) := hws.continuousOn
  have hLc : Continuous fun y : Vec d => L y := L.continuous
  have hint : ∀ g : Vec d → ℝ, ContinuousOn g (PDE.euclideanBall 0 R) →
      IntegrableOn g (PDE.euclideanBall (0 : Vec d) r) := fun g hg =>
    integrableOn_euclideanBall_of_continuousOn hr.le hrR hg
  have hcross : ∫ y in PDE.euclideanBall (0 : Vec d) r, w y * (v 0 + L y) = 0 := by
    have e : (fun y => w y * (v 0 + L y)) =
        fun y => v 0 * w y + ∑ i, L (PDE.basisVec i) * (w y * y i) := by
      funext y
      rw [clm_apply_eq_sum L y, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ => by ring
    have j1 : IntegrableOn (fun y => v 0 * w y) (PDE.euclideanBall (0 : Vec d) r) :=
      (hint w hwc).const_mul _
    have jk : ∀ i, IntegrableOn (fun y => L (PDE.basisVec i) * (w y * y i))
        (PDE.euclideanBall (0 : Vec d) r) := fun i =>
      (hint _ (hwc.mul (continuous_apply i).continuousOn)).const_mul _
    have j2 : IntegrableOn (fun y => ∑ i, L (PDE.basisVec i) * (w y * y i))
        (PDE.euclideanBall (0 : Vec d) r) := integrable_finsetSum _ fun i _ => jk i
    rw [e, integral_add j1 j2, integral_const_mul, hc0, integral_finsetSum _ fun i _ => jk i]
    simp only [integral_const_mul, hco, mul_zero, zero_add, Finset.sum_const_zero]
  have hℓc : ContinuousOn (fun y => v 0 + L y) (PDE.euclideanBall 0 R) :=
    (continuous_const.add hLc).continuousOn
  have hvw : ∀ y, v y ^ 2 = w y ^ 2 + (2 * (w y * (v 0 + L y)) + (v 0 + L y) ^ 2) := fun y => by
    simp only [hw]
    ring
  have hsplit : ∫ y in PDE.euclideanBall (0 : Vec d) r, v y ^ 2 =
      (∫ y in PDE.euclideanBall (0 : Vec d) r, w y ^ 2) +
        (2 * ∫ y in PDE.euclideanBall (0 : Vec d) r, w y * (v 0 + L y)) +
        ∫ y in PDE.euclideanBall (0 : Vec d) r, (v 0 + L y) ^ 2 := by
    have i1 : IntegrableOn (fun y => w y ^ 2) (PDE.euclideanBall (0 : Vec d) r) :=
      hint _ (hwc.pow 2)
    have i2 : IntegrableOn (fun y => 2 * (w y * (v 0 + L y))) (PDE.euclideanBall (0 : Vec d) r) :=
      (hint _ (hwc.mul hℓc)).const_mul 2
    have i3 : IntegrableOn (fun y => (v 0 + L y) ^ 2) (PDE.euclideanBall (0 : Vec d) r) :=
      hint _ (hℓc.pow 2)
    have i23 : IntegrableOn (fun y => 2 * (w y * (v 0 + L y)) + (v 0 + L y) ^ 2)
        (PDE.euclideanBall (0 : Vec d) r) := i2.add i3
    simp_rw [hvw]
    rw [integral_add i1 i23, integral_add i2 i3, integral_const_mul]
    ring
  have hnn : 0 ≤ ∫ y in PDE.euclideanBall (0 : Vec d) r, (v 0 + L y) ^ 2 :=
    setIntegral_nonneg (PDE.isOpen_euclideanBall _ _).measurableSet fun y _ => sq_nonneg _
  rw [hsplit, hcross]
  linarith

end QSH
