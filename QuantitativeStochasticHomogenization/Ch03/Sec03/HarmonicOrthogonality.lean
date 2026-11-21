import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicSecondOrderDecay
import PDEFoundation.Monotonicity.Core.BallDivergence
import PDEFoundation.PDE.HarmonicMeanValueLocal

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

end QSH
