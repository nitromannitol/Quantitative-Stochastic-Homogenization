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

end QSH
