import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipticRepresentative
import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity

/-!
# The Caccioppoli inequality on balls with an arbitrary center

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma C.2, prepared for the proof of Lemma 4.21 for the difference between a selected coordinate and
a corrected coordinate on `B_{r^{1+δ}}(z)`: for an `a`-harmonic `v` on `B_R(z)` and `0 < r < R`,
`∫_{B_r(z)} |∇v|² ≤ 4 Λ (32/(R - r))² ∫_{B_R(z)} (v - k)²` for every constant `k`. The proof is
the Caccioppoli inequality of the elliptic regularity library on the convex domain `B_R(z)` with
its smooth ball cutoff, for the pointwise elliptic representative of `a`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **Caccioppoli inequality on balls** `B_r(z) ⊆ B_R(z)`. -/
theorem caccioppoli_ball {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) {z : Vec d}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (ball z R)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball z R)))
    (hw : HasWeakGradient (ball z R) v g)
    (hdiv : HasWeakDivergence (ball z R) (fun x => (a x).mulVec (g x)) (fun _ => 0)) (k : ℝ) :
    ∫ x in ball z r, euclideanSq (g x) ≤
      4 * Λ * (32 / (R - r)) ^ 2 * ∫ x in ball z R, (v x - k) ^ 2 := by
  have hR : 0 < R := hr.trans hrR
  have hU : PDE.IsOpenBoundedConvexDomain (ball z R) := by
    rw [ball_eq_euclideanBall z hR]
    exact PDE.isOpenBoundedConvexDomain_euclideanBall z hR
  have hUm : MeasurableSet (ball z R) := measurableSet_ball z R
  have hrm : MeasurableSet (ball z r) := measurableSet_ball z r
  have hsol := isWeakDivergenceFormHarmonicOn_toH1FunctionOn hΛ a hUm hv hg hw hdiv
  have hEll := isEllipticFieldOn_ellipticFieldOf hΛ a hUm
  have η : PDE.QuantitativeSmoothCutoff (ball z r) (ball z R) (32 / (R - r)) := by
    rw [ball_eq_euclideanBall z hr, ball_eq_euclideanBall z hR]
    exact PDE.quantitativeBallCutoff z hr.le hrR
  have h := PDE.caccioppoli_coefficient_energy_on_inner (k := k) hU hrm hUm hEll one_pos
    (by linarith) hsol η subset_rfl
  simp only [div_one] at h
  have hsub : ball z r ⊆ ball z R := fun x (hx : euclideanNorm (x - z) < r) =>
    (lt_trans hx hrR : euclideanNorm (x - z) < R)
  have hint : IntegrableOn (fun x => PDE.vecDot (g x) (PDE.matVecMul (ellipticFieldOf a x) (g x)))
      (ball z r) :=
    (PDE.integrableOn_vecDot_of_memVectorL2On hg
      (PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hg)).mono_set hsub
  have hle : ∫ x in ball z r, euclideanSq (g x) ≤
      ∫ x in ball z r, PDE.vecDot (g x) (PDE.matVecMul (ellipticFieldOf a x) (g x)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => euclideanSq_nonneg _) hint
      (Eventually.of_forall fun x => ?_)
    have h1 := (isEllipticMatrix_ellipticFieldOf hΛ a x).2.2.1 (g x)
    rw [one_mul] at h1
    exact h1
  exact hle.trans h

end QSH
