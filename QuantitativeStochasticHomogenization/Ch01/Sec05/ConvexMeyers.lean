import QuantitativeStochasticHomogenization.AppC.GlobalMeyers
import QuantitativeStochasticHomogenization.Ch01.Sec05.ConvexBoundaryDensity

/-!
# The Meyers estimate (1.62) on convex domains

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, the estimate (1.62) of the proof of Theorem 1.17: for a bounded open convex `U` there
are `δ₀(U, d, Λ) > 0` and `C(U, d, Λ)` such that every solution `u ∈ w + H¹₀(U)` of
`-∇·(A∇u) = 0`, `A` a constant matrix with `Id ≤ A ≤ Λ Id`, satisfies
`‖∇u‖_{L̲^{(2+δ₀)∧p}(U)} ≤ C ‖∇w‖_{L̲^{(2+δ₀)∧p}(U)}` (`meyers_constantCoefficient_of_convex`). It is
Theorem C.7 (`theorem_C_7_of_boundaryDensity`) for the constant field `x ↦ A`
(`constantCoefficientField`), with the boundary density of convex domains
(`hasBoundaryDensity_of_convex`).
-/

open MeasureTheory Set

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The constant coefficient field `x ↦ A` for a symmetric matrix with `Id ≤ A ≤ Λ Id`. -/
def constantCoefficientField {Λ : ℝ} (A : Mat d) (hA : A.transpose = A)
    (hA0 : ∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (hA1 : ∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) : CoefficientField d Λ where
  field := fun _ => A
  locally_integrable := fun _ _ => locallyIntegrable_const _
  symmetric := fun _ => hA
  elliptic := fun _ ξ => ⟨hA0 ξ, hA1 ξ⟩

/-- `‖0‖_{W̲^{-1,p}(U)} = 0`. -/
theorem negativeSobolevOneNorm_zero_zero (p : ℝ) (U : Set (Vec d)) :
    negativeSobolevOneNorm p U (fun _ => 0) (fun _ => 0) = 0 := by
  simp [negativeSobolevOneNorm, distributionPairing, dot]

/-- **(1.62) on convex domains**: for `d ≥ 2` and a bounded open convex `U` with
`B_ρ(x₀) ⊆ U ⊆ B_R`, there are `δ > 0` and `C` such that, for `p > 2`, every constant symmetric
matrix `A` with `Id ≤ A ≤ Λ Id`, `w ∈ W^{1,p}(U)` of gradient `G` and every solution `u` of
`-∇·(A∇u) = 0` in `U` with `u - w ∈ H¹₀(U)`, of gradient `g`,
`‖∇u‖_{L̲^{(2+δ)∧p}(U)} ≤ C ‖∇w‖_{L̲^{(2+δ)∧p}(U)}`. -/
theorem meyers_constantCoefficient_of_convex (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {U : Set (Vec d)} (hUo : IsOpen U) (hUc : Convex ℝ U) {x₀ : Vec d} {ρ R : ℝ} (hρ : 0 < ρ)
    (hball : ball x₀ ρ ⊆ U) (hUR : U ⊆ ball 0 R) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ p : ℝ, 2 < p → ∀ A : Mat d, A.transpose = A →
      (∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) →
      (∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) →
      ∀ (u w : Vec d → ℝ) (g G : Vec d → Vec d),
      IsW1p U (ENNReal.ofReal p) w G →
      H01 U (fun x => u x - w x) (fun x => g x - G x) →
      HasWeakDivergence U (fun x => A.mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn U (ENNReal.ofReal (min (2 + δ) p)) (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal C * PDE.eLpMeanNormOn U (ENNReal.ofReal (min (2 + δ) p))
          (fun x => euclideanNorm (G x)) := by
  have hx₀U : x₀ ∈ U := hball (by
    show euclideanNorm (x₀ - x₀) < ρ
    simp [euclideanNorm, euclideanSq, dot, hρ])
  have hR : 0 < R := by
    have := hUR hx₀U
    simp only [ball, sub_zero, mem_ofPred_eq] at this
    exact lt_of_le_of_lt (Real.sqrt_nonneg _) this
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume ⟨x₀, hx₀U⟩).ne'
  have hc : 0 < min ((1 / 2 : ℝ) ^ d) ((ρ / (2 * R + ρ)) ^ d) :=
    lt_min (by positivity) (pow_pos (div_pos hρ (by linarith)) d)
  have hc1 : min ((1 / 2 : ℝ) ^ d) ((ρ / (2 * R + ρ)) ^ d) ≤ 1 :=
    (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨δ, C, hδ, hC, h⟩ := theorem_C_7_of_boundaryDensity hd hΛ hUo hU0 hR hUR hc hc1
    (hasBoundaryDensity_of_convex hUo hUc hρ hball hUR)
  refine ⟨δ, C, hδ, hC, fun p hp A hA hA0 hA1 u w g G hw hu hdiv => ?_⟩
  have hUt : volume U ≠ ⊤ :=
    measure_ne_top_of_subset hUR (volume_ball_ne_top' 0 R)
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have key := h p hp (constantCoefficientField A hA hA0 hA1) u w g G (fun _ => 0) (fun _ => 0)
    hw hu (memLp_const 0) (fun _ => memLp_const 0)
    (by rw [negativeSobolevOneNorm_zero_zero]; exact ENNReal.zero_ne_top)
    (by
      convert hdiv using 1
      · funext x
        simp [constantCoefficientField]
      · funext x
        simp)
  rwa [negativeSobolevOneNorm_zero_zero, add_zero] at key

end QSH
