import QuantitativeStochasticHomogenization.Front.Notation

/-!
# The boundary layer of a convex domain

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, the proof of Theorem 1.17: the boundary layer `U \ U_{2r}` has measure at most `C r`,
which (1.63) uses. For a convex `U` containing the Euclidean ball `B_ρ(x₀)`, the homothetic copy
`x₀ + s (U - x₀)`, `0 ≤ s < 1`, lies in `U` at Euclidean distance at least `(1 - s) ρ` from the
complement of `U` (`mem_of_mem_homothety_image`), and
`|U \ (x₀ + s (U - x₀))| ≤ d (1 - s) |U|` (`measureReal_sdiff_homothety_image_le`).
-/

open MeasureTheory Set

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `|c v| = |c| |v|` for the Euclidean norm. -/
theorem euclideanNorm_const_smul (c : ℝ) (v : Vec d) :
    euclideanNorm (c • v) = |c| * euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i, c * v i * (c * v i)) = c ^ 2 * ∑ i, v i * v i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **The homothetic copies are inside `U`, away from its complement**: if `U` is convex and
contains the Euclidean ball `B_ρ(x₀)`, `0 ≤ s < 1` and `y ∈ x₀ + s (U - x₀)`, then every `z` with
`|z - y| < (1 - s) ρ` lies in `U`. -/
theorem mem_of_mem_homothety_image {U : Set (Vec d)} (hUc : Convex ℝ U) {x₀ : Vec d} {ρ : ℝ}
    (hball : ∀ y, euclideanNorm (y - x₀) < ρ → y ∈ U) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {y : Vec d} (hy : y ∈ AffineMap.homothety x₀ s '' U) {z : Vec d}
    (hz : euclideanNorm (z - y) < (1 - s) * ρ) : z ∈ U := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h1s : 0 < 1 - s := by linarith
  have hp : x₀ + (1 - s)⁻¹ • (z - AffineMap.homothety x₀ s x) ∈ U := by
    refine hball _ ?_
    rw [add_sub_cancel_left, euclideanNorm_const_smul, abs_of_pos (inv_pos.2 h1s),
      inv_mul_lt_iff₀ h1s]
    exact hz
  have hcomb := hUc hx hp hs0 h1s.le (by ring)
  convert hcomb using 1
  rw [smul_add, smul_smul, mul_inv_cancel₀ h1s.ne', one_smul, AffineMap.homothety_apply,
    vsub_eq_sub, vadd_eq_add]
  module

/-- **The measure of the boundary layer**: if `U` is open, convex, of finite measure and contains
the Euclidean ball `B_ρ(x₀)`, `ρ > 0`, and `0 < s ≤ 1`, then `x₀ + s (U - x₀) ⊆ U` and
`|U \ (x₀ + s (U - x₀))| ≤ d (1 - s) |U|`. -/
theorem measureReal_sdiff_homothety_image_le {U : Set (Vec d)} (hUo : IsOpen U)
    (hUt : volume U ≠ ⊤) (hUc : Convex ℝ U) {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ y, euclideanNorm (y - x₀) < ρ → y ∈ U) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    AffineMap.homothety x₀ s '' U ⊆ U ∧
      volume.real (U \ AffineMap.homothety x₀ s '' U) ≤ d * (1 - s) * volume.real U := by
  have hx₀ : x₀ ∈ U := hball x₀ (by simp [euclideanNorm, euclideanSq, dot, hρ])
  have hsub : AffineMap.homothety x₀ s '' U ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hUc hx hx₀ hs0.le (by linarith : (0 : ℝ) ≤ 1 - s) (by ring)
    convert h using 1
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hVo : IsOpen (AffineMap.homothety x₀ s '' U) :=
    AffineMap.homothety_isOpenMap x₀ s hs0.ne' U hUo
  refine ⟨hsub, ?_⟩
  have hvol : volume (AffineMap.homothety x₀ s '' U) = ENNReal.ofReal (s ^ d) * volume U := by
    rw [Measure.addHaar_image_homothety, Module.finrank_fin_fun, abs_of_nonneg (by positivity)]
  rw [measureReal_sdiff hsub hVo.measurableSet hUt, measureReal_def, measureReal_def, hvol,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ s - 1 by linarith) d
  rw [add_sub_cancel] at hb
  have hU0 : 0 ≤ (volume U).toReal := ENNReal.toReal_nonneg
  nlinarith

end QSH
