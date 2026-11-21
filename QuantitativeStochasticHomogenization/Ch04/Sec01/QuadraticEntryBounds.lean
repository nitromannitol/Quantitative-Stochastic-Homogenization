import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakDivergenceZero
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanNormToLp
import QuantitativeStochasticHomogenization.Ch04.Sec01.EuclideanLipschitz

/-!
# Matrix entries from quadratic form bounds

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Mobility/DriftBoundPointwise.lean`.

Polarization of `ξ ↦ ξ · M ξ` and the bound of the entries of a matrix by the bounds of its quadratic form on unit vectors.
-/

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace QSH

/-! ### Euclidean and matrix algebra -/

/-- Each coordinate unit vector has Euclidean norm one. -/
theorem euclideanNorm_unitVector_eq_one {d : ℕ} (j : Fin d) :
    euclideanNorm (unitVector j) = 1 := by
  change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- The squared Euclidean norm is nonnegative. -/
theorem euclideanSq_nonneg_coords {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Polarization of the quadratic form of a matrix on `u + v` and `u - v`. -/
theorem polarization_mulVec {d : ℕ} (M : Mat d) (u v : Vec d) :
    dotProduct (u + v) (M.mulVec (u + v)) - dotProduct (u - v) (M.mulVec (u - v)) =
      2 * (dotProduct u (M.mulVec v) + dotProduct v (M.mulVec u)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub]
  ring

/-- The `p`-th coordinate of `M` applied to the `q`-th unit vector is the entry `M p q`. -/
theorem mulVec_single_apply_entry {d : ℕ} (M : Mat d) (q p : Fin d) :
    (M.mulVec (Pi.single q (1 : ℝ))) p = M p q := by
  change dotProduct (fun k => M p k) (Pi.single q (1 : ℝ)) = M p q
  rw [dotProduct_single, mul_one]

/-- A symmetric matrix whose quadratic form lies in `[0, Λ |ξ|²]` has all entries bounded by `Λ`.
The bound comes from the polarization identity on `e_p + e_q` and `e_p - e_q`. -/
theorem abs_entry_le_of_quadratic_bounds {d : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ) (M : Mat d)
    (hsymm : M.transpose = M) (hlow : ∀ ξ : Vec d, 0 ≤ dotProduct ξ (M.mulVec ξ))
    (hup : ∀ ξ : Vec d, dotProduct ξ (M.mulVec ξ) ≤ Λ * euclideanSq ξ) (p q : Fin d) :
    |M p q| ≤ Λ := by
  have hMsym : M q p = M p q := by
    have h := congrFun (congrFun hsymm p) q
    rwa [Matrix.transpose_apply] at h
  have h1 : dotProduct (Pi.single p (1 : ℝ) : Vec d) (M.mulVec (Pi.single q (1 : ℝ))) = M p q := by
    rw [single_dotProduct, one_mul, mulVec_single_apply_entry]
  have h2 : dotProduct (Pi.single q (1 : ℝ) : Vec d) (M.mulVec (Pi.single p (1 : ℝ))) = M p q := by
    rw [single_dotProduct, one_mul, mulVec_single_apply_entry, hMsym]
  have hpol := polarization_mulVec M (Pi.single p (1 : ℝ)) (Pi.single q (1 : ℝ))
  rw [h1, h2] at hpol
  have hnp : euclideanNorm (Pi.single p (1 : ℝ) : Vec d) = 1 := euclideanNorm_unitVector_eq_one p
  have hnq : euclideanNorm (Pi.single q (1 : ℝ) : Vec d) = 1 := euclideanNorm_unitVector_eq_one q
  have hsq_le : ∀ ξ : Vec d, euclideanNorm ξ ≤ 2 → euclideanSq ξ ≤ 4 := by
    intro ξ hξ
    have hn0 : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _
    have hsq : euclideanSq ξ = euclideanNorm ξ ^ 2 := by
      unfold euclideanNorm
      rw [Real.sq_sqrt (euclideanSq_nonneg_coords ξ)]
    rw [hsq]
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hξ)]
  have hplus : euclideanNorm (Pi.single p (1 : ℝ) + Pi.single q (1 : ℝ) : Vec d) ≤ 2 := by
    have h := euclideanNorm_add_le (Pi.single p (1 : ℝ) : Vec d) (Pi.single q (1 : ℝ))
    linarith
  have hminus : euclideanNorm (Pi.single p (1 : ℝ) - Pi.single q (1 : ℝ) : Vec d) ≤ 2 := by
    have hsub : (Pi.single p (1 : ℝ) - Pi.single q (1 : ℝ) : Vec d) =
        (Pi.single p (1 : ℝ) : Vec d) + (-1 : ℝ) • (Pi.single q (1 : ℝ) : Vec d) := by
      rw [neg_one_smul, sub_eq_add_neg]
    have h := euclideanNorm_add_le (Pi.single p (1 : ℝ) : Vec d)
      ((-1 : ℝ) • (Pi.single q (1 : ℝ) : Vec d))
    rw [euclideanNorm_smul_abs, abs_neg, abs_one, one_mul] at h
    rw [hsub]
    linarith
  have hEplus := mul_le_mul_of_nonneg_left (hsq_le _ hplus) hΛ
  have hEminus := mul_le_mul_of_nonneg_left (hsq_le _ hminus) hΛ
  have hupPlus := hup ((Pi.single p (1 : ℝ) : Vec d) + (Pi.single q (1 : ℝ) : Vec d))
  have hupMinus := hup ((Pi.single p (1 : ℝ) : Vec d) - (Pi.single q (1 : ℝ) : Vec d))
  have hlowPlus := hlow ((Pi.single p (1 : ℝ) : Vec d) + (Pi.single q (1 : ℝ) : Vec d))
  have hlowMinus := hlow ((Pi.single p (1 : ℝ) : Vec d) - (Pi.single q (1 : ℝ) : Vec d))
  rw [abs_le]
  constructor <;> linarith

/-! ### Measurability of differentiability sets -/

/-! ### Entry bound -/

/-! ### The column divergence and its pointwise bound -/

/-! ### Almost-sure differentiability at the origin -/

end QSH
