import QuantitativeStochasticHomogenization.Ch04.Sec03.CommutatorAlgebra

/-!
# Perturbation bounds for symmetric matrices

Elementary bounds used in the proof of Lemma 4.13 here, in the Euclidean norm `|·|` of `Vec d`:

* `euclideanNorm_mulVec_le_of_abs_dot_le`: a symmetric `M` with `|u·Mu| ≤ c|u|²` has `|Mu| ≤ c|u|`;
* `euclideanNorm_inv_mulVec_le_of_coercive`: `ξ·Aξ ≥ λ|ξ|²` with `λ > 0` gives `|A⁻¹v| ≤ λ⁻¹|v|`;
* `euclideanNorm_transpose_mulVec_sub_le`: if `|Pv - v| ≤ ε|v|` for all `v` then
  `|Pᵀv - v| ≤ √d ε |v|`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

open BaseExponent

/-- A symmetric matrix with `|u·Mu| ≤ c|u|²` satisfies `|Mu| ≤ c|u|`. -/
theorem euclideanNorm_mulVec_le_of_abs_dot_le {M : Mat d} (hM : M.transpose = M) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ u : Vec d, |dot u (M.mulVec u)| ≤ c * euclideanSq u) (u : Vec d) :
    euclideanNorm (M.mulVec u) ≤ c * euclideanNorm u := by
  -- polarization: `|v·Mu| ≤ (c/2)(|u|² + |v|²)`
  have hpol : ∀ v : Vec d, |dot v (M.mulVec u)| ≤ c / 2 * (euclideanSq u + euclideanSq v) := by
    intro v
    have h1 := h (u + v)
    have h2 := h (u - v)
    have e : dot (u + v) (M.mulVec (u + v)) - dot (u - v) (M.mulVec (u - v)) =
        4 * dot v (M.mulVec u) := by
      have := dot_add_mulVec_add_sub hM u v
      rw [this, dot_mulVec_comm hM]
    have hs : euclideanSq (u + v) + euclideanSq (u - v) = 2 * (euclideanSq u + euclideanSq v) := by
      rw [euclideanSq_add, show u - v = u + (-1 : ℝ) • v by simp [sub_eq_add_neg],
        euclideanSq_add, euclideanSq_smul]
      simp only [dot_eq_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have := abs_sub (dot (u + v) (M.mulVec (u + v))) (dot (u - v) (M.mulVec (u - v)))
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
    nlinarith
  by_cases hMu : euclideanNorm (M.mulVec u) = 0
  · rw [hMu]; exact mul_nonneg hc (euclideanNorm_nonneg u)
  by_cases hu : euclideanNorm u = 0
  · have hu0 : u = 0 := eq_zero_of_euclideanSq_le_zero (by rw [← euclideanNorm_sq, hu]; norm_num)
    simp [hu0, Matrix.mulVec_zero, euclideanNorm, euclideanSq, dot] at hMu
  have hMu0 : 0 < euclideanNorm (M.mulVec u) := lt_of_le_of_ne (euclideanNorm_nonneg _) (Ne.symm hMu)
  have hu0 : 0 < euclideanNorm u := lt_of_le_of_ne (euclideanNorm_nonneg _) (Ne.symm hu)
  set t : ℝ := euclideanNorm u / euclideanNorm (M.mulVec u) with ht
  have ht0 : 0 < t := div_pos hu0 hMu0
  have hv := hpol (t • M.mulVec u)
  rw [dot_eq_dotProduct, smul_dotProduct, ← dot_eq_dotProduct, smul_eq_mul, euclideanSq_smul,
    abs_mul, abs_of_pos ht0] at hv
  have hdot : dot (M.mulVec u) (M.mulVec u) = euclideanNorm (M.mulVec u) ^ 2 := by
    rw [euclideanNorm_sq]; rfl
  rw [hdot, ← euclideanNorm_sq, ← euclideanNorm_sq, abs_of_nonneg (sq_nonneg _)] at hv
  have htM : t * euclideanNorm (M.mulVec u) = euclideanNorm u := by
    rw [ht]; field_simp
  have : t ^ 2 * euclideanNorm (M.mulVec u) ^ 2 = euclideanNorm u ^ 2 := by
    rw [← htM]; ring
  -- `t |Mu|² ≤ c |u|²`, i.e. `|u| |Mu| ≤ c |u|²`
  have h1 : t * euclideanNorm (M.mulVec u) ^ 2 ≤ c * euclideanNorm u ^ 2 := by nlinarith
  have h2 : euclideanNorm u * euclideanNorm (M.mulVec u) ≤ c * euclideanNorm u ^ 2 := by
    have : t * euclideanNorm (M.mulVec u) ^ 2 = euclideanNorm u * euclideanNorm (M.mulVec u) := by
      rw [← htM]; ring
    linarith
  nlinarith

/-- `ξ·Aξ ≥ λ|ξ|²` with `λ > 0` gives `|A⁻¹v| ≤ λ⁻¹|v|`. -/
theorem euclideanNorm_inv_mulVec_le_of_coercive {A : Mat d} {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : Vec d, lam * euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) (v : Vec d) :
    euclideanNorm (A⁻¹.mulVec v) ≤ lam⁻¹ * euclideanNorm v := by
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 := hA w
    rw [hw, dot_eq_dotProduct, dotProduct_zero] at h1
    have h2 : euclideanSq w ≤ 0 := by nlinarith [euclideanSq_nonneg w]
    exact hw0 (eq_zero_of_euclideanSq_le_zero h2)
  set w := A⁻¹.mulVec v with hw
  have hAw : A.mulVec w = v := mulVec_inv_mulVec hdet v
  have h1 := hA w
  rw [hAw] at h1
  have h2 := dot_le w v
  rw [← euclideanNorm_sq] at h1
  have hw0 := euclideanNorm_nonneg w
  have hv0 := euclideanNorm_nonneg v
  rw [le_inv_mul_iff₀ hlam]
  nlinarith

/-- If `|Pv - v| ≤ ε|v|` for all `v`, then `|Pᵀv - v| ≤ √d ε |v|`. -/
theorem euclideanNorm_transpose_mulVec_sub_le {P : Mat d} {ε : ℝ} (hε : 0 ≤ ε)
    (hP : ∀ v : Vec d, euclideanNorm (P.mulVec v - v) ≤ ε * euclideanNorm v) (q : Vec d) :
    euclideanNorm (P.transpose.mulVec q - q) ≤ Real.sqrt d * (ε * euclideanNorm q) := by
  have hcomp : ∀ k, |(P.transpose.mulVec q - q) k| ≤ euclideanNorm q * ε := by
    intro k
    have e : (P.transpose.mulVec q - q) k = dot q (P.mulVec (unitVector k) - unitVector k) := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, dot,
        unitVector, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · simp
    rw [e]
    refine (abs_dot_le _ _).trans ?_
    have := hP (unitVector k)
    rw [euclideanNorm_unitVector, mul_one] at this
    exact mul_le_mul_of_nonneg_left this (euclideanNorm_nonneg q)
  have h1 := euclideanSq_le_of_abs_le hcomp
  rw [euclideanNorm, show Real.sqrt d * (ε * euclideanNorm q) =
      Real.sqrt (d * (euclideanNorm q * ε) ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (mul_nonneg (euclideanNorm_nonneg q) hε)]
    ring]
  exact Real.sqrt_le_sqrt h1

end QSH
