import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Quadratic forms from the parallelogram identity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3, (1.23) and Definition 1.2: the limit `μ̄(p)` of (1.22) is a quadratic form
`μ̄(p) = ½ p·āp` with `ā` symmetric.

A function `L : ℝ^d → ℝ` satisfying the parallelogram identity
`L(x + y) + L(x - y) = 2L(x) + 2L(y)` and a bound `|L(x)| ≤ M|x|²` is of this form. The
polarization `B(x, y) = (L(x + y) - L(x - y))/4` is additive in each variable (the argument of
Jordan and von Neumann); the bound and `B(n x, y) = n B(x, y)` make `x ↦ B(x, y)` continuous at
the origin, hence `ℝ`-linear, and `L(x) = B(x, x) = ½ x·āx` with `ā_{ij} = 2 B(e_i, e_j)`.
-/

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The polarization `B(x, y) = (L(x + y) - L(x - y))/4` of a function `L`. -/
def polarization (L : Vec d → ℝ) (x y : Vec d) : ℝ :=
  (L (x + y) - L (x - y)) / 4

private theorem euclideanSq_smul (c : ℝ) (x : Vec d) :
    euclideanSq (c • x) = c ^ 2 * euclideanSq x := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem euclideanSq_add_add_sub (x y : Vec d) :
    euclideanSq (x + y) + euclideanSq (x - y) = 2 * euclideanSq x + 2 * euclideanSq y := by
  simp only [euclideanSq, dot, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem euclideanSq_le_card_mul_norm_sq (x : Vec d) : euclideanSq x ≤ d * ‖x‖ ^ 2 := by
  unfold euclideanSq dot
  calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h
        nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
    _ = d * ‖x‖ ^ 2 := by simp

private theorem sum_smul_unitVector (x : Vec d) : ∑ i, x i • unitVector i = x := by
  funext j
  simp [unitVector, Finset.sum_apply, Pi.single_apply]

section Parallelogram

variable {L : Vec d → ℝ} (hL : ∀ x y, L (x + y) + L (x - y) = 2 * L x + 2 * L y)
include hL

theorem map_zero_of_parallelogram : L 0 = 0 := by
  have h := hL 0 0
  simp only [add_zero, sub_zero] at h
  linarith

theorem map_neg_of_parallelogram (x : Vec d) : L (-x) = L x := by
  have h := hL 0 x
  rw [zero_add, zero_sub, map_zero_of_parallelogram hL] at h
  linarith

theorem polarization_self (x : Vec d) : polarization L x x = L x := by
  have h := hL x x
  unfold polarization
  rw [sub_self, map_zero_of_parallelogram hL] at h ⊢
  linarith

theorem polarization_comm (x y : Vec d) : polarization L x y = polarization L y x := by
  unfold polarization
  rw [add_comm y x, ← map_neg_of_parallelogram hL (y - x), neg_sub]

theorem polarization_zero_left (y : Vec d) : polarization L 0 y = 0 := by
  unfold polarization
  rw [zero_add, zero_sub, map_neg_of_parallelogram hL, sub_self, zero_div]

theorem polarization_add_add_sub (x x' y : Vec d) :
    polarization L (x + x') y + polarization L (x - x') y = 2 * polarization L x y := by
  have h1 := hL (x + y) x'
  have h2 := hL (x - y) x'
  have e1 : x + y + x' = x + x' + y := by abel
  have e2 : x + y - x' = x - x' + y := by abel
  have e3 : x - y + x' = x + x' - y := by abel
  have e4 : x - y - x' = x - x' - y := by abel
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  unfold polarization
  linarith

theorem polarization_add_left (u v y : Vec d) :
    polarization L (u + v) y = polarization L u y + polarization L v y := by
  set x : Vec d := (1 / 2 : ℝ) • (u + v)
  set x' : Vec d := (1 / 2 : ℝ) • (u - v)
  have hu : x + x' = u := by
    simp only [x, x', ← smul_add]
    rw [show u + v + (u - v) = (2 : ℝ) • u by rw [two_smul]; abel, smul_smul]
    norm_num
  have hv : x - x' = v := by
    simp only [x, x', ← smul_sub]
    rw [show u + v - (u - v) = (2 : ℝ) • v by rw [two_smul]; abel, smul_smul]
    norm_num
  have huv : u + v = x + x := by
    simp only [x, ← add_smul]
    norm_num
  have h := polarization_add_add_sub hL x x' y
  have h2 := polarization_add_add_sub hL x x y
  rw [hu, hv] at h
  rw [sub_self, polarization_zero_left hL, add_zero] at h2
  rw [huv, h2, h]

/-- The polarization in its first variable, as an additive map. -/
def polarizationAddHom (y : Vec d) : Vec d →+ ℝ where
  toFun x := polarization L x y
  map_zero' := polarization_zero_left hL y
  map_add' u v := polarization_add_left hL u v y

theorem continuous_polarizationAddHom {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, |L x| ≤ M * euclideanSq x) (y : Vec d) :
    Continuous (polarizationAddHom hL y) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (M * (1 + euclideanSq y) / ε)
  have hy0 : 0 ≤ euclideanSq y := by
    unfold euclideanSq dot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  refine ⟨1 / (N * (d + 1)), by positivity, fun {x} hx => ?_⟩
  rw [dist_zero_right] at hx
  rw [map_zero, dist_zero_right, Real.norm_eq_abs]
  change |polarization L x y| < ε
  -- `B(x, y) = B(N x, y) / N`
  have hscale : polarization L ((N : ℝ) • x) y = N * polarization L x y := by
    have h := map_nsmul (polarizationAddHom hL y) N x
    change polarization L (N • x) y = N • polarization L x y at h
    rw [Nat.cast_smul_eq_nsmul ℝ N x, h, nsmul_eq_mul]
  have hNx : euclideanSq ((N : ℝ) • x) ≤ 1 := by
    rw [euclideanSq_smul]
    have h1 := euclideanSq_le_card_mul_norm_sq x
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hx' : ‖x‖ * (N * (d + 1)) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hx
    have hx0 : 0 ≤ ‖x‖ * (N * (d + 1)) := by positivity
    have hsq : (‖x‖ * (N * (d + 1))) ^ 2 ≤ 1 := by nlinarith
    calc (N : ℝ) ^ 2 * euclideanSq x ≤ N ^ 2 * (d * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (‖x‖ * N) ^ 2 * d := by ring
      _ ≤ (‖x‖ * N) ^ 2 * (d + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
      _ = (‖x‖ * (N * (d + 1))) ^ 2 := by ring
      _ ≤ 1 := hsq
  have hbound : |polarization L ((N : ℝ) • x) y| ≤ M * (1 + euclideanSq y) / 2 := by
    unfold polarization
    have h1 := hM ((N : ℝ) • x + y)
    have h2 := hM ((N : ℝ) • x - y)
    have h3 := euclideanSq_add_add_sub ((N : ℝ) • x) y
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc |L ((N : ℝ) • x + y) - L ((N : ℝ) • x - y)| / 4
        ≤ (|L ((N : ℝ) • x + y)| + |L ((N : ℝ) • x - y)|) / 4 := by
          gcongr; exact abs_sub _ _
      _ ≤ (M * euclideanSq ((N : ℝ) • x + y) + M * euclideanSq ((N : ℝ) • x - y)) / 4 := by
          gcongr
      _ = M * (2 * euclideanSq ((N : ℝ) • x) + 2 * euclideanSq y) / 4 := by
          rw [← mul_add, h3]
      _ ≤ M * (2 * 1 + 2 * euclideanSq y) / 4 := by gcongr
      _ = M * (1 + euclideanSq y) / 2 := by ring
  rw [hscale, abs_mul, abs_of_pos hN0] at hbound
  have hlt : M * (1 + euclideanSq y) / 2 < N * ε := by
    rw [div_lt_iff₀ hε] at hN
    have h0 : 0 ≤ M * (1 + euclideanSq y) := by positivity
    linarith
  nlinarith [abs_nonneg (polarization L x y)]

theorem polarization_smul_left {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |L x| ≤ M * euclideanSq x)
    (c : ℝ) (x y : Vec d) : polarization L (c • x) y = c * polarization L x y := by
  have h := map_real_smul (polarizationAddHom hL y) (continuous_polarizationAddHom hL hM0 hM y) c x
  change polarization L (c • x) y = c • polarization L x y at h
  rwa [smul_eq_mul] at h

theorem polarization_sum_left {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |L x| ≤ M * euclideanSq x)
    (x y : Vec d) : polarization L x y = ∑ i, x i * polarization L (unitVector i) y := by
  have h := map_sum (polarizationAddHom hL y) (fun i => x i • unitVector i) Finset.univ
  change polarization L (∑ i, x i • unitVector i) y =
    ∑ i, polarization L (x i • unitVector i) y at h
  rw [sum_smul_unitVector] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => polarization_smul_left hL hM0 hM _ _ _

/-- **A function with the parallelogram identity and a quadratic bound is a quadratic form**:
`L(x) = ½ x·Ax` for a symmetric matrix `A`. -/
theorem exists_symmetric_of_parallelogram {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, |L x| ≤ M * euclideanSq x) :
    ∃ A : Mat d, A.transpose = A ∧ ∀ x, L x = (1 / 2 : ℝ) * dot x (A.mulVec x) := by
  refine ⟨Matrix.of fun i j => 2 * polarization L (unitVector i) (unitVector j), ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [polarization_comm hL]
  · intro x
    rw [← polarization_self hL x, polarization_sum_left hL hM0 hM x x]
    simp only [dot, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [polarization_comm hL, polarization_sum_left hL hM0 hM x (unitVector i)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [polarization_comm hL]
    ring

end Parallelogram

end QSH
