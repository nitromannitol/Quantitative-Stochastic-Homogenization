import QuantitativeStochasticHomogenization.Ch04.Sec05.Proposition412

/-!
# Lemma 5.29 (i): blocks at all scales `r ∈ [R^{η₁}, R]`

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29 (i), (5.90), for centered local additive fields: the block estimate (4.117)
(= (5.89)), proved for `r ∈ [R^{η₁}, R^{η₂}]`, extends to `r ∈ [R^{η₁}, R]`. With `r₁ = R^{η₁}` the
additivity replaces `X(r)` by the heat average of `X(r₁)` (Step 1 of Proposition 4.12), whose
weight `g = (f 1_{□_R}) ∗ Φ_{√(r²-r₁²)}` has width at most `R`; it is cut along the cells of side `R`
around the center, where `|g| ≤ 2^{d/2} ∏ᵢ exp(-(|kᵢ| - 1)₊²/8)` by the Gaussian tail (5.95), and the
far cells carry a Gaussian tail.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

/-- The majorant of the weight on the cell `k`: `∏ᵢ exp(-(|kᵢ| - 1)₊²/8)`. -/
noncomputable def shiftedGaussian (m : ℤ) : ℝ := Real.exp (-((max (|(m : ℝ)| - 1) 0) ^ 2) / 8)

theorem summable_shiftedGaussian : Summable shiftedGaussian := by
  have hq0 : 0 ≤ Real.exp (-(1 / 4)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(1 / 4)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeo := (summable_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (3 / 8))
  have hbound : ∀ m : ℤ, shiftedGaussian m ≤ Real.exp (3 / 8) * Real.exp (-(1 / 4)) ^ m.natAbs := by
    intro m
    unfold shiftedGaussian
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hm : (m.natAbs : ℝ) = |(m : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hm]
    have h0 : |(m : ℝ)| - 1 ≤ max (|(m : ℝ)| - 1) 0 := le_max_left _ _
    have h1 : 2 * max (|(m : ℝ)| - 1) 0 - 1 ≤ (max (|(m : ℝ)| - 1) 0) ^ 2 := by
      nlinarith [sq_nonneg (max (|(m : ℝ)| - 1) 0 - 1)]
    linarith
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
    simpa using hbound n
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (hgeo.comp_injective (add_left_injective 1))
    have := hbound (-((n : ℤ) + 1))
    simp only [Function.comp_apply]
    convert this using 3
    omega

/-- The constant `∑_{m ∈ ℤ} exp(-(|m| - 1)₊²/8)`. -/
noncomputable def shiftedGaussianConst : ℝ := ∑' m : ℤ, shiftedGaussian m

theorem shiftedGaussianConst_nonneg : 0 ≤ shiftedGaussianConst :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem sum_latticeBox_prod_shiftedGaussian_le (N : ℕ) :
    ∑ k ∈ latticeBox d N, ∏ i, shiftedGaussian (k i) ≤ shiftedGaussianConst ^ d := by
  unfold latticeBox
  rw [Finset.sum_prod_piFinset (Finset.Icc (-(N : ℤ)) N) (fun _ m => shiftedGaussian m)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) ?_ d
  exact summable_shiftedGaussian.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)

/-- Points of the cell `z + R k + [-R/2, R/2)^d` are at Euclidean distance at least
`R (∑ᵢ (|kᵢ| - 1)₊²)^{1/2}` from the closed cube of side `R` around `z`. -/
theorem le_euclideanNorm_of_mem_cellAt {z : Vec d} {R : ℝ} (hR : 0 < R) {k : LatticeIndex d}
    {y x : Vec d} (hy : y ∈ cellAt z R k) (hx : x ∈ closedCube z R) :
    R * Real.sqrt (∑ i, (max (|(k i : ℝ)| - 1) 0) ^ 2) ≤ euclideanNorm (y - x) := by
  have hcoord : ∀ i, R * max (|(k i : ℝ)| - 1) 0 ≤ |y i - x i| := by
    intro i
    obtain ⟨h1, h2⟩ := hy i
    simp only [Pi.sub_apply] at h1 h2
    have hyz : R * |(k i : ℝ)| - R / 2 ≤ |y i - z i| := by
      rcases le_or_gt 0 (k i : ℝ) with hk | hk
      · rw [abs_of_nonneg hk]
        exact (by linarith : R * k i - R / 2 ≤ y i - z i).trans (le_abs_self _)
      · rw [abs_of_neg hk]
        have := neg_abs_le (y i - z i)
        linarith
    have hxz : |x i - z i| ≤ R / 2 := hx i
    have htri : |y i - z i| ≤ |y i - x i| + |x i - z i| := by
      calc |y i - z i| = |(y i - x i) + (x i - z i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rcases le_total (|(k i : ℝ)| - 1) 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact abs_nonneg _
    · rw [max_eq_left h]
      linarith
  rw [euclideanNorm, euclideanSq_eq_sum_sq, ← Real.sqrt_sq hR.le, ← Real.sqrt_mul (sq_nonneg _),
    Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h := hcoord i
  have h0 : 0 ≤ R * max (|(k i : ℝ)| - 1) 0 := mul_nonneg hR.le (le_max_right _ _)
  calc R ^ 2 * (max (|(k i : ℝ)| - 1) 0) ^ 2 = (R * max (|(k i : ℝ)| - 1) 0) ^ 2 := by ring
    _ ≤ |(y - x) i| ^ 2 := pow_le_pow_left₀ h0 (by simpa using h) 2
    _ = (y - x) i ^ 2 := sq_abs _

end QSH
