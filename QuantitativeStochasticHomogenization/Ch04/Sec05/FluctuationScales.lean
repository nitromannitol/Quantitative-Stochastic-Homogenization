import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationStep

/-!
# The scales of the induction in the proof of Proposition 4.12

Elementary inequalities between the scales `R`, `R' = R^{1-2ε}`, `r₁ = (R/2)^{η₁}` and
`r ∈ [R^{η₁}, R^{η₂}]` used in Section 4.5 of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*: the exponent `ε` and the threshold `R₀` of
(4.118), and the bounds of the four contributions of the induction step by `R^{-β-ε}`.
-/

namespace QSH

theorem le_rpow_of_rpow_inv_le {c κ R : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) (hR : c ^ κ⁻¹ ≤ R) :
    c ≤ R ^ κ := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hc _) hR hκ.le
  rwa [← Real.rpow_mul hc, inv_mul_cancel₀ hκ.ne', Real.rpow_one] at h

/-- The cost of Step 1: `((R/2)^{η₁})^{-α} ≤ 2^{η₁ α} R^{-β-ε}` when `β + ε ≤ η₁ α`. -/
theorem rpow_half_rpow_neg_le {R η₁ α β ε : ℝ} (hR : 1 ≤ R) (hβε : β + ε ≤ η₁ * α) :
    ((R / 2) ^ η₁) ^ (-α) ≤ 2 ^ (η₁ * α) * R ^ (-(β + ε)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [← Real.rpow_mul (by positivity), Real.div_rpow hR0.le (by norm_num),
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num), mul_comm]
  have e : -(η₁ * -α) = η₁ * α := by ring
  rw [e, show η₁ * -α = -(η₁ * α) by ring]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR (by linarith))
    (by positivity)

/-- The count of frame cells in terms of `R`: if `n ≤ R^{2ε}/2` and `R^{2ε} ≥ 1`, then
`5 d (2(n+2)+1)^{d-1} ≤ 5 d 6^{d-1} R^{2ε(d-1)}`. -/
theorem frame_count_le {d n : ℕ} {R ε : ℝ} (hR : 0 < R) (hn : (n : ℝ) ≤ R ^ (2 * ε) / 2)
    (hR1 : 1 ≤ R ^ (2 * ε)) :
    ((5 * d * (2 * (n + 2) + 1) ^ (d - 1) : ℕ) : ℝ) ≤
      5 * d * 6 ^ (d - 1) * R ^ (2 * ε * ((d - 1 : ℕ) : ℝ)) := by
  push_cast
  have h1 : (2 * ((n : ℝ) + 2) + 1) ≤ 6 * R ^ (2 * ε) := by linarith
  have h2 : (2 * ((n : ℝ) + 2) + 1) ^ (d - 1) ≤ (6 * R ^ (2 * ε)) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  rw [mul_pow, ← Real.rpow_natCast (R ^ (2 * ε)), ← Real.rpow_mul hR.le] at h2
  calc 5 * (d : ℝ) * (2 * ((n : ℝ) + 2) + 1) ^ (d - 1)
      ≤ 5 * d * (6 ^ (d - 1) * R ^ (2 * ε * ((d - 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 5 * d * 6 ^ (d - 1) * R ^ (2 * ε * ((d - 1 : ℕ) : ℝ)) := by ring

/-- The constant of the frame cells. -/
noncomputable def frameConst (d : ℕ) : ℝ :=
  Real.sqrt (2 * 4 ^ d) * Real.sqrt (5 * d * 6 ^ (d - 1))

theorem frameConst_nonneg (d : ℕ) : 0 ≤ frameConst d := by unfold frameConst; positivity

/-- **The frame cells**: with `R' = R^{1-2ε}`, `m ≤ 5 d 6^{d-1} R^{2ε(d-1)}`, `ε ≥ 0` and
`β ≤ d/2`, `R^{-d} (2·4^d)^{1/2} m^{1/2} R'^d C R'^{-β} ≤ K_d C R^{-β-ε}`. -/
theorem scale_cells_le {d : ℕ} (hd : 1 ≤ d) {R ε β C m : ℝ} (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hβ : β ≤ (d : ℝ) / 2) (hC : 0 ≤ C)
    (hm : m ≤ 5 * d * 6 ^ (d - 1) * R ^ (2 * ε * ((d - 1 : ℕ) : ℝ))) :
    R ^ (-(d : ℝ)) * (Real.sqrt (2 * 4 ^ d) * (Real.sqrt m *
      ((R ^ (1 - 2 * ε)) ^ d * (C * (R ^ (1 - 2 * ε)) ^ (-β))))) ≤
      frameConst d * C * R ^ (-(β + ε)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hdm : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]; simp
  have hsq : Real.sqrt m ≤ Real.sqrt (5 * d * 6 ^ (d - 1)) * R ^ (ε * ((d : ℝ) - 1)) := by
    calc Real.sqrt m ≤ Real.sqrt (5 * d * 6 ^ (d - 1) * R ^ (2 * ε * ((d - 1 : ℕ) : ℝ))) :=
          Real.sqrt_le_sqrt hm
      _ = Real.sqrt (5 * d * 6 ^ (d - 1)) * R ^ (ε * ((d : ℝ) - 1)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (R ^ _), ← Real.rpow_mul hR0.le,
            hdm]
          ring_nf
  have hexp : R ^ (-(d : ℝ)) * ((R ^ (1 - 2 * ε)) ^ d * (R ^ (1 - 2 * ε)) ^ (-β)) *
      R ^ (ε * ((d : ℝ) - 1)) ≤ R ^ (-(β + ε)) := by
    rw [← Real.rpow_natCast (R ^ (1 - 2 * ε)), ← Real.rpow_mul hR0.le, ← Real.rpow_mul hR0.le,
      ← Real.rpow_add hR0, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    refine Real.rpow_le_rpow_of_exponent_le hR ?_
    nlinarith
  have hA : 0 ≤ Real.sqrt (2 * 4 ^ d) := Real.sqrt_nonneg _
  calc R ^ (-(d : ℝ)) * (Real.sqrt (2 * 4 ^ d) * (Real.sqrt m *
        ((R ^ (1 - 2 * ε)) ^ d * (C * (R ^ (1 - 2 * ε)) ^ (-β)))))
      = Real.sqrt (2 * 4 ^ d) * C * Real.sqrt m *
          (R ^ (-(d : ℝ)) * ((R ^ (1 - 2 * ε)) ^ d * (R ^ (1 - 2 * ε)) ^ (-β))) := by ring
    _ ≤ Real.sqrt (2 * 4 ^ d) * C * (Real.sqrt (5 * d * 6 ^ (d - 1)) *
          R ^ (ε * ((d : ℝ) - 1))) *
          (R ^ (-(d : ℝ)) * ((R ^ (1 - 2 * ε)) ^ d * (R ^ (1 - 2 * ε)) ^ (-β))) := by
        gcongr
    _ = frameConst d * C * (R ^ (-(d : ℝ)) * ((R ^ (1 - 2 * ε)) ^ d *
          (R ^ (1 - 2 * ε)) ^ (-β)) * R ^ (ε * ((d : ℝ) - 1))) := by
        unfold frameConst
        ring
    _ ≤ frameConst d * C * R ^ (-(β + ε)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg (frameConst_nonneg d) hC)

/-- **The far part**: for `ρ ≤ R^{η₂}`, `R' = R^{1-2ε}` with `κ = 1 - 2ε - η₂ > 0`,
`exp(-R'²/(8ρ²)) ≤ exp(-R^{2κ}/8)`. -/
theorem exp_far_le {R ε η₂ ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 < ρ) (hρR : ρ ≤ R ^ η₂) :
    Real.exp (-((R ^ (1 - 2 * ε)) ^ 2 / (8 * ρ ^ 2))) ≤
      Real.exp (-(1 / 8 * R ^ (2 * (1 - 2 * ε - η₂)))) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  have hρ2 : ρ ^ 2 ≤ R ^ (2 * η₂) := by
    rw [mul_comm, Real.rpow_mul hR0.le, Real.rpow_two]
    exact pow_le_pow_left₀ hρ.le hρR 2
  have e : (R ^ (1 - 2 * ε)) ^ 2 = R ^ (2 * (1 - 2 * ε - η₂)) * R ^ (2 * η₂) := by
    rw [← Real.rpow_add hR0, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    congr 1
    push_cast
    ring
  rw [e, le_div_iff₀ (by positivity)]
  have hpos : 0 ≤ R ^ (2 * (1 - 2 * ε - η₂)) := Real.rpow_nonneg hR0.le _
  nlinarith

end QSH
