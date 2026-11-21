import QuantitativeStochasticHomogenization.Front.Notation

/-!
# The sharp quadratic halving iteration

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3, the endpoint of the first-order proof of Theorem 3.8 for `k = 1`: if a nonnegative
excess satisfies `E(R/2) ≤ ¼ (1 + C R^{-ν}) E(R)` at all large scales and `E(R) = o(R²)`, then `E`
vanishes at all large scales. With `q = 2^ν` and `K = C / (q - 1)`, the quantity
`Φ(R) = R^{-2} E(R) exp(-K R^{-ν})` satisfies `Φ(R/2) ≤ Φ(R)`, since `1 + x ≤ exp x`; along the
dyadic scales `Φ(t) ≤ Φ(2ⁿ t) ≤ (2ⁿ t)^{-2} E(2ⁿ t) → 0`.
-/

open Filter Topology

noncomputable section

namespace QSH

/-- **Sharp quadratic halving.** A nonnegative excess with `E(R/2) ≤ ¼ (1 + C R^{-ν}) E(R)` for
`R ≥ R₁` and `E(R) = o(R²)` vanishes at every `t ≥ R₁ / 2`. -/
theorem eq_zero_of_quarter_step {E : ℝ → ℝ} {C ν R₁ : ℝ} (hC : 0 ≤ C) (hν : 0 < ν)
    (hR₁ : 0 < R₁) (hE : ∀ R, 0 ≤ E R)
    (hstep : ∀ R, R₁ ≤ R → E (R / 2) ≤ 1 / 4 * (1 + C * R ^ (-ν)) * E R)
    (hgrowth : Tendsto (fun R => E R / R ^ 2) atTop (𝓝 0)) :
    ∀ t, R₁ ≤ 2 * t → E t = 0 := by
  intro t ht
  have ht0 : 0 < t := by linarith
  set q : ℝ := (2 : ℝ) ^ ν with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) hν
  have hq1' : q - 1 ≠ 0 := by linarith
  set K : ℝ := C / (q - 1) with hK
  have hK0 : 0 ≤ K := div_nonneg hC (by linarith)
  set Φ : ℝ → ℝ := fun R => E R / R ^ 2 * Real.exp (-(K * R ^ (-ν))) with hΦ
  have hmono : ∀ R, R₁ ≤ R → Φ (R / 2) ≤ Φ R := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₁ hR
    set u := R ^ (-ν) with hu
    have hhalf : (R / 2) ^ (-ν) = q * u := by
      rw [Real.div_rpow hR0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hq, hu]
      field_simp
    have hA : 0 ≤ E R / R ^ 2 := div_nonneg (hE R) (by positivity)
    have h4 : E (R / 2) / (R / 2) ^ 2 ≤ (1 + C * u) * (E R / R ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      calc E (R / 2) ≤ 1 / 4 * (1 + C * u) * E R := hstep R hR
        _ = (1 + C * u) * (E R / R ^ 2) * (R / 2) ^ 2 := by field_simp; ring
    have hexp : (1 + C * u) * Real.exp (-(K * (q * u))) ≤ Real.exp (-(K * u)) := by
      have h1 : 1 + C * u ≤ Real.exp (C * u) := by linarith [Real.add_one_le_exp (C * u)]
      have h2 : C * u + -(K * (q * u)) = -(K * u) := by
        rw [hK]
        field_simp
        ring
      calc (1 + C * u) * Real.exp (-(K * (q * u)))
          ≤ Real.exp (C * u) * Real.exp (-(K * (q * u))) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Real.exp (-(K * u)) := by rw [← Real.exp_add, h2]
    simp only [hΦ]
    rw [hhalf]
    calc E (R / 2) / (R / 2) ^ 2 * Real.exp (-(K * (q * u)))
        ≤ (1 + C * u) * (E R / R ^ 2) * Real.exp (-(K * (q * u))) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = (1 + C * u) * Real.exp (-(K * (q * u))) * (E R / R ^ 2) := by ring
      _ ≤ Real.exp (-(K * u)) * (E R / R ^ 2) := mul_le_mul_of_nonneg_right hexp hA
      _ = E R / R ^ 2 * Real.exp (-(K * u)) := by ring
  have hiter : ∀ n : ℕ, Φ t ≤ Φ (2 ^ n * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      have hle : R₁ ≤ 2 ^ (n + 1) * t := by
        calc R₁ ≤ 2 * t := ht
          _ ≤ 2 ^ (n + 1) * t := by
            refine mul_le_mul_of_nonneg_right ?_ ht0.le
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h := hmono (2 ^ (n + 1) * t) hle
      have heq : 2 ^ (n + 1) * t / 2 = 2 ^ n * t := by
        rw [pow_succ]
        ring
      rwa [heq] at h
  have hlim : Tendsto (fun n : ℕ => Φ (2 ^ n * t)) atTop (𝓝 0) := by
    have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * t) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const ht0
    refine squeeze_zero (fun n => ?_) (fun n => ?_) (hgrowth.comp htend)
    · exact mul_nonneg (div_nonneg (hE _) (by positivity)) (Real.exp_pos _).le
    · simp only [hΦ, Function.comp]
      refine mul_le_of_le_one_right (div_nonneg (hE _) (by positivity)) ?_
      exact Real.exp_le_one_iff.2
        (neg_nonpos.2 (mul_nonneg hK0 (Real.rpow_nonneg (by positivity) _)))
  have hΦt : Φ t ≤ 0 := ge_of_tendsto' hlim hiter
  have h1 : E t / t ^ 2 ≤ 0 := by
    rcases le_or_gt (E t / t ^ 2) 0 with hle | hcon
    · exact hle
    · have := mul_pos hcon (Real.exp_pos (-(K * t ^ (-ν))))
      simp only [hΦ] at hΦt
      linarith
  have h2 : E t ≤ 0 := by
    have h3 : E t = E t / t ^ 2 * t ^ 2 := by field_simp
    rw [h3]
    nlinarith [sq_nonneg t]
  exact le_antisymm h2 (hE t)

end QSH
