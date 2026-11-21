import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectorLocalizationHypotheses

/-!
# Size of the localization error bound

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Proposition 4.11 from Lemmas 4.21 and 4.22. The bound `localizationErrorBound` of
Lemma 4.22 is at most a constant times `κ + exp(-T²/(8r²)) + η` when `η ≤ 1`, with a constant
depending only on `d` and `Λ` when `|p|, |q| ≤ 1`; and at the outer radius `T = r^{1+δ}` the
Gaussian factor `exp(-T²/(8r²)) = exp(-r^{2δ}/8)` is at most `r^{-γ}` for every `γ` and all large
`r`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem linearCoefficient_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (p q : Vec d) :
    0 ≤ linearCoefficient d Λ p q :=
  add_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Nat.cast_nonneg d)) hΛ) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem sum_abs_le_of_euclideanNorm_le_one {p : Vec d} (hp : euclideanNorm p ≤ 1) :
    ∑ k, |p k| ≤ d := by
  calc ∑ k, |p k| ≤ ∑ _k : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => (abs_coord_le_euclideanNorm p k).trans hp
    _ = d := by simp

/-- The linear coefficient is at most `d² Λ + d` for `|p|, |q| ≤ 1`. -/
theorem linearCoefficient_le {Λ : ℝ} (hΛ : 0 ≤ Λ) {p q : Vec d} (hp : euclideanNorm p ≤ 1)
    (hq : euclideanNorm q ≤ 1) : linearCoefficient d Λ p q ≤ d * d * Λ + d := by
  have h1 := sum_abs_le_of_euclideanNorm_le_one hp
  have h2 := sum_abs_le_of_euclideanNorm_le_one hq
  unfold linearCoefficient
  have h3 : (∑ k, |p k|) * d * Λ ≤ d * d * Λ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg d)) hΛ
  linarith

/-- The constant of `localizationErrorBound_le`. -/
def localizationErrorConstant (d : ℕ) (Λ L : ℝ) : ℝ :=
  ((d : ℝ) * Λ / 2 + L / 2) * (d * (2 * L + 1) ^ 2) + L / 2 * (2 : ℝ) ^ ((d : ℝ) / 2) +
    ((d : ℝ) ^ 2 * Λ * (2 * (2 * L + 1) + 1) / 2 + L)

/-- **The localization error bound is linear in its errors**: for `0 ≤ η ≤ 1` and `0 ≤ κ`,
`localizationErrorBound ≤ A (κ + exp(-T²/(8r²)) + η)`. -/
theorem localizationErrorBound_le {Λ : ℝ} (hΛ : 0 ≤ Λ) (p q : Vec d) {η κ T r : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hκ : 0 ≤ κ) :
    localizationErrorBound d Λ p q η κ T r ≤
      localizationErrorConstant d Λ (linearCoefficient d Λ p q) *
        (κ + Real.exp (-(T ^ 2) / (8 * r ^ 2)) + η) := by
  set L := linearCoefficient d Λ p q
  have hL := linearCoefficient_nonneg hΛ p q
  set e := Real.exp (-(T ^ 2) / (8 * r ^ 2))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hdΛ : 0 ≤ (d : ℝ) * Λ := mul_nonneg (Nat.cast_nonneg d) hΛ
  have hd2Λ : 0 ≤ (d : ℝ) ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ
  set a1 := ((d : ℝ) * Λ / 2 + L / 2) * (d * (2 * L + 1) ^ 2)
  set a2 := L / 2 * (2 : ℝ) ^ ((d : ℝ) / 2)
  set a3 := (d : ℝ) ^ 2 * Λ * (2 * (2 * L + 1) + 1) / 2 + L
  have ha1 : 0 ≤ a1 := mul_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _))
  have ha2 : 0 ≤ a2 := mul_nonneg (by linarith) (by positivity)
  have ha3 : 0 ≤ a3 :=
    add_nonneg (div_nonneg (mul_nonneg hd2Λ (by linarith)) (by norm_num)) hL
  have hA : localizationErrorConstant d Λ L = a1 + a2 + a3 := rfl
  have hB : localizationErrorBound d Λ p q η κ T r =
      a1 * κ + a2 * e + ((d : ℝ) ^ 2 * Λ * (2 * (2 * L + 1) + η) / 2 + L) * η := by
    simp only [localizationErrorBound, a1, a2, e, L]
    ring
  have h3 : ((d : ℝ) ^ 2 * Λ * (2 * (2 * L + 1) + η) / 2 + L) * η ≤ a3 * η := by
    refine mul_le_mul_of_nonneg_right ?_ hη0
    have := mul_le_mul_of_nonneg_left (show 2 * (2 * L + 1) + η ≤ 2 * (2 * L + 1) + 1 by
      linarith) hd2Λ
    simp only [a3]
    linarith
  rw [hA, hB]
  have h4 : a1 * κ + a2 * e + a3 * η ≤ (a1 + a2 + a3) * (κ + e + η) := by
    nlinarith [mul_nonneg ha1 he, mul_nonneg ha1 hη0, mul_nonneg ha2 hκ, mul_nonneg ha2 hη0,
      mul_nonneg ha3 hκ, mul_nonneg ha3 he]
  linarith

/-- At the outer radius `T = r^{1+δ}`, `T²/(8r²) = r^{2δ}/8`. -/
theorem localizationOuterRadius_sq_div {δ r : ℝ} (hr : 0 < r) :
    localizationOuterRadius δ r ^ 2 / (8 * r ^ 2) = r ^ (2 * δ) / 8 := by
  unfold localizationOuterRadius
  rw [← Real.rpow_natCast (r ^ (1 + δ)) 2, ← Real.rpow_mul hr.le,
    show (1 + δ) * ((2 : ℕ) : ℝ) = 2 + 2 * δ by push_cast; ring,
    Real.rpow_add hr, Real.rpow_two]
  field_simp

/-- **The Gaussian factor at the outer radius decays faster than every power.** -/
theorem exists_exp_neg_le_rpow {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) ≤ r ^ (-γ) := by
  have h2δ : 0 < 2 * δ := by linarith
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (γ / (2 * δ)) (1 / 8)
    (by norm_num)).comp (tendsto_rpow_atTop h2δ)
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 1 one_pos)
  refine ⟨max R₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have h := hR₁ r (le_trans (le_max_left _ _) hr)
  simp only [Function.comp] at h
  rw [← Real.rpow_mul hr0.le, show 2 * δ * (γ / (2 * δ)) = γ by field_simp] at h
  have hexp : Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) =
      Real.exp (-(1 / 8) * r ^ (2 * δ)) := by
    rw [neg_div, localizationOuterRadius_sq_div hr0]
    congr 1
    ring
  rw [hexp, Real.rpow_neg hr0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hr0 _), mul_comm]
  exact h.le

end QSH
