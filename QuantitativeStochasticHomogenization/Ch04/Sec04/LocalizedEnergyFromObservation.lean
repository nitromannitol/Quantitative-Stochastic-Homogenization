import QuantitativeStochasticHomogenization.Ch04.Sec04.BallExcessDecayProof
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationProof

/-!
# The localized energy estimate (5.85) from the observation estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21 and (5.85). The exponents: with `β = d/2`,
`Δ = β(1 + δ) + δ - γ > 0`, `h = Δ/(2(1 + δ))`, the construction exponent `α = β - h` and the
regularity exponent `ϑ = 1 - h` satisfy `γ < α(1 + δ) + δ` and, for the intermediate radius
`S = r^{1+δ-ε}`, `(r/S)^ϑ S^{-β} = r^{-γ-h} ≤ r^{-γ}`. With the excess decay of one slope on
balls (`ballExcessDecay`) and the first-order Liouville theorem, the observation estimate
`LocalizationObservationEstimate` at the exponent `β = d/2` gives `QSH.Frozen.localizedEnergy`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The decrement `h = (β(1 + δ) + δ - γ)/(2(1 + δ))`. -/
def localizationDecrement (β δ γ : ℝ) : ℝ := (β * (1 + δ) + δ - γ) / (2 * (1 + δ))

/-- **The exponent budget**: with `h = localizationDecrement β δ γ`, the
construction exponent `β - h` is admissible and `(r/S)^{1-h} S^{-β} ≤ r^{-γ}`. -/
theorem localization_exponent_budget {β δ γ : ℝ} (hβ : 1 ≤ β) (hδ : 0 < δ)
    (hγ1 : β * (1 + δ) < γ) (hγ2 : γ < β * (1 + δ) + δ) :
    0 < localizationDecrement β δ γ ∧ localizationDecrement β δ γ < 1 / 2 ∧
      0 < β - localizationDecrement β δ γ ∧
      γ < (β - localizationDecrement β δ γ) * (1 + δ) + δ ∧
      ∀ r : ℝ, 1 ≤ r →
        (r / localizationIntermediateRadius δ (β - localizationDecrement β δ γ) γ r) ^
            (1 - localizationDecrement β δ γ) *
          localizationIntermediateRadius δ (β - localizationDecrement β δ γ) γ r ^ (-β) ≤
            r ^ (-γ) := by
  set h := localizationDecrement β δ γ with hhdef
  have h1δ : 0 < 1 + δ := by linarith
  have h2δ : (2 : ℝ) * (1 + δ) ≠ 0 := (mul_pos two_pos h1δ).ne'
  have hh : h * (2 * (1 + δ)) = β * (1 + δ) + δ - γ := by
    rw [hhdef, localizationDecrement, div_mul_cancel₀ _ h2δ]
  have hh0 : 0 < h := by
    rw [hhdef, localizationDecrement]
    exact div_pos (by linarith) (mul_pos two_pos h1δ)
  have hh2 : h < 1 / 2 := by
    rw [hhdef, localizationDecrement, div_lt_iff₀ (mul_pos two_pos h1δ)]
    linarith
  have hα0 : 0 < β - h := by linarith
  have hnum : (β - h) * (1 + δ) + δ - γ = (β * (1 + δ) + δ - γ) / 2 := by
    linear_combination (-1 / 2 : ℝ) * hh
  have hαγ : γ < (β - h) * (1 + δ) + δ := by linarith
  refine ⟨hh0, hh2, hα0, hαγ, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have h1α : 0 < 1 + (β - h) := by linarith
  have hcap : ((β - h) * (1 + δ) + δ - γ) / (1 + (β - h)) ≤ δ / 2 := by
    rw [div_le_iff₀ h1α, hnum]
    nlinarith [mul_pos hδ hα0]
  have hε : localizationEpsilon δ (β - h) γ = ((β - h) * (1 + δ) + δ - γ) / (1 + (β - h)) := by
    unfold localizationEpsilon
    exact min_eq_left hcap
  have hε1 : localizationEpsilon δ (β - h) γ * (1 + (β - h)) = (β * (1 + δ) + δ - γ) / 2 := by
    rw [hε, div_mul_cancel₀ _ h1α.ne', hnum]
  set L' := 1 + δ - localizationEpsilon δ (β - h) γ with hL'
  have F1 : L' * (1 + (β - h)) = (1 + δ) * (1 + (β - h)) - (β * (1 + δ) + δ - γ) / 2 := by
    rw [hL']
    linear_combination (-1 : ℝ) * hε1
  have e1 : (((1 - h) + β) * L' - (1 - h) - γ) * (1 + (β - h)) = h * (1 + (β - h)) := by
    linear_combination (1 - h + β) * F1 - ((1 + (β - h)) / 2) * hh
  have key : ((1 - h) + β) * L' - (1 - h) - γ = h := mul_right_cancel₀ h1α.ne' e1
  have hexp : (1 - L') * (1 - h) - L' * β ≤ -γ := by
    have : (1 - L') * (1 - h) - L' * β = -(h + γ) := by linear_combination (-1 : ℝ) * key
    linarith
  have hS : localizationIntermediateRadius δ (β - h) γ r = r ^ L' := rfl
  rw [hS, Real.div_rpow hr0.le (Real.rpow_nonneg hr0.le _), ← Real.rpow_mul hr0.le,
    ← Real.rpow_mul hr0.le]
  rw [show r ^ (1 - h) / r ^ (L' * (1 - h)) * r ^ (L' * -β) =
      r ^ ((1 - L') * (1 - h) - L' * β) by
    rw [div_eq_mul_inv, ← Real.rpow_neg hr0.le, ← Real.rpow_add hr0, ← Real.rpow_add hr0]
    congr 1
    ring]
  exact Real.rpow_le_rpow_of_exponent_le hr hexp

/-- **(5.85) from the observation estimate.** Given, for every window and every admissible
construction exponent `α`, structural constants with the observation estimate at the exponent
`d/2`, the frozen statement `QSH.Frozen.localizedEnergy` holds. -/
theorem localizedEnergy_of_observation
    (hObs : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∀ α : ℝ, 0 < α → α ≤ (d : ℝ) / 2 → γ < α * (1 + δ) + δ →
      ∃ σ θ C₀ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationObservationEstimate d Λ s δ γ α σ θ C₀ ((d : ℝ) / 2)) :
    QSH.Frozen.localizedEnergy := by
  refine localizedEnergy_of_slope firstOrderLiouville fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => ?_
  have hβ : 1 ≤ (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hγ2' : γ < (d : ℝ) / 2 * (1 + δ) + δ := lt_of_lt_of_le hγ2 (min_le_right _ _)
  obtain ⟨hh0, hh2, hα0, hαγ, hexp⟩ := localization_exponent_budget hβ hδ hγ1 hγ2'
  set h := localizationDecrement ((d : ℝ) / 2) δ γ
  have hαd : (d : ℝ) / 2 - h ≤ (d : ℝ) / 2 := by linarith
  obtain ⟨σ, θ, C₀, hσ, hσ2, hθ, hθ2, hC₀, hobs⟩ :=
    hObs d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 _ hα0 hαd hαγ
  have hs0 : 0 < s := by linarith
  have hγ0 : 0 < γ := lt_of_le_of_lt (mul_nonneg (by positivity) (by linarith)) hγ1
  have hγs : s * γ < d := by
    have h1 : γ < (d : ℝ) / s := lt_of_lt_of_le hγ2 (min_le_left _ _)
    rw [lt_div_iff₀ hs0] at h1
    linarith
  exact ⟨_, σ, θ, C₀, hα0, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀,
    localizationSlopeEstimate_of_excess_observation hΛ.le hs1.le hδ hα0 hαγ hγ0 hγs
      (by linarith : 0 < 1 - h) (by linarith : 1 - h < 1) hexp
      (ballExcessDecay hd hΛ) hobs⟩

end QSH
