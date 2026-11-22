import QuantitativeStochasticHomogenization.Ch05.Sec04.BlockEstimates
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationErrorDecay
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedEnergyJointMeasurability

/-!
# Boundedness and joint locality of the localized energy

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, (5.85)-(5.86): the block estimates of Section 5.4 use that the localized energy
`J₁^{(δ)}(·, ·, r, p, q)` of the construction of Section 4.4 is bounded and jointly measurable in
the coefficients and the center, with the coefficients restricted to the `r^{1+δ}`-neighbourhood
of the set of centers. Both properties hold for every localized family
(`localizedFieldInput`): the bound `M = (d²Λ + d)² / 2` is the variational bound of
`abs_familyJ1_le` on the unit balls, and the joint locality is
`measurable_indicator_familyJ1` with the open thickening `euclideanThickening (r^{1+δ}) U`.
Neither depends on the law.
-/

open MeasureTheory

namespace QSH

/-- **Boundedness and joint locality of the localized energy**: `LocalizedFieldInput` holds,
with `M = (d²Λ + d)² / 2`. -/
theorem localizedFieldInput : LocalizedFieldInput := by
  intro d hd Λ s δ γ η hΛ _ α σ θ C₀ C' hc
  obtain ⟨_, _, _, hσ, _, hθ, _, hC₀, _⟩ := hc
  have hΛ₀ : 0 ≤ Λ := by linarith
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let L : ℝ := (d : ℝ) * d * Λ + d
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L ^ 2 / 2, by positivity, ?_⟩
  intro P _ W _ r _ p q hp hq
  constructor
  · intro a z
    exact (abs_familyJ1_le hΛ₀ W a z r p q).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (linearCoefficient_nonneg hΛ₀ p q)
        (linearCoefficient_le hΛ₀ hp.le hq.le) 2) (by norm_num))
  · intro U hU
    exact measurable_indicator_familyJ1 hΛ₀ hσ hθ hC₀ W r p q hU
      (fun x hx y hy => ⟨x, hx, hy⟩)

end QSH
