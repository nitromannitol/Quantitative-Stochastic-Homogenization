import QuantitativeStochasticHomogenization.Ch04.Sec04.AdmissibleDenseSequence
import QuantitativeStochasticHomogenization.Ch05.Sec04CentralLimitTheoremForJ1

/-!
# Localized families and the measurability clause of (5.85)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, pp. 155-156, and (5.85). For positive smoothing constants `σ, θ` and gradient bound
`C₀`, localized families exist, and for every localized family the localized energy
`J₁^{(δ)}(z, r, p, q)` is `F(B_{r^{1+δ}}(z))`-measurable for all `z`, `r ≥ 2`, `p`, `q`. This is
the first of the two properties of a localization in (5.85).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **The measurability clause of (5.85)** holds for every localized family. -/
theorem measurable_localizedJ1_of_localizedFamily {d : ℕ} {Λ δ γ α σ θ C₀ : ℝ} (hΛ : 0 ≤ Λ)
    (hσ : 0 < σ) (hθ : 0 < θ) (hC₀ : 0 < C₀) (W : LocalizedFamily d Λ δ γ α σ θ C₀)
    (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma (ball z (localizationOuterRadius δ r)))
      inferInstance (fun a => localizedJ1 (W a z r hr) r p q) := by
  have hr0 : 0 < r := by linarith
  exact measurable_localizedJ1_of_basis hΛ (Real.rpow_pos_of_pos hr0 _)
    (mul_pos hσ (Real.rpow_pos_of_pos hr0 _)).ne'
    (div_pos (Real.rpow_pos_of_pos hr0 _) hθ) hC₀ hr0.ne' p q (fun a => W a z r hr)

/-- **Localized families with the measurability clause of (5.85)** exist for all positive
smoothing constants. -/
theorem exists_localizedFamily_measurable (d : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (δ γ α : ℝ) {σ θ C₀ : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (hC₀ : 0 < C₀) :
    ∃ W : LocalizedFamily d Λ δ γ α σ θ C₀, ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
      @Measurable (CoefficientField d Λ) ℝ (localSigma (ball z (localizationOuterRadius δ r)))
        inferInstance (fun a => localizedJ1 (W a z r hr) r p q) := by
  obtain ⟨W⟩ := nonempty_localizedFamily d Λ δ γ α hσ hθ hC₀.le
  exact ⟨W, measurable_localizedJ1_of_localizedFamily hΛ hσ hθ hC₀ W⟩

end QSH
