import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedFamilyMeasurability
import QuantitativeStochasticHomogenization.Frozen.LocalizedEnergy

/-!
# Reduction of (5.85) to the localization estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(5.85), Theorem 4.6 (iv) with Proposition 4.11. The localized families of Section 4.4 exist and
have the measurability property of (5.85) for all positive smoothing constants
(`exists_localizedFamily_measurable`). Hence (5.85) follows from the stochastic estimate
`|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)| ≤ O_s(C r^{-γ})` for the localized families, which is
the content of Proposition 4.11 at `α = d/2` (Lemmas 4.21 and 4.22), using `Fluc(s, d/2)` of
Theorem 4.6.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- The stochastic estimate of (5.85) for every localized family with the given constants. -/
def LocalizationEstimate (d : ℕ) (Λ s δ γ α σ θ C₀ C : ℝ) : Prop :=
  ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      AEOsBound P (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) s
        (C * r ^ (-γ))

/-- **(5.85) from the localization estimate.** -/
theorem localizedEnergy_of_localizationEstimate
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ C : ℝ, LocalizationConstants d δ γ α σ θ C₀ C ∧
        LocalizationEstimate d Λ s δ γ α σ θ C₀ C) :
    QSH.Frozen.localizedEnergy := by
  intro d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
  obtain ⟨α, σ, θ, C₀, C, hconst, hest⟩ := h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
  refine ⟨α, σ, θ, C₀, C, hconst, fun P hP => ?_⟩
  obtain ⟨-, -, -, hσ, -, hθ, -, hC₀, -⟩ := hconst
  obtain ⟨W, hW⟩ := exists_localizedFamily_measurable d (by linarith : (0 : ℝ) ≤ Λ) δ γ α hσ hθ hC₀
  exact ⟨W, fun z r hr p q hp hq => ⟨hW z r hr p q, hest P hP W z r hr p q hp hq⟩⟩

end QSH
