import QuantitativeStochasticHomogenization.Ch05.Sec04CentralLimitTheoremForJ1

/-!
# Frozen statement: (5.85), Theorem 4.6 (iv), Section 4.4

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(5.85), Theorem 4.6 (iv), Section 4.4, in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM (5.85)** (Theorem 4.6 (iv) with the localization of Section 4.4):
for `s ∈ (1, 2)`, `δ > 0` and `d/2 (1+δ) < γ < d/s ∧ (d/2 (1+δ) + δ)` there are structural
constants, chosen before the law, and for every law a family of selected least-norm coordinate
minimizers whose energies `J₁^{(δ)}(z, r, p, q)`, `r ≥ 2`, are `F(B_{r^{1+δ}}(z))`-measurable and
within `O_s(C r^{-γ})` of `J₁(Φ_{z,r}, p, q)`, the difference being almost surely measurable. -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.localizedEnergy : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
    1 < Λ → 1 < s → s < 2 → 0 < δ →
    (d : ℝ) / 2 * (1 + δ) < γ →
    γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
    ∃ α σ θ C₀ C : ℝ, LocalizationConstants d δ γ α σ θ C₀ C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C W
-- FROZEN-STATEMENT-END
