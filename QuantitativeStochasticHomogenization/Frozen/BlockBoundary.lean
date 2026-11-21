import QuantitativeStochasticHomogenization.Ch05.Sec04CentralLimitTheoremForJ1

/-!
# Frozen statement: Lemma 5.29 (ii), (5.91)-(5.92)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 5.29 (ii), (5.91)-(5.92), in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM Lemma 5.29 (ii), (5.91)-(5.92)**, for the localized energy of any family satisfying
(5.85) with admissible structural constants, with the exponents (5.82)-(5.83) and at scales
`r ≥ 2`: for `β ∈ [0, 1]`, `R^{βη} ≤ r ≤ R^{β/(1+δ)}` and `f` with `|f| ≤ 1` supported in the frame
`□_R(z) \ □_{R-R^β}(z)`, the block is `O_s(C R^{-d/2-(1-β)/2})`. -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.blockBoundary : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ η : ℝ, 1 < Λ → BlockWindow d s δ γ η →
    ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    ∀ α σ θ C₀ C' : ℝ, LocalizationConstants d δ γ α σ θ C₀ C' →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C' W →
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ (β * η) ≤ r → r ≤ R ^ (β / (1 + δ)) →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
        Function.support f ⊆ cube z R \ cube z (R - R ^ β) →
      OsBound P (fun a => |centeredBlock P (familyJ1 W) a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2 - (1 - β) / 2))
-- FROZEN-STATEMENT-END
