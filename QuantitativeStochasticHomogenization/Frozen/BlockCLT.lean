import QuantitativeStochasticHomogenization.Ch05.Sec04CentralLimitTheoremForJ1

/-!
# Frozen statement: Lemma 5.29 (i), (5.90)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 5.29 (i), (5.90), in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM Lemma 5.29 (i), (5.90)**, for the localized energy of any family satisfying (5.85) with
admissible structural constants, with the exponents (5.82)-(5.83) and at scales `R^η ≤ r ≤ R`
with `r ≥ 2`: for measurable `f` with `|f| ≤ 1` the block is `O_s(C R^{-d/2})`. -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.blockCLT : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ η : ℝ, 1 < Λ → BlockWindow d s δ γ η →
    ∀ α σ θ C₀ C' : ℝ, LocalizationConstants d δ γ α σ θ C₀ C' →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C' W →
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ η ≤ r → r ≤ R →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      OsBound P (fun a => |centeredBlock P (familyJ1 W) a z R r f p q|) s (C * R ^ (-(d : ℝ) / 2))
-- FROZEN-STATEMENT-END
