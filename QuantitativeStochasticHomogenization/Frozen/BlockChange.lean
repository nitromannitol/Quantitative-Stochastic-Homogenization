import QuantitativeStochasticHomogenization.Ch05.Sec04CentralLimitTheoremForJ1

/-!
# Frozen statement: Lemma 5.29 (iii)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 5.29 (iii), in the form used by the formalization of the Einstein relation.
-/

open MeasureTheory QSH
open scoped ENNReal

/-- **AKM Lemma 5.29 (iii)** (einstein input E3): the positive gain `ε` precedes `Λ`. -/
-- FROZEN-STATEMENT-BEGIN
def QSH.Frozen.blockChange : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ s δ γ η : ℝ, BlockWindow d s δ γ η →
    ∀ β : ℝ, η ≤ β → β < 1 →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ Λ : ℝ, 1 < Λ →
    ∀ α σ θ C₀ C' : ℝ, LocalizationConstants d δ γ α σ θ C₀ C' →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, IsLocalization P s δ γ α σ θ C₀ C' W →
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ R ^ η → R ^ η ≤ r → r ≤ R ^ β →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      OsBound P (fun a => |centeredBlock P (familyJ1 W) a z R r (fun _ => 1) p q -
          centeredBlock P (familyJ1 W) a z R (R ^ η) (fun _ => 1) p q|)
        s (C * R ^ (-(d : ℝ) / 2 - ε))
-- FROZEN-STATEMENT-END
