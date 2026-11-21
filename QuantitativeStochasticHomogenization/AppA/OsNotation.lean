import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Appendix A: The O_s Notation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix A. Numbered results of this appendix: Lemmas A.1, A.3–A.5, A.7–A.12.

Defined here: `X ≤ O_s(θ)`, (A.1).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **`X ≤ O_s(θ)`**, (A.1): `E[exp((θ⁻¹ X₊)^s)] ≤ 2`. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

end QSH
