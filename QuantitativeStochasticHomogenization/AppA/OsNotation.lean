import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Appendix A: The O_s Notation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix A. Numbered results of this appendix: Lemmas A.1, A.3–A.5, A.7–A.12.

Defined here: `X ≤ O_s(θ)`, (A.1), and its form for almost surely measurable random variables.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **`X ≤ O_s(θ)`**, (A.1): `E[exp((θ⁻¹ X₊)^s)] ≤ 2`. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

/-- **`X ≤ O_s(θ)` for an almost surely measurable `X`**: (A.1) for a random variable that is
measurable for the completion of `P`. This is the convention of Remark 5.17 for random variables
whose measurability the book does not discuss: the exceptional sets lie in measurable null sets,
equivalently the σ-algebra is enlarged to contain them. -/
def AEOsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  AEMeasurable X P ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

end QSH
