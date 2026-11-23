import QuantitativeStochasticHomogenization.Ch04.Sec03.Lemma413
import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAverages

/-!
# The Gaussian average estimates with their numerical constant

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3. The expectations (1) of the Gaussian averages, the commutator estimate (4.34) and the
linear estimate of Step 1, each with its numerical constant exposed, so that the constants can be
chosen before the law: `ExpectedAveragesEstimate P S β ↔ ∃ C > 0, ExpectedAveragesEstimateAt P S β C`
and similarly for `CommutatorEstimate` and `LinearAverageEstimate`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The expectations (1) of the Gaussian averages with constant `C`**. -/
def ExpectedAveragesEstimateAt (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (β C : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
    Integrable (fun a => ∫ x, heatKernel z r x • correctedField S a ξ x) P ∧
    Integrable (fun a => ∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) P ∧
    Integrable (fun a => ∫ x, heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) P ∧
    euclideanNorm ((∫ a, (∫ x, heatKernel z r x • correctedField S a ξ x) ∂P) - ξ) ≤
      C * euclideanNorm ξ * r ^ (-β) ∧
    euclideanNorm ((∫ a, (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) ∂P) -
      S.homogenized.mulVec ξ) ≤ C * euclideanNorm ξ * r ^ (-β) ∧
    |(∫ a, (∫ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∂P) -
      dot ξ (S.homogenized.mulVec ξ)| ≤ C * euclideanSq ξ * r ^ (-β)

/-- **The commutator estimate (4.34) with constant `C`**. -/
def CommutatorEstimateAt (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (s α C : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
    OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
      S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) s (C * r ^ (-α))

/-- **The linear estimate of Step 1 with constant `C`**. -/
def LinearAverageEstimateAt (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (s α C : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
    OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ)) s
      (C * (1 + euclideanNorm ξ) * r ^ (-α))

variable {P : Measure (CoefficientField d Λ)} {S : HomogenizationData P}

theorem expectedAveragesEstimate_iff_exists_at (β : ℝ) :
    ExpectedAveragesEstimate P S β ↔ ∃ C > 0, ExpectedAveragesEstimateAt P S β C := Iff.rfl

theorem commutatorEstimate_iff_exists_at (s α : ℝ) :
    CommutatorEstimate P S s α ↔ ∃ C > 0, CommutatorEstimateAt P S s α C := Iff.rfl

theorem linearAverageEstimate_iff_exists_at (s α : ℝ) :
    LinearAverageEstimate P S s α ↔ ∃ C > 0, LinearAverageEstimateAt P S s α C := Iff.rfl

/-- The expectations (1) with constant `C` hold with every larger constant. -/
theorem ExpectedAveragesEstimateAt.mono_const {β C C' : ℝ} (h : ExpectedAveragesEstimateAt P S β C)
    (hCC : C ≤ C') : ExpectedAveragesEstimateAt P S β C' := by
  intro z r hr ξ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h z r hr ξ
  have hρ : 0 ≤ r ^ (-β) := Real.rpow_nonneg (zero_le_one.trans hr) _
  have hn := euclideanNorm_nonneg ξ
  have hs := euclideanSq_nonneg ξ
  refine ⟨h1, h2, h3, h4.trans ?_, h5.trans ?_, h6.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hn) hρ
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hn) hρ
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hs) hρ

/-- The expectations (1) at the rate `r^{-β}` give them at every smaller rate, with the same
constant. -/
theorem ExpectedAveragesEstimateAt.mono {β β' C : ℝ} (h : ExpectedAveragesEstimateAt P S β C)
    (hC : 0 ≤ C) (hβ : β' ≤ β) : ExpectedAveragesEstimateAt P S β' C := by
  intro z r hr ξ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h z r hr ξ
  have hρ : r ^ (-β) ≤ r ^ (-β') := Real.rpow_le_rpow_of_exponent_le hr (neg_le_neg hβ)
  have hn := euclideanNorm_nonneg ξ
  have hs := euclideanSq_nonneg ξ
  refine ⟨h1, h2, h3, h4.trans ?_, h5.trans ?_, h6.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left hρ (mul_nonneg hC hn)
  · exact mul_le_mul_of_nonneg_left hρ (mul_nonneg hC hn)
  · exact mul_le_mul_of_nonneg_left hρ (mul_nonneg hC hs)

end QSH
