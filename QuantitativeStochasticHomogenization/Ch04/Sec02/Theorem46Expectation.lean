import QuantitativeStochasticHomogenization.Ch04.Sec01.BaseExponent

/-!
# Theorem 4.6 (ii) and the estimate (5.58)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.2, Theorem 4.6 (ii), Remark 4.18, (4.70), and Section 5.3, (5.58).

Remark 4.18 records that the proof of Proposition 4.10 also bounds the expectation of `J₁`: under
`Fluc(s, α)`, `|E[J₁(Φ_{z,r}, p, q)] - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ C r^{-2α}` ((4.70)). With
`α = d/2` this is Theorem 4.6 (ii), and together with Theorem 4.6 (iii) it gives (5.58):
`J₁(Φ_{z,r}, p, q) = ½ p·āp + ½ q·ā⁻¹q - p·q + O_s(C r^{-d/2})` for every `s ∈ (0, 2)`.

Defined here: `ExpectationJ1Estimate P A α`, the bound `C r^{-α}` on the distance of the
expectation of `J₁` to the homogenized energy, and `ExpectationEstimates P A`, the statement (4.70)
of Remark 4.18 as an implication from `Fluc(s, α)`.

Proved here: `theorem46_expectation_and_558`: Theorem 4.6 (ii) and (5.58) for every `s ∈ (0, 2)`
from the conclusions of Propositions 4.10–4.12 (through `additiveStructure_J1`), (4.70), and an
initial exponent; `osBound_abs_J1Heat_sub_homogenizedJ1` is the step from (ii) and (iii) to
(5.58).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The expectation of `J₁(Φ_{z,r}, p, q)` is within `C r^{-α}` of the homogenized energy, for every
`z`, `r ≥ 1` and `p, q` in the open unit ball. -/
def ExpectationJ1Estimate (P : Measure (CoefficientField d Λ)) (A : Mat d) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    |(∫ a, J1Heat a z r p q ∂P) - homogenizedJ1 A p q| ≤ C * r ^ (-α)

/-- **(4.70), Remark 4.18**: for every `s ∈ (0, 2)` and `α ∈ (0, d/2]`, `Fluc(s, α)` implies the bound
`C r^{-2α}` on the distance of the expectation of `J₁` to the homogenized energy. -/
def ExpectationEstimates (P : Measure (CoefficientField d Λ)) (A : Mat d) : Prop :=
  ∀ s α : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 →
    FlucJ1 P s α → ExpectationJ1Estimate P A (2 * α)

/-- **From Theorem 4.6 (ii) and (iii) to (5.58)**: `Fluc(s, d/2)` and the bound `C r^{-d}` on the
expectation give `|J₁(Φ_{z,r}, p, q) - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ O_s(C r^{-d/2})`. -/
theorem osBound_abs_J1Heat_sub_homogenizedJ1 {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] {A : Mat d} {s : ℝ} (hF : FlucJ1 P s ((d : ℝ) / 2))
    (hE : ExpectationJ1Estimate P A d)
    (hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d),
      Measurable fun a : CoefficientField d Λ => J1Heat a z r p q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 A p q|) s (C * r ^ (-((d : ℝ) / 2))) := by
  obtain ⟨C₁, hC₁, hF⟩ := hF
  obtain ⟨C₂, hC₂, hE⟩ := hE
  set L : ℝ := Real.log 2 ^ s⁻¹ with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  refine ⟨2 * ((2 : ℝ) ^ s⁻¹ * max C₁ (C₂ / L)),
    mul_pos two_pos (mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hC₁)), ?_⟩
  intro z r hr p q hp hq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨hJint, hos⟩ := hF z r hr p q hp hq
  have hs : 0 < s := hos.exponent_pos
  have hρ : 0 < r ^ (-((d : ℝ) / 2)) := Real.rpow_pos_of_pos hr0 _
  have hbias : |(∫ a, J1Heat a z r p q ∂P) - homogenizedJ1 A p q| ≤
      C₂ * r ^ (-((d : ℝ) / 2)) := by
    refine (hE z r hr p q hp hq).trans (mul_le_mul_of_nonneg_left ?_ hC₂.le)
    refine rpow_neg_le_rpow_neg hr ?_
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hconst : OsBound P (fun _ => C₂ * r ^ (-((d : ℝ) / 2))) s
      (C₂ * r ^ (-((d : ℝ) / 2)) / L) :=
    osBound_of_le_const measurable_const hs (mul_pos hC₂ hρ)
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hmax := (osBound_max hos hconst).const_mul two_pos
  have hm : Measurable fun a : CoefficientField d Λ => |J1Heat a z r p q - homogenizedJ1 A p q| :=
    continuous_abs.measurable.comp ((hmeas z r p q).sub measurable_const)
  have hle : ∀ a : CoefficientField d Λ, |J1Heat a z r p q - homogenizedJ1 A p q| ≤
      2 * max |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P| (C₂ * r ^ (-((d : ℝ) / 2))) := by
    intro a
    have h1 := abs_sub_le (J1Heat a z r p q) (∫ a', J1Heat a' z r p q ∂P) (homogenizedJ1 A p q)
    have h2 := le_max_left |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|
      (C₂ * r ^ (-((d : ℝ) / 2)))
    have h3 := le_max_right |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|
      (C₂ * r ^ (-((d : ℝ) / 2)))
    linarith
  refine (hmax.of_le hm hle).mono_scale (le_of_eq ?_)
  rw [show C₂ * r ^ (-((d : ℝ) / 2)) / L = C₂ / L * r ^ (-((d : ℝ) / 2)) by ring,
    ← max_mul_of_nonneg _ _ hρ.le]
  ring

/-- **Theorem 4.6 (ii) and (5.58)** for `J₁`: if the conclusions of Propositions 4.10, 4.11 and
4.12 hold, together with (4.70) and an initial exponent `Fluc(s, α₀)` for each `s ∈ (1, 2)`
(Proposition 4.3), and `a ↦ J₁(Φ_{z,r}, p, q)` is measurable, then for every `s ∈ (0, 2)`:
`|E[J₁(Φ_{z,r}, p, q)] - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ C r^{-d}` (Theorem 4.6 (ii)) and
`J₁(Φ_{z,r}, p, q) = ½ p·āp + ½ q·ā⁻¹q - p·q + O_s(C r^{-d/2})` ((5.58)). -/
theorem theorem46_expectation_and_558 {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] {A : Mat d} (hd : 1 ≤ d) (h410 : ImprovementOfAdditivity P J1Heat)
    (hbias : ExpectationEstimates P A) (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat)
    (hbase : ∀ s : ℝ, 1 < s → s < 2 → ∃ α₀ : ℝ, 0 < α₀ ∧ FlucJ1 P s α₀)
    (hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d),
      Measurable fun a : CoefficientField d Λ => J1Heat a z r p q)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P A d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 A p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hF := (additiveStructure_J1 hd h410 h411 h412 hbase hs0 hs2).1
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hE : ExpectationJ1Estimate P A d := by
    have := hbias s ((d : ℝ) / 2) hs0 hs2 hd2 le_rfl hF
    rwa [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at this
  exact ⟨hE, osBound_abs_J1Heat_sub_homogenizedJ1 hF hE hmeas⟩

/-- **(5.58) for a homogenization datum**: Theorem 4.6 (ii) and (5.58) with `ā` the matrix of `S`,
from the conclusions of Propositions 4.10 (with (4.70)), 4.11 and 4.12, the inputs of
Proposition 4.3 (the structure (4.12) of `A₁`, the bounds on `ā` and Proposition 3.21 at every
exponent `s ∈ (1, 2)`), and the measurability of `J₁`. -/
theorem estimate558 {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (S : HomogenizationData P) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ s : ℝ, 1 < s → s < 2 → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ GaussianCorrectorRate P S s C μ)
    (hmeas : ∀ (z : Vec d) (r : ℝ) (p q : Vec d),
      Measurable fun a : CoefficientField d Λ => J1Heat a z r p q)
    (h410 : ImprovementOfAdditivity P J1Heat) (hbias : ExpectationEstimates P S.homogenized)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) :=
  theorem46_expectation_and_558 hd h410 hbias h411 h412 (flucJ1_base S hA hspan hrate hmeas)
    hmeas hs0 hs2

end QSH
