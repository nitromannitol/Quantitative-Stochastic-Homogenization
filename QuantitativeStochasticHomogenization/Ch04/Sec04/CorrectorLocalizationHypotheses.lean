import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeMatchedColumns
import QuantitativeStochasticHomogenization.Ch04.Sec04.CorrectedCoordinate

/-!
# The almost sure hypotheses of Lemma 4.22 from first-order correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemmas 4.21 and 4.22. At a fixed coefficient field, let `φ_i` be whole-space solutions of
`-∇·a(e_i + ∇φ_i) = 0` with locally square integrable potentials and gradients `g_i` (the
correctors of `QSH.Corrector` at `a`). The corrected coordinates `(x - z)_i + φ_i` have weak
gradients `W_i = e_i + g_i`. The almost sure hypotheses of Lemma 4.22 at `(z, r)` with
`T ≥ r` then follow from: the sublinearity of the `φ_i` on `B_r(z)`, a bound on the Gaussian
energies of the `W_i` at scale `√2 r`, the first-order Liouville representation of `A₁` by the
`W_i`, and the closeness in `L²(Φ_{z,r}, B_T(z))` of the gradient of each localized coordinate to
a corrected gradient `W_i + ∑_j b_{ij} W_j` with small slopes (the content of Lemma 4.21).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {z : Vec d} {T r : ℝ}

/-- **The almost sure hypotheses of Lemma 4.22 from first-order correctors.** -/
theorem LocalizationApproximationAtUniform.of_correctors {Λ : ℝ} {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hd : 0 < d) (hr : 0 < r) (hrT : r ≤ T) {S σ θ C : ℝ}
    {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} {η κ Zv E ε ρ : ℝ}
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (φ : Fin d → Vec d → ℝ) (g : Fin d → Vec d → Vec d)
    (hφg : ∀ i, HasWeakGradient Set.univ (φ i) (g i))
    (hloc : ∀ i, ∀ R : ℝ, 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (g i) 2 (volume.restrict (ball 0 R)))
    (harm : ∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g i x))
      (fun _ => 0))
    (c : Fin d → ℝ)
    (hosc : ∀ i, ∫ x in ball z r, (φ i x - c i) ^ 2 ≤ ε ^ 2 * r ^ 2 * volume.real (ball z r))
    (hε : (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x *
      euclideanSq (unitVector i + g i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (unitVector i + g i x) ≤ E)
    (hκ : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
      (d * E / heatGramConstant d) ≤ κ)
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x))
    (hWmem : ∀ ξ : Vec d, ∃ w : HarmonicA1 a,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x))
    (b : Fin d → Fin d → ℝ) (hb : ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4) (hρ0 : 0 ≤ ρ)
    (hclose : ∀ i, ∫ x in ball z T, heatKernel z r x *
      euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤ ρ ^ 2)
    (hρ : ρ ≤ Real.sqrt (heatGramConstant d / 4) / d / 2)
    (hη : 2 * (2 * linearCoefficient d Λ p q + 1) * ρ /
      (Real.sqrt (heatGramConstant d / 4) / d) ≤ η)
    (hZ : (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
          (κ * (d * (2 * linearCoefficient d Λ p q + 1) ^ 2)) +
        linearCoefficient d Λ p q / 2 *
          ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)))) +
      ((d : ℝ) ^ 2 * Λ * (2 * (2 * linearCoefficient d Λ p q + 1) + η) / 2 +
        linearCoefficient d Λ p q) * η ≤ Zv) :
    LocalizationApproximationAtUniform a z T r hr.ne' B p q η κ Zv := by
  let uR := fun i => localCorrectedCoordinate a z r i 0 (φ i) (g i) (hφg i) (hloc i) (harm i)
  let uT := fun i => localCorrectedCoordinate a z T i 0 (φ i) (g i) (hφg i) (hloc i) (harm i)
  refine LocalizationApproximationAtUniform.of_slopes hΛ hd hr hrT hsmall
    (fun i => (uR i).potential) (fun i x => unitVector i + g i x)
    (fun i => (uR i).square_integrable) (fun i j => (uT i).memLp_grad j)
    (fun i => (uR i).weak_gradient) c (fun i => ?_) hε hE0 hW hE hκ hrep hWmem b hb hρ0
    hclose hρ hη hZ
  refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_))) (hosc i)
  show ((x - z) i + φ i x - 0 - (x - z) i - c i) ^ 2 = (φ i x - c i) ^ 2
  ring

/-- The bound of Lemma 4.22 in terms of the approximation error `η` and the outer energy ratio
`κ`, with the uniform linear coefficient `L = linearCoefficient d Λ p q`. -/
def localizationErrorBound (d : ℕ) (Λ : ℝ) (p q : Vec d) (η κ T r : ℝ) : ℝ :=
  (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
        (κ * (d * (2 * linearCoefficient d Λ p q + 1) ^ 2)) +
      linearCoefficient d Λ p q / 2 *
        ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)))) +
    ((d : ℝ) ^ 2 * Λ * (2 * (2 * linearCoefficient d Λ p q + 1) + η) / 2 +
      linearCoefficient d Λ p q) * η

/-- **Lemma 4.22 from its almost sure hypotheses with uniform constants.** -/
theorem LocalizationApproximationAtUniform.abs_sub_le {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {a : CoefficientField d Λ} {hr : r ≠ 0} {S σ θ C : ℝ} {B : LocalizedBasis a z T S σ θ C}
    {p q : Vec d} {η κ Z : ℝ} (h : LocalizationApproximationAtUniform a z T r hr B p q η κ Z) :
    |J1Heat a z r p q - localizedJ1 B r p q| ≤ Z :=
  abs_J1Heat_sub_localizedJ1_le_of_approximationAt hΛ hr (h.toAt' hΛ).toAt

/-- **Lemmas 4.21-4.22 at a coefficient field from first-order correctors, with the explicit
bound**: under the hypotheses of `LocalizationApproximationAtUniform.of_correctors`, the
localization error is at most `localizationErrorBound` evaluated at
`η = 2 (2L + 1) ρ d / √(m/4)` and `κ = 2^{d/2} exp(-T²/(8r²)) d E / m`,
`m = heatGramConstant d`. -/
theorem abs_J1Heat_sub_localizedJ1_le_of_correctors {Λ : ℝ} {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hd : 0 < d) (hr : 0 < r) (hrT : r ≤ T) {S σ θ C : ℝ}
    {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} {E ε ρ : ℝ}
    (hsmall : linearCoefficient d Λ p q ^ 2 / 2 *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4)
    (φ : Fin d → Vec d → ℝ) (g : Fin d → Vec d → Vec d)
    (hφg : ∀ i, HasWeakGradient Set.univ (φ i) (g i))
    (hloc : ∀ i, ∀ R : ℝ, 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (g i) 2 (volume.restrict (ball 0 R)))
    (harm : ∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g i x))
      (fun _ => 0))
    (c : Fin d → ℝ)
    (hosc : ∀ i, ∫ x in ball z r, (φ i x - c i) ^ 2 ≤ ε ^ 2 * r ^ 2 * volume.real (ball z r))
    (hε : (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16) (hE0 : 0 ≤ E)
    (hW : ∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x *
      euclideanSq (unitVector i + g i x)))
    (hE : ∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (unitVector i + g i x) ≤ E)
    (hrep : ∀ w : HarmonicA1 a, ∃ ξ : Vec d,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x))
    (hWmem : ∀ ξ : Vec d, ∃ w : HarmonicA1 a,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x))
    (b : Fin d → Fin d → ℝ) (hb : ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4) (hρ0 : 0 ≤ ρ)
    (hclose : ∀ i, ∫ x in ball z T, heatKernel z r x *
      euclideanSq ((B.coordinate i).grad x -
        ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤ ρ ^ 2)
    (hρ : ρ ≤ Real.sqrt (heatGramConstant d / 4) / d / 2) :
    |J1Heat a z r p q - localizedJ1 B r p q| ≤
      localizationErrorBound d Λ p q
        (2 * (2 * linearCoefficient d Λ p q + 1) * ρ / (Real.sqrt (heatGramConstant d / 4) / d))
        ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)) *
          (d * E / heatGramConstant d)) T r :=
  (LocalizationApproximationAtUniform.of_correctors hΛ hd hr hrT hsmall φ g hφg hloc harm c
    hosc hε hE0 hW hE le_rfl hrep hWmem b hb hρ0 hclose hρ le_rfl le_rfl).abs_sub_le hΛ

end QSH
