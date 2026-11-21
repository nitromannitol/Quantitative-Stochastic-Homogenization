import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationEstimateReduction
import QuantitativeStochasticHomogenization.Ch04.Sec04.HeatKernelMass

/-!
# The reduction of (5.85) with the Gaussian mass computed

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 4.11 from Lemmas 4.21 and 4.22. The Gaussian mass hypotheses of
`LocalizationApproximationAt` are discharged by `setIntegral_compl_ball_heatKernel_le` with
`ε₀ = 2^{d/2} exp(-T²/(8r²))`; what remains, almost surely, is the integrability of the Gaussian
energies of `A₁`, the relative outer energy `κ` of `A₁`, the approximation error `η` of Lemma 4.21
and the smallness of the Gaussian mass outside `B_T(z)` compared with the linear coefficient.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The almost sure hypotheses of Lemma 4.22 at a coefficient field, the Gaussian mass being
computed. -/
def LocalizationApproximationAt' (a : CoefficientField d Λ) (z : Vec d) (T r : ℝ) (hr : r ≠ 0)
    {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C) (p q : Vec d) (η κ Z : ℝ) : Prop :=
  0 ≤ T ∧ 0 ≤ η ∧ 0 ≤ κ ∧
  linearCoefficient d Λ p q ^ 2 / 2 *
    ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) ≤ 1 / 4 ∧
  (∀ w : HarmonicA1 a, Integrable (fun x => heatKernel z r x *
    (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))) ∧
  (∀ w : HarmonicA1 a,
    IntegrableOn (fun x => heatKernel z r x * euclideanSq (w.grad x)) (ball z T)ᶜ volume) ∧
  (∀ w : HarmonicA1 a,
    ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x) ≤
      κ * ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x)) ∧
  (∀ w : HarmonicA1 a,
    ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
      2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
    ∃ c : Vec d, ‖(fun k => scaleLp hr (w.ballGrad z T k)) -
      (fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k))‖ ≤ η) ∧
  (∀ c : Vec d,
    ‖(fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k))‖ ≤
      2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
    ∃ w : HarmonicA1 a,
      ‖(fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k)) -
        (fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ η) ∧
  (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
        (κ * (d * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) ^ 2)) +
      linearCoefficient d Λ p q / 2 *
        ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2)))) +
    ((d : ℝ) ^ 2 * Λ * (2 * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) +
      η) / 2 + tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖) * η ≤ Z

theorem LocalizationApproximationAt'.toAt {a : CoefficientField d Λ} {z : Vec d} {T r : ℝ}
    {hr : r ≠ 0} {S σ θ C : ℝ} {W : LocalizedBasis a z T S σ θ C} {p q : Vec d} {η κ Z : ℝ}
    (h : LocalizationApproximationAt' a z T r hr W p q η κ Z) :
    LocalizationApproximationAt a z T r hr W p q η
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(T ^ 2) / (8 * r ^ 2))) κ Z := by
  obtain ⟨hT, hη, hκ, hsmall, hint, hint2, houter, hAV, hVA, hZ⟩ := h
  exact ⟨hη, hκ, (integrable_heatKernel z hr).integrableOn,
    setIntegral_compl_ball_heatKernel_le z hr T hT, hsmall, hint, hint2, houter, hAV, hVA, hZ⟩

/-- **The stochastic form of Lemmas 4.21-4.22 with the Gaussian mass computed.** -/
def LocalizationApproximation' (d : ℕ) (Λ s δ γ α σ θ C₀ C : ℝ) : Prop :=
  ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∃ Z : CoefficientField d Λ → ℝ,
        AEOsBound P Z s (C * r ^ (-γ)) ∧
        ∀ᵐ a ∂P, (∃ η κ : ℝ, LocalizationApproximationAt' a z (localizationOuterRadius δ r) r
            (by linarith : r ≠ 0) (W a z r hr) p q η κ (Z a)) ∨
          |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q| ≤ Z a

theorem LocalizationApproximation'.toApproximation {s δ γ α σ θ C₀ C : ℝ}
    (h : LocalizationApproximation' d Λ s δ γ α σ θ C₀ C) :
    LocalizationApproximation d Λ s δ γ α σ θ C₀ C := by
  intro P hP W z r hr p q hp hq
  obtain ⟨Z, hZ, hae⟩ := h P hP W z r hr p q hp hq
  refine ⟨Z, hZ, ?_⟩
  filter_upwards [hae] with a ha
  rcases ha with ⟨η, κ, ha⟩ | ha
  · exact Or.inl ⟨η, _, κ, ha.toAt⟩
  · exact Or.inr ha

/-- **(5.85) from the stochastic form of Lemmas 4.21-4.22**, the Gaussian mass computed. -/
theorem localizedEnergy_of_approximation'
    (hJ1 : ∀ (d : ℕ) (Λ : ℝ) (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ (z : Vec d) (r : ℝ) (p q : Vec d), 2 ≤ r → AEMeasurable (fun a => J1Heat a z r p q) P)
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ C : ℝ, LocalizationConstants d δ γ α σ θ C₀ C ∧
        LocalizationApproximation' d Λ s δ γ α σ θ C₀ C) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_approximation hJ1 fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => by
    obtain ⟨α, σ, θ, C₀, C, hconst, happ⟩ := h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
    exact ⟨α, σ, θ, C₀, C, hconst, happ.toApproximation⟩

end QSH
