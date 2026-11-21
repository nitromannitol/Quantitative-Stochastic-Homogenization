import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationPerturbation
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedEnergyReduction

/-!
# The localization estimate from the approximation of `A₁`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 4.11 from Lemmas 4.21 and 4.22. The stochastic estimate of (5.85) for a localized
family follows from Lemma 4.22 (`abs_J1Heat_sub_localizedJ1_le_of_tail`) as soon as, almost surely,
the hypotheses of Lemma 4.22 hold with random errors `η`, `ε₀`, `κ` (the approximation error of
Lemma 4.21, the Gaussian mass outside the ball and the relative outer energy of `A₁`) whose
resulting bound is dominated by a random variable `Z ≤ O_s(C r^{-γ})`, and `J₁(Φ_{z,r}, p, q)` is
almost surely measurable.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `O_s` bounds are monotone for almost surely measurable variables. -/
theorem AEOsBound.of_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {s θ : ℝ} (hX : AEMeasurable X P) (hY : AEOsBound P Y s θ) (hle : ∀ᵐ ω ∂P, X ω ≤ Y ω) :
    AEOsBound P X s θ := by
  obtain ⟨-, hs, hθ, hint⟩ := hY
  refine ⟨hX, hs, hθ, le_trans (lintegral_mono_ae ?_) hint⟩
  filter_upwards [hle] with ω hω
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h0 : 0 ≤ θ⁻¹ * max (X ω) 0 := mul_nonneg (inv_nonneg.2 hθ.le) (le_max_right _ _)
  exact Real.rpow_le_rpow h0 (mul_le_mul_of_nonneg_left (max_le_max hω le_rfl)
    (inv_nonneg.2 hθ.le)) hs.le

/-- The local σ-algebras are coarser than the σ-algebra of the coefficient fields. -/
theorem localSigma_le_measurableSpace (U : Set (Vec d)) :
    localSigma (Λ := Λ) U ≤ (inferInstance : MeasurableSpace (CoefficientField d Λ)) :=
  iSup_le fun u => iSup_le fun i => iSup_le fun j =>
    le_iSup_of_le u.1 (le_iSup_of_le i (le_iSup_of_le j le_rfl))

/-- The almost sure hypotheses of Lemma 4.22 at a coefficient field, with the bound `Z`. -/
def LocalizationApproximationAt (a : CoefficientField d Λ) (z : Vec d) (T r : ℝ) (hr : r ≠ 0)
    {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C) (p q : Vec d) (η ε₀ κ Z : ℝ) : Prop :=
  0 ≤ η ∧ 0 ≤ κ ∧
  IntegrableOn (heatKernel z r) (ball z T)ᶜ volume ∧
  (∫ x in (ball z T)ᶜ, heatKernel z r x) ≤ ε₀ ∧
  linearCoefficient d Λ p q ^ 2 / 2 * ε₀ ≤ 1 / 4 ∧
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
      linearCoefficient d Λ p q / 2 * ε₀) +
    ((d : ℝ) ^ 2 * Λ * (2 * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) +
      η) / 2 + tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖) * η ≤ Z

theorem abs_J1Heat_sub_localizedJ1_le_of_approximationAt {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) {z : Vec d} {T r : ℝ} (hr : r ≠ 0) {S σ θ C : ℝ}
    {W : LocalizedBasis a z T S σ θ C} {p q : Vec d} {η ε₀ κ Z : ℝ}
    (h : LocalizationApproximationAt a z T r hr W p q η ε₀ κ Z) :
    |J1Heat a z r p q - localizedJ1 W r p q| ≤ Z := by
  obtain ⟨hη, hκ, hΦ, hmass, hε₀, hint, hint2, houter, hAV, hVA, hZ⟩ := h
  exact (abs_J1Heat_sub_localizedJ1_le_of_tail hΛ hr W p q hη hκ hΦ hmass hε₀ hint hint2
    houter hAV hVA).trans hZ

/-- **The stochastic form of Lemmas 4.21-4.22**: there is `Z ≤ O_s(C r^{-γ})` such that almost
surely either the hypotheses of Lemma 4.22 hold with errors whose bound is at most `Z`, or the
localization error is directly at most `Z` (the exceptional event of the book, where both energies
are bounded). -/
def LocalizationApproximation (d : ℕ) (Λ s δ γ α σ θ C₀ C : ℝ) : Prop :=
  ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∃ Z : CoefficientField d Λ → ℝ,
        AEOsBound P Z s (C * r ^ (-γ)) ∧
        ∀ᵐ a ∂P, (∃ η ε₀ κ : ℝ, LocalizationApproximationAt a z (localizationOuterRadius δ r) r
            (by linarith : r ≠ 0) (W a z r hr) p q η ε₀ κ (Z a)) ∨
          |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q| ≤ Z a

/-- **The localization estimate of (5.85) from the stochastic form of Lemmas 4.21-4.22.** -/
theorem localizationEstimate_of_approximation {s δ γ α σ θ C₀ C : ℝ} (hΛ : 0 ≤ Λ)
    (hσ : 0 < σ) (hθ : 0 < θ) (hC₀ : 0 < C₀)
    (hJ1 : ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (z : Vec d) (r : ℝ) (p q : Vec d), 2 ≤ r → AEMeasurable (fun a => J1Heat a z r p q) P)
    (h : LocalizationApproximation d Λ s δ γ α σ θ C₀ C) :
    LocalizationEstimate d Λ s δ γ α σ θ C₀ C := by
  intro P hP W z r hr p q hp hq
  obtain ⟨Z, hZ, hae⟩ := h P hP W z r hr p q hp hq
  have hmeas : AEMeasurable (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) P := by
    have h1 := hJ1 P hP z r p q hr
    have h2 : Measurable fun a => localizedJ1 (W a z r hr) r p q :=
      (measurable_localizedJ1_of_localizedFamily hΛ hσ hθ hC₀ W z r hr p q).mono
        (localSigma_le_measurableSpace _) le_rfl
    exact (h1.sub h2.aemeasurable).abs
  refine AEOsBound.of_le hmeas hZ ?_
  filter_upwards [hae] with a ha
  rcases ha with ⟨η, ε₀, κ, ha⟩ | ha
  · exact abs_J1Heat_sub_localizedJ1_le_of_approximationAt hΛ _ ha
  · exact ha

/-- **(5.85) from the stochastic form of Lemmas 4.21-4.22** and the almost sure measurability of
`J₁(Φ_{z,r}, p, q)`. -/
theorem localizedEnergy_of_approximation
    (hJ1 : ∀ (d : ℕ) (Λ : ℝ) (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ (z : Vec d) (r : ℝ) (p q : Vec d), 2 ≤ r → AEMeasurable (fun a => J1Heat a z r p q) P)
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ C : ℝ, LocalizationConstants d δ γ α σ θ C₀ C ∧
        LocalizationApproximation d Λ s δ γ α σ θ C₀ C) :
    QSH.Frozen.localizedEnergy := by
  refine localizedEnergy_of_localizationEstimate fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => ?_
  obtain ⟨α, σ, θ, C₀, C, hconst, happ⟩ := h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
  have hσ := hconst.2.2.2.1
  have hθ := hconst.2.2.2.2.2.1
  have hC₀ := hconst.2.2.2.2.2.2.2.1
  exact ⟨α, σ, θ, C₀, C, hconst, localizationEstimate_of_approximation (by linarith) hσ hθ hC₀
    (hJ1 d Λ) happ⟩

end QSH
