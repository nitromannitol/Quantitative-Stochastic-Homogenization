import QuantitativeStochasticHomogenization.Ch04.Sec04.InnerSlopeLocalization
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatGram
import QuantitativeStochasticHomogenization.Ch03.Sec03.DimensionA1

/-!
# Lemma 4.21 with the correctors of the homogenization data

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21. In `LocalizationInnerSlopeData` take for `φ_i` the corrector of slope `e_i` of a
homogenization data `S`, so that `W_i = e_i + ∇φ_{e_i}` is `correctorColumn S a i`. Almost
surely the correctors are whole-space solutions with locally square integrable potentials and
gradients, the Gaussian energies of the `W_i` are finite, and, under the first-order Liouville
theorem, the gradients of `A₁` are exactly the combinations `∑ ξ_i W_i`. What remains of the
pathwise hypotheses is quantitative: the oscillation of the correctors on `B_r(z)`, the Gaussian
energies of the `W_i` at scale `√2 r`, their energies on `B_T(z)`, and the single-slope estimate
of the selected coordinates below `S₁`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The quantitative pathwise hypotheses of Lemma 4.21 for the correctors of `S`: small
oscillation of `φ_{e_i}` on `B_r(z)`, Gaussian energies of `W_i = correctorColumn S a i` at scale
`√2 r` at most `E`, energies on `B_T(z)` at most `E₁ |B_T(z)|`, and slopes `b` with
`∑ b_{ij}² ≤ 1/4` such that `∫_{B_t(z)} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ K (t/r)² |B_t|` for
`r ≤ t ≤ S₁`. -/
def LocalizationCorrectorSlopeData {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (z : Vec d) (T S₁ r : ℝ)
    {S' σ θ C : ℝ} (B : LocalizedBasis a z T S' σ θ C) (E E₁ K : ℝ) : Prop :=
  (∃ (c : Fin d → ℝ) (ε : ℝ), (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16 ∧
    ∀ i, ∫ x in ball z r, ((S.corrector (unitVector i)).potential a x - c i) ^ 2 ≤
      ε ^ 2 * r ^ 2 * volume.real (ball z r)) ∧
  (∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (correctorColumn S a i x) ≤ E) ∧
  (∀ i, ∫ x in ball z T, euclideanSq (correctorColumn S a i x) ≤
    E₁ * volume.real (ball z T)) ∧
  ∃ b : Fin d → Fin d → ℝ, ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4 ∧
    ∀ i, ∀ t : ℝ, r ≤ t → t ≤ S₁ → ∫ x in ball z t,
      euclideanSq ((B.coordinate i).grad x -
        (correctorColumn S a i x + ∑ j, b i j • correctorColumn S a j x)) ≤
          K * (t / r) ^ 2 * volume.real (ball z t)

/-- **The structural pathwise hypotheses of Lemma 4.21 from the correctors**: almost surely,
`LocalizationCorrectorSlopeData` implies `LocalizationInnerSlopeData` at every center, radii,
localized basis and constants. -/
theorem ae_localizationInnerSlopeData_of_correctorSlopeData (hL : firstOrderLiouvilleStatement)
    (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (z : Vec d) (T S₁ r S' σ θ C : ℝ) (B : LocalizedBasis a z T S' σ θ C)
      (E E₁ K : ℝ), 0 < r → LocalizationCorrectorSlopeData S a z T S₁ r B E E₁ K →
        LocalizationInnerSlopeData a z T S₁ r B E E₁ K := by
  filter_upwards [ae_gradients_harmonicA1 hL hd hΛ hP S,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).weak_gradient,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).locally_square_integrable,
    ae_all_iff.2 fun i : Fin d => (S.corrector (unitVector i)).harmonic]
    with a hA1 hint hwg hloc harm
  intro z T S₁ r S' σ θ C B E E₁ K hr hdata
  obtain ⟨hosc, hE, hE₁, b, hb, hinner⟩ := hdata
  refine ⟨fun i => (S.corrector (unitVector i)).potential a,
    fun i => (S.corrector (unitVector i)).grad a, hwg, hloc, harm, hosc,
    fun i => hint i z (Real.sqrt 2 * r) (by positivity), hE, hE₁, fun w => ?_, fun ξ => ?_,
    b, hb, hinner⟩
  · obtain ⟨c, hc, -⟩ := hA1.1 w
    refine ⟨c, ?_⟩
    filter_upwards [hc] with x hx
    rw [hx, correctedAffineGrad_eq_sum]
    rfl
  · obtain ⟨w, -, hw⟩ := hA1.2 ξ
    refine ⟨w, Eventually.of_forall fun x => ?_⟩
    rw [hw, correctedAffineGrad_eq_sum]
    rfl

/-- **The single-slope estimate of Lemma 4.21 for the correctors on a good event** (the
remaining analytic input of (5.85) in this form): as `LocalizationInnerSlopeEstimate`, with the
correctors of one homogenization data `S` of each law and `LocalizationCorrectorSlopeData`. -/
def LocalizationCorrectorSlopeEstimate (d : ℕ) (Λ s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (c E E₁ K₁ C₁ : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ E ∧ 0 ≤ E₁ ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r →
            LocalizationCorrectorSlopeData S a z (localizationOuterRadius δ r)
              (c * localizationIntermediateRadius δ α γ r) r (W a z r hr) E E₁ (K₁ * Y a ^ 2)

/-- `LocalizationCorrectorSlopeEstimate` for the laws of a class `L`. -/
def LocalizationCorrectorSlopeEstimateOn {d : ℕ} {Λ : ℝ}
    (L : Measure (CoefficientField d Λ) → Prop) (s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (c E E₁ K₁ C₁ : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ E ∧ 0 ≤ E₁ ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), L P → ∃ S : HomogenizationData P,
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r →
            LocalizationCorrectorSlopeData S a z (localizationOuterRadius δ r)
              (c * localizationIntermediateRadius δ α γ r) r (W a z r hr) E E₁ (K₁ * Y a ^ 2)

theorem localizationInnerSlopeEstimateOn_of_correctorSlopeOn
    (hL : firstOrderLiouvilleStatement) (hd : 2 ≤ d) {Λ s δ γ α σ θ C₀ : ℝ} (hΛ : 1 < Λ)
    {L : Measure (CoefficientField d Λ) → Prop} (hLP : ∀ P, L P → LawHypotheses P)
    (h : LocalizationCorrectorSlopeEstimateOn L s δ γ α σ θ C₀) :
    LocalizationInnerSlopeEstimateOn L s δ γ α σ θ C₀ := by
  obtain ⟨c, E, E₁, K₁, C₁, hc, hc1, hE, hE₁, hK₁, hC₁, hmain⟩ := h
  refine ⟨c, E, E₁, K₁, C₁, hc, hc1, hE, hE₁, hK₁, hC₁, fun P hLP' W z r hr => ?_⟩
  obtain ⟨S, hS⟩ := hmain P hLP'
  obtain ⟨X, Y, hX0, hY0, hXos, hYos, hae⟩ := hS W z r hr
  refine ⟨X, Y, hX0, hY0, hXos, hYos, ?_⟩
  filter_upwards [hae, ae_localizationInnerSlopeData_of_correctorSlopeData hL hd hΛ (hLP P hLP') S]
    with a ha hstr hXr
  exact hstr _ _ _ _ _ _ _ _ _ _ _ _ (by linarith) (ha hXr)

theorem localizationInnerSlopeEstimate_of_correctorSlope (hL : firstOrderLiouvilleStatement)
    (hd : 2 ≤ d) {Λ s δ γ α σ θ C₀ : ℝ} (hΛ : 1 < Λ)
    (h : LocalizationCorrectorSlopeEstimate d Λ s δ γ α σ θ C₀) :
    LocalizationInnerSlopeEstimate d Λ s δ γ α σ θ C₀ :=
  localizationInnerSlopeEstimateOn_of_correctorSlopeOn hL hd hΛ (L := LawHypotheses)
    (fun _ h => h) h

/-- **(5.85) from the first-order Liouville theorem and the single-slope estimate of Lemma 4.21
for the correctors.** -/
theorem localizedEnergy_of_correctorSlope (hL : firstOrderLiouvilleStatement)
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ : ℝ, 0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
        0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationCorrectorSlopeEstimate d Λ s δ γ α σ θ C₀) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_innerSlope fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => by
    obtain ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀, hest⟩ :=
      h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
    exact ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀,
      localizationInnerSlopeEstimate_of_correctorSlope hL hd hΛ hest⟩

end QSH
