import QuantitativeStochasticHomogenization.Ch04.Sec03.LinearEstimateOptimal
import QuantitativeStochasticHomogenization.Front.Assumptions.MeasurableVersion

/-!
# Measurability of the flux averages and of the trial values

The Gaussian flux averages `∫ Φ_{y,ρ} a G ξ` and the values `∫ Φ_{y,r} (-½ G k·aG k - p·aG k + q·G k)`
of the functional of (4.8) at the corrected fields involve the evaluation `a(x)`, which is not a
measurable function of `a`. For every coefficient field, `a(x)` agrees for almost every `x` with
the jointly measurable version `coefficientVersion a x`, so both integrals are integrals of jointly
measurable functions: the flux averages are jointly measurable in the center, the radius and the
coefficient field (`measurable_fluxAverage_uncurry`), and the trial values in the center and the
coefficient field (`measurable_trialValue_uncurry`).

This removes these two measurability hypotheses from the linear estimate and Lemma 4.13 at the
exponent `d/2` (`commutator_linearAverage_half_dim`) and from (5.58)
(`estimate558_of_heatBound_rate_measurable_J1Heat`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Measurability

variable {P : Measure (CoefficientField d Λ)}

/-- **The flux averages are jointly measurable** in the center, the radius and the coefficient
field. -/
theorem measurable_fluxAverage_uncurry (S : HomogenizationData P) (ξ : Vec d) :
    Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ => fluxAverage S w.2 w.1.1 w.1.2 ξ := by
  set F : ((Vec d × ℝ) × CoefficientField d Λ) × Vec d → Vec d := fun q =>
    heatKernel q.1.1.1 q.1.1.2 q.2 •
      (coefficientVersion q.1.2 q.2).mulVec (correctedField S q.1.2 ξ q.2) with hFdef
  have hF : Measurable F := by
    have hg1 : Measurable fun q : ((Vec d × ℝ) × CoefficientField d Λ) × Vec d => (q.1.1, q.2) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have hg2 : Measurable fun q : ((Vec d × ℝ) × CoefficientField d Λ) × Vec d => (q.1.2, q.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hmv : Continuous (fun q : Mat d × Vec d => q.1.mulVec q.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact ((measurable_heatKernel_center_radius (d := d)).comp hg1).smul
      (hmv.measurable.comp ((measurable_coefficientVersion.comp hg2).prodMk
        ((measurable_correctedField S ξ).comp hg2)))
  have hfun : (fun w : (Vec d × ℝ) × CoefficientField d Λ => fluxAverage S w.2 w.1.1 w.1.2 ξ) =
      fun w => ∫ x, F (w, x) := by
    funext w
    unfold fluxAverage
    refine integral_congr_ae ?_
    filter_upwards [ae_coefficientVersion_eq w.2] with x hx
    simp only [hFdef, hx]
  rw [hfun]
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))).measurable

/-- **The trial values are jointly measurable** in the center and the coefficient field. -/
theorem measurable_trialValue_uncurry (S : HomogenizationData P) (r : ℝ) (p q k : Vec d) :
    Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k := by
  let Ψ : Mat d × Vec d → ℝ := fun m => -(1 / 2 : ℝ) * dot m.2 (m.1.mulVec m.2) -
    dot p (m.1.mulVec m.2) + dot q m.2
  have hc : Continuous Ψ := by
    have h1 : Continuous (fun m : Mat d × Vec d => dot m.2 (m.1.mulVec m.2)) :=
      continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
    have h2 : Continuous (fun m : Mat d × Vec d => dot p (m.1.mulVec m.2)) :=
      continuous_const.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
    have h3 : Continuous (fun m : Mat d × Vec d => dot q m.2) :=
      continuous_const.dotProduct continuous_snd
    exact ((continuous_const.mul h1).sub h2).add h3
  let F : (Vec d × CoefficientField d Λ) × Vec d → ℝ := fun w =>
    heatKernel w.1.1 r w.2 * Ψ (coefficientVersion w.1.2 w.2, correctedField S w.1.2 k w.2)
  have hF : Measurable F := by
    have hg1 : Measurable fun w : (Vec d × CoefficientField d Λ) × Vec d => ((w.1.1, r), w.2) :=
      ((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd
    have hg2 : Measurable fun w : (Vec d × CoefficientField d Λ) × Vec d => (w.1.2, w.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hk : Measurable fun w : (Vec d × CoefficientField d Λ) × Vec d => heatKernel w.1.1 r w.2 :=
      (measurable_heatKernel_center_radius (d := d)).comp hg1
    have hΨ : Measurable fun w : (Vec d × CoefficientField d Λ) × Vec d =>
        Ψ (coefficientVersion w.1.2 w.2, correctedField S w.1.2 k w.2) :=
      hc.measurable.comp ((measurable_coefficientVersion.comp hg2).prodMk
        ((measurable_correctedField S k).comp hg2))
    exact hk.mul hΨ
  have hfun : (fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k) =
      fun w => ∫ x, F (w, x) := by
    funext w
    unfold trialValue j1Functional
    refine integral_congr_ae ?_
    filter_upwards [ae_coefficientVersion_eq w.2] with x hx
    simp only [F, Ψ, hx]
  rw [hfun]
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))).measurable

/-- **Lemma 4.13 and the linear estimate at the exponent `d/2`** as in
`linearAverageEstimate_half_dim`, without the measurability hypotheses on the flux averages and the
trial values. -/
theorem commutator_linearAverage_half_dim [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 < Λ) (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    CommutatorEstimate P S s ((d : ℝ) / 2) ∧ LinearAverageEstimate P S s ((d : ℝ) / 2) :=
  linearAverageEstimate_half_dim hd S hΛ hspan hrate hexp hmeasJ
    (measurable_trialValue_uncurry S) (measurable_fluxAverage_uncurry S) hheat h411 h412 hs0 hs2

/-- **(5.58) and Theorem 4.6 (ii)** as in `estimate558_of_heatBound_and_rate`, without the
measurability hypotheses on the flux averages and the trial values. -/
theorem estimate558_of_heatBound_rate_measurable_J1Heat [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 < Λ) (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) :=
  estimate558_of_heatBound_and_rate hd S hΛ hspan hrate hexp hmeasJ
    (measurable_trialValue_uncurry S) (measurable_fluxAverage_uncurry S) hheat h411 h412 hs0 hs2

end Measurability

end QSH
