import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAveragesFromRate
import QuantitativeStochasticHomogenization.Ch04.Sec03.LinearEstimateOptimal
import QuantitativeStochasticHomogenization.Ch04.Sec03.FluxAverageMeasurability

/-!
# (5.58) without the expectations (1) as a hypothesis

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3 and (5.58).

The flux averages and the trial values are the averages of the jointly measurable flux and energy
densities (`fluxAverage_eq_integral_fluxDensity`, `trialValue_eq_integral_densities`); they are
jointly measurable (`measurable_fluxAverage_uncurry`, `measurable_trialValue_uncurry`), and by
`expectedAveragesEstimate_of_rate` the expectations (1) follow from Proposition 3.21 and the
assumptions on the law. Hence
`estimate558_of_heatBound_and_law`: (5.58) and Theorem 4.6 (ii) from (4.12), Proposition 3.21 at
every exponent in `(0, d)`, the measurability of `J₁`, the bound from the heat identity (H), and the
conclusions of Propositions 4.11 and 4.12.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

section Measurability

variable {P : Measure (CoefficientField d Λ)}

theorem fluxAverage_eq_integral_fluxDensity (S : HomogenizationData P) (a : CoefficientField d Λ)
    (y : Vec d) (ρ : ℝ) (ξ : Vec d) :
    fluxAverage S a y ρ ξ = ∫ x, heatKernel y ρ x • fluxDensity S ξ a x :=
  (integral_heatKernel_smul_fluxDensity S ξ a y ρ).symm

theorem trialValue_eq_integral_densities (S : HomogenizationData P) (a : CoefficientField d Λ)
    (y : Vec d) (r : ℝ) (p q k : Vec d) :
    trialValue S a y r p q k = ∫ x, heatKernel y r x * (-(1 / 2 : ℝ) * energyDensity S k a x -
      dot p (fluxDensity S k a x) + dot q (correctedField S a k x)) := by
  unfold trialValue j1Functional
  refine integral_congr_ae ?_
  filter_upwards [ae_fluxDensity_eq S k a, ae_energyDensity_eq S k a] with x hx1 hx2
  rw [hx1, hx2]

end Measurability

/-- **(5.58) and Theorem 4.6 (ii)** from the structure (4.12) of `A₁`, Proposition 3.21 at every
exponent `τ ∈ (0, d)`, the measurability of `J₁`, the bound from the heat identity (H), and the
conclusions of Propositions 4.11 and 4.12, for a law satisfying (0.10)–(0.11). -/
theorem estimate558_of_heatBound_and_law {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have : IsProbabilityMeasure P := hP.1
  have hdr : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C1, μ1, -, hμ1, hr1⟩ := hrate 1 one_pos hdr
  exact estimate558_of_heatBound_and_rate hd S hΛ hspan hrate
    (fun β hβ _ => expectedAveragesEstimate_of_rate hP S hΛ.le one_pos hμ1 hr1 hβ) hmeasJ
    (measurable_trialValue_uncurry S) (measurable_fluxAverage_uncurry S) hheat h411 h412 hs0 hs2

/-- **Lemma 4.13 and the linear estimate at the exponent `d/2`** without the expectations (1) and
the measurability of the trial and of the flux averages as hypotheses. -/
theorem linearAverageEstimate_half_dim_of_law {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    CommutatorEstimate P S s ((d : ℝ) / 2) ∧ LinearAverageEstimate P S s ((d : ℝ) / 2) := by
  have : IsProbabilityMeasure P := hP.1
  have hdr : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C1, μ1, -, hμ1, hr1⟩ := hrate 1 one_pos hdr
  exact linearAverageEstimate_half_dim hd S hΛ hspan hrate
    (fun β hβ _ => expectedAveragesEstimate_of_rate hP S hΛ.le one_pos hμ1 hr1 hβ) hmeasJ
    (measurable_trialValue_uncurry S) (measurable_fluxAverage_uncurry S) hheat h411 h412 hs0 hs2

end QSH
