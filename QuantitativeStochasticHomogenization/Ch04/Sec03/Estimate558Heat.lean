import QuantitativeStochasticHomogenization.Ch04.Sec03.Estimate558Commutator
import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentityReduction

/-!
# (5.58) from the bound of the heat identity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13 and Proposition 4.10, and Section 5.3, (5.58).

`estimate558_of_heatIdentity`: (5.58) and Theorem 4.6 (ii) from the inputs of
`estimate558_of_inputs`, with the linear estimate of Step 1 replaced by the bound
(`HeatIdentityBound`) that the heat identity (H) of the route used here gives, and the joint
measurability of the commutators in the center and the radius.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **(5.58) and Theorem 4.6 (ii)** from the inputs of `estimate558_of_inputs`, with the linear
estimate of Step 1 replaced by the bound from the heat identity. -/
theorem estimate558_of_heatIdentity {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hμ : ∀ (n : ℕ) (ξ : Vec d),
      AEStronglyMeasurable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (havg : AveragesIntegrable P S) (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d), Measurable (fun a => gradientAverage S a z r ξ) ∧
      Measurable (fun a => fluxAverage S a z r ξ))
    (hmeasC : ∀ i, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      commutatorNorm S w.2 w.1.1 w.1.2 i)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hd1 : 1 ≤ d := by omega
  refine estimate558_of_commutator hd S hΛ hμ hspan hrate hN hexp havg htrial hmeasJ hmeasL hmeasA
    (fun s' α hs0' hs2' hα0 _ _ hC => ?_) h411 h412 hs0 hs2
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set τ : ℝ := (s' * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s' * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s' ≤ τ / ((d : ℝ) / 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hτ1
  obtain ⟨CN, -, hNτ⟩ := hN τ hτ0 hτ2
  exact linearAverageEstimate_of_heat hd1 S hΛ.le hs0' hα0 hC hheat hmeasC
    (fun z r ξ => (hmeasA z r ξ).1) hNτ hτs havg

end QSH
