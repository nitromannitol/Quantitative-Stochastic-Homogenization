import QuantitativeStochasticHomogenization.Ch04.Sec03.Estimate558Heat

/-!
# Measurability of the gradient averages

The gradient averages `∫ Φ_{y,ρ} G ξ` of the corrected fields are jointly measurable in the
center, the radius and the coefficient field (`measurable_gradientAverage_uncurry`), since the
corrector gradients are jointly measurable. The flux averages involve the evaluation `a(x)` of the
coefficient field, which is not measurable for the σ-algebra of the coefficient fields; their
measurability remains a hypothesis.

`estimate558_of_heat`: (5.58) as in `estimate558_of_heatIdentity`, with the measurability
hypotheses on the averages and the commutators reduced to the joint measurability of the flux
averages.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Measurability

variable {P : Measure (CoefficientField d Λ)}

theorem measurable_heatKernel_center_radius :
    Measurable fun w : (Vec d × ℝ) × Vec d => heatKernel w.1.1 w.1.2 w.2 := by
  unfold heatKernel euclideanHeatKernel euclideanSq dot
  fun_prop

theorem measurable_correctedField (S : HomogenizationData P) (ξ : Vec d) :
    Measurable fun p : CoefficientField d Λ × Vec d => correctedField S p.1 ξ p.2 := by
  unfold correctedField correctedCoordinate
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_const.add (S.corrector (unitVector i)).measurable_grad).const_smul (ξ i)

theorem measurable_gradientAverage_uncurry (S : HomogenizationData P) (ξ : Vec d) :
    Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ => gradientAverage S w.2 w.1.1 w.1.2 ξ := by
  have hg1 : Measurable fun q : ((Vec d × ℝ) × CoefficientField d Λ) × Vec d => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hg2 : Measurable fun q : ((Vec d × ℝ) × CoefficientField d Λ) × Vec d => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have h1 := (measurable_heatKernel_center_radius (d := d)).comp hg1
  have h2 := (measurable_correctedField S ξ).comp hg2
  have hF := h1.smul h2
  have hI := hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))
  exact hI.measurable

theorem measurable_gradientAverage (S : HomogenizationData P) (z : Vec d) (r : ℝ) (ξ : Vec d) :
    Measurable fun a => gradientAverage S a z r ξ := by
  have hg : Measurable fun a : CoefficientField d Λ => ((z, r), a) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_gradientAverage_uncurry S ξ).comp hg
  exact h

theorem measurable_fluxAverage_of (S : HomogenizationData P)
    (hF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ) (z : Vec d) (r : ℝ) (ξ : Vec d) :
    Measurable fun a => fluxAverage S a z r ξ := by
  have hg : Measurable fun a : CoefficientField d Λ => ((z, r), a) :=
    measurable_const.prodMk measurable_id
  have h := (hF ξ).comp hg
  exact h

theorem measurable_commutatorNorm (S : HomogenizationData P)
    (hF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ) (i : Fin d) :
    Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ => commutatorNorm S w.2 w.1.1 w.1.2 i := by
  have hP := measurable_gradientAverage_uncurry S (unitVector i)
  have hFi := hF (unitVector i)
  have h := measurable_commutator S.homogenized hP hFi
  exact h

end Measurability

/-- **(5.58) and Theorem 4.6 (ii)** as in `estimate558_of_heatIdentity`, with the measurability
hypotheses reduced to the joint measurability of the flux averages. -/
theorem estimate558_of_heat {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
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
    (hmeasF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) :=
  estimate558_of_heatIdentity hd S hΛ hμ hspan hrate hN hexp havg htrial hmeasJ hmeasL
    (fun z r ξ => ⟨measurable_gradientAverage S z r ξ, measurable_fluxAverage_of S hmeasF z r ξ⟩)
    (measurable_commutatorNorm S hmeasF) hheat h411 h412 hs0 hs2

end QSH
