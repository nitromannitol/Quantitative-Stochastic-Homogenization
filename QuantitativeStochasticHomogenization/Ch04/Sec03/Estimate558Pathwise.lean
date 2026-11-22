import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedCommutatorDecay

/-!
# (5.58) from the pathwise heat bound

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3 and (5.58).

`estimate558_of_pathwise_and_law`: (5.58) and Theorem 4.6 (ii) for a law satisfying (0.10)–(0.11),
from (4.12), Proposition 3.21 at every exponent in `(0, d)`, the measurability of `J₁`, the
conclusions of Propositions 4.11 and 4.12, and the heat identity (H) in the lower-integral form
`HeatPathwiseBound` for a positive jointly measurable kernel of mass at most `C_k / u`. The
expectations (1) come from `expectedAveragesEstimate_of_rate` and the absolute convergence of the
time integral from `heatIdentityBound_of_pathwise_of_rate`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

/-- **(5.58) and Theorem 4.6 (ii) from the pathwise heat bound**, for a law satisfying
(0.10)–(0.11). -/
theorem estimate558_of_pathwise_and_law {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {k : ℝ → ℝ → Vec d → ℝ} {Ck : ℝ} (hkm : ∀ r, Measurable (Function.uncurry (k r)))
    (hk0 : ∀ r u x, 0 < k r u x)
    (hki : ∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹)
    (hpath : HeatPathwiseBound P S k)
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
  have hheat := heatIdentityBound_of_pathwise_of_rate S hΛ.le hkm hk0 hki hpath one_pos hμ1 hr1
  exact estimate558_of_heatBound_and_law hP hd S hΛ hspan hrate hmeasJ hheat h411 h412 hs0 hs2

end QSH
