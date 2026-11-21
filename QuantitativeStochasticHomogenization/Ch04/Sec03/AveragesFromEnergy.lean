import QuantitativeStochasticHomogenization.Ch04.Sec03.AverageMeasurability

/-!
# The averages of the corrected fields from the energy

If the energy density of a measurable field `G` is integrable against `Φ_{z,r}`, so are `G` and its
flux `aG`, since `|G| ≤ (1 + G·aG)/2` and `|aG| ≤ Λ|G|` (`integrable_averages_of_energy`).
Consequently the energy bound below the scale gives the almost sure integrability of the three
averages (`averagesIntegrable_of_energyBound`) and of the trial (`trialIntegrable_of_energyBound`),
and (5.58) holds without these hypotheses (`estimate558_of_heatIdentityBound`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem euclideanNorm_coefficient_mulVec_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (x u : Vec d) :
    euclideanNorm ((a x).mulVec u) ≤ Λ * euclideanNorm u :=
  euclideanNorm_mulVec_le_of_abs_dot_le (a.symmetric x) hΛ (fun v => by
    obtain ⟨h1, h2⟩ := a.elliptic x v
    rw [abs_of_nonneg ((euclideanSq_nonneg v).trans h1)]
    exact h2) u

theorem norm_le_euclideanNorm (v : Vec d) : ‖v‖ ≤ euclideanNorm v :=
  (pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg v)).mpr fun i => by
    rw [Real.norm_eq_abs]; exact abs_apply_le_euclideanNorm v i

/-- **`Φ G` and `Φ aG` are integrable when the energy `Φ G·aG` is.** -/
theorem integrable_averages_of_energy (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (z : Vec d) {r : ℝ}
    (hr : 0 < r) {G : Vec d → Vec d} (hGm : AEStronglyMeasurable G volume)
    (hE : Integrable fun x => heatKernel z r x * dot (G x) ((a x).mulVec (G x))) :
    Integrable (fun x => heatKernel z r x • G x) ∧
      Integrable (fun x => heatKernel z r x • (a x).mulVec (G x)) := by
  have hΦ : Integrable (fun x => heatKernel z r x) := integrable_heatKernel z hr
  have hΦm : AEStronglyMeasurable (fun x => heatKernel z r x) volume := hΦ.aestronglyMeasurable
  have hB : Integrable (fun x => (1 / 2 : ℝ) * (heatKernel z r x +
      heatKernel z r x * dot (G x) ((a x).mulVec (G x)))) := (hΦ.add hE).const_mul _
  have hpt : ∀ x, heatKernel z r x * euclideanNorm (G x) ≤ (1 / 2 : ℝ) * (heatKernel z r x +
      heatKernel z r x * dot (G x) ((a x).mulVec (G x))) := by
    intro x
    have hΦ0 := heatKernel_nonneg z r x
    have h1 : euclideanNorm (G x) ≤ (1 + euclideanSq (G x)) / 2 := by
      rw [← euclideanNorm_sq]; nlinarith [sq_nonneg (euclideanNorm (G x) - 1)]
    have h2 := (a.elliptic x (G x)).1
    have h3 : euclideanNorm (G x) ≤ (1 + dot (G x) ((a x).mulVec (G x))) / 2 := by linarith
    calc heatKernel z r x * euclideanNorm (G x)
        ≤ heatKernel z r x * ((1 + dot (G x) ((a x).mulVec (G x))) / 2) :=
          mul_le_mul_of_nonneg_left h3 hΦ0
      _ = (1 / 2 : ℝ) * (heatKernel z r x + heatKernel z r x * dot (G x) ((a x).mulVec (G x))) := by
          ring
  have hGc : ∀ j, AEStronglyMeasurable (fun x => G x j) volume := fun j =>
    (continuous_apply j).comp_aestronglyMeasurable hGm
  have hmv : AEStronglyMeasurable (fun x => (a x).mulVec (G x)) volume := by
    refine (aemeasurable_pi_iff.mpr fun k => ?_).aestronglyMeasurable
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.aemeasurable_fun_sum _ fun j _ =>
      ((a.locally_integrable k j).aestronglyMeasurable.aemeasurable.mul (hGc j).aemeasurable)
  constructor
  · refine hB.mono' (hΦm.smul hGm) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _ _)]
    exact (mul_le_mul_of_nonneg_left (norm_le_euclideanNorm _) (heatKernel_nonneg _ _ _)).trans
      (hpt x)
  · refine (hB.const_mul Λ).mono' (hΦm.smul hmv) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _ _)]
    have hΦ0 := heatKernel_nonneg z r x
    calc heatKernel z r x * ‖(a x).mulVec (G x)‖
        ≤ heatKernel z r x * (Λ * euclideanNorm (G x)) := mul_le_mul_of_nonneg_left
          ((norm_le_euclideanNorm _).trans (euclideanNorm_coefficient_mulVec_le a hΛ x _)) hΦ0
      _ = Λ * (heatKernel z r x * euclideanNorm (G x)) := by ring
      _ ≤ Λ * ((1 / 2 : ℝ) * (heatKernel z r x +
          heatKernel z r x * dot (G x) ((a x).mulVec (G x)))) :=
          mul_le_mul_of_nonneg_left (hpt x) hΛ

/-- **The averages of the corrected fields are integrable** under the energy bound below the
scale. -/
theorem averagesIntegrable_of_energyBound {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ CN : ℝ} (hN : GaussianEnergyBound P S τ CN) :
    AveragesIntegrable P S := by
  obtain ⟨X, -, -, -, hXe⟩ := hN
  filter_upwards [hXe] with a ha
  intro z r hr ξ
  have hE := (ha z r hr ξ).1
  have hg : Measurable fun x : Vec d => (a, x) := measurable_const.prodMk measurable_id
  have hGm := (measurable_correctedField S ξ).comp hg
  obtain ⟨h1, h2⟩ := integrable_averages_of_energy a hΛ z (zero_lt_one.trans_le hr)
    hGm.aestronglyMeasurable hE
  exact ⟨h1, h2, hE⟩

/-- **The trial is integrable** under the energy bound below the scale. -/
theorem trialIntegrable_of_energyBound {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ CN : ℝ} (hN : GaussianEnergyBound P S τ CN) :
    TrialIntegrable P S := by
  filter_upwards [averagesIntegrable_of_energyBound S hΛ hN] with a ha
  intro z R hR p q
  obtain ⟨h1, h2, h3⟩ := ha z R hR (homogenizedSlope S.homogenized p q)
  have hfun : (fun x => heatKernel z R x *
      j1Integrand a p q (correctedField S a (homogenizedSlope S.homogenized p q)) x) = fun x =>
        -(1 / 2 : ℝ) * (heatKernel z R x *
          dot (correctedField S a (homogenizedSlope S.homogenized p q) x)
            ((a x).mulVec (correctedField S a (homogenizedSlope S.homogenized p q) x))) -
        dot p (heatKernel z R x •
          (a x).mulVec (correctedField S a (homogenizedSlope S.homogenized p q) x)) +
        dot q (heatKernel z R x • correctedField S a (homogenizedSlope S.homogenized p q) x) := by
    funext x
    simp only [j1Integrand, dot_eq_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hfun]
  exact ((h3.const_mul _).sub (integrable_dot_left p h2)).add (integrable_dot_left q h1)

/-- **(5.58) and Theorem 4.6 (ii)** as in `estimate558_of_heat`, without the integrability of the
averages and of the trial (consequences of the energy bound). -/
theorem estimate558_of_heatIdentityBound {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hμ : ∀ (n : ℕ) (ξ : Vec d),
      AEStronglyMeasurable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
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
          (C * r ^ (-((d : ℝ) / 2))) := by
  obtain ⟨CN, -, hN1⟩ := hN 1 one_pos (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  exact estimate558_of_heat hd S hΛ hμ hspan hrate hN hexp
    (averagesIntegrable_of_energyBound S hΛ.le hN1) (trialIntegrable_of_energyBound S hΛ.le hN1)
    hmeasJ hmeasL hmeasF hheat h411 h412 hs0 hs2

end QSH
