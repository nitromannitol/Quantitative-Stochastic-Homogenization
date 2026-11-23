import QuantitativeStochasticHomogenization.Ch05.Sec03.UniformEnergyEstimate
import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientGram

/-!
# Proposition 4.10 and (4.70) with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10 and Remark 4.18.

From the Gaussian inputs with constants chosen before the law (`UniformGaussianInputs`), the route
of Section 4.3 gives the two conclusions of Proposition 4.10 and the expectation estimate (4.70)
with constants chosen before the law, for every bounded jointly measurable version of `J₁`
(`uniformImprovementOfAdditivity_of_gaussianInputs`, `uniformExpectationEstimates_of_gaussianInputs`):
for an incoming constant `C_F` of `Fluc(s, α)`, Lemma 4.13 and the heat identity give the linear
estimate at `(s, α)` with a constant chosen before the law (`exists_uniform_commutator_linear`), the
trial gap at the homogenized slope is then `O_{s/2}(C r^{-2α})`
(`exists_trialGapEstimateAt_of_linearAverages`), and it gives `Add(s, α + η)`, `Add(s/2, 2α)` and
(4.70) (`exists_addEstimateAt_improved_of_trialGap`, `addEstimateAt_of_trialGapEstimateAt`,
`abs_integral_J1Heat_sub_le_of_trialGap`). The exponent is `η = min(μ(τ)/2, τ/s - d/2)` with
`τ = (s d/2 + d)/2`.

The homogenized matrix does not depend on the homogenization data (`HomogenizationData.homogenized_eq`,
from the limit (1.22)), so (4.70) holds for every homogenization data.

With these, the remaining inputs of the bootstrap are `UniformGaussianInputs` and Proposition 4.11
with constants chosen before the law (`bootstrapInputs_of_gaussianInputs`), and the Gaussian inputs
follow from Proposition 3.21 and the heat identity (H) with constants chosen before the law
(`bootstrapInputs_of_rate_heat_localization`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The homogenized matrix is determined by the law**: two homogenization data have the same
matrix, since both quadratic forms are the limit (1.22) and the matrices are symmetric. -/
theorem HomogenizationData.homogenized_eq {P : Measure (CoefficientField d Λ)}
    (S S' : HomogenizationData P) : S.homogenized = S'.homogenized := by
  have hq : ∀ e : Vec d, dot e (S.homogenized.mulVec e) = dot e (S'.homogenized.mulVec e) := by
    intro e
    have h := tendsto_nhds_unique (S.variational_limit e) (S'.variational_limit e)
    linarith
  have hpol : ∀ (M : Mat d) (i j : Fin d),
      dot (unitVector i + unitVector j) (M.mulVec (unitVector i + unitVector j)) =
        M i i + M i j + M j i + M j j := by
    intro M i j
    have e : dot (unitVector i + unitVector j) (M.mulVec (unitVector i + unitVector j)) =
        dot (unitVector i) (M.mulVec (unitVector i)) +
          dot (unitVector i) (M.mulVec (unitVector j)) +
          dot (unitVector j) (M.mulVec (unitVector i)) +
          dot (unitVector j) (M.mulVec (unitVector j)) := by
      simp only [dot_eq_dotProduct, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
      ring
    rw [e, dot_unitVector_mulVec, dot_unitVector_mulVec, dot_unitVector_mulVec,
      dot_unitVector_mulVec]
  ext i j
  have h1 := hq (unitVector i + unitVector j)
  rw [hpol, hpol] at h1
  have h2 := hq (unitVector i)
  have h3 := hq (unitVector j)
  rw [dot_unitVector_mulVec, dot_unitVector_mulVec] at h2 h3
  have hs : S.homogenized j i = S.homogenized i j := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun S.symmetric i) j
  have hs' : S'.homogenized j i = S'.homogenized i j := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun S'.symmetric i) j
  linarith

/-- **The trial gap estimate with the constant chosen before the law**, at the exponents `(s, α)`,
an exponent `τ ∈ (s d/2, d)` and the incoming constant `C_F` of `Fluc(s, α)`, for the
homogenization data of the Gaussian inputs with constants `C(τ)`, `μ(τ)`, `C_E`. -/
theorem exists_uniform_trialGap (hd : 2 ≤ d) (hΛ : 1 < Λ) {C μ : ℝ → ℝ} {CE Ck : ℝ} (hCE : 0 < CE)
    (hCμ : ∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ)
    (hG : ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      HeatIdentityBound P S Ck ∧ ExpectedAveragesEstimateAt P S d CE ∧
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    {s α τ CF : ℝ} (hs0 : 0 < s) (hα0 : 0 < α) (hα : α ≤ (d : ℝ) / 2)
    (hτ1 : s * ((d : ℝ) / 2) < τ) (hτ2 : τ < d) (hCF : 0 < CF) :
    ∃ Cg : ℝ, 0 < Cg ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        GaussianCorrectorRate P S τ (C τ) (μ τ) ∧ TrialIntegrable P S ∧
        TrialExpectationEstimateAt P S (2 * α) (5 * (2 * CE)) ∧
        ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s α CF →
          TrialGapEstimateAt P S J (s / 2) (2 * α) Cg := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb2 : 0 < (d : ℝ) / 2 := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ1
  have hτs : s ≤ τ / ((d : ℝ) / 2) := by rw [le_div_iff₀ hb2]; exact hτ1.le
  obtain ⟨hCτ, hμτ⟩ := hCμ τ hτ0 hτ2
  have hCN0 : 0 < gaussianRateEnergyScale τ (C τ) Λ :=
    lt_max_of_lt_left (mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hCτ))
  obtain ⟨Cc, Cl, hCc, hCl, hCL⟩ := exists_uniform_commutator_linear (Ck := Ck) hd hΛ
    hs0 hα0 hα hCF hτ0 hCτ hμτ hCE hτs
  obtain ⟨Cg, hCg, hgap⟩ := exists_trialGapEstimateAt_of_linearAverages hd1 hΛ0 hs0 hα hτ1 hCτ
    hμτ hCN0 hCF hCl (by positivity : (0 : ℝ) < 2 * CE)
  refine ⟨Cg, hCg, fun P hP => ?_⟩
  have := hP.1
  obtain ⟨S, hH, hE, hr⟩ := hG P hP
  have hA := S.homogenizedMatrixBounds hΛ0
  have hspan := ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S
  have hN := (gaussianEnergyBound_of_rate_at S (fun ξ => (hA ξ).2) hτ0 hμτ.le
    (hr τ hτ0 hτ2)).2
  have hint := averagesIntegrable_of_lawHypotheses hd hΛ hP S
  have hEα : ExpectedAveragesEstimateAt P S α CE := hE.mono hCE.le (by linarith)
  have hE2α : ExpectedAveragesEstimateAt P S (2 * α) CE := hE.mono hCE.le (by linarith)
  have hobj := trialObjectiveExpectationAt_of_expectedAverages S hint hCE hE2α
  refine ⟨S, hr τ hτ0 hτ2, trialIntegrable_of_energyBound S hΛ0 hN,
    trialExpectationEstimateAt_of_objective S hA (by positivity) hobj, fun J hJ hF => ?_⟩
  obtain ⟨-, hlin⟩ := hCL P hP S J hJ.measurable_slice hJ.2.2 hF (hr τ hτ0 hτ2) hEα hH
  exact hgap P S hA hspan J hJ.measurable_slice (fun a z r p q _ hp hq => hJ.2.1 a z r p q hp hq)
    hJ.2.2 (measurable_trialValue_uncurry S) (hr τ hτ0 hτ2) hN hF hlin hobj

/-- **Proposition 4.10 with constants chosen before the law**, from the Gaussian inputs with
constants chosen before the law: `η = min(μ(τ)/2, τ/s - d/2)`, `τ = (s d/2 + d)/2`. -/
theorem uniformImprovementOfAdditivity_of_gaussianInputs (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hG : UniformGaussianInputs d Λ) : UniformImprovementOfAdditivity d Λ := by
  intro s hs0 hs2
  obtain ⟨C, μ, CE, Ck, hCE, hCμ, hG⟩ := hG
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ0 : 0 ≤ Λ := by linarith
  set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s * ((d : ℝ) / 2) < τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ1
  have hκd : (d : ℝ) / 2 < τ / s := by rw [lt_div_iff₀ hs0]; linarith
  obtain ⟨hCτ, hμτ⟩ := hCμ τ hτ0 hτ2
  refine ⟨min (μ τ / 2) (τ / s - (d : ℝ) / 2), lt_min (by positivity) (by linarith),
    fun α CF hα0 hα hCF => ?_⟩
  obtain ⟨Cg, hCg, hgap⟩ := exists_uniform_trialGap hd hΛ hCE hCμ hG hs0 hα0 hα hτ1 hτ2 hCF
  obtain ⟨D₁, hD₁, hadd⟩ := exists_addEstimateAt_improved_of_trialGap (Λ := Λ) hs0 hα hτ1 hCτ hμτ
    hCg
  refine ⟨max D₁ (max 1 ((1 + (1 - s / 2) / (s / 2 * Real.log 2)) ^ (s / 2)⁻¹) * Cg),
    lt_max_of_lt_left hD₁, fun P hP J hJ hF => ?_⟩
  have := hP.1
  obtain ⟨S, hr, htrial, -, hg⟩ := hgap P hP
  have hA := S.homogenizedMatrixBounds hΛ0
  have hspan := ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S
  have hJb : ∀ a z r p q, 1 ≤ r → euclideanNorm p < 1 → euclideanNorm q < 1 →
      |J a z r p q| ≤ |Λ| + 1 := fun a z r p q _ hp hq => hJ.2.1 a z r p q hp hq
  have hgJ := hg J hJ hF
  exact ⟨(hadd P S hA hspan htrial J hJ.measurable_slice hJb hJ.2.2 hr hgJ).mono_const
      (le_max_left _ _),
    (addEstimateAt_of_trialGapEstimateAt S hspan htrial hJ.measurable_slice hJb hJ.2.2 hCg
      hgJ).mono_const (le_max_right _ _)⟩

/-- **(4.70) with constants chosen before the law**, from the Gaussian inputs with constants
chosen before the law, for every homogenization data. -/
theorem uniformExpectationEstimates_of_gaussianInputs (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hG : UniformGaussianInputs d Λ) : UniformExpectationEstimates d Λ := by
  intro s α CF hs0 hs2 hα0 hα hCF
  obtain ⟨C, μ, CE, Ck, hCE, hCμ, hG⟩ := hG
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s * ((d : ℝ) / 2) < τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  obtain ⟨Cg, hCg, hgap⟩ := exists_uniform_trialGap hd hΛ hCE hCμ hG hs0 hα0 hα hτ1 hτ2 hCF
  refine ⟨(1 + 2 * ((Nat.ceil (s / 2)⁻¹).factorial : ℝ)) * Cg + 5 * (2 * CE), by positivity,
    fun P hP S' J hJ hF z r hr p q hp hq => ?_⟩
  have := hP.1
  obtain ⟨S, -, -, hexp, hg⟩ := hgap P hP
  have hspan := ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S
  rw [S'.homogenized_eq S]
  exact abs_integral_J1Heat_sub_le_of_trialGap S hspan hJ.2.2 (hg J hJ hF) hexp z r hr p q hp hq

/-- **The inputs of the bootstrap from the Gaussian inputs and Proposition 4.11**, all with
constants chosen before the law: Proposition 4.10 and (4.70) follow from the Gaussian inputs. -/
theorem bootstrapInputs_of_gaussianInputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformLocalizationEstimates d Λ) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ ∧
      UniformExpectationEstimates d Λ := fun d hd Λ hΛ =>
  ⟨(h d hd Λ hΛ).1, uniformImprovementOfAdditivity_of_gaussianInputs hd hΛ (h d hd Λ hΛ).1,
    (h d hd Λ hΛ).2, uniformExpectationEstimates_of_gaussianInputs hd hΛ (h d hd Λ hΛ).1⟩

/-- **The inputs of the bootstrap from Proposition 3.21, the heat identity (H) and
Proposition 4.11**, all with constants chosen before the law (`uniformGaussianInputs_of_rate_heat`
and `bootstrapInputs_of_gaussianInputs`). -/
theorem bootstrapInputs_of_rate_heat_localization
    (hrate : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C μ : ℝ → ℝ,
      (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Ck : ℝ,
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        ∃ k : ℝ → ℝ → Vec d → ℝ, (∀ r, Measurable (Function.uncurry (k r))) ∧
        (∀ r u x, 0 < k r u x) ∧ (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k)
    (h411 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformLocalizationEstimates d Λ) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ ∧
      UniformExpectationEstimates d Λ :=
  bootstrapInputs_of_gaussianInputs fun d hd Λ hΛ =>
    ⟨uniformGaussianInputs_of_rate_heat hd hΛ (hrate d hd Λ hΛ) (hH d hd Λ hΛ), h411 d hd Λ hΛ⟩

end QSH
