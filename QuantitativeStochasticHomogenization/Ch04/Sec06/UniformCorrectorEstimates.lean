import QuantitativeStochasticHomogenization.Ch04.Sec02.Theorem46UniformBase
import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevSublinear
import QuantitativeStochasticHomogenization.Ch04.Opening.Theorem41Energy
import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentityReduction
import QuantitativeStochasticHomogenization.Ch04.Sec03.EnergyFromRate
import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentityFromPathwise
import QuantitativeStochasticHomogenization.Ch04.Sec03.FluxAverageMeasurability
import QuantitativeStochasticHomogenization.Ch05.Sec04.LocalizedAdditivityProof
import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAveragesFromRate
import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedCommutatorDecay

/-!
# The commutator and linear estimates with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3 (Lemma 4.13 and Step 1 of the proof of Proposition 4.10), Theorem 4.6 and the inputs
of Theorem 4.24 ((4.126)) and Theorem 4.1.

`exists_uniform_commutator_linear`: for `s > 0`, `α ∈ (0, d/2]` and `τ > 0` with
`s ≤ τ/(d/2)`, the constants of `Fluc(s, α)` (for a jointly measurable version of `J₁`), of
Proposition 3.21 at `τ`, of the expectations (1) and of the heat identity (H) determine the
constants of the commutator estimate (4.34) and of the linear estimate, for every law satisfying
the assumptions.

`UniformGaussianInputs d Λ` collects, for one homogenization data `S` of each law, the heat
identity (H) with kernel mass `C_k/u`, the expectations (1) at the rate `r^{-d}` with one
constant, and Proposition 3.21 at every exponent `τ ∈ (0, d)` with constants `C(τ)`, `μ(τ)`
chosen before the law. With Propositions 4.10 and 4.11 with constants chosen before the law,
it gives:
* the commutator and linear estimates at `(s, d/2)` with constants chosen before the law
  (`exists_uniform_commutator_linear_half_dim`), hence `QSH.Frozen.negativeSobolevCorrector`
  (`negativeSobolevCorrector_of_uniform_inputs`), `QSH.Frozen.averagedCorrectorGradient`
  (`averagedCorrectorGradient_of_uniform_inputs`) and the Gaussian gradient bound
  `UniformLinearAverageEstimate` (`uniformLinearAverageEstimate_of_uniform_inputs`);
* Theorem 4.6 (i) and (iii) with constants chosen before the law
  (`uniformAdditivityJ1_of_uniform_inputs`, `uniformFluctuationJ1_of_uniform_inputs`), hence
  `QSH.Frozen.blockCLT`, `QSH.Frozen.blockBoundary` and `QSH.Frozen.blockChange`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **Lemma 4.13 and the linear estimate with constants chosen before the law**: the constants
`C_F` of `Fluc(s, α)` for a jointly measurable version of `J₁`, `C_R, μ` of Proposition 3.21 at
`τ`, `C_E` of the expectations (1) at the rate `r^{-α}` and `C_k` of the heat identity (H)
determine the constants of the commutator estimate (4.34) and of the linear estimate at `(s, α)`,
for every law satisfying the assumptions and every homogenization data. -/
theorem exists_uniform_commutator_linear (hd : 2 ≤ d) (hΛ : 1 < Λ)
    {s α CF τ CR μ CE Ck : ℝ} (hs0 : 0 < s) (hα0 : 0 < α) (hα : α ≤ (d : ℝ) / 2)
    (hCF : 0 < CF) (hτ : 0 < τ) (hCR : 0 < CR) (hμ : 0 < μ) (hCE : 0 < CE)
    (hτs : s ≤ τ / ((d : ℝ) / 2)) :
    ∃ Cc Cl : ℝ, 0 < Cc ∧ 0 < Cl ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (S : HomogenizationData P) (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ),
      (∀ (r : ℝ) (p q : Vec d),
        Measurable fun w : CoefficientField d Λ × Vec d => J w.1 w.2 r p q) →
      (∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q) →
      FlucEstimateAt P J s α CF → GaussianCorrectorRate P S τ CR μ →
      ExpectedAveragesEstimateAt P S α CE → HeatIdentityBound P S Ck →
      CommutatorEstimateAt P S s α Cc ∧ LinearAverageEstimateAt P S s α Cl := by
  have hd1 : 1 ≤ d := by omega
  have hΛ0 : 0 < Λ := by linarith
  have hCN : 0 < gaussianRateEnergyScale τ CR Λ :=
    lt_max_of_lt_left (mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hCR))
  obtain ⟨Cc, hCc, hC⟩ := exists_uniform_commutator_of_fluctuations hd1 hΛ0 hs0 hα0.le hα hCF
    hμ hCR hCN hCE hτs
  obtain ⟨Cl, hCl, hL⟩ := exists_uniform_linear_of_heat (Ck := Ck) hd1 hΛ0.le hs0 hα0 hCc hCN
    hτs
  refine ⟨Cc, Cl, hCc, hCl, fun P hP S J hJm hJ hF hrate hE hH => ?_⟩
  have := hP.1
  have hA := S.homogenizedMatrixBounds hΛ0.le
  have hspan := ae_gradientsOfA1AreCorrected_of_liouville firstOrderLiouville hd hΛ hP S
  have hN := (gaussianEnergyBound_of_rate_at S (fun ξ => (hA ξ).2) hτ hμ.le hrate).2
  have hint := averagesIntegrable_of_lawHypotheses hd hΛ hP S
  have hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d),
      Measurable (fun a => gradientAverage S a z r ξ) ∧
        Measurable (fun a => fluxAverage S a z r ξ) := fun z r ξ =>
    ⟨measurable_gradientAverage S z r ξ,
      measurable_fluxAverage_of S (measurable_fluxAverage_uncurry S) z r ξ⟩
  have hc := hC P S hA hspan J hJm hJ hF hrate hN hint hE hmeasA
  exact ⟨hc, hL P S hc hH (measurable_commutatorNorm_uncurry S) (fun z r ξ => (hmeasA z r ξ).1)
    hN hint⟩

/-- **The Gaussian inputs with constants chosen before the law** (Proposition 3.21, the
expectations (1) and the heat identity (H)): there are `C(τ), μ(τ) > 0` for `τ ∈ (0, d)` and
`C_E > 0`, `C_k` such that every law satisfying the assumptions has homogenization data `S` with the
heat identity (H) with kernel mass `C_k/u`, the expectations (1) at the rate `r^{-d}` with
constant `C_E`, and Proposition 3.21 at every `τ ∈ (0, d)` with constant `C(τ)` and rate
`μ(τ)`. -/
def UniformGaussianInputs (d : ℕ) (Λ : ℝ) : Prop :=
  ∃ (C μ : ℝ → ℝ) (CE Ck : ℝ), 0 < CE ∧ (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      HeatIdentityBound P S Ck ∧ ExpectedAveragesEstimateAt P S d CE ∧
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ)

/-- **The Gaussian inputs from Proposition 3.21 and the heat identity (H)**, both with constants
chosen before the law: the expectations (1) at the rate `r^{-d}` follow with a constant chosen
before the law (`expectedAveragesEstimateAt_of_energy_and_rate` with the energy bound below the
scale at `τ = 1`), and the heat identity in the lower-integral form `HeatPathwiseBound` with
kernel mass `(d + 1)/u` gives `HeatIdentityBound` (`heatIdentityBound_of_pathwise_of_rate`). -/
theorem uniformGaussianInputs_of_rate_heat (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hrate : ∃ C μ : ℝ → ℝ, (∀ τ : ℝ, 0 < τ → τ < d → 0 < C τ ∧ 0 < μ τ) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
        ∀ τ : ℝ, 0 < τ → τ < d → GaussianCorrectorRate P S τ (C τ) (μ τ))
    (hH : ∃ Ck : ℝ, ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ S : HomogenizationData P, ∃ k : ℝ → ℝ → Vec d → ℝ,
        (∀ r, Measurable (Function.uncurry (k r))) ∧ (∀ r u x, 0 < k r u x) ∧
        (∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹) ∧
        HeatPathwiseBound P S k) :
    UniformGaussianInputs d Λ := by
  obtain ⟨C, μ, hCμ, hrate⟩ := hrate
  obtain ⟨Ck, hH⟩ := hH
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1d : (1 : ℝ) < d := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨hC1, hμ1⟩ := hCμ 1 one_pos h1d
  obtain ⟨Cβ, hCβ, hCβb⟩ := periodizationError_le_rpow (d := d) (β := d) (by linarith)
  set CN : ℝ := gaussianRateEnergyScale 1 (C 1) Λ with hCN
  have hCN0 : 0 < CN :=
    lt_max_of_lt_left (mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hC1))
  have hc0 : 0 < (cellHeatLower d)⁻¹ := inv_pos.mpr (cellHeatLower_pos d)
  have hm : 0 ≤ momentConstant (1 / d) * CN ^ (d : ℝ) :=
    mul_nonneg (momentConstant_pos _).le (Real.rpow_nonneg hCN0.le _)
  refine ⟨C, μ, ((d : ℝ) + 1) * Cβ * (cellHeatLower d)⁻¹ * (Λ + 1) *
    (1 + CN * (1 + momentConstant (1 / d) * CN ^ (d : ℝ))), Ck, by positivity, hCμ,
    fun P hP => ?_⟩
  have := hP.1
  obtain ⟨S, hS⟩ := hrate P hP
  have hA := S.homogenizedMatrixBounds hΛ0
  have hN := (gaussianEnergyBound_of_rate_at S (fun ξ => (hA ξ).2) one_pos hμ1.le
    (hS 1 one_pos h1d)).2
  obtain ⟨k, hkm, hk0, hki, hpath⟩ := hH P hP S
  exact ⟨S, heatIdentityBound_of_pathwise_of_rate S hΛ0 hkm hk0 hki hpath one_pos hμ1
      (hS 1 one_pos h1d),
    expectedAveragesEstimateAt_of_energy_and_rate hd0 hP S hΛ0 hN hμ1 (hS 1 one_pos h1d) hCβ hCβb,
    hS⟩

theorem UniformGaussianInputs.uniformBaseFluctuation (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hG : UniformGaussianInputs d Λ) : UniformBaseFluctuation d Λ := by
  obtain ⟨C, μ, _, _, _, hCμ, hG⟩ := hG
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine uniformBaseFluctuation_of_rate hd hΛ fun u hu1 hu2 => ?_
  obtain ⟨hC, hμ⟩ := hCμ u (by linarith) (by linarith)
  refine ⟨C u, μ u, hC, hμ, fun P hP => ?_⟩
  obtain ⟨S, -, -, hr⟩ := hG P hP
  exact ⟨S, hr u (by linarith) (by linarith)⟩

theorem UniformGaussianInputs.hasJointHeatVersion (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hG : UniformGaussianInputs d Λ) (P : Measure (CoefficientField d Λ)) (hP : LawHypotheses P) :
    HasJointHeatVersion P := by
  obtain ⟨_, _, _, _, _, _, hG⟩ := hG
  obtain ⟨S, -⟩ := hG P hP
  exact hasJointHeatVersion_of_lawHypotheses hd hΛ hP S

/-- **The commutator and linear estimates at `(s, d/2)` with constants chosen before the law**,
from the Gaussian inputs and Propositions 4.10 and 4.11 with constants chosen before the law:
the bootstrap gives `Fluc(s, d/2)` with one constant for the jointly measurable versions of `J₁`
(`exists_uniform_flucEstimateAt_half_dim`), and Lemma 4.13 and the heat identity give the two
estimates (`exists_uniform_commutator_linear`, at `τ = (s d/2 + d)/2`). -/
theorem exists_uniform_commutator_linear_half_dim (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hG : UniformGaussianInputs d Λ) (h410 : UniformImprovementOfAdditivity d Λ)
    (h411 : UniformLocalizationEstimates d Λ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∃ Cc Cl : ℝ, 0 < Cc ∧ 0 < Cl ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ S : HomogenizationData P, CommutatorEstimateAt P S s ((d : ℝ) / 2) Cc ∧
        LinearAverageEstimateAt P S s ((d : ℝ) / 2) Cl := by
  have hbase := hG.uniformBaseFluctuation hd hΛ
  obtain ⟨C, μ, CE, Ck, hCE, hCμ, hG⟩ := hG
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb2 : 0 < (d : ℝ) / 2 := by linarith
  obtain ⟨CF, hCF, hF⟩ := exists_uniform_flucEstimateAt_half_dim hd hbase h410 h411 hs0 hs2
  set τ : ℝ := (s * ((d : ℝ) / 2) + d) / 2 with hτ
  have hτ1 : s * ((d : ℝ) / 2) ≤ τ := by rw [hτ]; nlinarith
  have hτ2 : τ < d := by rw [hτ]; nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτs : s ≤ τ / ((d : ℝ) / 2) := by rw [le_div_iff₀ hb2]; exact hτ1
  obtain ⟨hCτ, hμτ⟩ := hCμ τ hτ0 hτ2
  obtain ⟨Cc, Cl, hCc, hCl, h⟩ := exists_uniform_commutator_linear (Ck := Ck) hd hΛ
    hs0 hb2 le_rfl hCF hτ0 hCτ hμτ hCE hτs
  refine ⟨Cc, Cl, hCc, hCl, fun P hP => ?_⟩
  obtain ⟨S, hH, hE, hr⟩ := hG P hP
  obtain ⟨J, hJ⟩ := (hasJointHeatVersion_of_lawHypotheses hd hΛ hP S).exists_isBoundedJointVersion
    (by omega)
  exact ⟨S, h P hP S J hJ.measurable_slice hJ.2.2 (hF P hP J hJ) (hr τ hτ0 hτ2)
    (hE.mono hCE.le (by linarith)) hH⟩

/-- **The Gaussian gradient bound with constants chosen before the law**: the linear estimate
`|∫ Φ_{z,r} (ξ + ∇φ_ξ) - ξ| ≤ O_s(C (1 + |ξ|) r^{-d/2})` for every `s ∈ (0, 2)`, with `C` depending
only on `s, d, Λ`. -/
def UniformLinearAverageEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s : ℝ, 1 < Λ → 0 < s → s < 2 → ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∃ S : HomogenizationData P,
      ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
        OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ))
          s (C * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2)))

theorem uniformLinearAverageEstimate_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    UniformLinearAverageEstimate := by
  intro d hd Λ s hΛ hs0 hs2
  obtain ⟨hG, h410, h411⟩ := h d hd Λ hΛ
  obtain ⟨_, Cl, _, hCl, hP⟩ :=
    exists_uniform_commutator_linear_half_dim hd hΛ hG h410 h411 hs0 hs2
  exact ⟨Cl, hCl, fun P hPl => (hP P hPl).imp fun _ hS => hS.2⟩

/-- **(4.126), `QSH.Frozen.negativeSobolevCorrector`**, from the Gaussian inputs and
Propositions 4.10 and 4.11 with constants chosen before the law. -/
theorem negativeSobolevCorrector_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_commutator_linear fun d hd Λ hΛ => ?_
  obtain ⟨hG, h410, h411⟩ := h d hd Λ hΛ
  obtain ⟨Cc, Cl, hCc, hCl, hP⟩ :=
    exists_uniform_commutator_linear_half_dim hd hΛ hG h410 h411 one_pos one_lt_two
  exact ⟨Cc, Cl, hCc, hCl, hP⟩

/-- **Theorem 4.1, `QSH.Frozen.averagedCorrectorGradient`**, from the Gaussian inputs and
Propositions 4.10 and 4.11 with constants chosen before the law. -/
theorem averagedCorrectorGradient_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    QSH.Frozen.averagedCorrectorGradient := by
  refine averagedCorrectorGradient_of_linearAverage_uniform fun d hd Λ hΛ => ?_
  obtain ⟨hG, h410, h411⟩ := h d hd Λ hΛ
  obtain ⟨_, Cl, _, hCl, hP⟩ :=
    exists_uniform_commutator_linear_half_dim hd hΛ hG h410 h411 one_pos one_lt_two
  exact ⟨1, Cl, le_rfl, hCl, fun P hPl => (hP P hPl).imp fun _ hS => hS.2⟩

/-- **Theorem 4.6 (i) with constants chosen before the law**, `UniformAdditivityJ1`, from the
Gaussian inputs and Propositions 4.10 and 4.11 with constants chosen before the law. -/
theorem uniformAdditivityJ1_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    UniformAdditivityJ1 :=
  uniformAdditivityJ1_of_bootstrap
    (fun d hd Λ hΛ => ⟨(h d hd Λ hΛ).1.uniformBaseFluctuation hd hΛ, (h d hd Λ hΛ).2.1,
      (h d hd Λ hΛ).2.2⟩)
    fun d hd Λ hΛ => (h d hd Λ hΛ).1.hasJointHeatVersion hd hΛ

/-- **Theorem 4.6 (iii) with constants chosen before the law**, `UniformFluctuationJ1`, from the
Gaussian inputs and Propositions 4.10 and 4.11 with constants chosen before the law. -/
theorem uniformFluctuationJ1_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    UniformFluctuationJ1 :=
  uniformFluctuationJ1_of_bootstrap
    (fun d hd Λ hΛ => ⟨(h d hd Λ hΛ).1.uniformBaseFluctuation hd hΛ, (h d hd Λ hΛ).2.1,
      (h d hd Λ hΛ).2.2⟩)
    fun d hd Λ hΛ => (h d hd Λ hΛ).1.hasJointHeatVersion hd hΛ

theorem UniformGaussianInputs.nonempty_homogenizationData (hG : UniformGaussianInputs d Λ)
    (P : Measure (CoefficientField d Λ)) (hP : LawHypotheses P) :
    Nonempty (HomogenizationData P) := by
  obtain ⟨_, _, _, _, _, _, hG⟩ := hG
  obtain ⟨S, -⟩ := hG P hP
  exact ⟨S⟩

/-- **Lemma 5.29 (i), `QSH.Frozen.blockCLT`**, from the Gaussian inputs and Propositions 4.10 and
4.11 with constants chosen before the law. -/
theorem blockCLT_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    QSH.Frozen.blockCLT :=
  blockCLT_of_uniformAdditivityJ1 (uniformAdditivityJ1_of_uniform_inputs h)
    fun d hd Λ hΛ P hP => (h d hd Λ hΛ).1.nonempty_homogenizationData P hP

/-- **Lemma 5.29 (ii), `QSH.Frozen.blockBoundary`**, from the Gaussian inputs and
Propositions 4.10 and 4.11 with constants chosen before the law. -/
theorem blockBoundary_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    QSH.Frozen.blockBoundary :=
  blockBoundary_of_uniformAdditivityJ1 (uniformAdditivityJ1_of_uniform_inputs h)
    fun d hd Λ hΛ P hP => (h d hd Λ hΛ).1.nonempty_homogenizationData P hP

/-- **Lemma 5.29 (iii), `QSH.Frozen.blockChange`**, from the Gaussian inputs and
Propositions 4.10 and 4.11 with constants chosen before the law. -/
theorem blockChange_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ) :
    QSH.Frozen.blockChange :=
  blockChange_of_uniformAdditivityJ1 (uniformAdditivityJ1_of_uniform_inputs h)
    fun d hd Λ hΛ P hP => (h d hd Λ hΛ).1.nonempty_homogenizationData P hP

end QSH
