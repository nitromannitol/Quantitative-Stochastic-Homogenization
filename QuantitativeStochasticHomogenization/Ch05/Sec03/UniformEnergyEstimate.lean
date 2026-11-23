import QuantitativeStochasticHomogenization.Ch04.Sec06.UniformCorrectorEstimates
import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimates

/-!
# (5.58) with constants chosen before the law

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(5.58), Theorem 4.6 (ii) and (iii) and Remark 4.18.

`UniformExpectationEstimates d Λ` is (4.70) of Remark 4.18 with constants chosen before the law:
`Fluc(s, α)` with constant `C` for a bounded jointly measurable version of `J₁` gives
`|E[J₁(Φ_{z,r}, p, q)] - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ D r^{-2α}` with `D` depending only on
`s, α, C, d, Λ`. With the inputs of the bootstrap it gives (5.58) at `s = 1` with a constant
depending only on `d` and `Λ`, for every law and every homogenization data
(`uniformEnergyEstimate_of_uniform_inputs`): this is the hypothesis `h558` of
`coarsenedCoefficientEstimates_of_energyEstimate_liouville`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **(4.70) with constants chosen before the law**: for `s ∈ (0, 2)`, `α ∈ (0, d/2]` and every
constant `C` there is `D` such that, for every law satisfying the assumptions, homogenization data
`S` and bounded jointly measurable version `J` of `J₁`, `Fluc(s, α)` for `J` with constant `C`
gives `|E[J₁(Φ_{z,r}, p, q)] - (½ p·āp + ½ q·ā⁻¹q - p·q)| ≤ D r^{-2α}`. -/
def UniformExpectationEstimates (d : ℕ) (Λ : ℝ) : Prop :=
  ∀ s α C : ℝ, 0 < s → s < 2 → 0 < α → α ≤ (d : ℝ) / 2 → 0 < C → ∃ D : ℝ, 0 < D ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
      ∀ J, IsBoundedJointVersion P J → FlucEstimateAt P J s α C →
        ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
          euclideanNorm p < 1 → euclideanNorm q < 1 →
          |(∫ a, J1Heat a z r p q ∂P) - homogenizedJ1 S.homogenized p q| ≤ D * r ^ (-(2 * α))

/-- **(5.58) at `s = 1` with a constant chosen before the law**, for every law and every
homogenization data, from the Gaussian inputs and Propositions 4.10 and 4.11 and (4.70) with
constants chosen before the law: `Fluc(1, d/2)` for a version (the bootstrap) and the bias
`D r^{-d} ≤ D r^{-d/2}`. -/
theorem uniformEnergyEstimate_of_uniform_inputs
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → UniformGaussianInputs d Λ ∧
      UniformImprovementOfAdditivity d Λ ∧ UniformLocalizationEstimates d Λ ∧
      UniformExpectationEstimates d Λ) :
    ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀ := by
  intro d hd Λ hΛ
  obtain ⟨hG, h410, h411, hbias⟩ := h d hd Λ hΛ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb2 : 0 < (d : ℝ) / 2 := by linarith
  obtain ⟨CF, hCF, hF⟩ := exists_uniform_flucEstimateAt_half_dim hd
    (hG.uniformBaseFluctuation hd hΛ) h410 h411 one_pos one_lt_two
  obtain ⟨D, hD, hE⟩ := hbias 1 ((d : ℝ) / 2) CF one_pos one_lt_two hb2 le_rfl hCF
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨CF + D / Real.log 2, add_pos hCF (div_pos hD hl), fun P hP S z r hr p q hp hq => ?_⟩
  have := hP.1
  obtain ⟨J, hJ⟩ := (hG.hasJointHeatVersion hd hΛ P hP).exists_isBoundedJointVersion (by omega)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨-, hb⟩ := hF P hP J hJ z r hr p q hp hq
  have he : (fun a => J a z r p q) =ᵐ[P] fun a => J1Heat a z r p q :=
    hJ.2.2.mono fun a ha => ha z r p q
  have hint : ∫ a', J a' z r p q ∂P = ∫ a', J1Heat a' z r p q ∂P := integral_congr_ae he
  set c := homogenizedJ1 S.homogenized p q with hc
  have hbE : |(∫ a', J a' z r p q ∂P) - c| ≤ D * r ^ (-((d : ℝ) / 2)) := by
    have h1 := hE P hP S J hJ (hF P hP J hJ) z r hr p q hp hq
    rw [← hint, ← hc] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hconst : OsBound P (fun _ => D * r ^ (-((d : ℝ) / 2))) 1
      (D * r ^ (-((d : ℝ) / 2)) / Real.log 2 ^ (1 : ℝ)⁻¹) :=
    osBound_of_le_const measurable_const one_pos (by positivity)
      (Eventually.of_forall fun _ => le_rfl)
  have hsum := osBound_add hb hconst le_rfl
  have hJz : Measurable fun a : CoefficientField d Λ => J a z r p q :=
    (hJ.measurable_slice r p q).comp (measurable_id.prodMk measurable_const)
  have hm : Measurable fun a => |J a z r p q - c| :=
    continuous_abs.measurable.comp (hJz.sub measurable_const)
  have hle : ∀ a, |J a z r p q - c| ≤
      |J a z r p q - ∫ a', J a' z r p q ∂P| + D * r ^ (-((d : ℝ) / 2)) := fun a => by
    have := abs_sub_le (J a z r p q) (∫ a', J a' z r p q ∂P) c
    linarith
  have hos := (hsum.of_le hm hle).mono_scale (le_of_eq (show
      CF * r ^ (-((d : ℝ) / 2)) + D * r ^ (-((d : ℝ) / 2)) / Real.log 2 ^ (1 : ℝ)⁻¹ =
        (CF + D / Real.log 2) * r ^ (-(d : ℝ) / 2) by
    rw [inv_one, Real.rpow_one, neg_div]; ring))
  refine hos.aeOsBound_congr ?_
  filter_upwards [hJ.2.2] with a ha
  rw [ha z r p q]

end QSH
