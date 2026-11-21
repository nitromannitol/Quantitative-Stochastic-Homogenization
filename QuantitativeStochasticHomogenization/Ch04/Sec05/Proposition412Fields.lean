import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationPointwise

/-!
# The centered localized fields of a bounded additive local quantity

For the proof of Proposition 4.12 of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Section 4.5, (4.107): given a bounded jointly measurable
field `J(a, z, r, p, q)` with `|J| ≤ M` and localized fields `J^{(δ)}` as in `LocFieldEstimate`, the
truncations `[J^{(δ)}]_M = max(-M, min(M, J^{(δ)}))` are within `|J - J^{(δ)}|` of `J`, and their
centerings are centered local fields; with `Add(s, α)` they are additive in the sense of (4.116).

Proved here: the truncation inequality (`abs_clamp_sub_le`), and the centered bound of a heat
average of a bounded field of stochastic bounds (`exists_centeredOsBound_heatAverage_sub`), from
Lemmas A.9 and A.10 applied to the probability measure `Φ_{x,ρ}(y) dy`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace QSH

variable {d : ℕ}

/-- The truncation at level `M`. -/
def clampAt (M v : ℝ) : ℝ := max (-M) (min M v)

theorem abs_clampAt_le {M : ℝ} (hM : 0 ≤ M) (v : ℝ) : |clampAt M v| ≤ M := by
  unfold clampAt
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampAt_zero {M : ℝ} (hM : 0 ≤ M) : clampAt M 0 = 0 := by
  unfold clampAt
  rw [min_eq_right hM, max_eq_right (by linarith)]

theorem continuous_clampAt (M : ℝ) : Continuous (clampAt M) := by
  unfold clampAt
  fun_prop

/-- **Truncation** brings a value closer to every point of `[-M, M]`. -/
theorem abs_clampAt_sub_le {M u v : ℝ} (hu : |u| ≤ M) : |clampAt M v - u| ≤ |v - u| := by
  unfold clampAt
  rw [abs_le] at hu
  obtain ⟨hu1, hu2⟩ := hu
  rcases le_total v M with h1 | h1 <;> rcases le_total (-M) v with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2]
  · rw [min_eq_right h1, max_eq_left h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The probability measure `Φ_{x,ρ}(y) dy`. -/
noncomputable def heatMeasure (x : Vec d) (ρ : ℝ) : Measure (Vec d) :=
  volume.withDensity fun y => (Real.toNNReal (heatKernel x ρ y) : ℝ≥0∞)

theorem measurable_heatKernel_right (x : Vec d) (ρ : ℝ) : Measurable (heatKernel x ρ) := by
  have : Continuous (heatKernel x ρ) := by
    unfold heatKernel euclideanHeatKernel euclideanSq dot
    fun_prop
  exact this.measurable

theorem integral_heatMeasure (x : Vec d) (ρ : ℝ) (g : Vec d → ℝ) :
    ∫ y, g y ∂heatMeasure x ρ = ∫ y, heatKernel x ρ y * g y := by
  unfold heatMeasure
  have hm : Measurable fun y => Real.toNNReal (heatKernel x ρ y) :=
    measurable_real_toNNReal.comp (measurable_heatKernel_right x ρ)
  rw [integral_withDensity_eq_integral_smul hm]
  congr 1
  funext y
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (heatKernel_nonneg x ρ y)]

theorem heatMeasure_univ (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) : heatMeasure x ρ Set.univ = 1 := by
  unfold heatMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral _ (by
      simpa only [Real.coe_toNNReal _ (heatKernel_nonneg x ρ _)] using integrable_heatKernel x hρ)]
  simp only [Real.coe_toNNReal _ (heatKernel_nonneg x ρ _)]
  rw [integral_heatKernel x hρ, ENNReal.ofReal_one]

instance (x : Vec d) (ρ : ℝ) [Fact (0 < ρ)] : IsProbabilityMeasure (heatMeasure x ρ) :=
  ⟨heatMeasure_univ x Fact.out⟩

/-- **Centered heat averages of stochastic bounds** (Lemmas A.9 and A.10 for `Φ_{x,ρ}(y) dy`): for
`s ∈ (1, 2]` there is `C(s)` such that for a bounded jointly measurable family `V(y)` with
`|V(y)| ≤ O_s(θ)`, `∫ Φ_{x,ρ} V - E[∫ Φ_{x,ρ} V] = 𝒪_s(C θ)`. -/
theorem exists_centeredOsBound_heatAverage_sub [IsProbabilityMeasure P] {s : ℝ} (hs1 : 1 < s)
    (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Vec d → Ω → ℝ) (θ B : ℝ) (x : Vec d) (ρ : ℝ), 0 < ρ →
      Measurable (Function.uncurry V) → (∀ y a, |V y a| ≤ B) →
      (∀ y, OsBound P (fun a => |V y a|) s θ) →
      CenteredOsBound P (fun a => (∫ y, heatKernel x ρ y * V y a) -
        ∫ a', (∫ y, heatKernel x ρ y * V y a') ∂P) s (C * θ) := by
  obtain ⟨C, hC, h⟩ := exists_centeredOsBound_integral_sub hs1 hs2
  refine ⟨C, hC, fun V θ B x ρ hρ hV hVB hVθ => ?_⟩
  have : Fact (0 < ρ) := ⟨hρ⟩
  have hne : heatMeasure x ρ ≠ 0 := by
    intro h0
    have := heatMeasure_univ x hρ
    rw [h0] at this
    simp at this
  have h1 := h P (heatMeasure x ρ) hne V θ B hV hVB hVθ
  rw [probReal_univ, one_mul] at h1
  simpa only [integral_heatMeasure] using h1

end QSH
