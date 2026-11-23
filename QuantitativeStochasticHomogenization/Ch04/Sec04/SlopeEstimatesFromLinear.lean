import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationProof

/-!
# The single-slope estimate on the classes of laws with the linear estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21 on the classes of laws `LawHypotheses P ∧ ∃ S, GaussianGradientAverageBound P S s β C`
(the laws with the linear estimate at the exponent `β`), for every construction exponent
`α < β`: the excess decay of the subendpoint high-contrast homogenization at an exponent
`ϑ < 1` closes the exponent budget `(r/S)^ϑ S^{-β} ≤ r^{-γ}`, because
`(δ - ε) + β(1 + δ - ε) - γ ≥ (β - α)((1 + δ) - D/(1 + α)) > 0` with `D = α(1 + δ) + δ - γ`, and
the observation of the smoothed correctors is `smoothedCorrectorObservation_of_gaussianGradient`.
The only remaining input is the finite-ball observation (`FiniteBallObservation`).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The exponent budget for `α < β`.** -/
theorem exists_slope_budget {δ γ α β : ℝ} (hδ : 0 < δ) (hα : 0 < α) (hαβ : α < β)
    (hγ : 0 < γ) (hαγ : γ < α * (1 + δ) + δ) :
    ∃ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 ∧ ∀ r : ℝ, 1 ≤ r →
      (r / localizationIntermediateRadius δ α γ r) ^ ϑ *
        localizationIntermediateRadius δ α γ r ^ (-β) ≤ r ^ (-γ) := by
  set ε := localizationEpsilon δ α γ with hεdef
  have hε : 0 < ε := localizationEpsilon_pos hδ hα hαγ
  have hεδ : ε ≤ δ / 2 := min_le_right _ _
  have hεD : ε ≤ (α * (1 + δ) + δ - γ) / (1 + α) := min_le_left _ _
  have hδε : 0 < δ - ε := by linarith
  set q := (γ - β * (1 + δ - ε)) / (δ - ε) with hq
  -- the budget is strictly positive
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hδε]
    have h1 : ε * (1 + α) ≤ α * (1 + δ) + δ - γ := by
      rwa [le_div_iff₀ (by linarith)] at hεD
    have h2 : (α * (1 + δ) + δ - γ) < (1 + α) * (1 + δ) := by nlinarith
    have h3 : ε * (1 + α) * (1 + β) ≤ (α * (1 + δ) + δ - γ) * (1 + β) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have key : 0 < (β - α) * ((1 + α) * (1 + δ) - (α * (1 + δ) + δ - γ)) :=
      mul_pos (sub_pos.2 hαβ) (by linarith)
    have h4 : 0 < (1 + α) * (β * (1 + δ - ε) + δ - ε - γ) := by linarith
    have h5 := (mul_pos_iff_of_pos_left (by linarith : (0 : ℝ) < 1 + α)).1 h4
    linarith
  set ϑ := (1 + max 0 q) / 2 with hϑ
  have hm : max 0 q < 1 := max_lt one_pos hq1
  have hm0 := le_max_left 0 q
  refine ⟨ϑ, by rw [hϑ]; linarith, by rw [hϑ]; linarith, fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hS : localizationIntermediateRadius δ α γ r = r ^ (1 + δ - ε) := rfl
  rw [hS]
  have e1 : r / r ^ (1 + δ - ε) = r ^ (-(δ - ε)) := by
    rw [div_eq_iff (Real.rpow_pos_of_pos hr0 _).ne', ← Real.rpow_add hr0,
      show -(δ - ε) + (1 + δ - ε) = 1 by ring, Real.rpow_one]
  rw [e1, ← Real.rpow_mul hr0.le, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
  refine Real.rpow_le_rpow_of_exponent_le hr ?_
  have hϑq : q ≤ ϑ := by
    have := le_max_right 0 q
    linarith
  have h4 : q * (δ - ε) ≤ ϑ * (δ - ε) := mul_le_mul_of_nonneg_right hϑq hδε.le
  have h5 : q * (δ - ε) = γ - β * (1 + δ - ε) := by
    have := hδε.ne'
    rw [hq]; field_simp
  linarith

/-- **The single-slope estimate on the classes of laws with the linear estimate**, from the
finite-ball observation. -/
theorem slopeEstimateOnClass_of_linear_finiteBall (hd : 2 ≤ d) (hΛ : 1 < Λ)
    (hD : ∀ k : ℝ, 0 < k → ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      FiniteBallObservation d Λ σ θ k)
    {s β α δ γ C : ℝ} (hs1 : 1 < s) (hs2 : s < 2) (hα : 0 < α) (hαβ : α < β) (hδ : 0 < δ)
    (hγ : 0 < γ) (hαγ : γ < α * (1 + δ) + δ) (hγs : s * γ < d) (hC : 0 < C) :
    ∃ σ θ C₀ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
      SlopeEstimateOnClass (fun P : Measure (CoefficientField d Λ) => LawHypotheses P ∧
        ∃ S : HomogenizationData P, GaussianGradientAverageBound P S s β C) s δ γ α σ θ C₀ := by
  have hβ : 0 < β := hα.trans hαβ
  have hε : 0 < localizationEpsilon δ α γ := localizationEpsilon_pos hδ hα hαγ
  obtain ⟨ϑ, hϑ0, hϑ1, hexp⟩ := exists_slope_budget hδ hα hαβ hγ hαγ
  set k : ℝ := (d : ℝ) + 1 + β * (1 + δ) / localizationEpsilon δ α γ with hk
  have hk0 : 0 < k := by
    have h1 : 0 < β * (1 + δ) / localizationEpsilon δ α γ := div_pos (mul_pos hβ (by linarith)) hε
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hk]; linarith
  obtain ⟨σ, θ, hσ, hσ2, hθ, hθ2, hFB⟩ := hD k hk0
  obtain ⟨μ, C', hμ, hC', hG⟩ := smoothedCorrectorObservation_of_gaussianGradient (Λ := Λ)
    (β := β) hd hΛ hs1 hs2 hδ hα hαγ hγ hγs hσ hθ hC
  obtain ⟨C₀, hC₀, hslope⟩ := slopeEstimateOnClass_of_finiteBall_smoothed hd hΛ
    (Lw := fun P : Measure (CoefficientField d Λ) => LawHypotheses P ∧
      ∃ S : HomogenizationData P, GaussianGradientAverageBound P S s β C)
    (fun P h => h.1) hs1.le hδ hα hαγ hγ hγs hβ hσ hϑ0 hϑ1 hexp le_rfl hFB
    ⟨μ, C', hμ, hC', fun P ⟨hP, S, hS⟩ => ⟨S, hG P hP S hS⟩⟩
  exact ⟨σ, θ, C₀, hσ, hσ2, hθ, hθ2, hC₀, hslope C₀ le_rfl⟩

/-- **(5.85) from the finite-ball observation and the linear estimate at the exponent `d/2`**
with a constant chosen before the law. -/
theorem localizedEnergy_of_finiteBall_linear
    (hD : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ k : ℝ, 0 < k →
      ∃ σ θ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ FiniteBallObservation d Λ σ θ k)
    (hlin : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s : ℝ, 1 < Λ → 1 < s → s < 2 → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, GaussianGradientAverageBound P S s ((d : ℝ) / 2) C) :
    QSH.Frozen.localizedEnergy := by
  refine localizedEnergy_of_finiteBall_smoothed hD fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 α hα
    _ hαγ σ θ hσ hθ => ?_
  obtain ⟨C, hC, hS⟩ := hlin d hd Λ s hΛ hs1 hs2
  have hs0 : 0 < s := by linarith
  have hγ0 : 0 < γ := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 * (1 + δ) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hγs : s * γ < d := by
    have h := lt_of_lt_of_le hγ2 (min_le_left _ _)
    rw [lt_div_iff₀ hs0] at h
    linarith
  obtain ⟨μ, C', hμ, hC', hG⟩ := smoothedCorrectorObservation_of_gaussianGradient (Λ := Λ)
    (β := (d : ℝ) / 2) hd hΛ hs1 hs2 hδ hα hαγ hγ0 hγs hσ hθ hC
  refine ⟨μ, C', hμ, hC', fun P hP => ?_⟩
  obtain ⟨S, hSP⟩ := hS P hP
  exact ⟨S, hG P hP S hSP⟩

end QSH
