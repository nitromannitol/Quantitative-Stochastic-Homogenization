import QuantitativeStochasticHomogenization.Ch02.Sec03.CoarseDeviationOs

/-!
# The rate (2.68) of `E(m)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.3, (2.68) in the form used in the proofs of Theorems 2.17 and 2.18: for `d ≥ 2` and
`Λ > 1` there is `α(d, Λ) ∈ (0, 1/d]` such that for every `s ∈ (0, d)` there is `C(s, d, Λ)` with,
for every law satisfying the assumptions and every `m ∈ ℕ`, a random variable `V ≤ O₁(C 3^{-ms})`
such that `E(m)^{1/2} ≤ C 3^{-mα(d-s)} + V` for every coefficient field
(`exists_sqrt_coarseDeviation_le`). The proof is that of Theorem 2.17: Theorem 2.4 with
`(s + d)/2` in place of `s` and `sqrt_coarseDeviation_le_os` with `ρ = 3^{-mβ(d-s)}`,
`β = 1/(2(2d - 1))`; the exponent is `α = min(α₀/4, β)`, `α₀` that of Theorem 2.4.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **(2.68)**: `E(m)^{1/2} ≤ C 3^{-mα(d-s)} + O₁(C 3^{-ms})`. -/
theorem exists_sqrt_coarseDeviation_le (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / d ∧ ∀ s : ℝ, 0 < s → s < d → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ m : ℕ,
        ∃ V : CoefficientField d Λ → ℝ, OsBound P V 1 (C * (3 : ℝ) ^ (-((m : ℝ) * s))) ∧
          ∀ a : CoefficientField d Λ,
            √(coarseDeviation P m a) ≤ C * (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) + V a := by
  have : NeZero d := ⟨by omega⟩
  have hΛ0 : 0 ≤ Λ := by linarith
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h31 : (1 : ℝ) ≤ 3 := by norm_num
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨α₀, hα₀, hα₀', h24⟩ := theorem_2_4 hd hΛ
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 1 / (2 * (2 * d - 1)) := ⟨_, rfl⟩
  have h2d1 : (0 : ℝ) < 2 * d - 1 := by linarith
  have hβ0 : 0 < β := by rw [hβ]; exact div_pos one_pos (mul_pos two_pos h2d1)
  have hβ2 : β * (2 * d - 1) = 1 / 2 := by
    rw [hβ, one_div, inv_mul_eq_div, div_eq_iff (mul_pos two_pos h2d1).ne']
    ring
  refine ⟨min (α₀ / 4) β, lt_min (by linarith) hβ0, ?_, fun s hs hsd => ?_⟩
  · refine (min_le_right _ _).trans ?_
    rw [hβ, div_le_div_iff₀ (mul_pos two_pos h2d1) (by linarith)]
    linarith
  have hds : 0 < (d : ℝ) - s := by linarith
  have hαβ : min (α₀ / 4) β ≤ β := min_le_right _ _
  have hαα : min (α₀ / 4) β ≤ α₀ / 4 := min_le_left _ _
  obtain ⟨C₄, hC₄, h24s⟩ := h24 ((s + d) / 2) (by linarith) (by linarith)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = min (α₀ * ((d : ℝ) - (s + d) / 2)) 1 := ⟨_, rfl⟩
  have hγ1 : γ ≤ 1 := by rw [hγ]; exact min_le_right _ _
  have hγα : γ ≤ α₀ * ((d : ℝ) - (s + d) / 2) := by rw [hγ]; exact min_le_left _ _
  have hαγ : min (α₀ / 4) β * ((d : ℝ) - s) ≤ γ / 2 := by
    have i1 : min (α₀ / 4) β * ((d : ℝ) - s) ≤ α₀ / 4 * ((d : ℝ) - s) :=
      mul_le_mul_of_nonneg_right hαα hds.le
    have i2 : min (α₀ / 4) β * ((d : ℝ) - s) ≤ β * ((d : ℝ) - s) :=
      mul_le_mul_of_nonneg_right hαβ hds.le
    have i3 : β * ((d : ℝ) - s) ≤ β * (2 * d - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hβ0.le
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), hγ]
    exact le_min (by linarith) (by linarith)
  have h24γ : ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ n : ℕ,
      OsBound P (fun a =>
        frobeniusNorm (coarseMatrix a (triadicCube d n) - homogenizedMatrix P) +
          frobeniusNorm (coarseDualMatrix a (triadicCube d n) - homogenizedMatrix P) -
            C₄ * (3 : ℝ) ^ (-((n : ℝ) * γ))) 1 (C₄ * (3 : ℝ) ^ (-((n : ℝ) * ((s + d) / 2)))) := by
    intro P hP n
    refine (h24s P hP n).of_le (((measurable_frobeniusNorm_coarseMatrix_sub hΛ0
      (volume_triadicCube_ne_top d n) _).add (measurable_frobeniusNorm_coarseDualMatrix_sub hΛ0
        (volume_triadicCube_ne_zero d n) (volume_triadicCube_ne_top d n) _)).sub_const _)
      fun a => ?_
    have hn : (n : ℝ) * γ ≤ (n : ℝ) * α₀ * ((d : ℝ) - (s + d) / 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hγα (Nat.cast_nonneg n)
    have := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h31 (neg_le_neg hn))
      hC₄.le
    linarith
  obtain ⟨K_E, hK_E, hE⟩ := sqrt_coarseDeviation_le_os (σ := (s + d) / 2) hd hΛ0 hC₄ hC₄
    (by linarith) (by linarith) hγ1
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (1 - (3 : ℝ) ^ (γ / 2 - 1))⁻¹ := ⟨_, rfl⟩
  have hG0 : 0 < G := by
    rw [hG]
    have : (3 : ℝ) ^ (γ / 2 - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by linarith)
    exact inv_pos.mpr (by linarith)
  have hsC : 0 < √C₄ := Real.sqrt_pos.mpr hC₄
  refine ⟨√C₄ * G + 1 + K_E, by positivity, fun P hP m => ?_⟩
  set α := min (α₀ / 4) β with hα
  have ht0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (3 : ℝ) ^ (-((m : ℝ) * β * ((d : ℝ) - s))) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨V, hVos, hVle⟩ := hE P hP (h24γ P hP) m ρ hρ0
  have hVs : K_E * ρ ^ (1 - 2 * (d : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) * ((s + d) / 2))) =
      K_E * (3 : ℝ) ^ (-((m : ℝ) * s)) := by
    rw [mul_assoc, hρ, ← Real.rpow_mul h3.le, ← Real.rpow_add h3]
    congr 2
    linear_combination ((m : ℝ) * ((d : ℝ) - s)) * hβ2
  have hQ0 : 0 ≤ (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) := by positivity
  refine ⟨V, (hVos.mono_scale (le_of_eq hVs)).mono_scale ?_, fun a => ?_⟩
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ √C₄ * G + 1 := by positivity
    linarith
  have hEa := hVle a
  rw [← hG] at hEa
  have hD : (3 : ℝ) ^ (-((m : ℝ) * (γ / 2))) ≤ (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) := by
    refine Real.rpow_le_rpow_of_exponent_le h31 ?_
    have : (m : ℝ) * (α * ((d : ℝ) - s)) ≤ (m : ℝ) * (γ / 2) :=
      mul_le_mul_of_nonneg_left hαγ ht0
    rw [mul_assoc]
    linarith
  have hρQ : ρ ≤ (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) := by
    rw [hρ]
    refine Real.rpow_le_rpow_of_exponent_le h31 ?_
    have : (m : ℝ) * (α * ((d : ℝ) - s)) ≤ (m : ℝ) * (β * ((d : ℝ) - s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαβ hds.le) ht0
    rw [mul_assoc, mul_assoc]
    linarith
  have i1 := mul_le_mul_of_nonneg_left hD (mul_pos hsC hG0).le
  have i2 := mul_le_mul_of_nonneg_left (le_of_lt (lt_add_one (0 : ℝ))) hQ0
  have i3 : 0 ≤ K_E * (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) := mul_nonneg hK_E.le hQ0
  have e : (√C₄ * G + 1 + K_E) * (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) =
      √C₄ * G * (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) +
        (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) +
          K_E * (3 : ℝ) ^ (-((m : ℝ) * α * ((d : ℝ) - s))) := by ring
  rw [e]
  linarith

end QSH
