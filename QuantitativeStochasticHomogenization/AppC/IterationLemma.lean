import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# An iteration lemma for the Gehring estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.6: if `A, ξ ≥ 0` and `ρ : [1/2, 1) → [0, ∞)` satisfies
`sup_{t ∈ [1/2, 1)} (1 - t)^ξ ρ(t) < ∞` and `ρ(s) ≤ ρ(t)/2 + (t - s)^{-ξ} A` for all
`1/2 ≤ s < t < 1`, then `ρ(1/2) ≤ C A` for a constant `C(ξ)`.

The proof is the book's: with `M := sup_{t ∈ [1/2, 1)} (1 - t)^ξ ρ(t)` and `t := 1 - θ (1 - s)`,
multiplying the hypothesis by `(1 - s)^ξ` gives `(1 - s)^ξ ρ(s) ≤ (3/4) M + (1 - θ)^{-ξ} A`, hence
`M ≤ 4 (1 - θ)^{-ξ} A` and `ρ(1/2) ≤ 2^ξ M`. The book takes `θ = (3/4)^{1/ξ}` for `ξ > 0`; here
`θ = (2/3)^{1 / max ξ 1}`, which satisfies `θ^{-ξ} ≤ 3/2` also for `ξ = 0`.
-/

namespace QSH

/-- **Lemma C.6.** For `ξ ≥ 0` there is `C(ξ) < ∞` such that, if `A ≥ 0` and
`ρ : [1/2, 1) → [0, ∞)` has `sup_{t ∈ [1/2, 1)} (1 - t)^ξ ρ(t) < ∞` and
`ρ(s) ≤ ρ(t)/2 + (t - s)^{-ξ} A` for all `1/2 ≤ s < t < 1`, then `ρ(1/2) ≤ C A`. The book
assumes `ξ ≥ 0`; the proof below does not use it. -/
theorem lemma_C_6 (ξ : ℝ) :
    ∃ C : ℝ, ∀ (A : ℝ), 0 ≤ A → ∀ ρ : ℝ → ℝ, (∀ t ∈ Set.Ico (1 / 2 : ℝ) 1, 0 ≤ ρ t) →
      BddAbove ((fun t => (1 - t) ^ ξ * ρ t) '' Set.Ico (1 / 2 : ℝ) 1) →
      (∀ s t : ℝ, 1 / 2 ≤ s → s < t → t < 1 → ρ s ≤ 1 / 2 * ρ t + (t - s) ^ (-ξ) * A) →
      ρ (1 / 2) ≤ C * A := by
  set θ : ℝ := (2 / 3 : ℝ) ^ (1 / max ξ 1) with hθdef
  have hmax : 0 < max ξ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (one_div_pos.mpr hmax)
  have hθξ : 2 / 3 ≤ θ ^ ξ := by
    rw [hθdef, ← Real.rpow_mul (by norm_num), one_div_mul_eq_div]
    calc (2 / 3 : ℝ) = (2 / 3) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (2 / 3) ^ (ξ / max ξ 1) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
          (div_le_one_of_le₀ (le_max_left _ _) hmax.le)
  have hθneg : θ ^ (-ξ) ≤ 3 / 2 := by
    rw [Real.rpow_neg hθ0.le]
    calc (θ ^ ξ)⁻¹ ≤ (2 / 3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hθξ
      _ = 3 / 2 := by norm_num
  have hce : θ ^ ξ * θ ^ (-ξ) = 1 := by
    rw [← Real.rpow_add hθ0, add_neg_cancel, Real.rpow_zero]
  set K : ℝ := (1 - θ) ^ (-ξ) with hK
  refine ⟨2 ^ ξ * (4 * K), fun A hA ρ hρ hbdd h => ?_⟩
  set S := (fun t => (1 - t) ^ ξ * ρ t) '' Set.Ico (1 / 2 : ℝ) 1 with hS
  set M := sSup S with hM
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hSne : S.Nonempty := ⟨_, Set.mem_image_of_mem _ hhalf⟩
  have hle : ∀ t ∈ Set.Ico (1 / 2 : ℝ) 1, (1 - t) ^ ξ * ρ t ≤ M :=
    fun t ht => le_csSup hbdd (Set.mem_image_of_mem _ ht)
  have hM0 : 0 ≤ M :=
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hρ _ hhalf)).trans (hle _ hhalf)
  have key : ∀ s ∈ Set.Ico (1 / 2 : ℝ) 1, (1 - s) ^ ξ * ρ s ≤ 3 / 4 * M + K * A := by
    intro s ⟨hs1, hs2⟩
    set t : ℝ := 1 - θ * (1 - s) with htdef
    have h1s : 0 < 1 - s := by linarith
    have ht1 : 1 - t = θ * (1 - s) := by rw [htdef]; ring
    have hts : t - s = (1 - θ) * (1 - s) := by rw [htdef]; ring
    have hst : s < t := by nlinarith
    have ht : t < 1 := by nlinarith
    have hρst := h s t hs1 hst ht
    have hMt := hle t ⟨hs1.trans hst.le, ht⟩
    have hρt : 0 ≤ ρ t := hρ t ⟨hs1.trans hst.le, ht⟩
    have e1 : (1 - t) ^ ξ = θ ^ ξ * (1 - s) ^ ξ := by
      rw [ht1, Real.mul_rpow hθ0.le h1s.le]
    have e2 : (t - s) ^ (-ξ) = K * (1 - s) ^ (-ξ) := by
      rw [hts, Real.mul_rpow (by linarith) h1s.le]
    have hab : (1 - s) ^ ξ * (1 - s) ^ (-ξ) = 1 := by
      rw [← Real.rpow_add h1s, add_neg_cancel, Real.rpow_zero]
    have heq : (1 - s) ^ ξ * (1 / 2 * ρ t + (t - s) ^ (-ξ) * A) =
        1 / 2 * (θ ^ (-ξ) * ((1 - t) ^ ξ * ρ t)) + K * A := by
      rw [e1, e2]
      linear_combination (-(1 / 2) * (1 - s) ^ ξ * ρ t) * hce + (K * A) * hab
    have hX0 : 0 ≤ (1 - t) ^ ξ * ρ t := mul_nonneg (Real.rpow_nonneg (by linarith) _) hρt
    calc (1 - s) ^ ξ * ρ s ≤ (1 - s) ^ ξ * (1 / 2 * ρ t + (t - s) ^ (-ξ) * A) :=
          mul_le_mul_of_nonneg_left hρst (Real.rpow_nonneg h1s.le _)
      _ = 1 / 2 * (θ ^ (-ξ) * ((1 - t) ^ ξ * ρ t)) + K * A := heq
      _ ≤ 1 / 2 * (3 / 2 * M) + K * A := by
          have := mul_le_mul hθneg hMt hX0 (by norm_num)
          linarith
      _ = 3 / 4 * M + K * A := by ring
  have hMle : M ≤ 3 / 4 * M + K * A := csSup_le hSne (by
    rintro y ⟨s, hs, rfl⟩
    exact key s hs)
  have hM4 : M ≤ 4 * K * A := by linarith
  have hρhalf : (1 - 1 / 2 : ℝ) ^ ξ * ρ (1 / 2) ≤ M := hle _ hhalf
  have h2 : (2 : ℝ) ^ ξ * (1 - 1 / 2 : ℝ) ^ ξ = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  have h2pos : 0 ≤ (2 : ℝ) ^ ξ := Real.rpow_nonneg (by norm_num) _
  calc ρ (1 / 2) = (2 : ℝ) ^ ξ * ((1 - 1 / 2 : ℝ) ^ ξ * ρ (1 / 2)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ ξ * M := mul_le_mul_of_nonneg_left hρhalf h2pos
    _ ≤ 2 ^ ξ * (4 * K * A) := mul_le_mul_of_nonneg_left hM4 h2pos
    _ = 2 ^ ξ * (4 * K) * A := by ring

end QSH
