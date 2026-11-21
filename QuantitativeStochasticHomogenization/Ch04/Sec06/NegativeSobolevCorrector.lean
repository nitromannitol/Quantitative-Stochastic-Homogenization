import QuantitativeStochasticHomogenization.Ch04.Sec06.HeatNegativeNorm
import QuantitativeStochasticHomogenization.Frozen.NegativeSobolevCorrector

/-!
# Section 4.6: (4.126) from the heat bracket estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126) after Theorem 4.24, for `p = 2`, an integer `m > d/2` and `s = 1`. By
`negativeIntegerSobolevNorm_le_heatBracket`, the normalized `H^{-m}(B_1)` norms of the components of
`∇φ_e(·/ε)` and `a(·/ε)(e + ∇φ_e(·/ε)) - ā e` are bounded pathwise by a constant times their heat
brackets (`heatBracket (m - 1)`). The statement `QSH.Frozen.negativeSobolevCorrector` therefore follows
from the heat bracket estimate `HeatBracketEstimate`: measurable majorants `O_1(C ε^{d/2})` of the
heat brackets of these `2d` components, which hold almost surely together with the Gaussian moments
of the components (`negativeSobolevCorrector_of_heatBracket`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

theorem OsBound.max_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P X s θ) : OsBound P (fun ω => max (X ω) 0) s θ := by
  obtain ⟨hm, hs, hθ, hint⟩ := h
  refine ⟨hm.max measurable_const, hs, hθ, ?_⟩
  have h1 : ∀ ω, max (max (X ω) 0) 0 = max (X ω) 0 := fun ω => max_eq_left (le_max_right _ _)
  simp_rw [h1]
  exact hint

/-- A field with Gaussian moments: `F` is measurable and `F exp(-‖x‖²/16)` is integrable. -/
def HasGaussianMoment {d : ℕ} (F : Vec d → ℝ) : Prop :=
  AEStronglyMeasurable F volume ∧ Integrable (fun x => F x * Real.exp (-(‖x‖ ^ 2) / 16))

/-- **The heat bracket estimate** of order `m` for the corrector of `S` in the direction `e` at the
scale `ε`: the heat brackets of the components of `∇φ_e(·/ε)` and of
`a(·/ε)(e + ∇φ_e(·/ε)) - ā e` have measurable majorants `O_1(C ε^{d/2})`. -/
def HeatBracketEstimate {d : ℕ} {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (m : ℕ) (C : ℝ) (e : Vec d) (ε : ℝ) : Prop :=
  ∀ j : Fin d, ∃ Z₁ Z₂ : CoefficientField d Λ → ℝ,
    OsBound P Z₁ 1 (C * ε ^ ((d : ℝ) / 2)) ∧ OsBound P Z₂ 1 (C * ε ^ ((d : ℝ) / 2)) ∧
    ∀ᵐ a ∂P,
      (HasGaussianMoment (fun x => (S.corrector e).grad a (ε⁻¹ • x) j) ∧
        heatBracket (m - 1) (fun x => (S.corrector e).grad a (ε⁻¹ • x) j) ≤
          ENNReal.ofReal (Z₁ a)) ∧
      (HasGaussianMoment (fun x => ((a (ε⁻¹ • x)).mulVec (e + (S.corrector e).grad a (ε⁻¹ • x)) -
          S.homogenized.mulVec e) j) ∧
        heatBracket (m - 1) (fun x => ((a (ε⁻¹ • x)).mulVec
          (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) j) ≤
          ENNReal.ofReal (Z₂ a))

/-- **(4.126) from the heat bracket estimate.** -/
theorem negativeSobolevCorrector_of_heatBracket
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ m : ℕ, (d : ℝ) / 2 < m →
      ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → HeatBracketEstimate S m C e ε) :
    QSH.Frozen.negativeSobolevCorrector := by
  intro d hd Λ hΛ m hm
  obtain ⟨C, hC, hP⟩ := h d hd Λ hΛ m hm
  have hd1 : 1 ≤ d := by omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    have h0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    have h1 : 0 < m := by exact_mod_cast h0
    exact ⟨m - 1, by omega⟩
  set K := (volume (originBall d 1)).toReal⁻¹ * unitBallTestConstant d (n + 1) with hK
  have hKpos : 0 < K := mul_pos (inv_pos.mpr (ENNReal.toReal_pos volume_originBall_pos.ne'
    volume_originBall_lt_top.ne)) (unitBallTestConstant_pos d (n + 1))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨K * (2 * d * C), by positivity, fun P hPl => ?_⟩
  obtain ⟨S, hS⟩ := hP P hPl
  refine ⟨S, fun e he ε hε hε2 => ?_⟩
  choose Z₁ Z₂ hZ₁ hZ₂ hae using hS e he ε hε hε2
  have hsum : OsBound P (fun a => ∑ j : Fin d, (max (Z₁ j a) 0 + max (Z₂ j a) 0)) 1
      (∑ j : Fin d, (C * ε ^ ((d : ℝ) / 2) + C * ε ^ ((d : ℝ) / 2))) :=
    osBound_finset_sum Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ le_rfl fun j _ =>
      osBound_add (hZ₁ j).max_zero (hZ₂ j).max_zero le_rfl
  have hθ : K * ∑ j : Fin d, (C * ε ^ ((d : ℝ) / 2) + C * ε ^ ((d : ℝ) / 2)) =
      K * (2 * d * C) * ε ^ ((d : ℝ) / 2) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hZ := hsum.const_mul hKpos
  rw [hθ] at hZ
  refine ⟨fun a => K * ∑ j : Fin d, (max (Z₁ j a) 0 + max (Z₂ j a) 0), hZ.1, hZ, ?_⟩
  have hall := ae_all_iff.mpr hae
  filter_upwards [hall] with a ha
  simp only [Nat.add_sub_cancel] at ha
  unfold vectorNegativeIntegerSobolevNorm
  have hK0 : 0 ≤ K := hKpos.le
  have hnn : ∀ j, 0 ≤ max (Z₁ j a) 0 + max (Z₂ j a) 0 := fun j =>
    add_nonneg (le_max_right _ _) (le_max_right _ _)
  rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_sum_of_nonneg fun j _ => hnn j, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨⟨hG, hGb⟩, ⟨hF, hFb⟩⟩ := ha j
  rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), mul_add]
  refine add_le_add ?_ ?_
  · refine (negativeIntegerSobolevNorm_le_heatBracket hd1 n hG.1 hG.2).trans ?_
    gcongr
    exact hGb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · refine (negativeIntegerSobolevNorm_le_heatBracket hd1 n hF.1 hF.2).trans ?_
    gcongr
    exact hFb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

end QSH
