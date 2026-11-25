import QuantitativeStochasticHomogenization.Ch02.Sec03.MaximizerHatBound
import QuantitativeStochasticHomogenization.Ch02.Sec03.CoarseDeviationOs

/-!
# Theorem 2.17: the convergence of the maximizers of `J(□_m, p, q)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.3, Theorem 2.17, (2.66): for `d ≥ 2` there is `α(d, Λ) ∈ (0, 1/d]` such that for every
`s ∈ (0, d)` there is `C(s, d, Λ) < ∞` with, for every `p, q ∈ B₁` and `m ∈ ℕ`,
`‖∇v(·, □_m, p, q) - (ā⁻¹q - p)‖_{Ĥ̲⁻¹(□_m)} + ‖a∇v(·, □_m, p, q) - (q - āp)‖_{Ĥ̲⁻¹(□_m)} ≤
C 3^{m - mα(d-s)} + O₁(C 3^{m - ms})` (`theorem_2_17`).

The statement `X ≤ A + O₁(θ)` is written, as in (0.42), with one random variable `Y ≤ O₁(θ)`
(`OsBound P Y 1 θ`) such that `X ≤ A + Y` for every coefficient field; here `Y` does not depend on
`p, q ∈ B₁` nor on the choice of the maximizer, so no measurability of the left side is needed.
The hypotheses `d ≥ 2` and `Λ > 1` are those of Theorem 2.4 (`theorem_2_4`), on which the proof
rests.

The proof is the book's: the deterministic bound (2.67) (`vectorHat_defectMaximizer_le`), the
bound (2.68) of `E(m)` (`sqrt_coarseDeviation_le_os`) and the bound of
`J(□_m, ā⁻¹q, q)^{1/2}` by (2.65) (`sqrt_le_two_mul_sqrt_add_os`), both from Theorem 2.4 applied
with `(s + d)/2` instead of `s`, and Young's inequality (2.23) of Remark 2.6 with
`ρ = 3^{-mβ(d-s)}`, `β = 1/(2(2d - 1))`. The exponent is `α = min(α₀/4, β)`, `α₀` that of
Theorem 2.4.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **Theorem 2.17**, (2.66): for `d ≥ 2` and `Λ > 1` there is `α(d, Λ) ∈ (0, 1/d]` such that for
every `s ∈ (0, d)` there is `C(s, d, Λ) < ∞` with, for every law `P` satisfying (0.10)–(0.11) and
every `m ∈ ℕ`, a random variable `Y ≤ O₁(C 3^{m - ms})` such that for every coefficient field `a`,
`p, q ∈ B₁` and every maximizer `v = v(·, □_m, p, q)` of (2.9) of gradient `g`,
`‖∇v - (ā⁻¹q - p)‖_{Ĥ̲⁻¹(□_m)} + ‖a∇v - (q - āp)‖_{Ĥ̲⁻¹(□_m)} ≤ C 3^{m - mα(d-s)} + Y`. -/
theorem theorem_2_17 (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / d ∧ ∀ s : ℝ, 0 < s → s < d → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ m : ℕ,
        ∃ Y : CoefficientField d Λ → ℝ, OsBound P Y 1 (C * (3 : ℝ) ^ ((m : ℝ) - m * s)) ∧
          ∀ (a : CoefficientField d Λ) (p q : Vec d), p ∈ originBall d 1 →
            q ∈ originBall d 1 → ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
            IsDefectMaximizer a (triadicCube d m) p q v g →
            vectorHatNegativeSobolevNorm (triadicCube d m)
                (fun x => g x - ((homogenizedMatrix P)⁻¹.mulVec q - p)) +
              vectorHatNegativeSobolevNorm (triadicCube d m)
                (fun x => (a x).mulVec (g x) - (q - (homogenizedMatrix P).mulVec p)) ≤
            ENNReal.ofReal (C * (3 : ℝ) ^ ((m : ℝ) - m * α * (d - s)) + Y a) := by
  have : NeZero d := ⟨by omega⟩
  have hΛ0 : 0 ≤ Λ := by linarith
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h31 : (1 : ℝ) ≤ 3 := by norm_num
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨α₀, hα₀, hα₀', h24⟩ := theorem_2_4 hd hΛ
  obtain ⟨K₁, K₂, hK₁, hK₂, hA⟩ := vectorHat_defectMaximizer_le (d := d) (Λ := Λ)
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
  -- Theorem 2.4 at `(s + d)/2`
  obtain ⟨C₄, hC₄, h24s⟩ := h24 ((s + d) / 2) (by linarith) (by linarith)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = min (α₀ * ((d : ℝ) - (s + d) / 2)) 1 := ⟨_, rfl⟩
  have hγ1 : γ ≤ 1 := by rw [hγ]; exact min_le_right _ _
  have hγα : γ ≤ α₀ * ((d : ℝ) - (s + d) / 2) := by rw [hγ]; exact min_le_left _ _
  have hγds : γ ≤ (d : ℝ) - s := by
    have : α₀ * ((d : ℝ) - (s + d) / 2) ≤ 1 / 2 * ((d : ℝ) - (s + d) / 2) :=
      mul_le_mul_of_nonneg_right hα₀' (by linarith)
    linarith
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
  have hsG : 0 < √C₄ * G := mul_pos hsC hG0
  have hC0 : 0 < 2 + √C₄ * G + K_E := by linarith
  refine ⟨K₁ * (2 + √C₄ * G + K_E) + K₂ * (3 * √C₄),
    add_pos (mul_pos hK₁ hC0) (mul_pos hK₂ (by linarith)), fun P hP m => ?_⟩
  set α := min (α₀ / 4) β with hα
  have ht0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hT : (3 : ℝ) ^ m = (3 : ℝ) ^ (m : ℝ) := (Real.rpow_natCast 3 m).symm
  have hT0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (3 : ℝ) ^ (-((m : ℝ) * β * ((d : ℝ) - s))) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨V, hVos, hVle⟩ := hE P hP (h24γ P hP) m ρ hρ0
  obtain ⟨hWos, hWle⟩ := sqrt_le_two_mul_sqrt_add_os
    (c := C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))) (mul_pos hC₄ (Real.rpow_pos_of_pos h3 _))
    (h24γ P hP m)
  have hsq : √(C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))) = √C₄ * (3 : ℝ) ^ (-((m : ℝ) * (γ / 2))) := by
    rw [Real.sqrt_mul hC₄.le, Real.sqrt_eq_rpow ((3 : ℝ) ^ _), ← Real.rpow_mul h3.le]
    congr 2
    ring
  -- the scales of the random parts
  have hVs : K_E * ρ ^ (1 - 2 * (d : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) * ((s + d) / 2))) =
      K_E * (3 : ℝ) ^ (-((m : ℝ) * s)) := by
    rw [mul_assoc, hρ, ← Real.rpow_mul h3.le, ← Real.rpow_add h3]
    congr 2
    linear_combination ((m : ℝ) * ((d : ℝ) - s)) * hβ2
  have hWs : (√(C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))))⁻¹ *
      (C₄ * (3 : ℝ) ^ (-((m : ℝ) * ((s + d) / 2)))) ≤ √C₄ * (3 : ℝ) ^ (-((m : ℝ) * s)) := by
    have hinv : (√C₄)⁻¹ * C₄ = √C₄ := by
      rw [inv_mul_eq_div, div_eq_iff hsC.ne']
      exact (Real.mul_self_sqrt hC₄.le).symm
    rw [hsq, mul_inv, ← Real.rpow_neg h3.le]
    calc (√C₄)⁻¹ * (3 : ℝ) ^ (-(-((m : ℝ) * (γ / 2)))) *
          (C₄ * (3 : ℝ) ^ (-((m : ℝ) * ((s + d) / 2))))
        = ((√C₄)⁻¹ * C₄) * ((3 : ℝ) ^ (-(-((m : ℝ) * (γ / 2)))) *
            (3 : ℝ) ^ (-((m : ℝ) * ((s + d) / 2)))) := by ring
      _ = √C₄ * (3 : ℝ) ^ (-(-((m : ℝ) * (γ / 2))) + -((m : ℝ) * ((s + d) / 2))) := by
          rw [hinv, ← Real.rpow_add h3]
      _ ≤ √C₄ * (3 : ℝ) ^ (-((m : ℝ) * s)) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h31 ?_) hsC.le
          nlinarith [mul_nonneg ht0 (sub_nonneg.2 hγds)]
  have hR : (3 : ℝ) ^ m * (3 : ℝ) ^ (-((m : ℝ) * s)) = (3 : ℝ) ^ ((m : ℝ) - m * s) := by
    rw [hT, ← Real.rpow_add h3, ← sub_eq_add_neg]
  have hR0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) - m * s) := by positivity
  refine ⟨fun a => K₁ * (3 : ℝ) ^ m * V a + K₂ * (3 : ℝ) ^ m *
      ((√(C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))))⁻¹ *
        max (frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) +
          frobeniusNorm (coarseDualMatrix a (triadicCube d m) - homogenizedMatrix P) -
            C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))) 0), ?_, fun a p q hp hq v g hmax => ?_⟩
  · refine (osBound_add (hVos.const_mul (mul_pos hK₁ hT0)) (hWos.const_mul (mul_pos hK₂ hT0))
      le_rfl).mono_scale ?_
    rw [hVs]
    have i1 := mul_le_mul_of_nonneg_left hWs (mul_pos hK₂ hT0).le
    have e1 : K₁ * (3 : ℝ) ^ m * (K_E * (3 : ℝ) ^ (-((m : ℝ) * s))) =
        K₁ * K_E * ((3 : ℝ) ^ m * (3 : ℝ) ^ (-((m : ℝ) * s))) := by ring
    have e2 : K₂ * (3 : ℝ) ^ m * (√C₄ * (3 : ℝ) ^ (-((m : ℝ) * s))) =
        K₂ * √C₄ * ((3 : ℝ) ^ m * (3 : ℝ) ^ (-((m : ℝ) * s))) := by ring
    rw [e2, hR] at i1
    rw [e1, hR]
    have j1 := mul_nonneg (mul_nonneg hK₁.le (by linarith : (0 : ℝ) ≤ 2 + √C₄ * G)) hR0
    have j2 := mul_nonneg (mul_nonneg hK₂.le hsC.le) hR0
    linarith
  · dsimp only
    refine (hA P hP m a p q hp hq v g hmax).trans (ENNReal.ofReal_le_ofReal ?_)
    have hEa := hVle a
    have hFa : √(frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix a (triadicCube d m) - homogenizedMatrix P)) ≤
        2 * (√C₄ * (3 : ℝ) ^ (-((m : ℝ) * (γ / 2)))) +
          (√(C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))))⁻¹ *
            max (frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) +
              frobeniusNorm (coarseDualMatrix a (triadicCube d m) - homogenizedMatrix P) -
                C₄ * (3 : ℝ) ^ (-((m : ℝ) * γ))) 0 := by
      rw [← hsq]
      exact hWle a
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (3 : ℝ) ^ ((m : ℝ) - m * α * (d - s)) := ⟨_, rfl⟩
    rw [← hQ]
    have hmα : (m : ℝ) * (α * ((d : ℝ) - s)) ≤ (m : ℝ) * (γ / 2) :=
      mul_le_mul_of_nonneg_left hαγ ht0
    have hmγ : (m : ℝ) * γ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hγ1 ht0
    have hQ1 : 1 ≤ Q := by
      rw [hQ]
      refine Real.one_le_rpow h31 ?_
      linarith
    have hDQ : (3 : ℝ) ^ m * (3 : ℝ) ^ (-((m : ℝ) * (γ / 2))) ≤ Q := by
      rw [hT, ← Real.rpow_add h3, hQ]
      refine Real.rpow_le_rpow_of_exponent_le h31 ?_
      linarith
    have hρQ : (3 : ℝ) ^ m * ρ ≤ Q := by
      rw [hT, hρ, ← Real.rpow_add h3, hQ]
      refine Real.rpow_le_rpow_of_exponent_le h31 ?_
      have : (m : ℝ) * (α * ((d : ℝ) - s)) ≤ (m : ℝ) * (β * ((d : ℝ) - s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαβ hds.le) ht0
      linarith
    rw [← hG] at hEa
    have i1 := mul_le_mul_of_nonneg_left hEa (mul_pos hK₁ hT0).le
    have i2 := mul_le_mul_of_nonneg_left hFa (mul_pos hK₂ hT0).le
    have i3 := mul_le_mul_of_nonneg_left hDQ (mul_pos (mul_pos hK₁ hsC) hG0).le
    have i4 := mul_le_mul_of_nonneg_left hρQ hK₁.le
    have i5 := mul_le_mul_of_nonneg_left hDQ (mul_pos hK₂ hsC).le
    have i6 : K₁ ≤ K₁ * Q := le_mul_of_one_le_right hK₁.le hQ1
    have hKE : 0 ≤ K₁ * K_E * Q := mul_nonneg (mul_nonneg hK₁.le hK_E.le) (by linarith)
    have hK2 : 0 ≤ K₂ * √C₄ * Q := mul_nonneg (mul_nonneg hK₂.le hsC.le) (by linarith)
    linarith

end QSH
