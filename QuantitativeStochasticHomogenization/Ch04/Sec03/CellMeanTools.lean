import QuantitativeStochasticHomogenization.Ch04.Sec03.PeriodicAverages
import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Elementary tools for the expectations of the Gaussian averages

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10, and Appendix A.

* `OsBound.integrable_of_nonneg`: a nonnegative `X ≤ O_s(θ)` is integrable for every `s > 0`
  (the moment bound (A.2) at order one: `y ≤ 1 + k! exp(y^s)` for `k s ≥ 1`).
* `heatKernel_zero_one_ge_of_mem_cell`: on the unit cell `[-1/2, 1/2)^d` the mask `Φ_{0,1}` is at
  least `(4π)^{-d/2} e^{-d/16}`.
* `exp_neg_le_rpow`: `exp(-4π²(r² - 1)) ≤ C_β r^{-β}` for `r ≥ 1`.
* `tendsto_periodizationError`: the periodization error tends to `0` along `r = n + 1`.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Moments of stochastic bounds -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem le_one_add_factorial_mul_exp_rpow {y s : ℝ} (hy : 0 ≤ y) (hs : 0 < s) :
    y ≤ 1 + (⌈s⁻¹⌉₊.factorial : ℝ) * Real.exp (y ^ s) := by
  set k := ⌈s⁻¹⌉₊ with hkdef
  have hk : 1 ≤ s * k := by
    have h1 : s⁻¹ ≤ (k : ℝ) := Nat.le_ceil _
    calc (1 : ℝ) = s * s⁻¹ := (mul_inv_cancel₀ hs.ne').symm
      _ ≤ s * k := mul_le_mul_of_nonneg_left h1 hs.le
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rcases le_or_gt y 1 with hy1 | hy1
  · have : 0 ≤ (k.factorial : ℝ) * Real.exp (y ^ s) := by positivity
    linarith
  · have h1 : y ≤ y ^ (s * k) := Real.self_le_rpow_of_one_le hy1.le hk
    have h2 : y ^ (s * k) = (y ^ s) ^ k := by
      rw [Real.rpow_mul hy, Real.rpow_natCast]
    have h3 : (y ^ s) ^ k / k.factorial ≤ Real.exp (y ^ s) :=
      Real.pow_div_factorial_le_exp _ (Real.rpow_nonneg hy _) k
    have h4 : (y ^ s) ^ k ≤ k.factorial * Real.exp (y ^ s) := by
      rw [div_le_iff₀ hf] at h3
      linarith
    linarith

/-- **A nonnegative `X ≤ O_s(θ)` is integrable**, for every exponent `s > 0`. -/
theorem OsBound.integrable_of_nonneg [IsFiniteMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P X s θ) (hX0 : ∀ ω, 0 ≤ X ω) : Integrable X P := by
  obtain ⟨hXm, hs, hθ, hint⟩ := h
  set k := ⌈s⁻¹⌉₊
  have hEm := measurable_osIntegrand hXm s θ
  have hEi : Integrable (fun ω => Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) P := by
    refine ⟨hEm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact hint.trans_lt (by norm_num)
  have hB : Integrable (fun ω => θ * (1 + (k.factorial : ℝ) *
      Real.exp ((θ⁻¹ * max (X ω) 0) ^ s))) P :=
    ((integrable_const 1).add (hEi.const_mul _)).const_mul _
  refine hB.mono' hXm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
  have hy : 0 ≤ θ⁻¹ * max (X ω) 0 := mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_right _ _)
  have h1 := le_one_add_factorial_mul_exp_rpow hy hs
  have h2 : X ω = θ * (θ⁻¹ * max (X ω) 0) := by
    rw [max_eq_left (hX0 ω), ← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
  calc X ω = θ * (θ⁻¹ * max (X ω) 0) := h2
    _ ≤ θ * (1 + (k.factorial : ℝ) * Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) :=
        mul_le_mul_of_nonneg_left h1 hθ.le

end Moments

/-! ## The mask on the unit cell -/

/-- The lower bound `(4π)^{-d/2} e^{-d/16}` of `Φ_{0,1}` on the unit cell. -/
def cellHeatLower (d : ℕ) : ℝ := (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) / 16)

theorem cellHeatLower_pos (d : ℕ) : 0 < cellHeatLower d := by
  unfold cellHeatLower; positivity

theorem heatKernel_zero_one_ge_of_mem_cell {x : Vec d}
    (hx : x ∈ latticeCell 1 (0 : LatticeIndex d)) : cellHeatLower d ≤ heatKernel 0 1 x := by
  unfold heatKernel euclideanHeatKernel cellHeatLower
  rw [one_pow, mul_one, sub_zero]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hsq : euclideanSq x ≤ (d : ℝ) / 4 := by
    unfold euclideanSq dot
    have hi : ∀ i, x i * x i ≤ 1 / 4 := by
      intro i
      obtain ⟨h1, h2⟩ := hx i
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_sub, zero_add] at h1 h2
      nlinarith
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = (d : ℝ) / 4 := by simp; ring
  have : -(d : ℝ) / 16 ≤ -euclideanSq x / 4 := by linarith
  linarith

/-! ## Decay of the periodization error -/

/-- `exp(-4π²(r² - 1)) ≤ C_β r^{-β}` for `r ≥ 1`. -/
theorem exp_neg_le_rpow {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) ≤ C * r ^ (-β) := by
  set k := ⌈β⌉₊ with hkdef
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  refine ⟨k.factorial * Real.exp (4 * Real.pi ^ 2), by positivity, fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hrβ : r ^ β ≤ r ^ (2 * k : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hr ?_
    have : β ≤ (k : ℝ) := Nat.le_ceil _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h2k : r ^ (2 * k : ℝ) = (r ^ 2) ^ k := by
    rw [Real.rpow_mul hr0.le, Real.rpow_natCast, Real.rpow_two]
  have hexp : (4 * Real.pi ^ 2 * r ^ 2) ^ k / k.factorial ≤ Real.exp (4 * Real.pi ^ 2 * r ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have hpow : (r ^ 2) ^ k ≤ (4 * Real.pi ^ 2 * r ^ 2) ^ k :=
    pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_left (by positivity) hπ) k
  have hmain : r ^ β ≤ k.factorial * Real.exp (4 * Real.pi ^ 2 * r ^ 2) := by
    rw [div_le_iff₀ hf] at hexp
    calc r ^ β ≤ (r ^ 2) ^ k := hrβ.trans h2k.le
      _ ≤ (4 * Real.pi ^ 2 * r ^ 2) ^ k := hpow
      _ ≤ _ := by linarith
  have hrβ0 : 0 < r ^ β := Real.rpow_pos_of_pos hr0 β
  rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, le_div_iff₀ hrβ0]
  calc Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) * r ^ β
      ≤ Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) *
        (k.factorial * Real.exp (4 * Real.pi ^ 2 * r ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ = k.factorial * Real.exp (4 * Real.pi ^ 2) := by
        rw [mul_comm, mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- The periodization error is nonnegative. -/
theorem periodizationError_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ (1 + thetaError (r ^ 2)) ^ d - 1 := by
  have h := thetaError_nonneg (show 0 < r ^ 2 by positivity)
  have : (1 : ℝ) ≤ (1 + thetaError (r ^ 2)) ^ d := one_le_pow₀ (by linarith)
  linarith

/-- **The periodization error at scale `r` is at most `C_β r^{-β}`** for `r ≥ 1`. -/
theorem periodizationError_le_rpow {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → (1 + thetaError (r ^ 2)) ^ d - 1 ≤ C * r ^ (-β) := by
  obtain ⟨C, hC, hCb⟩ := exp_neg_le_rpow hβ
  set K := (d : ℝ) * (1 + thetaError 1) ^ d * thetaError 1 with hKdef
  have hE1 := thetaError_nonneg (t := 1) one_pos
  have hK : 0 ≤ K := by positivity
  refine ⟨(K + 1) * C, by positivity, fun r hr => ?_⟩
  calc (1 + thetaError (r ^ 2)) ^ d - 1
      ≤ K * Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) := periodizationError_le hr
    _ ≤ K * (C * r ^ (-β)) := mul_le_mul_of_nonneg_left (hCb r hr) hK
    _ ≤ (K + 1) * (C * r ^ (-β)) := by
        have : 0 ≤ C * r ^ (-β) := by
          have := Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) (-β); positivity
        nlinarith
    _ = (K + 1) * C * r ^ (-β) := by ring

/-- The periodization error tends to `0` along the scales `n + 1`. -/
theorem tendsto_periodizationError :
    Tendsto (fun n : ℕ => (1 + thetaError (((n : ℝ) + 1) ^ 2)) ^ d - 1) atTop (𝓝 0) := by
  obtain ⟨C, hC, hCb⟩ := periodizationError_le_rpow (d := d) one_pos
  have hlim : Tendsto (fun n : ℕ => C * ((n : ℝ) + 1) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop one_pos).comp h1
    simpa using h2.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => periodizationError_nonneg (by positivity)) fun n => hCb _ ?_
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end QSH
