import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianDuality
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatAverageDecay

/-!
# Small-time and large-time limits of tested heat smoothings

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1: for a field `f` with Gaussian moments and a smooth compactly supported test `ψ`,
`∫ f (Φ_t * ψ) → ∫ f ψ` as `t → 0`; and if `f - c` has a pairing bound at large scales then
`∫ f (Φ_t * ψ) → c ∫ ψ` as `t → ∞`. These are the two endpoints of the heat formula (6.7).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

private theorem euclideanSq_nonneg'' (v : Vec d) : 0 ≤ euclideanSq v := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun l _ => mul_self_nonneg _

/-- At small times the heat kernel is dominated by `Φ_2` away from the origin. -/
theorem euclideanHeatKernel_le_mul_two_of_le {t δ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ)
    {z : Vec d} (hz : δ ≤ euclideanNorm z) :
    euclideanHeatKernel t z ≤
      ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (d.factorial : ℝ) * (8 / δ ^ 2) ^ d *
        (8 * Real.pi) ^ ((d : ℝ) / 2)) * euclideanHeatKernel 2 z := by
  set S := euclideanSq z with hS
  have hS0 : 0 ≤ S := euclideanSq_nonneg'' z
  have hSδ : δ ^ 2 ≤ S := by
    have h := pow_le_pow_left₀ hδ.le hz 2
    rwa [euclideanNorm, Real.sq_sqrt hS0] at h
  set a : ℝ := δ ^ 2 / 8 with ha
  have ha0 : 0 < a := by positivity
  -- the exponential splits
  have hexp : Real.exp (-S / (4 * t)) ≤ Real.exp (-a / t) * Real.exp (-S / 8) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : a / t ≤ S / (8 * t) := by
      rw [ha, div_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : S / 8 ≤ S / (8 * t) := by
      exact div_le_div_of_nonneg_left hS0 (by positivity) (by nlinarith)
    have h3 : S / (4 * t) = S / (8 * t) + S / (8 * t) := by
      field_simp
      ring
    rw [neg_div, neg_div, neg_div]
    linarith
  -- the power of `t`
  have hpow : t ^ (-(d : ℝ) / 2) * Real.exp (-a / t) ≤ (d.factorial : ℝ) / a ^ d := by
    have hu : 0 ≤ a / t := by positivity
    have hfac := Real.pow_div_factorial_le_exp (a / t) hu d
    have h1 : t ^ (-(d : ℝ) / 2) ≤ (t⁻¹) ^ d := by
      rw [← Real.rpow_natCast, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
    have h2 : (t⁻¹) ^ d * Real.exp (-a / t) ≤ (d.factorial : ℝ) / a ^ d := by
      have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
      rw [div_pow, div_le_iff₀ (by positivity)] at hfac
      rw [le_div_iff₀ (by positivity), neg_div, Real.exp_neg]
      have hE : 0 < Real.exp (a / t) := Real.exp_pos _
      calc (t⁻¹) ^ d * (Real.exp (a / t))⁻¹ * a ^ d
          = (a ^ d / t ^ d) * (Real.exp (a / t))⁻¹ := by
            rw [inv_pow]; field_simp
        _ ≤ (d.factorial * Real.exp (a / t)) * (Real.exp (a / t))⁻¹ := by
            gcongr
            linarith [hfac]
        _ = d.factorial := by field_simp
    calc t ^ (-(d : ℝ) / 2) * Real.exp (-a / t) ≤ (t⁻¹) ^ d * Real.exp (-a / t) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := h2
  have hk2 : euclideanHeatKernel 2 z = (8 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-S / 8) := by
    unfold euclideanHeatKernel
    rw [← hS]
    congr 2 <;> ring
  rw [hk2]
  show (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-euclideanSq z / (4 * t)) ≤ _
  rw [← hS]
  have hfour : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) :=
    Real.mul_rpow (by positivity) ht.le
  rw [hfour]
  have hcancel : (8 * Real.pi) ^ ((d : ℝ) / 2) * (8 * Real.pi) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  have hfa : (d.factorial : ℝ) / a ^ d = d.factorial * (8 / δ ^ 2) ^ d := by
    rw [ha, div_pow, div_pow]
    have h8 : (0 : ℝ) < 8 ^ d := by positivity
    have hδd : (0 : ℝ) < (δ ^ 2) ^ d := by positivity
    field_simp
  calc (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-S / (4 * t))
      ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) *
          (Real.exp (-a / t) * Real.exp (-S / 8)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * (t ^ (-(d : ℝ) / 2) * Real.exp (-a / t)) *
          Real.exp (-S / 8) := by ring
    _ ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) / a ^ d) * Real.exp (-S / 8) := by
        gcongr
    _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * (8 / δ ^ 2) ^ d) *
          ((8 * Real.pi) ^ ((d : ℝ) / 2) * (8 * Real.pi) ^ (-(d : ℝ) / 2)) *
          Real.exp (-S / 8) := by rw [hfa, hcancel, mul_one]
    _ = _ := by ring

end QSH
