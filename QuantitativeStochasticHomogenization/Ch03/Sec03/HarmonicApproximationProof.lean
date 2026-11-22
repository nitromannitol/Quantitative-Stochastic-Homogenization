import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationCore

/-!
# Proof of the harmonic approximation (2) and the first-order Liouville theorem

`harmonicApproximation` proves `harmonicApproximationStatement` with `ν = μ/(d + 2)`: at the scale
`R`, with `η = R^{-ν} ≤ 1/8`, the one-scale harmonic approximation is applied to
`v = w - ℓ_{c,p}` and to the correctors recentred at their means on the ball `B_{LR} ⊇ E_R`, whose
`L²` norms are at most `|B_{LR}|^{1/2} C₁ (LR)^{1-μ}`. The error is
`ε = K₁ η ‖v‖_{L²(E_R)} + K₂ R^{-μ} η^{-d-1} ‖v‖_{L²(E_R)}`, and `R^{-μ} η^{-d-1} = η`. Dividing by
`|E_b|^{1/2}` with `|E_R| ≤ 2^d |E_b|` gives the normalized estimate. With the harmonic expansion,
`firstOrderLiouville` proves Theorem 3.8 for `k = 1` without hypotheses.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem HasWeakGradient.sub_const {f : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ f g) (c : ℝ) :
    HasWeakGradient Set.univ (fun x => f x - c) g := by
  have h2 := hasWeakGradient_add h (hasWeakGradient_const (-c))
  have e1 : (fun x => f x + -c) = fun x => f x - c := by funext x; ring
  have e2 : (fun x => g x + (0 : Vec d)) = g := by funext x; simp
  rw [e1, e2] at h2
  exact h2

theorem HasWeakDivergence.sub_const_field {F : Vec d → Vec d} {f : Vec d → ℝ}
    (h : HasWeakDivergence Set.univ F f) (c : Vec d) :
    HasWeakDivergence Set.univ (fun x => F x - c) f := by
  have h2 := hasWeakDivergence_add h (hasWeakDivergence_const_field (-c))
  have e1 : (fun x => F x + -c) = fun x => F x - c := by funext x; abel
  have e2 : (fun x => f x + (0 : ℝ)) = f := by funext x; simp
  rw [e1, e2] at h2
  exact h2

theorem memLp_component {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict U)) (l : Fin d) :
    MemLp (fun x => g x l) 2 (volume.restrict U) :=
  hg.of_le ((continuous_apply l).comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => norm_le_pi_norm (g x) l)

theorem memLp_coordinate_ball (R : ℝ) (i : Fin d) :
    MemLp (fun x : Vec d => x i) 2 (volume.restrict (ball (0 : Vec d) R)) := by
  refine (memLp_dot_ball (unitVector i) R).ae_eq (Eventually.of_forall fun x => ?_)
  exact dot_unitVector_left i x

theorem integral_sq_le_of_scalarRms_le {B : Set (Vec d)} {f : Vec d → ℝ} {T : ℝ}
    (hB : 0 < volume.real B) (h : scalarRms volume B f ≤ T) :
    ∫ x in B, f x ^ 2 ≤ volume.real B * T ^ 2 := by
  have hA : 0 ≤ ⨍ x in B, f x ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 measureReal_nonneg) (integral_nonneg fun x => sq_nonneg _)
  have h2 : ⨍ x in B, f x ^ 2 ≤ T ^ 2 := by
    have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    unfold scalarRms at h'
    rwa [Real.sq_sqrt hA] at h'
  rw [setAverage_eq, smul_eq_mul] at h2
  calc ∫ x in B, f x ^ 2 = volume.real B * ((volume.real B)⁻¹ * ∫ x in B, f x ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
    _ ≤ volume.real B * T ^ 2 := mul_le_mul_of_nonneg_left h2 hB.le

theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) n), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hx]

/-- `R^{1-μ} / (R η^{d+1}) = η` for `η = R^{-ν}`, `ν (d + 2) = μ`. -/
theorem rpow_div_mul_pow_eq {R μ : ℝ} (hR : 0 < R) :
    R ^ (1 - μ) / (R * (R ^ (-(μ / (d + 2)))) ^ (d + 1)) = R ^ (-(μ / (d + 2))) := by
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  set η := R ^ (-(μ / (d + 2))) with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos hR _
  have h1 : η ^ (d + 2) = R ^ (-μ) := by
    rw [hηdef, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    field_simp
  have h2 : R ^ (1 - μ) = R * η ^ (d + 2) := by
    rw [h1, sub_eq_add_neg, Real.rpow_add hR, Real.rpow_one]
  rw [h2, pow_succ]
  field_simp

/-- The error of the one-scale approximation in closed form. -/
theorem harmonicApproximation_error_eq {η R L μ V CK Kc N2 C₁ fM det nM Q : ℝ} (n : ℕ)
    (hη : 0 < η) (hR : 0 < R) (hL : 0 < L) (hV : 0 ≤ V) (hCK : 0 ≤ CK) (hKc : 0 ≤ Kc)
    (hdet : 0 < det) :
    n * (η ^ 2 * R) * (Real.sqrt (fM / det) * (Real.sqrt (Kc * N2) / (η * R))) +
        det⁻¹ * nM ^ 2 * (Q * (Real.sqrt (V * (L * R) ^ n) * (C₁ * (L * R) ^ (1 - μ))) *
          (Real.sqrt (Kc * N2) / (η * R))) * Real.sqrt ((η ^ 2 * R)⁻¹ ^ n * CK) =
      (n * Real.sqrt (fM / det) * Real.sqrt Kc * η +
        det⁻¹ * nM ^ 2 * Q * Real.sqrt V * Real.sqrt (L ^ n) * C₁ * L ^ (1 - μ) *
          Real.sqrt Kc * Real.sqrt CK * (R ^ (1 - μ) / (R * η ^ (n + 1)))) * Real.sqrt N2 := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have e1 : Real.sqrt (Kc * N2) = Real.sqrt Kc * Real.sqrt N2 := Real.sqrt_mul hKc _
  have e2 : Real.sqrt (V * (L * R) ^ n) = Real.sqrt V * Real.sqrt (L ^ n) * Real.sqrt R ^ n := by
    rw [Real.sqrt_mul hV, mul_pow, Real.sqrt_mul (pow_nonneg hL.le n), sqrt_pow_eq hR.le]
    ring
  have e3 : (L * R) ^ (1 - μ) = L ^ (1 - μ) * R ^ (1 - μ) := Real.mul_rpow hL.le hR.le
  have e4 : Real.sqrt ((η ^ 2 * R)⁻¹ ^ n * CK) = (η ^ n * Real.sqrt R ^ n)⁻¹ * Real.sqrt CK := by
    rw [Real.sqrt_mul (pow_nonneg (inv_nonneg.2 (by positivity)) n), inv_pow, Real.sqrt_inv,
      sqrt_pow_eq (by positivity), Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le, mul_pow]
  rw [e1, e2, e3, e4]
  field_simp
  ring

end QSH
