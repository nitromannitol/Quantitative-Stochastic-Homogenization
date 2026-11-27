import QuantitativeStochasticHomogenization.Ch03.Sec03.HomogeneousHarmonic
import QuantitativeStochasticHomogenization.Ch03.Sec03.Implication348

/-!
# The estimate (3.53) of the proof of (3.46)

Armstrong–Kuusi–Mourrat, Section 3.3, Step 1 of the proof of (3.46). For `q ∈ Ā_k` homogeneous of
degree `k ≥ 1` and the radii `r_m = 2^m r₀`, let `u_m` be solutions in `B_{r_m}` close to `q` as in
(3.52), `w_m = u_{m+1} - u_m`, `φ_m ∈ A_{k-1}` given by `(iii')_{k-1}` for `w_m`, and `p_m ∈ Ā_{k-1}`
given by `(i)_{k-1}` for `φ_m`. Then `v_n = u_n - ∑_{m<n} φ_m` satisfies (3.53),
`‖v_n - q‖_{L̲²(B_{r_j})} ≤ C r_j^{-δ} ‖q‖_{L̲²(B_{r_j})}` for `j ≤ n`, and its increments
`v_{n+1} - v_n = w_n - φ_n` are geometrically small on `B_{r_j}` (`bound_353`).
-/

open MeasureTheory Filter Set
open scoped Pointwise

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The norm of a homogeneous function of degree `k` on dilated balls. -/
theorem scalarRms_ball_homogeneous {k : ℕ} {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x) {t r : ℝ} (ht : 0 < t) :
    scalarRms volume (ball 0 (t * r)) q = t ^ k * scalarRms volume (ball 0 r) q := by
  have e := TwoScale.scalarRms_comp_smul ht (ball (0 : Vec d) r) q
  rw [smul_ball_zero ht] at e
  rw [← e]
  have e2 : (fun y => q (t • y)) = fun y => t ^ k * q y := funext (hq t ht)
  rw [e2, scalarRms_const_mul, abs_of_pos (pow_pos ht k)]

theorem rpow_combine_one {t ρ k δ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) :
    (ρ / (t * ρ)) ^ (k - δ / 2) * (t * ρ) ^ (-δ) * t ^ k = t ^ (-(δ / 2)) * ρ ^ (-δ) := by
  rw [show ρ / (t * ρ) = t⁻¹ by field_simp, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
    Real.mul_rpow ht.le hρ.le]
  have e : t ^ (-(k - δ / 2)) * t ^ (-δ) * t ^ k = t ^ (-(δ / 2)) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1; ring
  calc t ^ (-(k - δ / 2)) * (t ^ (-δ) * ρ ^ (-δ)) * t ^ k
      = (t ^ (-(k - δ / 2)) * t ^ (-δ) * t ^ k) * ρ ^ (-δ) := by ring
    _ = _ := by rw [e]

/-- (B1): the increment `w_m = u_{m+1} - u_m` of two solutions close to a homogeneous `q`. -/
theorem scalarRms_increment_le {k : ℕ} {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x)
    (hqL2 : ∀ r : ℝ, 0 < r → MemLp q 2 (volume.restrict (ball (0 : Vec d) r)))
    {r C δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hC : 0 ≤ C) {u₀ u₁ : Vec d → ℝ}
    (hu₀ : MemLp u₀ 2 (volume.restrict (ball (0 : Vec d) r)))
    (hu₁ : MemLp u₁ 2 (volume.restrict (ball (0 : Vec d) (2 * r))))
    (hb₀ : scalarRms volume (ball 0 r) (fun x => u₀ x - q x) ≤
      C * r ^ (-δ) * scalarRms volume (ball 0 r) q)
    (hb₁ : scalarRms volume (ball 0 (2 * r)) (fun x => u₁ x - q x) ≤
      C * (2 * r) ^ (-δ) * scalarRms volume (ball 0 (2 * r)) q) :
    scalarRms volume (ball 0 r) (fun x => u₁ x - u₀ x) ≤
      C * (Real.sqrt (2 ^ d) * 2 ^ k + 1) * r ^ (-δ) * scalarRms volume (ball 0 r) q := by
  have h2r : r ≤ 2 * r := by linarith
  have hu₁r : MemLp u₁ 2 (volume.restrict (ball (0 : Vec d) r)) :=
    hu₁.mono_measure (Measure.restrict_mono (ball_zero_subset_ball_zero h2r) le_rfl)
  have hqr := hqL2 r hr
  have e : (fun x => u₁ x - u₀ x) = fun x => (u₁ x - q x) - (u₀ x - q x) := by funext x; ring
  rw [e]
  refine (scalarRms_sub_le (hu₁r.sub hqr) (hu₀.sub hqr)).trans ?_
  have h1 := scalarRms_ball_le hr h2r (hu₁.sub (hqL2 _ (by linarith)))
  rw [show 2 * r / r = 2 by field_simp] at h1
  rw [scalarRms_ball_homogeneous hq two_pos] at hb₁
  have hpow : (2 * r) ^ (-δ) ≤ r ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hr h2r (by linarith)
  have hq0 := scalarRms_nonneg (d := d) (ball 0 r) q
  have hs := Real.sqrt_nonneg ((2 : ℝ) ^ d)
  calc scalarRms volume (ball 0 r) (fun x => u₁ x - q x) +
        scalarRms volume (ball 0 r) (fun x => u₀ x - q x)
      ≤ Real.sqrt (2 ^ d) * (C * (2 * r) ^ (-δ) * (2 ^ k * scalarRms volume (ball 0 r) q)) +
          C * r ^ (-δ) * scalarRms volume (ball 0 r) q :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hb₁ hs)) hb₀
    _ ≤ Real.sqrt (2 ^ d) * (C * r ^ (-δ) * (2 ^ k * scalarRms volume (ball 0 r) q)) +
          C * r ^ (-δ) * scalarRms volume (ball 0 r) q := by
        gcongr
    _ = _ := by ring

/-- (B2): the correction of `w` by `(iii')_{k-1}` on the smaller ball `B_ρ`, `ρ = R/t`. -/
theorem scalarRms_correction_small {k : ℕ} {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x) {ρ t C₃ K δ : ℝ} (hρ : 0 < ρ)
    (ht : 0 < t) (hC₃ : 0 ≤ C₃) {w φ : Vec d → ℝ}
    (hφ : scalarRms volume (ball 0 ρ) (fun x => w x - φ x) ≤
      C₃ * (ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) * scalarRms volume (ball 0 (t * ρ)) w)
    (hw : scalarRms volume (ball 0 (t * ρ)) w ≤
      K * (t * ρ) ^ (-δ) * scalarRms volume (ball 0 (t * ρ)) q) :
    scalarRms volume (ball 0 ρ) (fun x => w x - φ x) ≤
      C₃ * K * (t ^ (-(δ / 2)) * ρ ^ (-δ)) * scalarRms volume (ball 0 ρ) q := by
  rw [scalarRms_ball_homogeneous hq ht] at hw
  have hc : 0 ≤ C₃ * (ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) :=
    mul_nonneg hC₃ (Real.rpow_nonneg (by positivity) _)
  refine hφ.trans ((mul_le_mul_of_nonneg_left hw hc).trans (le_of_eq ?_))
  have e := rpow_combine_one (k := (k : ℝ)) (δ := δ) ht hρ
  rw [Real.rpow_natCast] at e
  calc C₃ * (ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) * (K * (t * ρ) ^ (-δ) *
        (t ^ k * scalarRms volume (ball 0 ρ) q))
      = C₃ * K * ((ρ / (t * ρ)) ^ ((k : ℝ) - δ / 2) * (t * ρ) ^ (-δ) * t ^ k) *
          scalarRms volume (ball 0 ρ) q := by ring
    _ = _ := by rw [e]

/-- (B4): the growth of a correction `φ` close to `p ∈ Ā_{k-1}` from `B_ρ` to `B_{tρ}`. -/
theorem scalarRms_correction_large {k : ℕ} (hk : 1 ≤ k) {q : Vec d → ℝ}
    (hq : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = t ^ k * q x)
    {ρ t r₀ C₁ C₂₇ C₃ K δ : ℝ} (hρ : 0 < ρ) (ht : 1 ≤ t) (hr₀ : 0 < r₀) (hr₀ρ : r₀ ≤ ρ)
    (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hsmall : C₁ * r₀ ^ (-δ) ≤ 1 / 2) (hC₂₇ : 0 ≤ C₂₇)
    (hC₃ : 0 ≤ C₃) (hK : 0 ≤ K) {w φ p : Vec d → ℝ}
    (hwL2 : MemLp w 2 (volume.restrict (ball (0 : Vec d) ρ)))
    (hφL2 : ∀ r : ℝ, 0 < r → MemLp φ 2 (volume.restrict (ball (0 : Vec d) r)))
    (hpL2 : ∀ r : ℝ, 0 < r → MemLp p 2 (volume.restrict (ball (0 : Vec d) r)))
    (hφp : ∀ R : ℝ, r₀ ≤ R → scalarRms volume (ball 0 R) (fun x => φ x - p x) ≤
      C₁ * R ^ (-δ) * scalarRms volume (ball 0 R) p)
    (hgrow : scalarRms volume (ball 0 (t * ρ)) p ≤ C₂₇ * t ^ (k - 1) * scalarRms volume (ball 0 ρ) p)
    (hφw : scalarRms volume (ball 0 ρ) (fun x => w x - φ x) ≤ C₃ * scalarRms volume (ball 0 ρ) w)
    (hw : scalarRms volume (ball 0 ρ) w ≤ K * ρ ^ (-δ) * scalarRms volume (ball 0 ρ) q) :
    scalarRms volume (ball 0 (t * ρ)) φ ≤
      4 * C₂₇ * (1 + C₃) * K * (t ^ (δ - 1) * (t * ρ) ^ (-δ)) *
        scalarRms volume (ball 0 (t * ρ)) q := by
  have ht0 : 0 < t := by linarith
  have htρ : 0 < t * ρ := mul_pos ht0 hρ
  have hr₀tρ : r₀ ≤ t * ρ := hr₀ρ.trans (by nlinarith)
  have hsm : ∀ R : ℝ, r₀ ≤ R → C₁ * R ^ (-δ) ≤ 1 / 2 := fun R hR =>
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr₀ hR (by linarith)) hC₁).trans
      hsmall
  -- `‖φ‖_{tρ} ≤ 2 ‖p‖_{tρ}` and `‖p‖_ρ ≤ 2 ‖φ‖_ρ`
  have h1 : scalarRms volume (ball 0 (t * ρ)) φ ≤ 2 * scalarRms volume (ball 0 (t * ρ)) p := by
    have h := scalarRms_le_add_of_sub (hpL2 _ htρ) (hφL2 _ htρ)
    have e : (fun x => p x - φ x) = fun x => -1 * (φ x - p x) := by funext x; ring
    rw [e, scalarRms_const_mul, abs_neg, abs_one, one_mul] at h
    have h' := hφp _ hr₀tρ
    have := hsm _ hr₀tρ
    have hp0 := scalarRms_nonneg (d := d) (ball 0 (t * ρ)) p
    nlinarith
  have h2 : scalarRms volume (ball 0 ρ) p ≤ 2 * scalarRms volume (ball 0 ρ) φ := by
    have h := scalarRms_le_add_of_sub (hφL2 _ hρ) (hpL2 _ hρ)
    have h' := hφp _ hr₀ρ
    have := hsm _ hr₀ρ
    have hp0 := scalarRms_nonneg (d := d) (ball 0 ρ) p
    nlinarith
  have h3 : scalarRms volume (ball 0 ρ) φ ≤ (1 + C₃) * scalarRms volume (ball 0 ρ) w := by
    have h := scalarRms_le_add_of_sub hwL2 (hφL2 _ hρ)
    linarith
  rw [scalarRms_ball_homogeneous hq ht0]
  have htk : t ^ (k - 1) * t = t ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have hpow : t ^ (k - 1) * ρ ^ (-δ) = t ^ (δ - 1) * (t * ρ) ^ (-δ) * t ^ k := by
    rw [Real.mul_rpow ht0.le hρ.le, ← htk]
    have e1 : t ^ (δ - 1) * t ^ (-δ) * t = 1 := by
      rw [← Real.rpow_add ht0, show δ - 1 + -δ = -1 by ring, Real.rpow_neg_one,
        inv_mul_cancel₀ ht0.ne']
    calc t ^ (k - 1) * ρ ^ (-δ) = t ^ (k - 1) * ρ ^ (-δ) * (t ^ (δ - 1) * t ^ (-δ) * t) := by
          rw [e1, mul_one]
      _ = _ := by ring
  have hw0 := scalarRms_nonneg (d := d) (ball 0 ρ) w
  calc scalarRms volume (ball 0 (t * ρ)) φ
      ≤ 2 * (C₂₇ * t ^ (k - 1) * (2 * ((1 + C₃) * (K * ρ ^ (-δ) *
          scalarRms volume (ball 0 ρ) q)))) := by
        refine h1.trans (mul_le_mul_of_nonneg_left (hgrow.trans ?_) (by norm_num))
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left hw (by linarith)))
          (by norm_num)
    _ = 4 * C₂₇ * (1 + C₃) * K * (t ^ (k - 1) * ρ ^ (-δ)) * scalarRms volume (ball 0 ρ) q := by
        ring
    _ = _ := by rw [hpow]; ring

end QSH
