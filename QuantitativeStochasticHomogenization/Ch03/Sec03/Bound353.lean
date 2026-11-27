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

end QSH
