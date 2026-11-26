import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoliLemma
import QuantitativeStochasticHomogenization.AppB.TheoremB8
import QuantitativeStochasticHomogenization.Ch01.Sec05.BoundaryLayer

/-!
# Convex domains have boundary density

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the hypothesis of the global Meyers estimate (Theorem C.7) used in the proof of Theorem 1.17, for
convex domains: a bounded open convex `U ⊆ B_R` containing the ball `B_ρ(x₀)` satisfies
`HasBoundaryDensity U c (2R)` with `c = min (2^{-d}) ((ρ/(2R + ρ))^d)`
(`hasBoundaryDensity_of_convex`). At `z ∈ ∂U`:

* outside, a supporting half-space at `z` (Hahn–Banach) contains the ball of radius `r/2` tangent
  to it at `z`, which lies in `B_r(z) \ U`;
* inside, the open segments from `z ∈ closure U` to the points of `B_ρ(x₀)` lie in `U`, so `U`
  contains the ball `z + t (B_ρ(x₀) - z)` of radius `tρ`, `t = r/(2R + ρ)`, which lies in
  `B_r(z)`.
-/

open MeasureTheory Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanNorm_add_le' (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y :=
  PDE.vecEuclideanNorm_add_le x y

/-- A continuous linear functional on `ℝ^d` is the pairing with the vector of its values on the
coordinate vectors. -/
theorem continuousLinearMap_apply_eq_dot (f : Vec d →L[ℝ] ℝ) (y : Vec d) :
    f y = dot (fun i => f (Pi.single i 1)) y := by
  conv_lhs => rw [pi_eq_sum_univ y]
  simp only [map_sum, map_smul, smul_eq_mul, dot]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- **Exterior density at the boundary of an open convex set**: for `z ∉ U` and `r > 0`, the ball
of radius `r/2` tangent at `z` to a supporting half-space lies in `B_r(z) \ U`. -/
theorem exists_ball_subset_ball_sdiff_of_convex {U : Set (Vec d)} (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hne : U.Nonempty) {z : Vec d} (hz : z ∉ U) {r : ℝ} (hr : 0 < r) :
    ∃ c : Vec d, ball c (r / 2) ⊆ ball z r \ U := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUc hUo hz
  obtain ⟨x₀, hx₀⟩ := hne
  set n : Vec d := fun i => f (Pi.single i 1) with hn
  have hfn : ∀ y, f y = dot n y := fun y => continuousLinearMap_apply_eq_dot f y
  have hN0 : 0 < euclideanNorm n := by
    have h := hf x₀ hx₀
    rw [hfn, hfn] at h
    by_contra hle
    have h0 : euclideanNorm n = 0 := le_antisymm (not_lt.mp hle) (Real.sqrt_nonneg _)
    have hn0 : n = 0 := (PDE.vecEuclideanNorm_eq_zero_iff).1 h0
    simp [hn0, dot] at h
  refine ⟨z + (r / 2 * (euclideanNorm n)⁻¹) • n, fun y hy => ?_⟩
  have hw : euclideanNorm (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n)) < r / 2 := hy
  have hyz : y - z = (r / 2 * (euclideanNorm n)⁻¹) • n +
      (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n)) := by abel
  have hnn : dot n n = euclideanNorm n ^ 2 := by
    rw [euclideanNorm, Real.sq_sqrt (show 0 ≤ euclideanSq n by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (n i))]
    rfl
  have hcs : |dot n (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n))| ≤
      euclideanNorm n * euclideanNorm (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n)) :=
    PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
  have hdot : dot n (y - z) = r / 2 * euclideanNorm n +
      dot n (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n)) := by
    have e : ∀ w : Vec d, dot n ((r / 2 * (euclideanNorm n)⁻¹) • n + w) =
        r / 2 * (euclideanNorm n)⁻¹ * dot n n + dot n w := fun w => by
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hyz, e, hnn, sq, ← mul_assoc, mul_assoc (r / 2), inv_mul_cancel₀ hN0.ne', mul_one]
  constructor
  · show euclideanNorm (y - z) < r
    rw [hyz]
    refine lt_of_le_of_lt (euclideanNorm_add_le' _ _) ?_
    rw [euclideanNorm_const_smul, abs_of_pos (mul_pos (half_pos hr) (inv_pos.2 hN0)), mul_assoc,
      inv_mul_cancel₀ hN0.ne', mul_one]
    linarith
  · intro hyU
    have h1 := hf y hyU
    rw [hfn, hfn] at h1
    have h2 : dot n (y - z) = dot n y - dot n z := by
      simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have h3 := neg_abs_le (dot n (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n)))
    have h4 : euclideanNorm n * euclideanNorm (y - (z + (r / 2 * (euclideanNorm n)⁻¹) • n)) <
        euclideanNorm n * (r / 2) := mul_lt_mul_of_pos_left hw hN0
    linarith

/-- **Interior density at the boundary of an open convex set**: for `z ∈ closure U`, `U ⊆ B_R`,
`B_ρ(x₀) ⊆ U` and `0 < r ≤ 2R`, `U ∩ B_r(z)` contains a ball of radius `rρ/(2R + ρ)`. -/
theorem exists_ball_subset_ball_inter_of_convex {U : Set (Vec d)} (hUo : IsOpen U)
    (hUc : Convex ℝ U) {x₀ : Vec d} {ρ R : ℝ} (hρ : 0 < ρ) (hball : ball x₀ ρ ⊆ U)
    (hUR : U ⊆ ball 0 R) {z : Vec d} (hz : z ∈ closure U) {r : ℝ} (hr : 0 < r)
    (hrR : r ≤ 2 * R) :
    ∃ c : Vec d, ball c (r / (2 * R + ρ) * ρ) ⊆ ball z r ∩ U := by
  have hx₀U : x₀ ∈ U := hball (by
    show euclideanNorm (x₀ - x₀) < ρ
    simp [euclideanNorm, euclideanSq, dot, hρ])
  have hx₀R : euclideanNorm x₀ < R := by
    have := hUR hx₀U
    simpa [ball] using this
  have hR : 0 < R := lt_of_le_of_lt (Real.sqrt_nonneg _) hx₀R
  have hzR : euclideanNorm z ≤ R := by
    have hcl : closure U ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le ?_ continuous_const)
      · have := hUR hx
        simp only [ball, sub_zero, mem_ofPred_eq] at this
        exact this.le
      · unfold euclideanNorm euclideanSq dot
        exact (continuous_finsetSum _ fun i _ =>
          (continuous_apply i).mul (continuous_apply i)).sqrt
    exact hcl hz
  have hden : (0 : ℝ) < 2 * R + ρ := by linarith
  set t : ℝ := r / (2 * R + ρ) with ht
  have ht0 : 0 < t := div_pos hr hden
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hden]
    linarith
  refine ⟨z + t • (x₀ - z), fun y hy => ?_⟩
  have hw : euclideanNorm (y - (z + t • (x₀ - z))) < t * ρ := hy
  have hy₀ : x₀ + t⁻¹ • (y - (z + t • (x₀ - z))) ∈ U := by
    refine hball ?_
    show euclideanNorm (x₀ + t⁻¹ • (y - (z + t • (x₀ - z))) - x₀) < ρ
    rw [add_sub_cancel_left, euclideanNorm_const_smul, abs_of_pos (inv_pos.2 ht0),
      inv_mul_lt_iff₀ ht0]
    exact hw
  have hseg : y ∈ openSegment ℝ z (x₀ + t⁻¹ • (y - (z + t • (x₀ - z)))) := by
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    module
  have hyU : y ∈ U := by
    have h := hUc.openSegment_closure_interior_subset_interior hz
      (by rwa [hUo.interior_eq]) hseg
    rwa [hUo.interior_eq] at h
  refine ⟨?_, hyU⟩
  show euclideanNorm (y - z) < r
  have hyz : y - z = t • (x₀ - z) + (y - (z + t • (x₀ - z))) := by abel
  rw [hyz]
  refine lt_of_le_of_lt (euclideanNorm_add_le' _ _) ?_
  rw [euclideanNorm_const_smul, abs_of_pos ht0]
  have hxz : euclideanNorm (x₀ - z) ≤ 2 * R := by
    have h1 : euclideanNorm (x₀ + -z) ≤ euclideanNorm x₀ + euclideanNorm (-z) :=
      euclideanNorm_add_le' _ _
    have h2 : euclideanNorm (-z) = euclideanNorm z := PDE.vecEuclideanNorm_neg z
    rw [← sub_eq_add_neg, h2] at h1
    linarith
  have h3 : t * euclideanNorm (x₀ - z) ≤ t * (2 * R) := mul_le_mul_of_nonneg_left hxz ht0.le
  have h4 : t * (2 * R) + t * ρ = r := by
    rw [← mul_add, ht, div_mul_cancel₀ r hden.ne']
  linarith

/-- **Bounded open convex sets have boundary density**: if `U` is open and convex,
`B_ρ(x₀) ⊆ U ⊆ B_R`, then `HasBoundaryDensity U (min (2^{-d}) ((ρ/(2R + ρ))^d)) (2R)`. -/
theorem hasBoundaryDensity_of_convex {U : Set (Vec d)} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {x₀ : Vec d} {ρ R : ℝ} (hρ : 0 < ρ) (hball : ball x₀ ρ ⊆ U) (hUR : U ⊆ ball 0 R) :
    HasBoundaryDensity U (min ((1 / 2 : ℝ) ^ d) ((ρ / (2 * R + ρ)) ^ d)) (2 * R) := by
  have hx₀U : x₀ ∈ U := hball (by
    show euclideanNorm (x₀ - x₀) < ρ
    simp [euclideanNorm, euclideanSq, dot, hρ])
  have hR : 0 < R := by
    have := hUR hx₀U
    simp only [ball, sub_zero, mem_ofPred_eq] at this
    exact lt_of_le_of_lt (Real.sqrt_nonneg _) this
  intro z hz r hr hrR
  rw [hUo.frontier_eq] at hz
  have hκ : 0 ≤ (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := ENNReal.toReal_nonneg
  have hfin : volume (ball z r) ≠ ⊤ := volume_ball_ne_top' z r
  constructor
  · obtain ⟨c, hc⟩ := exists_ball_subset_ball_inter_of_convex hUo hUc hρ hball hUR hz.1 hr hrR
    have h1 := measureReal_mono hc (measure_ne_top_of_subset inter_subset_left hfin)
    rw [volume_real_ball_eq_unit c (mul_pos (div_pos hr (by linarith)) hρ)] at h1
    rw [volume_real_ball_eq_unit z hr]
    have e : (r / (2 * R + ρ) * ρ) ^ d = (ρ / (2 * R + ρ)) ^ d * r ^ d := by
      rw [← mul_pow]
      congr 1
      ring
    rw [e] at h1
    have h2 : min ((1 / 2 : ℝ) ^ d) ((ρ / (2 * R + ρ)) ^ d) * (r ^ d *
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) ≤
        (ρ / (2 * R + ρ)) ^ d * (r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    rw [mul_assoc] at h1
    exact h2.trans h1
  · obtain ⟨c, hc⟩ := exists_ball_subset_ball_sdiff_of_convex hUo hUc ⟨x₀, hx₀U⟩ hz.2 hr
    have h1 := measureReal_mono hc (measure_ne_top_of_subset sdiff_subset hfin)
    rw [volume_real_ball_eq_unit c (half_pos hr)] at h1
    rw [volume_real_ball_eq_unit z hr]
    have e : (r / 2) ^ d = (1 / 2 : ℝ) ^ d * r ^ d := by
      rw [← mul_pow]
      congr 1
      ring
    rw [e, mul_assoc] at h1
    have h2 : min ((1 / 2 : ℝ) ^ d) ((ρ / (2 * R + ρ)) ^ d) * (r ^ d *
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) ≤
        (1 / 2 : ℝ) ^ d * (r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    exact h2.trans h1

end QSH
