import PDEFoundation.Monotonicity.MonoSqBallsProof
import PDEFoundation.Monotonicity.MonoSqBalls.Lower
import PDEFoundation.Monotonicity.MonoSqBalls.Avg
import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Sphere means of harmonic functions vanishing to second order

A classically harmonic `C²` function `w` on `B_R` with `w(0) = 0` and `∇w(0) = 0` satisfies
`|w(x)| ≤ K |x|²` near the origin, so its sphere means `m(s) = ⨍_{∂B_s} w²` are `O(s⁴)`. The
growth inequality `(s/r)^{2N(r)} m(r) ≤ m(s)` of the Almgren frequency `N` then forces `N ≥ 2`
when `w` is not identically zero, and the second growth inequality gives the sharp decay
`m(s) ≤ (s/r)⁴ m(r)` for `0 < s < r < R`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Quartic bound for the sphere means of `w²` near `0` when `w` vanishes to second order. -/
theorem exists_sphereMean_sq_le_four (hd : 0 < d) {R : ℝ} (hR : 0 < R) {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ 2 w (PDE.euclideanBall 0 R)) (hw0 : w 0 = 0)
    (hdw0 : fderiv ℝ w 0 = 0) :
    ∃ K ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      PDE.sphereMean (0 : Vec d) s (fun x => w x ^ 2) ≤ K * s ^ 4 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hopen := PDE.isOpen_euclideanBall (0 : Vec d) R
  have h0 : (0 : Vec d) ∈ PDE.euclideanBall (0 : Vec d) R := by
    have h : PDE.vecNormSq (0 : Vec d) = 0 := by simp [PDE.vecNormSq, PDE.vecDot]
    rw [PDE.mem_euclideanBall_zero_iff, h]
    positivity
  have hca : ContDiffAt ℝ 2 w 0 := hw.contDiffAt (hopen.mem_nhds h0)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ w) 0 := hca.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hlip⟩ := hfd.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨ε₀, hε₀, hε₀R⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds h0)
  refine ⟨(K : ℝ) ^ 2, min ε ε₀, lt_min hε hε₀, fun s hs hsε => ?_⟩
  have hsε' : s < ε := hsε.trans_le (min_le_left _ _)
  have hsε₀ : s < ε₀ := hsε.trans_le (min_le_right _ _)
  have h0t : (0 : Vec d) ∈ t := hεt (Metric.mem_ball_self hε)
  refine PDE.MonoSqBalls.sphereMean_le_of_le ((hw.continuousOn.mono ?_).pow 2) (fun x hx => ?_)
  · intro x hx
    rw [PDE.mem_euclideanSphere_zero_iff] at hx
    have hxn : ‖x‖ ≤ s := by
      refine (pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_
      have := PDE.abs_apply_le_vecEuclideanNorm x i
      rwa [PDE.vecEuclideanNorm, hx, Real.sqrt_sq hs.le] at this
    exact hε₀R (by rw [Metric.mem_ball, dist_zero_right]; exact hxn.trans_lt hsε₀)
  · rw [PDE.mem_euclideanSphere_zero_iff] at hx
    have hxn : ‖x‖ ≤ s := by
      refine (pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_
      have := PDE.abs_apply_le_vecEuclideanNorm x i
      rwa [PDE.vecEuclideanNorm, hx, Real.sqrt_sq hs.le] at this
    have hS : ∀ z ∈ Metric.closedBall (0 : Vec d) ‖x‖, ‖z‖ < ε ∧ ‖z‖ < ε₀ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact ⟨hz.trans_lt (hxn.trans_lt hsε'), hz.trans_lt (hxn.trans_lt hsε₀)⟩
    have hdiff : ∀ z ∈ Metric.closedBall (0 : Vec d) ‖x‖, DifferentiableAt ℝ w z := by
      intro z hz
      have hzR : z ∈ PDE.euclideanBall (0 : Vec d) R :=
        hε₀R (by rw [Metric.mem_ball, dist_zero_right]; exact (hS z hz).2)
      exact ((hw.contDiffAt (hopen.mem_nhds hzR)).differentiableAt (by norm_num))
    have hbound : ∀ z ∈ Metric.closedBall (0 : Vec d) ‖x‖, ‖fderiv ℝ w z‖ ≤ K * ‖x‖ := by
      intro z hz
      have hzt : z ∈ t := hεt (by rw [Metric.mem_ball, dist_zero_right]; exact (hS z hz).1)
      have h1 := hlip.dist_le_mul z hzt 0 h0t
      rw [hdw0, dist_zero_right, dist_zero_right] at h1
      have hz' : ‖z‖ ≤ ‖x‖ := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
      exact h1.trans (mul_le_mul_of_nonneg_left hz' K.2)
    have hmv := (convex_closedBall (0 : Vec d) ‖x‖).norm_image_sub_le_of_norm_fderiv_le hdiff
      hbound (Metric.mem_closedBall_self (norm_nonneg x))
      (by rw [Metric.mem_closedBall, dist_zero_right])
    rw [hw0, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
    have h2 : |w x| ≤ K * s ^ 2 := by
      calc |w x| ≤ K * ‖x‖ * ‖x‖ := hmv
        _ ≤ K * s * s := by
            have hK : (0 : ℝ) ≤ K := K.2
            have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
            nlinarith [mul_le_mul hxn hxn hx0 hs.le]
        _ = K * s ^ 2 := by ring
    calc w x ^ 2 = |w x| ^ 2 := (sq_abs _).symm
      _ ≤ (K * s ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (K : ℝ) ^ 2 * s ^ 4 := by ring

/-- The Almgren frequency of a harmonic function vanishing to second order at `0` and not
identically zero is at least `2`. -/
theorem two_le_almgrenFrequency (hd : 0 < d) {R : ℝ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ 2 w (PDE.euclideanBall 0 R))
    (hharm : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian w x = 0)
    (hpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < PDE.sphereIntegral 0 r (fun x => w x ^ 2))
    (hw0 : w 0 = 0) (hdw0 : fderiv ℝ w 0 = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) : 2 ≤ PDE.almgrenFrequency w r := by
  by_contra hlt
  push Not at hlt
  have hR : 0 < R := hr.trans hrR
  obtain ⟨K, ε, hε, hK⟩ := exists_sphereMean_sq_le_four hd hR hw hw0 hdw0
  have hmr := PDE.LogMean.mean_pos hd hr (hpos r ⟨hr, hrR⟩)
  set e : ℝ := 2 * PDE.almgrenFrequency w r with he
  set M := PDE.sphereMean (0 : Vec d) r (fun x => w x ^ 2) with hM
  have hc : 0 < 4 - e := by rw [he]; linarith
  have hlim : Tendsto (fun s : ℝ => K * r ^ e * s ^ (4 - e)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s ^ (4 - e)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (4 - e))) :=
      (Real.continuousAt_rpow_const 0 (4 - e) (Or.inr hc.le)).tendsto
    rw [Real.zero_rpow hc.ne'] at h1
    simpa using (h1.const_mul (K * r ^ e)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), K * r ^ e * s ^ (4 - e) < M :=
    (hlim.eventually (gt_mem_nhds hmr))
  have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (min ε r) := Ioo_mem_nhdsGT (lt_min hε hr)
  obtain ⟨s, hs1, hs3, hs2⟩ := (hev.and hev2).exists
  have hs0 : 0 < s := hs3
  have hsε : s < ε := hs2.trans_le (min_le_left _ _)
  have hsr : s < r := hs2.trans_le (min_le_right _ _)
  have hg := PDE.MonoSqBalls.growth_first hd hw hharm hpos hs0 hsr hrR
  have hms := hK s hs0 hsε
  have hrp : 0 < r ^ e := Real.rpow_pos_of_pos hr _
  have hsp : 0 < s ^ e := Real.rpow_pos_of_pos hs0 _
  rw [← he, Real.div_rpow hs0.le hr.le, ← hM] at hg
  have h3 : s ^ e / r ^ e * M ≤ K * s ^ 4 := hg.trans hms
  have h4 : s ^ (4 - e) = s ^ 4 / s ^ e := by
    rw [Real.rpow_sub hs0]
    congr 1
    exact_mod_cast Real.rpow_natCast s 4
  rw [h4] at hs1
  have h5 : M ≤ K * r ^ e * (s ^ 4 / s ^ e) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hrp] at h3
    rw [mul_div_assoc', le_div_iff₀ hsp]
    nlinarith [h3]
  exact absurd hs1 (not_lt.mpr h5)

/-- **Sharp decay of sphere means** for harmonic functions vanishing to second order. -/
theorem sphereMean_sq_le_four (hd : 0 < d) {R : ℝ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ 2 w (PDE.euclideanBall 0 R))
    (hharm : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R, PDE.euclideanCoordLaplacian w x = 0)
    (hw0 : w 0 = 0) (hdw0 : fderiv ℝ w 0 = 0) {s r : ℝ} (hs : 0 < s) (hsr : s < r)
    (hrR : r < R) :
    PDE.sphereMean (0 : Vec d) s (fun x => w x ^ 2) ≤
      (s / r) ^ 4 * PDE.sphereMean (0 : Vec d) r (fun x => w x ^ 2) := by
  have : NeZero d := ⟨hd.ne'⟩
  rcases PDE.dichotomy_zero_or_sphereIntegral_sq_pos hd hw hharm with h0 | hpos
  · have hR : 0 < R := hs.trans (hsr.trans hrR)
    have hz : ∀ t : ℝ, 0 ≤ t → t < R →
        PDE.sphereMean (0 : Vec d) t (fun x => w x ^ 2) = 0 := by
      intro t ht0 htR
      rw [PDE.sphereMean_congr_of_eqOn (g := fun _ => (0 : ℝ)) hR (by rwa [abs_of_nonneg ht0])
        (fun x hx => by simp only [h0 x hx]; ring)]
      simp [PDE.sphereMean]
    rw [hz s hs.le (hsr.trans hrR), hz r (hs.trans hsr).le hrR, mul_zero]
  · have h1 := PDE.MonoSqBalls.growth_second hd hw hharm hpos hs hsr hrR
    have hN := two_le_almgrenFrequency hd hw hharm hpos hw0 hdw0 hs (hsr.trans hrR)
    have hmr := PDE.LogMean.mean_pos hd (hs.trans hsr) (hpos r ⟨hs.trans hsr, hrR⟩)
    have hsr1 : s / r ≤ 1 := (div_le_one (hs.trans hsr)).mpr hsr.le
    have h2 : (s / r) ^ (2 * PDE.almgrenFrequency w s) ≤ (s / r) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (div_pos hs (hs.trans hsr)) hsr1 (by linarith)
    have h4 : (s / r) ^ (4 : ℝ) = (s / r) ^ 4 := by exact_mod_cast Real.rpow_natCast (s / r) 4
    rw [h4] at h2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hmr.le)

end QSH
