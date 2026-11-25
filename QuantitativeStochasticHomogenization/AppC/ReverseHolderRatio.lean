import QuantitativeStochasticHomogenization.AppC.VanishingSobolevPoincare

/-!
# Changing the ratio of the balls in a reverse Hölder inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, proof of Corollary C.9 and Theorem C.7. Near the boundary the reverse Hölder
inequality of Corollary C.9 comes from Lemma C.8 on a ball centred at a boundary point, which is
larger than the ball of the inequality; Gehring's lemma (Lemma C.4) is stated for the balls
`B_{r/2}(z) ⊆ B_r(z)`. This file passes from the balls `B_{ρ/8}(y) ⊆ B_ρ(y)` to the balls
`B_{r/2}(z) ⊆ B_r(z)` by the Vitali covering lemma (Lemma C.5): `B_{r/2}(z)` is covered by the
balls `B_{r/16}(x_j)`, five times larger than disjoint balls `B_{r/80}(x_j)` inside `B_r(z)`, and
the reverse Hölder inequality on each `B_{r/2}(x_j) ⊆ B_r(z)` is summed.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `‖f‖_{L̲^s(A)} ≤ (|B| / |A|)^{1/s} ‖f‖_{L̲^s(B)}` for `A ⊆ B`. -/
theorem eLpMeanNormOn_le_of_subset {A B : Set (Vec d)} (hAB : A ⊆ B) (hA0 : volume A ≠ 0)
    (hBt : volume B ≠ ⊤) (s : ℝ≥0∞) (f : Vec d → ℝ) :
    PDE.eLpMeanNormOn A s f ≤
      (volume B / volume A) ^ (1 / s).toReal * PDE.eLpMeanNormOn B s f := by
  have hAt : volume A ≠ ⊤ := ne_top_of_le_ne_top hBt (measure_mono hAB)
  have hB0 : volume B ≠ 0 := fun h => hA0 (measure_mono_null hAB h)
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hAt.lt_top,
    PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hBt.lt_top, ← mul_assoc,
    ← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
  have e : volume B / volume A * (volume B)⁻¹ = (volume A)⁻¹ := by
    rw [div_eq_mul_inv, mul_comm (volume B), mul_assoc, ENNReal.mul_inv_cancel hB0 hBt, mul_one]
  rw [e]
  exact mul_le_mul_right (eLpNorm_mono_measure f (Measure.restrict_mono hAB le_rfl)) _

theorem volume_ball_eq_of_radius (x y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball x ρ) = volume (ball y ρ) := by
  rw [volume_ball_eq_unit x hρ, volume_ball_eq_unit y hρ]

/-- `‖f‖_{L̲^s(B_{r/2}(x))} ≤ 2^d ‖f‖_{L̲^s(B_r(z))}` for `B_{r/2}(x) ⊆ B_r(z)` and `s ≥ 1`. -/
theorem eLpMeanNormOn_half_ball_le {x z : Vec d} {r : ℝ} (hr : 0 < r)
    (hsub : ball x (r / 2) ⊆ ball z r) {s : ℝ≥0∞} (hs : 1 ≤ s) (f : Vec d → ℝ) :
    PDE.eLpMeanNormOn (ball x (r / 2)) s f ≤
      ENNReal.ofReal (2 ^ d) * PDE.eLpMeanNormOn (ball z r) s f := by
  have hr2 : 0 < r / 2 := by linarith
  refine (eLpMeanNormOn_le_of_subset hsub (volume_ball_ne_zero' x hr2)
    (volume_ball_ne_top' z r) s f).trans ?_
  gcongr ?_ * _
  have hratio : volume (ball z r) / volume (ball x (r / 2)) ≤ ENNReal.ofReal (2 ^ d) := by
    refine ENNReal.div_le_of_le_mul ?_
    have e : volume (ball z r) = ENNReal.ofReal (2 ^ d) * volume (ball x (r / 2)) := by
      rw [volume_ball_eq_of_radius x z hr2, show r = 2 * (r / 2) by ring, volume_ball_mul z
        (by norm_num : (0 : ℝ) < 2) hr2, show 2 * (r / 2) / 2 = r / 2 by ring]
    exact e.le
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ d) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
  have ht : (1 / s).toReal ≤ 1 := by
    have : 1 / s ≤ 1 := by
      rw [one_div]
      exact ENNReal.inv_le_one.mpr hs
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  calc (volume (ball z r) / volume (ball x (r / 2))) ^ (1 / s).toReal
      ≤ ENNReal.ofReal (2 ^ d) ^ (1 / s).toReal := ENNReal.rpow_le_rpow hratio ENNReal.toReal_nonneg
    _ ≤ ENNReal.ofReal (2 ^ d) ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h1 ht
    _ = ENNReal.ofReal (2 ^ d) := ENNReal.rpow_one _

/-- **From the balls `B_{ρ/8}(y) ⊆ B_ρ(y)` to the balls `B_{r/2}(z) ⊆ B_r(z)`.** If
`‖f‖_{L̲²(B_{ρ/8}(y))} ≤ K (‖f‖_{L̲^q(B_ρ(y))} + ‖g‖_{L̲²(B_ρ(y))})` for every ball
`B_ρ(y) ⊆ B_R`, then `‖f‖_{L̲²(B_{r/2}(z))} ≤ 10^d 2^d K (‖f‖_{L̲^q(B_r(z))} + ‖g‖_{L̲²(B_r(z))})`
for every ball `B_r(z) ⊆ B_R`. -/
theorem reverseHolder_half_of_eighth {R K q : ℝ} (hK : 0 ≤ K) (hq : 1 ≤ q) {f g : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume)
    (h8 : ∀ (y : Vec d) (ρ : ℝ), 0 < ρ → ball y ρ ⊆ ball 0 R →
      PDE.eLpMeanNormOn (ball y (ρ / 8)) 2 f ≤ ENNReal.ofReal K *
        (PDE.eLpMeanNormOn (ball y ρ) (ENNReal.ofReal q) f +
          PDE.eLpMeanNormOn (ball y ρ) 2 g)) :
    ∀ (z : Vec d) (r : ℝ), 0 < r → ball z r ⊆ ball 0 R →
      PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ≤ ENNReal.ofReal (10 ^ d * 2 ^ d * K) *
        (PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f +
          PDE.eLpMeanNormOn (ball z r) 2 g) := by
  intro z r hr hzR
  have hr2 : 0 < r / 2 := by linarith
  have hr16 : 0 < r / 16 := by linarith
  have hr80 : 0 < r / 80 := by linarith
  set A := PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal q) f +
    PDE.eLpMeanNormOn (ball z r) 2 g with hAdef
  -- the Vitali covering
  obtain ⟨J, hJc, hJd, hJcov⟩ := lemma_C_5 (ι := ball z (r / 2)) (fun x => x.1)
    (fun _ => r / 80) (r / 80) (fun _ => le_rfl)
  have hcov : ball z (r / 2) ⊆ ⋃ j ∈ J, ball j.1 (r / 16) := by
    intro x hx
    have h := hJcov (mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self_of_pos x hr80⟩)
    rwa [show 5 * (r / 80) = r / 16 by ring] at h
  have hsubj : ∀ j : ball z (r / 2), ball j.1 (r / 2) ⊆ ball z r := by
    intro j y hy
    have hj : euclideanNorm (j.1 - z) < r / 2 := j.2
    have hy' : euclideanNorm (y - j.1) < r / 2 := hy
    change euclideanNorm (y - z) < r
    have := euclideanNorm_sub_le_add y j.1 z
    linarith
  have hsub80 : ∀ j : ball z (r / 2), ball j.1 (r / 80) ⊆ ball z r := fun j =>
    (ball_subset_ball_of_norm (by
      have hj : euclideanNorm (j.1 - z) < r / 2 := j.2
      have : euclideanNorm (j.1 - j.1) = 0 := by simp [euclideanNorm, euclideanSq, dot]
      linarith)).trans (hsubj j)
  -- the bound on each covering ball
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hbound : ∀ j : ball z (r / 2), PDE.eLpMeanNormOn (ball j.1 (r / 16)) 2 f ≤
      ENNReal.ofReal (2 ^ d * K) * A := by
    intro j
    have h := h8 j.1 (r / 2) hr2 ((hsubj j).trans hzR)
    rw [show r / 2 / 8 = r / 16 by ring] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (2 ^ d)), mul_assoc]
    gcongr ENNReal.ofReal K * ?_
    rw [hAdef, mul_add]
    exact add_le_add (eLpMeanNormOn_half_ball_le hr (hsubj j) hq1 f)
      (eLpMeanNormOn_half_ball_le hr (hsubj j) one_le_two g)
  -- summation
  have hJcount : Countable J := hJc.to_subtype
  have hfm : ∀ U : Set (Vec d), AEStronglyMeasurable f (volume.restrict U) := fun U =>
    hf.restrict
  have hvol16 : ∀ j : ball z (r / 2), volume (ball j.1 (r / 16)) =
      ENNReal.ofReal (5 ^ d) * volume (ball j.1 (r / 80)) := by
    intro j
    rw [show r / 16 = 5 * (r / 80) by ring, volume_ball_mul j.1 (by norm_num) hr80]
  set T := ENNReal.ofReal (2 ^ d * K) * A with hTdef
  have hint : ∫⁻ x in ball z (r / 2), ‖f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) * volume (ball z r) := by
    calc ∫⁻ x in ball z (r / 2), ‖f x‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ x in ⋃ j : J, ball j.1.1 (r / 16), ‖f x‖ₑ ^ (2 : ℝ) := by
          refine lintegral_mono_set ?_
          intro x hx
          obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcov hx)
          exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
      _ ≤ ∑' j : J, ∫⁻ x in ball j.1.1 (r / 16), ‖f x‖ₑ ^ (2 : ℝ) :=
          lintegral_iUnion_le _ _
      _ = ∑' j : J, volume (ball j.1.1 (r / 16)) *
            PDE.eLpMeanNormOn (ball j.1.1 (r / 16)) 2 f ^ (2 : ℝ) := by
          refine tsum_congr fun j => ?_
          exact lintegral_ball_eq_volume_mul j.1.1 hr16 (hfm _)
      _ ≤ ∑' j : J, volume (ball j.1.1 (r / 16)) * T ^ (2 : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          gcongr
          exact hbound j.1
      _ = ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) * ∑' j : J, volume (ball j.1.1 (r / 80)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun j => ?_
          rw [hvol16 j.1]
          ring
      _ = ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) * volume (⋃ j ∈ J, ball j.1 (r / 80)) := by
          rw [measure_biUnion hJc hJd fun j _ => (isOpen_ball_vitali j.1 (r / 80)).measurableSet]
      _ ≤ ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) * volume (ball z r) := by
          gcongr
          exact iUnion₂_subset fun j _ => hsub80 j
  -- the normalized norm on `B_{r/2}(z)`
  have hvol2 : volume (ball z r) = ENNReal.ofReal (2 ^ d) * volume (ball z (r / 2)) := by
    rw [show r = 2 * (r / 2) by ring, volume_ball_mul z (by norm_num : (0 : ℝ) < 2) hr2,
      show 2 * (r / 2) / 2 = r / 2 by ring]
  have hsq : PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ^ (2 : ℝ) ≤
      (ENNReal.ofReal (10 ^ d * 2 ^ d * K) * A) ^ (2 : ℝ) := by
    have e := lintegral_ball_eq_volume_mul z hr2 (hfm (ball z (r / 2)))
    have hB0 := volume_ball_ne_zero' z hr2
    have hBt := volume_ball_ne_top' z (r / 2)
    have h1 : PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ^ (2 : ℝ) ≤
        ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) * ENNReal.ofReal (2 ^ d) := by
      have h0 : volume (ball z (r / 2)) * PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ^ (2 : ℝ) ≤
          volume (ball z (r / 2)) * (ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) *
            ENNReal.ofReal (2 ^ d)) := by
        calc volume (ball z (r / 2)) * PDE.eLpMeanNormOn (ball z (r / 2)) 2 f ^ (2 : ℝ)
            = ∫⁻ x in ball z (r / 2), ‖f x‖ₑ ^ (2 : ℝ) := e.symm
          _ ≤ ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) * volume (ball z r) := hint
          _ = volume (ball z (r / 2)) * (ENNReal.ofReal (5 ^ d) * T ^ (2 : ℝ) *
              ENNReal.ofReal (2 ^ d)) := by
            rw [hvol2]
            ring
      exact (ENNReal.mul_le_mul_iff_right hB0 hBt).mp h0
    refine h1.trans ?_
    rw [hTdef, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    have hK2 : ENNReal.ofReal (5 ^ d) * ENNReal.ofReal (2 ^ d * K) ^ (2 : ℝ) *
        ENNReal.ofReal (2 ^ d) ≤ ENNReal.ofReal (10 ^ d * 2 ^ d * K) ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_two, Real.rpow_two]
      have h10 : (10 : ℝ) ^ d = 5 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
      have h5 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
      have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      rw [h10]
      have hK0 : 0 ≤ K ^ 2 := sq_nonneg K
      have e1 : 5 ^ d * (2 ^ d * K) ^ 2 * 2 ^ d = (5 ^ d * 2 ^ d) * (2 ^ d) ^ 2 * K ^ 2 := by ring
      have e2 : (5 ^ d * 2 ^ d * 2 ^ d * K) ^ 2 =
          (5 ^ d * 2 ^ d) ^ 2 * (2 ^ d) ^ 2 * K ^ 2 := by ring
      rw [e1, e2]
      have ha : (1 : ℝ) ≤ 5 ^ d * 2 ^ d := one_le_mul_of_one_le_of_one_le h5 h2
      have h52 : (5 : ℝ) ^ d * 2 ^ d ≤ (5 ^ d * 2 ^ d) ^ 2 := by
        have := mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 5 ^ d * 2 ^ d)
        rw [mul_one] at this
        rw [sq]
        exact this
      have h22 : 0 ≤ ((2 : ℝ) ^ d) ^ 2 * K ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_right h52 h22
      calc (5 : ℝ) ^ d * 2 ^ d * (2 ^ d) ^ 2 * K ^ 2 = 5 ^ d * 2 ^ d * ((2 ^ d) ^ 2 * K ^ 2) := by
            ring
        _ ≤ (5 ^ d * 2 ^ d) ^ 2 * ((2 ^ d) ^ 2 * K ^ 2) := h3
        _ = (5 ^ d * 2 ^ d) ^ 2 * (2 ^ d) ^ 2 * K ^ 2 := by ring
    calc ENNReal.ofReal (5 ^ d) * (ENNReal.ofReal (2 ^ d * K) ^ (2 : ℝ) * A ^ (2 : ℝ)) *
          ENNReal.ofReal (2 ^ d)
        = ENNReal.ofReal (5 ^ d) * ENNReal.ofReal (2 ^ d * K) ^ (2 : ℝ) *
            ENNReal.ofReal (2 ^ d) * A ^ (2 : ℝ) := by ring
      _ ≤ ENNReal.ofReal (10 ^ d * 2 ^ d * K) ^ (2 : ℝ) * A ^ (2 : ℝ) := by gcongr
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hsq
