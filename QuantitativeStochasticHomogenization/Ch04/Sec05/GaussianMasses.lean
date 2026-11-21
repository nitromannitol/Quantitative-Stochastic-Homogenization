import QuantitativeStochasticHomogenization.Ch04.Opening
import QuantitativeStochasticHomogenization.Ch04.Sec05.CubeDecomposition

/-!
# Masses of the heat kernel masks

Facts about the masks `Φ_{z,r}` of (4.1) used in the proof of Proposition 4.12 of Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, Section 4.5:

* `Φ_{z,r}` is a probability density in either variable (`integral_heatKernel`,
  `integral_heatKernel_center`), from the Gaussian integral on Euclidean space;
* its mass at Euclidean distance at least `t` from the center is at most
  `2^{d/2} exp(-t²/(8r²))` (`setIntegral_heatKernel_le_of_far`), the Gaussian tail (4.123);
* on the cell `z + L k + [-L/2, L/2)^d` with `r ≤ L` it is at most
  `(4πr²)^{-d/2} ∏ᵢ exp(-kᵢ²/16)` (`heatKernel_le_of_mem_latticeCell`), and these majorants have
  a sum over the cells bounded in terms of `d` only (`sum_latticeBox_prod_exp_le`): the Riemann
  sum of Step 3.
-/

open MeasureTheory

namespace QSH

variable {d : ℕ}

theorem euclideanHeatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Vec d) :
    0 ≤ euclideanHeatKernel t x :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

theorem heatKernel_nonneg (z : Vec d) (r : ℝ) (x : Vec d) : 0 ≤ heatKernel z r x :=
  euclideanHeatKernel_nonneg (sq_nonneg r) _

theorem euclideanSq_eq_norm_sq (x : Vec d) :
    euclideanSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [← euclideanNorm_eq_norm, euclideanNorm, Real.sq_sqrt]
  rw [euclideanSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **The heat kernel is a probability density.** -/
theorem integral_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec d, euclideanHeatKernel t x = 1 := by
  have hb : 0 < 1 / (4 * t) := by positivity
  have hmp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
  have h1 : ∫ x : Vec d,
      Real.exp (-(1 / (4 * t)) * ‖(MeasurableEquiv.toLp 2 (Fin d → ℝ)) x‖ ^ 2) =
      ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(1 / (4 * t)) * ‖y‖ ^ 2) :=
    hmp.integral_comp' (fun y => Real.exp (-(1 / (4 * t)) * ‖y‖ ^ 2))
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin] at h1
  have hpt : (fun x : Vec d => euclideanHeatKernel t x) = fun x =>
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(1 / (4 * t)) * ‖(MeasurableEquiv.toLp 2 (Fin d → ℝ)) x‖ ^ 2) := by
    funext x
    unfold euclideanHeatKernel
    congr 2
    rw [MeasurableEquiv.coe_toLp, ← euclideanSq_eq_norm_sq]
    ring
  rw [hpt, integral_const_mul, h1]
  have hpos : 0 < 4 * Real.pi * t := by positivity
  have he : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by field_simp
  rw [he, neg_div, Real.rpow_neg hpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hpos _).ne']

theorem integrable_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec d => euclideanHeatKernel t x) := by
  by_contra h
  have := integral_euclideanHeatKernel (d := d) ht
  rw [integral_undef h] at this
  exact zero_ne_one this

theorem heatKernel_comm (x : Vec d) (r : ℝ) (y : Vec d) : heatKernel x r y = heatKernel y r x := by
  have h : euclideanSq (y - x) = euclideanSq (x - y) := by
    simp only [euclideanSq, dot]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  unfold heatKernel euclideanHeatKernel
  rw [h]

theorem integrable_heatKernel (x : Vec d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => heatKernel x r y) := by
  simp only [heatKernel]
  exact (integrable_euclideanHeatKernel (pow_pos hr 2)).comp_sub_right x

/-- `Φ_{x,r}` has mass one. -/
theorem integral_heatKernel (x : Vec d) {r : ℝ} (hr : 0 < r) : ∫ y, heatKernel x r y = 1 := by
  simp only [heatKernel]
  rw [integral_sub_right_eq_self (fun y => euclideanHeatKernel (r ^ 2) y) x]
  exact integral_euclideanHeatKernel (pow_pos hr 2)

/-- `x ↦ Φ_{x,r}(y)` has mass one. -/
theorem integral_heatKernel_center (y : Vec d) {r : ℝ} (hr : 0 < r) :
    ∫ x, heatKernel x r y = 1 := by
  simp only [heatKernel_comm _ r y]
  exact integral_heatKernel y hr

theorem integrable_heatKernel_center (y : Vec d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => heatKernel x r y) := by
  simp only [heatKernel_comm _ r y]
  exact integrable_heatKernel y hr

/-! ### The Gaussian tail -/

theorem euclideanHeatKernel_le_of_le_euclideanNorm {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    {w : Vec d} (hw : t ≤ euclideanNorm w) :
    euclideanHeatKernel s w ≤
      2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * s))) * euclideanHeatKernel (2 * s) w := by
  have hsq : t ^ 2 ≤ euclideanSq w := by
    have h0 : 0 ≤ euclideanSq w := by
      rw [euclideanSq_eq_sum_sq]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have := pow_le_pow_left₀ ht hw 2
    rwa [euclideanNorm, Real.sq_sqrt h0] at this
  have hpos : 0 < 4 * Real.pi * s := by positivity
  have htwo : (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * s)) ^ (-(d : ℝ) / 2) =
      (4 * Real.pi * s) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (2 * s) = 2 * (4 * Real.pi * s) by ring,
      Real.mul_rpow (by norm_num) hpos.le, ← mul_assoc, ← Real.rpow_add (by norm_num),
      show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  unfold euclideanHeatKernel
  rw [← htwo]
  have hexp : Real.exp (-euclideanSq w / (4 * s)) ≤
      Real.exp (-(t ^ 2 / (8 * s))) * Real.exp (-euclideanSq w / (4 * (2 * s))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h8 : t ^ 2 / (8 * s) ≤ euclideanSq w / (8 * s) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have e1 : -euclideanSq w / (4 * s) = -(euclideanSq w / (8 * s)) - euclideanSq w / (8 * s) := by
      field_simp
      ring
    have e2 : -euclideanSq w / (4 * (2 * s)) = -(euclideanSq w / (8 * s)) := by
      field_simp
      ring
    rw [e1, e2]
    linarith
  have hc : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * s)) ^ (-(d : ℝ) / 2) := by
    positivity
  calc 2 ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * s)) ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanSq w / (4 * s))
      ≤ 2 ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * s)) ^ (-(d : ℝ) / 2) *
        (Real.exp (-(t ^ 2 / (8 * s))) * Real.exp (-euclideanSq w / (4 * (2 * s)))) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring

/-- **The Gaussian tail**: the mass of `Φ_{x,r}` on a measurable set at Euclidean distance at
least `t ≥ 0` from `x` is at most `2^{d/2} exp(-t²/(8r²))`. -/
theorem setIntegral_heatKernel_le_of_far (x : Vec d) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hfar : ∀ y ∈ S, t ≤ euclideanNorm (y - x)) :
    ∫ y in S, heatKernel x r y ≤ 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * r ^ 2))) := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  set c : ℝ := 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * r ^ 2))) with hcdef
  have hc : 0 ≤ c := by positivity
  have hi2 : Integrable (fun y : Vec d => c * euclideanHeatKernel (2 * r ^ 2) (y - x)) :=
    ((integrable_euclideanHeatKernel (by positivity)).comp_sub_right x).const_mul c
  calc ∫ y in S, heatKernel x r y
      ≤ ∫ y in S, c * euclideanHeatKernel (2 * r ^ 2) (y - x) := by
        refine setIntegral_mono_on (integrable_heatKernel x hr).integrableOn hi2.integrableOn hS
          fun y hy => ?_
        exact euclideanHeatKernel_le_of_le_euclideanNorm hr2 ht (hfar y hy)
    _ ≤ ∫ y, c * euclideanHeatKernel (2 * r ^ 2) (y - x) :=
        setIntegral_le_integral hi2 (Filter.Eventually.of_forall fun y =>
          mul_nonneg hc (euclideanHeatKernel_nonneg (by positivity) _))
    _ = c := by
        rw [integral_const_mul, integral_sub_right_eq_self
          (fun y => euclideanHeatKernel (2 * r ^ 2) y) x,
          integral_euclideanHeatKernel (by positivity), mul_one]

/-! ### The Riemann sum over lattice cells -/

theorem sq_le_four_mul_sq_of_mem_cell {L a : ℝ} {m : ℤ} (hL : 0 ≤ L)
    (h1 : L * m - L / 2 ≤ a) (h2 : a < L * m + L / 2) : L ^ 2 * (m : ℝ) ^ 2 ≤ 4 * a ^ 2 := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    have ha : a ≤ L * m / 2 := by nlinarith
    have hLm : L * m / 2 ≤ 0 := by nlinarith
    nlinarith
  · subst hm
    simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have ha : L * m / 2 ≤ a := by nlinarith
    have hLm : 0 ≤ L * m / 2 := by positivity
    nlinarith

/-- On the cell `z + L k + [-L/2, L/2)^d`, with `0 < r ≤ L`,
`Φ_{z,r} ≤ (4πr²)^{-d/2} ∏ᵢ exp(-kᵢ²/16)`. -/
theorem heatKernel_le_of_mem_latticeCell {z y : Vec d} {L r : ℝ} (hr : 0 < r) (hrL : r ≤ L)
    {k : LatticeIndex d} (hy : y - z ∈ latticeCell L k) :
    heatKernel z r y ≤ (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) *
      ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16) := by
  have hL : 0 < L := hr.trans_le hrL
  unfold heatKernel euclideanHeatKernel
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hcoord : ∀ i, L ^ 2 * (k i : ℝ) ^ 2 ≤ 4 * (y - z) i ^ 2 := fun i =>
    sq_le_four_mul_sq_of_mem_cell hL.le (hy i).1 (hy i).2
  have hsum : L ^ 2 * ∑ i, (k i : ℝ) ^ 2 ≤ 4 * euclideanSq (y - z) := by
    rw [euclideanSq_eq_sum_sq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hcoord i
  have hLr : r ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hr.le hrL 2
  have hk0 : 0 ≤ ∑ i, (k i : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : (∑ i, (k i : ℝ) ^ 2) / 16 ≤ euclideanSq (y - z) / (4 * r ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  calc -euclideanSq (y - z) / (4 * r ^ 2) = -(euclideanSq (y - z) / (4 * r ^ 2)) := by ring
    _ ≤ -((∑ i, (k i : ℝ) ^ 2) / 16) := neg_le_neg key
    _ = ∑ i, -((k i : ℝ) ^ 2) / 16 := by rw [Finset.sum_div, ← Finset.sum_neg_distrib]; simp [neg_div]

/-- The constant `∑_{m ∈ ℤ} exp(-m²/16)`. -/
noncomputable def latticeGaussianConst : ℝ := ∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 16)

theorem summable_exp_neg_sq_div_sixteen :
    Summable fun m : ℤ => Real.exp (-((m : ℝ) ^ 2) / 16) := by
  have hq0 : 0 ≤ Real.exp (-(1 / 16)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(1 / 16)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeo := summable_geometric_of_lt_one hq0 hq1
  have hbound : ∀ n : ℕ, Real.exp (-((n : ℝ) ^ 2) / 16) ≤ Real.exp (-(1 / 16)) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    linarith
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
    simpa using hbound n
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (hgeo.comp_injective (add_left_injective 1))
    have := hbound (n + 1)
    simp only [Function.comp_apply]
    convert this using 3
    push_cast
    ring

theorem latticeGaussianConst_nonneg : 0 ≤ latticeGaussianConst :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- **The Riemann sum**: `∑_{|k| ≤ N} ∏ᵢ exp(-kᵢ²/16) ≤ (∑_{m ∈ ℤ} exp(-m²/16))^d`. -/
theorem sum_latticeBox_prod_exp_le (N : ℕ) :
    ∑ k ∈ latticeBox d N, ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16) ≤ latticeGaussianConst ^ d := by
  unfold latticeBox
  rw [Finset.sum_prod_piFinset (Finset.Icc (-(N : ℤ)) N)
    (fun _ m => Real.exp (-((m : ℝ) ^ 2) / 16))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) ?_ d
  exact summable_exp_neg_sq_div_sixteen.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)

end QSH
