import QuantitativeStochasticHomogenization.Ch04.Sec05.Proposition412

/-!
# Lemma 5.29 (i): blocks at all scales `r ∈ [R^{η₁}, R]`

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29 (i), (5.90), for centered local additive fields: the block estimate (4.117)
(= (5.89)), proved for `r ∈ [R^{η₁}, R^{η₂}]`, extends to `r ∈ [R^{η₁}, R]`. With `r₁ = R^{η₁}` the
additivity replaces `X(r)` by the heat average of `X(r₁)` (Step 1 of Proposition 4.12), whose
weight `g = (f 1_{□_R}) ∗ Φ_{√(r²-r₁²)}` has width at most `R`; it is cut along the cells of side `R`
around the center, where `|g| ≤ 2^{d/2} ∏ᵢ exp(-(|kᵢ| - 1)₊²/8)` by the Gaussian tail (5.95), and the
far cells carry a Gaussian tail.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

/-- The majorant of the weight on the cell `k`: `∏ᵢ exp(-(|kᵢ| - 1)₊²/8)`. -/
noncomputable def shiftedGaussian (m : ℤ) : ℝ := Real.exp (-((max (|(m : ℝ)| - 1) 0) ^ 2) / 8)

theorem summable_shiftedGaussian : Summable shiftedGaussian := by
  have hq0 : 0 ≤ Real.exp (-(1 / 4)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(1 / 4)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeo := (summable_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (3 / 8))
  have hbound : ∀ m : ℤ, shiftedGaussian m ≤ Real.exp (3 / 8) * Real.exp (-(1 / 4)) ^ m.natAbs := by
    intro m
    unfold shiftedGaussian
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hm : (m.natAbs : ℝ) = |(m : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hm]
    have h0 : |(m : ℝ)| - 1 ≤ max (|(m : ℝ)| - 1) 0 := le_max_left _ _
    have h1 : 2 * max (|(m : ℝ)| - 1) 0 - 1 ≤ (max (|(m : ℝ)| - 1) 0) ^ 2 := by
      nlinarith [sq_nonneg (max (|(m : ℝ)| - 1) 0 - 1)]
    linarith
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
    simpa using hbound n
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (hgeo.comp_injective (add_left_injective 1))
    have := hbound (-((n : ℤ) + 1))
    simp only [Function.comp_apply]
    convert this using 3
    omega

/-- The constant `∑_{m ∈ ℤ} exp(-(|m| - 1)₊²/8)`. -/
noncomputable def shiftedGaussianConst : ℝ := ∑' m : ℤ, shiftedGaussian m

theorem shiftedGaussianConst_nonneg : 0 ≤ shiftedGaussianConst :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem sum_latticeBox_prod_shiftedGaussian_le (N : ℕ) :
    ∑ k ∈ latticeBox d N, ∏ i, shiftedGaussian (k i) ≤ shiftedGaussianConst ^ d := by
  unfold latticeBox
  rw [Finset.sum_prod_piFinset (Finset.Icc (-(N : ℤ)) N) (fun _ m => shiftedGaussian m)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) ?_ d
  exact summable_shiftedGaussian.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)

/-- Points of the cell `z + R k + [-R/2, R/2)^d` are at Euclidean distance at least
`R (∑ᵢ (|kᵢ| - 1)₊²)^{1/2}` from the closed cube of side `R` around `z`. -/
theorem le_euclideanNorm_of_mem_cellAt {z : Vec d} {R : ℝ} (hR : 0 < R) {k : LatticeIndex d}
    {y x : Vec d} (hy : y ∈ cellAt z R k) (hx : x ∈ closedCube z R) :
    R * Real.sqrt (∑ i, (max (|(k i : ℝ)| - 1) 0) ^ 2) ≤ euclideanNorm (y - x) := by
  have hcoord : ∀ i, R * max (|(k i : ℝ)| - 1) 0 ≤ |y i - x i| := by
    intro i
    obtain ⟨h1, h2⟩ := hy i
    simp only [Pi.sub_apply] at h1 h2
    have hyz : R * |(k i : ℝ)| - R / 2 ≤ |y i - z i| := by
      rcases le_or_gt 0 (k i : ℝ) with hk | hk
      · rw [abs_of_nonneg hk]
        exact (by linarith : R * k i - R / 2 ≤ y i - z i).trans (le_abs_self _)
      · rw [abs_of_neg hk]
        have := neg_abs_le (y i - z i)
        linarith
    have hxz : |x i - z i| ≤ R / 2 := hx i
    have htri : |y i - z i| ≤ |y i - x i| + |x i - z i| := by
      calc |y i - z i| = |(y i - x i) + (x i - z i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rcases le_total (|(k i : ℝ)| - 1) 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact abs_nonneg _
    · rw [max_eq_left h]
      linarith
  rw [euclideanNorm, euclideanSq_eq_sum_sq, ← Real.sqrt_sq hR.le, ← Real.sqrt_mul (sq_nonneg _),
    Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h := hcoord i
  have h0 : 0 ≤ R * max (|(k i : ℝ)| - 1) 0 := mul_nonneg hR.le (le_max_right _ _)
  calc R ^ 2 * (max (|(k i : ℝ)| - 1) 0) ^ 2 = (R * max (|(k i : ℝ)| - 1) 0) ^ 2 := by ring
    _ ≤ |(y - x) i| ^ 2 := pow_le_pow_left₀ h0 (by simpa using h) 2
    _ = (y - x) i ^ 2 := sq_abs _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {s δ α B A : ℝ}

/-- The heat average of a block weight is at most `2^{d/2} ∏ᵢ exp(-(|kᵢ| - 1)₊²/8)` on the cell
`k` of side `R ≥ ρ`. -/
theorem abs_heatSmooth_le_of_mem_cellAt {f : Vec d → ℝ} (hf1 : ∀ x, |f x| ≤ 1) {z : Vec d}
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ≤ R) (hfz : ∀ x ∉ closedCube z R, f x = 0)
    {k : LatticeIndex d} {y : Vec d} (hy : y ∈ cellAt z R k) :
    |heatSmooth f ρ y| ≤ 2 ^ ((d : ℝ) / 2) * ∏ i, shiftedGaussian (k i) := by
  set S : ℝ := ∑ i, (max (|(k i : ℝ)| - 1) 0) ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  set t : ℝ := R * Real.sqrt S with htdef
  have ht : 0 ≤ t := by positivity
  have h1 : |heatSmooth f ρ y| ≤ ∫ x, (closedCube z R).indicator (fun x => heatKernel x ρ y) x := by
    unfold heatSmooth
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      ((integrable_heatKernel_center y hρ).indicator (measurableSet_closedCube z R))
      (Filter.Eventually.of_forall fun x => ?_))
    by_cases hx : x ∈ closedCube z R
    · show |f x * heatKernel x ρ y| ≤ (closedCube z R).indicator (fun x => heatKernel x ρ y) x
      rw [Set.indicator_of_mem hx, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _ _)]
      exact mul_le_of_le_one_left (heatKernel_nonneg _ _ _) (hf1 x)
    · show |f x * heatKernel x ρ y| ≤ (closedCube z R).indicator (fun x => heatKernel x ρ y) x
      rw [Set.indicator_of_notMem hx, hfz x hx, zero_mul, abs_zero]
  have h2 : ∫ x, (closedCube z R).indicator (fun x => heatKernel x ρ y) x =
      ∫ x in closedCube z R, heatKernel y ρ x := by
    rw [integral_indicator (measurableSet_closedCube z R)]
    simp_rw [heatKernel_comm _ ρ y]
  have h3 := setIntegral_heatKernel_le_of_far y hρ ht (measurableSet_closedCube z R)
    (fun x hx => by
      rw [euclideanNorm_sub_comm']
      exact le_euclideanNorm_of_mem_cellAt hR hy hx)
  have h4 : Real.exp (-(t ^ 2 / (8 * ρ ^ 2))) ≤ ∏ i, shiftedGaussian (k i) := by
    unfold shiftedGaussian
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.mpr ?_
    have et : t ^ 2 = R ^ 2 * S := by rw [htdef, mul_pow, Real.sq_sqrt hS]
    have hsum : ∑ i, -((max (|(k i : ℝ)| - 1) 0) ^ 2) / 8 = -(S / 8) := by
      rw [hSdef, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, et, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
    have hρ2 : ρ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hρ.le hρR 2
    nlinarith
  calc |heatSmooth f ρ y| ≤ 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * ρ ^ 2))) :=
        (h1.trans_eq h2).trans h3
    _ ≤ 2 ^ ((d : ℝ) / 2) * ∏ i, shiftedGaussian (k i) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **Lemma 5.29 (i), (5.90)**, for centered local additive fields: the block estimate holds for
all scales `r ∈ [R^{η₁}, R]`. -/
theorem exists_blockBound_all_scales (hd : 1 ≤ d) (hmono : Monotone F) (hs1 : 1 < s) (hs2 : s ≤ 2) (hB0 : 0 < B)
    (hA0 : 0 < A) {η₁ η₂ β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ (d : ℝ) / 2) (hδ : 0 < δ)
    (hη₁ : 0 < η₁) (hη₁₂ : η₁ < η₂) (hη₂ : η₂ * (1 + δ) < 1) (hα : β < η₁ * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure Ω) [IsProbabilityMeasure P], HasUnitRange P F →
      ∀ (X : CenteredLocalFields P F s δ α B A) (R : ℝ), 1 ≤ R →
      ∀ r : ℝ, R ^ η₁ ≤ r → r ≤ R → ∀ (z : Vec d) (f : Vec d → ℝ), Measurable f →
      (∀ x, |f x| ≤ 1) → (∀ x ∉ closedCube z R, f x = 0) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x) s (C * R ^ (-β)) := by
  classical
  obtain ⟨Cb, hCb, hBlock⟩ := exists_blockBound (Ω := Ω) hd hmono hs1 hs2 hB0 hA0 hβ0 hβ hδ hη₁ hη₁₂
    hη₂ hα
  obtain ⟨C₀, hC₀, hfar⟩ := exists_centeredOsBound_far_block (Ω := Ω) (F := F) (δ := δ)
    (α := α) (A := A) hs1 hs2 hB0
  obtain ⟨Ce, hCe, hexp⟩ := exists_exp_neg_rpow_le (c := 1 / 8) (κ := 2) (by norm_num)
    (by norm_num) β
  set G : ℝ := 2 ^ ((d : ℝ) / 2) * shiftedGaussianConst ^ d with hGdef
  have hG : 0 ≤ G := by have := shiftedGaussianConst_nonneg; positivity
  set C : ℝ := Cb + A + Cb * G + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) with hCdef
  refine ⟨C, by positivity, fun P _ hF X R hR r hr1 hr2 z f hf hf1 hfz => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRβ : 0 ≤ R ^ (-β) := Real.rpow_nonneg hR0.le _
  by_cases hrR : r ≤ R ^ η₂
  · refine (hBlock P hF X R R hR le_rfl r hr1 hrR z f hf hf1 hfz).mono_scale ?_
    refine mul_le_mul_of_nonneg_right ?_ hRβ
    have : 0 ≤ A + Cb * G + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) := by positivity
    rw [hCdef]
    linarith
  push Not at hrR
  set r₁ : ℝ := R ^ η₁ with hr₁def
  have hr₁1 : 1 ≤ r₁ := Real.one_le_rpow hR hη₁.le
  have hr₁r : r₁ < r :=
    (Real.rpow_le_rpow_of_exponent_le hR hη₁₂.le).trans_lt hrR
  have hr₁sq : r₁ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr₁r (by linarith) two_ne_zero
  set ρ : ℝ := Real.sqrt (r ^ 2 - r₁ ^ 2) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (by linarith)
  have hρR : ρ ≤ R := by
    calc ρ ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (by have := sq_nonneg r₁; linarith)
      _ = r := Real.sqrt_sq (by linarith)
      _ ≤ R := hr2
  have hfi := integrable_of_abs_le_one_of_closedCube hf hf1 hR0.le hfz
  set g : Vec d → ℝ := heatSmooth f ρ with hgdef
  have hgm : Measurable g := measurable_heatSmooth hf ρ
  have hgi : Integrable g := integrable_heatSmooth hfi hf hρ
  have hT1 := centeredOsBound_block_additivity_defect X hr₁1 hr₁r hR0 hf hf1 hfz
  set N : ℕ := ⌈R⌉₊ with hNdef
  have hNR : R ≤ N := Nat.le_ceil R
  set S : Set (Vec d) := (boxAt z R N)ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_boxAt z hR0 N).compl
  set m : LatticeIndex d → ℝ := fun k => 2 ^ ((d : ℝ) / 2) * ∏ i, shiftedGaussian (k i) with hmdef
  have hm : ∀ k, 0 < m k := fun k => mul_pos (by positivity)
    (Finset.prod_pos fun i _ => Real.exp_pos _)
  set w : LatticeIndex d → Vec d → ℝ := fun k y => (m k)⁻¹ * (cellAt z R k).indicator g y
    with hwdef
  have hwm : ∀ k, Measurable (w k) := fun k =>
    measurable_const.mul (hgm.indicator (measurableSet_cellAt z R k))
  have hw1 : ∀ k y, |w k y| ≤ 1 := by
    intro k y
    by_cases hy : y ∈ cellAt z R k
    · simp only [hwdef, Set.indicator_of_mem hy]
      rw [abs_mul, abs_inv, abs_of_pos (hm k), inv_mul_le_iff₀ (hm k), mul_one]
      exact abs_heatSmooth_le_of_mem_cellAt hf1 hR0 hρ hρR hfz hy
    · simp only [hwdef, Set.indicator_of_notMem hy, mul_zero, abs_zero]
      exact zero_le_one
  have hwz : ∀ k y, y ∉ closedCube (z + R • latticeShift k) R → w k y = 0 := by
    intro k y hy
    simp only [hwdef, Set.indicator_of_notMem (fun h => hy (cellAt_subset_closedCube z R k h)),
      mul_zero]
  have hpiece : ∀ k ∈ latticeBox d N, CenteredOsBound P
      (fun a => R ^ (-(d : ℝ)) * ∫ y, (cellAt z R k).indicator g y * X.field r₁ a y) s
      (m k * (Cb * R ^ (-β))) := by
    intro k _
    have h1 := (hBlock P hF X R R hR le_rfl r₁ le_rfl
      (Real.rpow_le_rpow_of_exponent_le hR hη₁₂.le) _ (w k) (hwm k) (hw1 k) (hwz k)).const_mul
      (hm k)
    convert h1 using 1
    funext a
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext y
    simp only [hwdef]
    have hmk := (hm k).ne'
    field_simp
  have hbox : (latticeBox d N).Nonempty := ⟨0, mem_latticeBox.mpr fun i => by simp⟩
  have hcells := centeredOsBound_finset_sum_le (latticeBox d N) hbox hpiece
  have hcellsle : ∑ k ∈ latticeBox d N, m k * (Cb * R ^ (-β)) ≤ Cb * G * R ^ (-β) := by
    rw [← Finset.sum_mul]
    have h1 : ∑ k ∈ latticeBox d N, m k ≤ G := by
      rw [hGdef, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_latticeBox_prod_shiftedGaussian_le N) (by positivity)
    calc (∑ k ∈ latticeBox d N, m k) * (Cb * R ^ (-β)) ≤ G * (Cb * R ^ (-β)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hCb.le hRβ)
      _ = Cb * G * R ^ (-β) := by ring
  have hfarS : ∀ x ∈ closedCube z R, ∀ y ∈ S, (N : ℝ) * R ≤ euclideanNorm (y - x) := by
    intro x hx y hy
    obtain ⟨i, hi⟩ := exists_le_abs_of_cellIndex_notMem hR0 hy
    have hxi := hx i
    have h1 : |y i - x i| ≤ euclideanNorm (y - x) := by
      simpa using abs_apply_le_euclideanNorm' (y - x) i
    have h2 : |(y - z) i| ≤ |y i - x i| + |x i - z i| := by
      simp only [Pi.sub_apply]
      calc |y i - z i| = |(y i - x i) + (x i - z i)| := by ring_nf
        _ ≤ |y i - x i| + |x i - z i| := abs_add_le _ _
    nlinarith
  have hT4 := hfar P X r₁ hR0 hρ (by positivity) hf hf1 hfz hSm hfarS
  rw [← hgdef] at hT4
  have hT4le : C₀ * (B * 2 ^ ((d : ℝ) / 2) * Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2)))) ≤
      C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-β) := by
    have h1 : Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2))) ≤ Real.exp (-(1 / 8 * R ^ (2 : ℝ))) := by
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      rw [Real.rpow_two, le_div_iff₀ (by positivity)]
      have hNR' : R * R ≤ (N : ℝ) * R := mul_le_mul_of_nonneg_right hNR hR0.le
      have hρ2 : ρ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hρ.le hρR 2
      have h3 : (R * R) ^ 2 ≤ ((N : ℝ) * R) ^ 2 := pow_le_pow_left₀ (by positivity) hNR' 2
      have h4 : R ^ 2 * ρ ^ 2 ≤ R ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hρ2 (sq_nonneg R)
      have e1 : 1 / 8 * R ^ 2 * (8 * ρ ^ 2) = R ^ 2 * ρ ^ 2 := by ring
      have e2 : R ^ 2 * R ^ 2 = (R * R) ^ 2 := by ring
      rw [e1]
      linarith
    have hB' : 0 ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2)) := by positivity
    calc C₀ * (B * 2 ^ ((d : ℝ) / 2) * Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2))))
        = C₀ * (B * 2 ^ ((d : ℝ) / 2)) * Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2))) := by ring
      _ ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2)) * (Ce * R ^ (-β)) :=
          mul_le_mul_of_nonneg_left (h1.trans (hexp R hR)) hB'
      _ = C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-β) := by ring
  have hT1le : A * r₁ ^ (-α) ≤ A * R ^ (-β) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0.le
    rw [hr₁def, ← Real.rpow_mul hR0.le]
    have e : η₁ * -α = -(η₁ * α) := by ring
    exact Real.rpow_le_rpow_of_exponent_le hR (by rw [e]; linarith)
  have hcellsR : CenteredOsBound P (fun a => ∑ k ∈ latticeBox d N,
      R ^ (-(d : ℝ)) * ∫ y, (cellAt z R k).indicator g y * X.field r₁ a y) s
      (∑ k ∈ latticeBox d N, m k * (Cb * R ^ (-β))) := hcells
  have hall := (hT1.add hcellsR).add hT4
  refine hall.congr_ae (measurable_block X r hf _)
    (Filter.Eventually.of_forall fun a => ?_) |>.mono_scale ?_
  · have hDint : Integrable fun x => f x * (X.field r a x -
        ∫ y, heatKernel x ρ y * X.field r₁ a y) := by
      refine hfi.mul_bdd (c := 2 * B) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (((X.measurable r).comp measurable_prodMk_left).sub
          ((measurable_heatAverage _ (X.measurable r₁) ρ).comp
            measurable_prodMk_left)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_sub _ _).trans ?_
        have := X.abs_le r a x
        have := X.abs_heatAverage_le r₁ a x hρ
        linarith
    have hHint : Integrable fun x => f x * ∫ y, heatKernel x ρ y * X.field r₁ a y := by
      refine hfi.mul_bdd (c := B) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact ((measurable_heatAverage _ (X.measurable r₁) ρ).comp
          measurable_prodMk_left).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        exact X.abs_heatAverage_le r₁ a x hρ
    have hsplit1 : ∫ x, f x * X.field r a x = (∫ x, f x * (X.field r a x -
        ∫ y, heatKernel x ρ y * X.field r₁ a y)) +
        ∫ x, f x * ∫ y, heatKernel x ρ y * X.field r₁ a y := by
      rw [← integral_add hDint hHint]
      congr 1
      funext x
      ring
    have hfub := integral_mul_heat_eq hfi hρ (G := fun y => X.field r₁ a y)
      ((X.measurable r₁).comp measurable_prodMk_left) (X.abs_le r₁ a)
    have hik : ∀ k, Integrable fun y => (cellAt z R k).indicator g y * X.field r₁ a y :=
      fun k => X.integrable_mul r₁ a (hgi.indicator (measurableSet_cellAt z R k))
    have hiS : Integrable fun y => S.indicator g y * X.field r₁ a y :=
      X.integrable_mul r₁ a (hgi.indicator hSm)
    have hA1 : Integrable fun y => ∑ k ∈ latticeBox d N,
        (cellAt z R k).indicator g y * X.field r₁ a y :=
      integrable_finsetSum _ fun k _ => hik k
    have hpt : (fun y => g y * X.field r₁ a y) = fun y =>
        (∑ k ∈ latticeBox d N, (cellAt z R k).indicator g y * X.field r₁ a y) +
          S.indicator g y * X.field r₁ a y := by
      funext y
      rw [← Finset.sum_mul, ← add_mul, sum_indicator_cellAt_add z hR0 N]
    have hsplit2 : ∫ y, g y * X.field r₁ a y =
        (∑ k ∈ latticeBox d N, ∫ y, (cellAt z R k).indicator g y * X.field r₁ a y) +
          ∫ y, S.indicator g y * X.field r₁ a y := by
      rw [hpt]
      calc ∫ y, ((∑ k ∈ latticeBox d N, (cellAt z R k).indicator g y * X.field r₁ a y) +
            S.indicator g y * X.field r₁ a y)
          = (∫ y, ∑ k ∈ latticeBox d N, (cellAt z R k).indicator g y * X.field r₁ a y) +
            ∫ y, S.indicator g y * X.field r₁ a y := integral_add hA1 hiS
        _ = _ := by rw [integral_finsetSum _ fun k _ => hik k]
    show _ = R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x
    beta_reduce
    rw [hsplit1, hfub, hsplit2, mul_add, mul_add, Finset.mul_sum, hρdef, add_assoc]
  · calc A * r₁ ^ (-α) + ∑ k ∈ latticeBox d N, m k * (Cb * R ^ (-β)) +
          C₀ * (B * 2 ^ ((d : ℝ) / 2) * Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2))))
        ≤ A * R ^ (-β) + Cb * G * R ^ (-β) + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-β) := by
          gcongr
      _ = (A + Cb * G + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce)) * R ^ (-β) := by ring
      _ ≤ C * R ^ (-β) := by
          refine mul_le_mul_of_nonneg_right ?_ hRβ
          rw [hCdef]
          linarith

end QSH
