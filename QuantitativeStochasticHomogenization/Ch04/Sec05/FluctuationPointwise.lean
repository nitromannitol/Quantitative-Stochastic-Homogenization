import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationEstimate

/-!
# Step 3 of the proof of Proposition 4.12

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.5, Step 3: from the block estimate (4.117) to (4.115),
`X(R, ·, z) = 𝒪_s(C R^{-β})` for every `R ≥ 1` and `z`. With `r = R^{η₁}` the additivity (4.116)
replaces `X(R, ·, z)` by `∫ Φ_{z,√(R²-r²)} X(r)`; the heat kernel is cut along the cells of side `R`
around `z`, each cell contributes a block of (4.117) weighted by the maximum of the kernel on the
cell, the Riemann sum of these maxima is bounded (`sum_latticeBox_prod_exp_le`), and the cells
farther than `N R` with `N ≥ R` carry a Gaussian tail.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {s δ α B A : ℝ}

/-- The maximum of `Φ_{z,ρ}` on the cell `z + R k + [-R/2, R/2)^d` given by
`heatKernel_le_of_mem_latticeCell`. -/
noncomputable def cellMax (ρ : ℝ) (k : LatticeIndex d) : ℝ :=
  (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) * ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16)

theorem cellMax_pos {ρ : ℝ} (hρ : 0 < ρ) (k : LatticeIndex d) : 0 < cellMax ρ k := by
  unfold cellMax
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Finset.prod_pos fun i _ => Real.exp_pos _)

/-- `R^d ∑_{|k| ≤ N} max_{cell k} Φ_{z,ρ} ≤ (2π)^{-d/2} G^d` for `R²/2 ≤ ρ² `. -/
theorem riemann_sum_cellMax_le {R ρ : ℝ} (hR : 0 < R) (hρR : R ^ 2 / 2 ≤ ρ ^ 2)
    (N : ℕ) :
    ∑ k ∈ latticeBox d N, R ^ d * cellMax ρ k ≤
      (2 * Real.pi) ^ (-(d : ℝ) / 2) * latticeGaussianConst ^ d := by
  unfold cellMax
  have e : ∑ k ∈ latticeBox d N, R ^ d * ((4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) *
      ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16)) = R ^ d * (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) *
      ∑ k ∈ latticeBox d N, ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h1 : R ^ d * (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
    have h2 : (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) ≤ (2 * Real.pi * R ^ 2) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos])
        (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    have h3 : (2 * Real.pi * R ^ 2) ^ (-(d : ℝ) / 2) = (2 * Real.pi) ^ (-(d : ℝ) / 2) * R ^ (-(d : ℝ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast R 2,
        ← Real.rpow_mul hR.le]
      congr 2
      push_cast
      ring
    rw [h3] at h2
    calc R ^ d * (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2)
        ≤ R ^ d * ((2 * Real.pi) ^ (-(d : ℝ) / 2) * R ^ (-(d : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
          rw [mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hR, add_neg_cancel,
            Real.rpow_zero, mul_one]
  have hG := sum_latticeBox_prod_exp_le (d := d) N
  have hS : 0 ≤ ∑ k ∈ latticeBox d N, ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16) :=
    Finset.sum_nonneg fun k _ => (Finset.prod_pos fun i _ => Real.exp_pos _).le
  calc R ^ d * (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) *
        ∑ k ∈ latticeBox d N, ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16)
      ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) *
        ∑ k ∈ latticeBox d N, ∏ i, Real.exp (-((k i : ℝ) ^ 2) / 16) :=
        mul_le_mul_of_nonneg_right h1 hS
    _ ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) * latticeGaussianConst ^ d :=
        mul_le_mul_of_nonneg_left hG (by positivity)

theorem sum_indicator_cellAt_add (z : Vec d) {L : ℝ} (hL : 0 < L) (N : ℕ) (h : Vec d → ℝ)
    (y : Vec d) :
    ∑ k ∈ latticeBox d N, (cellAt z L k).indicator h y + (boxAt z L N)ᶜ.indicator h y = h y := by
  classical
  have e : ∀ k, (cellAt z L k).indicator h y = (latticeCell L k).indicator (fun w => h (w + z))
      (y - z) := by
    intro k
    by_cases hy : y - z ∈ latticeCell L k
    · rw [Set.indicator_of_mem (show y ∈ cellAt z L k from hy), Set.indicator_of_mem hy,
        sub_add_cancel]
    · rw [Set.indicator_of_notMem (show y ∉ cellAt z L k from hy), Set.indicator_of_notMem hy]
  simp only [e]
  rw [sum_indicator_latticeCell hL, sub_add_cancel]
  by_cases hb : cellIndex L (y - z) ∈ latticeBox d N
  · simp only [hb, ↓reduceIte]
    rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (show y ∈ boxAt z L N from hb)),
      add_zero]
  · simp only [hb, ↓reduceIte]
    rw [Set.indicator_of_mem (show y ∈ (boxAt z L N)ᶜ from hb), zero_add]

/-- **Step 3 of the proof of Proposition 4.12, (4.115)**: under the hypotheses of (4.117), the
fields themselves are `𝒪_s(C R^{-β})` at every point. -/
theorem exists_centeredOsBound_field [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (hF : HasUnitRange P F) (hmono : Monotone F) (hs1 : 1 < s) (hs2 : s ≤ 2)
    (hB0 : 0 < B) (hA0 : 0 < A) {η₁ η₂ β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ (d : ℝ) / 2)
    (hδ : 0 < δ) (hη₁ : 0 < η₁) (hη₁₂ : η₁ < η₂) (hη₂ : η₂ * (1 + δ) < 1)
    (hα : β < η₁ * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : CenteredLocalFields P F s δ α B A) (R : ℝ), 1 ≤ R → ∀ z : Vec d,
      CenteredOsBound P (fun a => X.field R a z) s (C * R ^ (-β)) := by
  classical
  obtain ⟨Cb, hCb, hBlock⟩ := exists_blockBound hd hF hmono hs1 hs2 hB0 hA0 hβ0 hβ hδ hη₁ hη₁₂
    hη₂ hα
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_abs_le hs1 hs2
  obtain ⟨Ce, hCe, hexp⟩ := exists_exp_neg_rpow_le (c := 1 / 8) (κ := 2) (by norm_num)
    (by norm_num) β
  have hη₁1 : η₁ < 1 := by
    have : η₂ ≤ η₂ * (1 + δ) := le_mul_of_one_le_right (hη₁.trans hη₁₂).le (by linarith)
    linarith
  set R₃ : ℝ := max 2 ((2 : ℝ) ^ (2 - 2 * η₁)⁻¹) with hR₃def
  have hB := hB0
  have hA := hA0
  set G : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) * latticeGaussianConst ^ d with hGdef
  have hG : 0 ≤ G := by have := latticeGaussianConst_nonneg; positivity
  set C : ℝ := A + Cb * G + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) +
    C₀ * B * R₃ ^ β with hCdef
  have hR₃ : 0 < R₃ := by positivity
  have hC1 : 0 ≤ A + Cb * G + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) := by positivity
  refine ⟨C, by positivity, fun X R hR z => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRβ : 0 ≤ R ^ (-β) := Real.rpow_nonneg hR0.le _
  by_cases hRs : R < R₃
  · have h := h₀ P (fun a => X.field R a z) B
      ((X.measurable R).comp (measurable_id.prodMk measurable_const)) hB
      (fun a => X.abs_le R a z) (X.centered R z)
    refine h.mono_scale ?_
    have h2 : 1 ≤ R₃ ^ β * R ^ (-β) := by
      have h3 : R₃ ^ (-β) ≤ R ^ (-β) := Real.rpow_le_rpow_of_nonpos hR0 hRs.le (by linarith)
      have h4 : R₃ ^ β * R₃ ^ (-β) = 1 := by
        rw [← Real.rpow_add hR₃, add_neg_cancel, Real.rpow_zero]
      calc (1 : ℝ) = R₃ ^ β * R₃ ^ (-β) := h4.symm
        _ ≤ R₃ ^ β * R ^ (-β) := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hR₃.le _)
    calc C₀ * B ≤ C₀ * B * (R₃ ^ β * R ^ (-β)) :=
          le_mul_of_one_le_right (by positivity) h2
      _ = (C₀ * B * R₃ ^ β) * R ^ (-β) := by ring
      _ ≤ C * R ^ (-β) := mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) hRβ
  push Not at hRs
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hRs
  have hR2η : 2 ≤ R ^ (2 - 2 * η₁) :=
    le_rpow_of_rpow_inv_le (by norm_num) (by linarith) ((le_max_right _ _).trans hRs)
  set r : ℝ := R ^ η₁ with hrdef
  have hr1 : 1 ≤ r := Real.one_le_rpow hR hη₁.le
  have hrR : r < R := by
    calc r < R ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) hη₁1
      _ = R := Real.rpow_one R
  have hr2 : r ^ 2 ≤ R ^ 2 / 2 := by
    have e : R ^ 2 = r ^ 2 * R ^ (2 - 2 * η₁) := by
      rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_natCast (R ^ η₁), ← Real.rpow_mul hR0.le,
        ← Real.rpow_add hR0]
      congr 1
      push_cast
      ring
    have hr0 : 0 ≤ r ^ 2 := sq_nonneg r
    rw [e]
    nlinarith
  set ρ : ℝ := Real.sqrt (R ^ 2 - r ^ 2) with hρdef
  have hρsq : ρ ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (by nlinarith)
  have hρR2 : R ^ 2 / 2 ≤ ρ ^ 2 := by rw [hρsq]; linarith
  have hρR : ρ ≤ R := by
    rw [hρdef]
    calc Real.sqrt (R ^ 2 - r ^ 2) ≤ Real.sqrt (R ^ 2) :=
          Real.sqrt_le_sqrt (by have := sq_nonneg r; linarith)
      _ = R := Real.sqrt_sq hR0.le
  have hadd := X.additive r R hr1 hrR z
  set N : ℕ := ⌈R⌉₊ with hNdef
  have hNR : R ≤ N := Nat.le_ceil R
  set S : Set (Vec d) := (boxAt z R N)ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_boxAt z hR0 N).compl
  set w : LatticeIndex d → Vec d → ℝ :=
    fun k y => (cellMax ρ k)⁻¹ * (cellAt z R k).indicator (heatKernel z ρ) y with hwdef
  have hwm : ∀ k, Measurable (w k) := fun k =>
    measurable_const.mul (((measurable_heatKernel_prod ρ).comp
      (measurable_const.prodMk measurable_id)).indicator (measurableSet_cellAt z R k))
  have hw1 : ∀ k y, |w k y| ≤ 1 := by
    intro k y
    have hm := cellMax_pos hρ k
    by_cases hy : y ∈ cellAt z R k
    · simp only [hwdef, Set.indicator_of_mem hy]
      rw [abs_mul, abs_inv, abs_of_pos hm, abs_of_nonneg (heatKernel_nonneg z ρ y),
        inv_mul_le_iff₀ hm, mul_one]
      exact heatKernel_le_of_mem_latticeCell hρ hρR hy
    · simp only [hwdef, Set.indicator_of_notMem hy, mul_zero, abs_zero]
      exact zero_le_one
  have hwz : ∀ k y, y ∉ closedCube (z + R • latticeShift k) R → w k y = 0 := by
    intro k y hy
    simp only [hwdef, Set.indicator_of_notMem (fun h => hy (cellAt_subset_closedCube z R k h)),
      mul_zero]
  have hpiece : ∀ k ∈ latticeBox d N, CenteredOsBound P
      (fun a => ∫ y, (cellAt z R k).indicator (heatKernel z ρ) y * X.field r a y) s
      (cellMax ρ k * (R ^ d * (Cb * R ^ (-β)))) := by
    intro k _
    have h1 := centeredOsBound_of_rpow_neg_mul hR0 (hBlock X R R hR le_rfl r le_rfl
      (Real.rpow_le_rpow_of_exponent_le hR hη₁₂.le) _ (w k) (hwm k) (hw1 k) (hwz k))
    have h2 := h1.const_mul (cellMax_pos hρ k)
    convert h2 using 1
    funext a
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [hwdef]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (cellMax_pos hρ k).ne', one_mul]
  have hbox : (latticeBox d N).Nonempty := ⟨0, mem_latticeBox.mpr fun i => by simp⟩
  have hsum := centeredOsBound_finset_sum_le (latticeBox d N) hbox hpiece
  have hsumle : ∑ k ∈ latticeBox d N, cellMax ρ k * (R ^ d * (Cb * R ^ (-β))) ≤
      Cb * G * R ^ (-β) := by
    have e : ∑ k ∈ latticeBox d N, cellMax ρ k * (R ^ d * (Cb * R ^ (-β))) =
        (∑ k ∈ latticeBox d N, R ^ d * cellMax ρ k) * (Cb * R ^ (-β)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    calc (∑ k ∈ latticeBox d N, R ^ d * cellMax ρ k) * (Cb * R ^ (-β))
        ≤ G * (Cb * R ^ (-β)) :=
          mul_le_mul_of_nonneg_right (riemann_sum_cellMax_le hR0 hρR2 N)
            (mul_nonneg hCb.le hRβ)
      _ = Cb * G * R ^ (-β) := by ring
  have hfarS : ∀ y ∈ S, (N : ℝ) * R ≤ euclideanNorm (y - z) := by
    intro y hy
    obtain ⟨i, hi⟩ := exists_le_abs_of_cellIndex_notMem hR0 hy
    have h1 : |(y - z) i| ≤ euclideanNorm (y - z) := abs_apply_le_euclideanNorm' (y - z) i
    nlinarith
  have hΦi : Integrable (S.indicator (heatKernel z ρ)) := (integrable_heatKernel z hρ).indicator hSm
  have hΦm : Measurable (S.indicator (heatKernel z ρ)) :=
    ((measurable_heatKernel_prod ρ).comp (measurable_const.prodMk measurable_id)).indicator hSm
  set b : ℝ := B * (2 ^ ((d : ℝ) / 2) * Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2))))
    with hbdef
  have hb : 0 < b := by positivity
  have hfarB : ∀ a, |∫ y, S.indicator (heatKernel z ρ) y * X.field r a y| ≤ b := by
    intro a
    refine (abs_integral_mul_le (X.abs_le r) hΦi a).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB.le
    have e : (fun y => |S.indicator (heatKernel z ρ) y|) = S.indicator (heatKernel z ρ) := by
      funext y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, abs_of_nonneg (heatKernel_nonneg z ρ y)]
      · rw [Set.indicator_of_notMem hy, abs_zero]
    rw [e, integral_indicator hSm]
    exact setIntegral_heatKernel_le_of_far z hρ (by positivity) hSm hfarS
  have hfar := h₀ P _ b (measurable_integral_mul hΦm (X.measurable r)) hb hfarB
    (integral_integral_mul_eq_zero (X.measurable r) (X.abs_le r) (X.centered r) hΦi)
  have hble : C₀ * b ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-β) := by
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
    have h2 := hexp R hR
    have hB' : 0 ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2)) := by positivity
    calc C₀ * b = C₀ * (B * 2 ^ ((d : ℝ) / 2)) *
          Real.exp (-(((N : ℝ) * R) ^ 2 / (8 * ρ ^ 2))) := by rw [hbdef]; ring
      _ ≤ C₀ * (B * 2 ^ ((d : ℝ) / 2)) * (Ce * R ^ (-β)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hB'
      _ = C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-β) := by ring
  have hall := (hadd.add hsum).add hfar
  refine hall.congr_ae ((X.measurable R).comp (measurable_id.prodMk measurable_const))
    (Filter.Eventually.of_forall fun a => ?_) |>.mono_scale ?_
  · have hpt : (fun y => heatKernel z ρ y * X.field r a y) = fun y =>
        (∑ k ∈ latticeBox d N, (cellAt z R k).indicator (heatKernel z ρ) y * X.field r a y) +
          S.indicator (heatKernel z ρ) y * X.field r a y := by
      funext y
      rw [← Finset.sum_mul, ← add_mul, sum_indicator_cellAt_add z hR0 N]
    have hik : ∀ k, Integrable fun y => (cellAt z R k).indicator (heatKernel z ρ) y *
        X.field r a y := fun k =>
      X.integrable_mul r a ((integrable_heatKernel z hρ).indicator (measurableSet_cellAt z R k))
    have hiS : Integrable fun y => S.indicator (heatKernel z ρ) y * X.field r a y :=
      X.integrable_mul r a hΦi
    have hA1 : Integrable fun y => ∑ k ∈ latticeBox d N,
        (cellAt z R k).indicator (heatKernel z ρ) y * X.field r a y :=
      integrable_finsetSum _ fun k _ => hik k
    have hint : ∫ y, heatKernel z ρ y * X.field r a y =
        (∑ k ∈ latticeBox d N, ∫ y, (cellAt z R k).indicator (heatKernel z ρ) y *
          X.field r a y) + ∫ y, S.indicator (heatKernel z ρ) y * X.field r a y := by
      rw [hpt]
      calc ∫ y, ((∑ k ∈ latticeBox d N, (cellAt z R k).indicator (heatKernel z ρ) y *
            X.field r a y) + S.indicator (heatKernel z ρ) y * X.field r a y)
          = (∫ y, ∑ k ∈ latticeBox d N, (cellAt z R k).indicator (heatKernel z ρ) y *
            X.field r a y) + ∫ y, S.indicator (heatKernel z ρ) y * X.field r a y :=
            integral_add hA1 hiS
        _ = _ := by rw [integral_finsetSum _ fun k _ => hik k]
    show _ = X.field R a z
    beta_reduce
    rw [hint]
    ring
  · have hr : A * r ^ (-α) ≤ A * R ^ (-β) := by
      refine mul_le_mul_of_nonneg_left ?_ hA.le
      rw [hrdef, ← Real.rpow_mul hR0.le]
      have e : η₁ * -α = -(η₁ * α) := by ring
      exact Real.rpow_le_rpow_of_exponent_le hR (by rw [e]; linarith)
    calc A * r ^ (-α) + ∑ k ∈ latticeBox d N,
          cellMax ρ k * (R ^ d * (Cb * R ^ (-β))) + C₀ * b
        ≤ A * R ^ (-β) + Cb * G * R ^ (-β) +
          C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce) * R ^ (-β) := by gcongr
      _ = (A + Cb * G + C₀ * (B * 2 ^ ((d : ℝ) / 2) * Ce)) * R ^ (-β) := by ring
      _ ≤ C * R ^ (-β) := by
          refine mul_le_mul_of_nonneg_right ?_ hRβ
          rw [hCdef]
          have : 0 ≤ C₀ * B * R₃ ^ β := by positivity
          linarith

end QSH
