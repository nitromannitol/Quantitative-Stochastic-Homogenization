import QuantitativeStochasticHomogenization.Ch05.Sec04.Lemma529Clt

/-!
# Lemma 5.29 (ii): blocks supported in a boundary layer

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29 (ii), (5.91)-(5.92), for centered local additive fields: for `b ∈ [0, 1]`,
`r ∈ [R^{b η₁}, R^{b/(1+δ)}]` and `f` with `|f| ≤ 1` supported in `□_R(z) \ □_{R-R^b}(z)`,
`R^{-d} ∫ f X(r) = 𝒪_s(C R^{-d/2-(1-b)/2})`. The block is cut along the cells of side `L = R^b`;
at most `8 d (2N+1)^{d-1}` cells, `N ≤ R/(2L) + 2`, meet the support, each contributes a block of
side `L` bounded by Lemma 5.29 (i), and the cells are coloured by their residues modulo `8`, so
that cells of the same colour have neighbourhoods of radius `r^{1+δ} ≤ L` at distance larger than
one (Lemma A.12).
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

/-- The residue of a lattice index modulo `8`. -/
def latticeResidue8 (k : LatticeIndex d) : Fin d → ZMod 8 := fun i => (k i : ZMod 8)

/-- Neighbourhoods of radius at most `L` of the closed cubes of side `L ≥ 1` around `z + L k` and
`z + L k'`, for distinct `k, k'` with the same residue modulo `8`, are separated by a unit. -/
theorem separatedByUnit_of_latticeResidue8 {L ρ : ℝ} (hL : 1 ≤ L) (hρ : ρ ≤ L) {z : Vec d}
    {k k' : LatticeIndex d} (hkk : k ≠ k') (hres : latticeResidue8 k = latticeResidue8 k') :
    SeparatedByUnit (euclideanThickening ρ (closedCube (z + L • latticeShift k) L))
      (euclideanThickening ρ (closedCube (z + L • latticeShift k') L)) := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := Function.ne_iff.mp hkk
  have hdvd : (8 : ℤ) ∣ k i - k' i := by
    have := congrFun hres i
    simp only [latticeResidue8] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this.symm
  have h8 : (8 : ℝ) ≤ |(k i : ℝ) - k' i| := by
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hi (by linarith)
    have h1 : (8 : ℤ) ≤ |k i - k' i| := by
      rw [hm, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 8)]
      have : 1 ≤ |m| := Int.one_le_abs hm0
      linarith
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    exact this
  refine ⟨2 * L, by linarith, fun x hx y hy => ?_⟩
  have hx' := abs_sub_lt_of_mem_euclideanThickening_closedCube hx i
  have hy' := abs_sub_lt_of_mem_euclideanThickening_closedCube hy i
  simp only [Pi.add_apply, Pi.smul_apply, latticeShift, smul_eq_mul] at hx' hy'
  have hcoord := abs_apply_le_euclideanNorm' (x - y) i
  simp only [Pi.sub_apply] at hcoord
  have hL0 : 0 ≤ L := by linarith
  have hdist : L * |(k i : ℝ) - k' i| ≤ |x i - y i| + |x i - (z i + L * k i)| +
      |y i - (z i + L * k' i)| := by
    rw [← abs_of_nonneg hL0, ← abs_mul, abs_of_nonneg hL0]
    calc |L * ((k i : ℝ) - k' i)| = |((z i + L * k i) - x i) + (x i - y i) +
          (y i - (z i + L * k' i))| := by ring_nf
      _ ≤ |(z i + L * k i) - x i| + |x i - y i| + |y i - (z i + L * k' i)| := abs_add_three _ _ _
      _ = |x i - y i| + |x i - (z i + L * k i)| + |y i - (z i + L * k' i)| := by
          rw [abs_sub_comm (z i + L * k i) (x i)]
          ring
  nlinarith

/-- The cells of side `L` of the box `|k| ≤ N` with a coordinate of modulus at least `R/(2L) - 1`. -/
noncomputable def layerCells (R L : ℝ) (N : ℕ) : Finset (LatticeIndex d) := by
  classical
  exact (latticeBox d N).filter fun k => ∃ i, R / (2 * L) - 1 ≤ |(k i : ℝ)|

/-- The cell of a point of the boundary layer `□_R(z) \ □_{R-L}(z)` is a layer cell. -/
theorem cellIndex_mem_layerCells {z : Vec d} {R L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : R / (2 * L) + 1 ≤ N) {y : Vec d} (hy : y ∈ cube z R \ cube z (R - L)) :
    cellIndex L (y - z) ∈ layerCells R L N := by
  classical
  obtain ⟨hyR, hyL⟩ := hy
  simp only [layerCells, Finset.mem_filter, mem_latticeBox, cellIndex, Pi.sub_apply]
  have hfl : ∀ t : ℝ, (⌊t⌋ : ℝ) ≤ t ∧ t - 1 < ⌊t⌋ := fun t => ⟨Int.floor_le t, by
    have := Int.lt_floor_add_one t; linarith⟩
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := hyR i
    rw [abs_lt] at h1
    obtain ⟨hf1, hf2⟩ := hfl ((y i - z i) / L + 1 / 2)
    have hRL : R / (2 * L) * L = R / 2 := by field_simp
    have e1 : (y i - z i) / L < R / (2 * L) := by
      rw [div_lt_iff₀ hL, hRL]; linarith
    have e2 : -(R / (2 * L)) < (y i - z i) / L := by
      rw [lt_div_iff₀ hL, neg_mul, hRL]; linarith
    have : |(⌊(y i - z i) / L + 1 / 2⌋ : ℝ)| ≤ N := by
      rw [abs_le]; constructor <;> linarith
    exact_mod_cast this
  · simp only [cube, Set.mem_ofPred_eq, not_forall, not_lt] at hyL
    obtain ⟨i, hi⟩ := hyL
    refine ⟨i, ?_⟩
    obtain ⟨hf1, hf2⟩ := hfl ((y i - z i) / L + 1 / 2)
    rcases le_total 0 (y i - z i) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hi
      have e : R / (2 * L) ≤ (y i - z i) / L + 1 / 2 := by
        have : (R - L) / 2 / L ≤ (y i - z i) / L := div_le_div_of_nonneg_right hi hL.le
        have e' : (R - L) / 2 / L = R / (2 * L) - 1 / 2 := by field_simp
        linarith
      exact (by linarith : R / (2 * L) - 1 ≤ (⌊(y i - z i) / L + 1 / 2⌋ : ℝ)).trans (le_abs_self _)
    · rw [abs_of_nonpos hneg] at hi
      have e : (y i - z i) / L + 1 / 2 ≤ -(R / (2 * L)) + 1 := by
        have : (y i - z i) / L ≤ -((R - L) / 2) / L := div_le_div_of_nonneg_right (by linarith) hL.le
        have e' : -((R - L) / 2) / L = -(R / (2 * L)) + 1 / 2 := by field_simp; ring
        linarith
      exact (by linarith : R / (2 * L) - 1 ≤ -(⌊(y i - z i) / L + 1 / 2⌋ : ℝ)).trans (neg_le_abs _)

/-- **The number of layer cells**: at most `8 d (2N+1)^{d-1}` for `N ≤ R/(2L) + 2`. -/
theorem card_layerCells_le {R L : ℝ} {N : ℕ} (hN : (N : ℝ) ≤ R / (2 * L) + 2) :
    (layerCells (d := d) R L N).card ≤ 8 * d * (2 * N + 1) ^ (d - 1) := by
  classical
  set B : Finset ℤ := Finset.Icc (-(N : ℤ)) (-((N : ℤ) - 3)) ∪ Finset.Icc ((N : ℤ) - 3) N
    with hBdef
  have hB : B.card ≤ 8 := by
    refine (Finset.card_union_le _ _).trans ?_
    simp only [Int.card_Icc]
    omega
  have hsub : layerCells (d := d) R L N ⊆
      Finset.univ.biUnion fun i => (latticeBox d N).filter fun k => k i ∈ B := by
    intro k hk
    simp only [layerCells, Finset.mem_filter] at hk
    obtain ⟨hkb, i, hi⟩ := hk
    have hki : |k i| ≤ (N : ℤ) := mem_latticeBox.mp hkb i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    refine ⟨i, hkb, ?_⟩
    have h3 : ((N : ℤ) - 3 : ℝ) ≤ |(k i : ℝ)| := by push_cast; linarith
    have h3' : (N : ℤ) - 3 ≤ |k i| := by
      have : (((N : ℤ) - 3 : ℤ) : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by push_cast at h3 ⊢; exact h3
      exact_mod_cast this
    simp only [hBdef, Finset.mem_union, Finset.mem_Icc]
    rcases abs_le.mp hki with ⟨h1, h2⟩
    rcases le_abs'.mp h3' with h | h <;> [left; right] <;> constructor <;> omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ i : Fin d, ((latticeBox d N).filter fun k => k i ∈ B).card
      ≤ ∑ _i : Fin d, B.card * (2 * N + 1) ^ (d - 1) :=
        Finset.sum_le_sum fun i _ => card_filter_coord_le B i
    _ = d * (B.card * (2 * N + 1) ^ (d - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ d * (8 * (2 * N + 1) ^ (d - 1)) := by gcongr
    _ = 8 * d * (2 * N + 1) ^ (d - 1) := by ring

theorem sum_indicator_cellAt_finset (z : Vec d) {L : ℝ} (hL : 0 < L) (T : Finset (LatticeIndex d))
    (h : Vec d → ℝ) (y : Vec d) :
    ∑ k ∈ T, (cellAt z L k).indicator h y = if cellIndex L (y - z) ∈ T then h y else 0 := by
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

/-- The constant of the boundary layer. -/
noncomputable def layerConst (d : ℕ) : ℝ := Real.sqrt (2 * 8 ^ d) * Real.sqrt (8 * d * 6 ^ (d - 1))

theorem layerConst_nonneg (d : ℕ) : 0 ≤ layerConst d := by unfold layerConst; positivity

/-- The scale of the boundary layer: with `L = R^b`, `m ≤ 8 d 6^{d-1} R^{(1-b)(d-1)}`,
`R^{-d} (2·8^d)^{1/2} m^{1/2} L^d C L^{-d/2} ≤ K_d C R^{-d/2-(1-b)/2}`. -/
theorem scale_layer_le (hd : 1 ≤ d) {R b C m : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hm : m ≤ 8 * d * 6 ^ (d - 1) * R ^ ((1 - b) * ((d - 1 : ℕ) : ℝ))) :
    R ^ (-(d : ℝ)) * (Real.sqrt (2 * 8 ^ d) * (Real.sqrt m *
      ((R ^ b) ^ d * (C * (R ^ b) ^ (-((d : ℝ) / 2)))))) ≤
      layerConst d * C * R ^ (-(d : ℝ) / 2 - (1 - b) / 2) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hdm : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]; simp
  have hsq : Real.sqrt m ≤ Real.sqrt (8 * d * 6 ^ (d - 1)) * R ^ ((1 - b) * ((d : ℝ) - 1) / 2) := by
    calc Real.sqrt m ≤ Real.sqrt (8 * d * 6 ^ (d - 1) * R ^ ((1 - b) * ((d - 1 : ℕ) : ℝ))) :=
          Real.sqrt_le_sqrt hm
      _ = Real.sqrt (8 * d * 6 ^ (d - 1)) * R ^ ((1 - b) * ((d : ℝ) - 1) / 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (R ^ _), ← Real.rpow_mul hR0.le,
            hdm]
          ring_nf
  have hexp : R ^ (-(d : ℝ)) * ((R ^ b) ^ d * (R ^ b) ^ (-((d : ℝ) / 2))) *
      R ^ ((1 - b) * ((d : ℝ) - 1) / 2) = R ^ (-(d : ℝ) / 2 - (1 - b) / 2) := by
    rw [← Real.rpow_natCast (R ^ b), ← Real.rpow_mul hR0.le, ← Real.rpow_mul hR0.le,
      ← Real.rpow_add hR0, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1
    ring
  have hA : 0 ≤ Real.sqrt (2 * 8 ^ d) := Real.sqrt_nonneg _
  calc R ^ (-(d : ℝ)) * (Real.sqrt (2 * 8 ^ d) * (Real.sqrt m *
        ((R ^ b) ^ d * (C * (R ^ b) ^ (-((d : ℝ) / 2))))))
      = Real.sqrt (2 * 8 ^ d) * C * Real.sqrt m *
          (R ^ (-(d : ℝ)) * ((R ^ b) ^ d * (R ^ b) ^ (-((d : ℝ) / 2)))) := by ring
    _ ≤ Real.sqrt (2 * 8 ^ d) * C * (Real.sqrt (8 * d * 6 ^ (d - 1)) *
          R ^ ((1 - b) * ((d : ℝ) - 1) / 2)) *
          (R ^ (-(d : ℝ)) * ((R ^ b) ^ d * (R ^ b) ^ (-((d : ℝ) / 2)))) := by gcongr
    _ = layerConst d * C * (R ^ (-(d : ℝ)) * ((R ^ b) ^ d * (R ^ b) ^ (-((d : ℝ) / 2))) *
          R ^ ((1 - b) * ((d : ℝ) - 1) / 2)) := by
        unfold layerConst
        ring
    _ = layerConst d * C * R ^ (-(d : ℝ) / 2 - (1 - b) / 2) := by rw [hexp]

variable {Ω : Type*} [MeasurableSpace Ω] {F : Set (Vec d) → MeasurableSpace Ω} {s δ α B A : ℝ}

/-- **Lemma 5.29 (ii), (5.91)-(5.92)**, for centered local additive fields. -/
theorem exists_blockBound_layer (hd : 1 ≤ d) (hmono : Monotone F) (hs1 : 1 < s) (hs2 : s ≤ 2)
    (hB0 : 0 < B) (hA0 : 0 < A) {η₁ η₂ : ℝ} (hδ : 0 < δ) (hη₁ : 0 < η₁) (hη₁₂ : η₁ < η₂)
    (hη₂ : η₂ * (1 + δ) < 1) (hα : (d : ℝ) / 2 < η₁ * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure Ω) [IsProbabilityMeasure P], HasUnitRange P F →
      ∀ (X : CenteredLocalFields P F s δ α B A) (R : ℝ), 1 ≤ R → ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ r : ℝ, R ^ (b * η₁) ≤ r → r ≤ R ^ (b / (1 + δ)) → ∀ (z : Vec d) (f : Vec d → ℝ),
      Measurable f → (∀ x, |f x| ≤ 1) → (∀ x, f x ≠ 0 → x ∈ cube z R \ cube z (R - R ^ b)) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x) s
        (C * R ^ (-(d : ℝ) / 2 - (1 - b) / 2)) := by
  classical
  obtain ⟨Cb, hCb, hblk⟩ := exists_blockBound_all_scales (Ω := Ω) (F := F) hd hmono hs1 hs2
    hB0 hA0 (β := (d : ℝ) / 2) (by positivity) le_rfl hδ hη₁ hη₁₂ hη₂ hα
  refine ⟨layerConst d * Cb + 1, by have := layerConst_nonneg d; positivity, ?_⟩
  intro P _ hF X R hR b hb0 hb1 r hr1 hr2 z f hf hf1 hfsupp
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set L : ℝ := R ^ b with hLdef
  have hL1 : 1 ≤ L := Real.one_le_rpow hR hb0
  have hL0 : 0 < L := by linarith
  have hLR : L ≤ R := by
    calc L ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hb1
      _ = R := Real.rpow_one R
  have hbδ : b / (1 + δ) ≤ b := div_le_self hb0 (by linarith)
  have hrL : r ≤ L := hr2.trans (Real.rpow_le_rpow_of_exponent_le hR hbδ)
  have hLη : L ^ η₁ ≤ r := by rw [hLdef, ← Real.rpow_mul hR0.le]; exact hr1
  have hr1' : 1 ≤ r := (Real.one_le_rpow hL1 hη₁.le).trans hLη
  have hr0 : 0 < r := by linarith
  have hρ : r ^ (1 + δ) ≤ L := by
    calc r ^ (1 + δ) ≤ (R ^ (b / (1 + δ))) ^ (1 + δ) :=
          Real.rpow_le_rpow hr0.le hr2 (by linarith)
      _ = L := by
          rw [← Real.rpow_mul hR0.le, div_mul_cancel₀ _ (by linarith)]
  set N : ℕ := ⌈R / (2 * L)⌉₊ + 1 with hNdef
  have hN1 : R / (2 * L) + 1 ≤ N := by
    have := Nat.le_ceil (R / (2 * L))
    push_cast [hNdef]
    linarith
  have hN2 : (N : ℝ) ≤ R / (2 * L) + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ R / (2 * L) by positivity)
    push_cast [hNdef]
    linarith
  set T : Finset (LatticeIndex d) := layerCells R L N with hTdef
  have hT : T.Nonempty := by
    refine ⟨fun i => if i = ⟨0, hd⟩ then (N : ℤ) else 0, ?_⟩
    simp only [hTdef, layerCells, Finset.mem_filter, mem_latticeBox]
    refine ⟨fun i => ?_, ⟨0, hd⟩, ?_⟩
    · by_cases h : i = ⟨0, hd⟩
      · simp [h]
      · simp [h]
    · simp only [ite_true, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
      linarith
  set w : LatticeIndex d → Vec d → ℝ := fun k => (cellAt z L k).indicator f with hwdef
  have hwm : ∀ k, Measurable (w k) := fun k => hf.indicator (measurableSet_cellAt z L k)
  have hw1 : ∀ k y, |w k y| ≤ 1 := by
    intro k y
    by_cases hy : y ∈ cellAt z L k
    · simp only [hwdef, Set.indicator_of_mem hy]; exact hf1 y
    · simp only [hwdef, Set.indicator_of_notMem hy, abs_zero]; exact zero_le_one
  have hwz : ∀ k y, y ∉ closedCube (z + L • latticeShift k) L → w k y = 0 := fun k y hy =>
    Set.indicator_of_notMem (fun h => hy (cellAt_subset_closedCube z L k h)) _
  set θ : ℝ := L ^ d * (Cb * L ^ (-((d : ℝ) / 2))) with hθdef
  have hW : ∀ k, CenteredOsBound P (fun a => ∫ x, w k x * X.field r a x) s θ := fun k =>
    centeredOsBound_of_rpow_neg_mul hL0
      (hblk P hF X L hL1 r hLη hrL _ (w k) (hwm k) (hw1 k) (hwz k))
  set U : LatticeIndex d → Set (Vec d) :=
    fun k => euclideanThickening (r ^ (1 + δ)) (closedCube (z + L • latticeShift k) L) with hUdef
  have hloc : ∀ k, Measurable[F (U k)] (fun a => ∫ x, w k x * X.field r a x) := fun k =>
    measurable_integral_mul_local (X.isLocal r hr1' _ (measurableSet_closedCube _ _)) (hwm k)
      (hwz k)
  have : Nonempty T := hT.coe_sort
  have hsum := centeredOsBound_sum_of_colouring hF hmono (ι := T) (κ := Fin d → ZMod 8)
    (fun k => latticeResidue8 k.1) (U := fun k => U k.1)
    (fun k => measurableSet_euclideanThickening _ _)
    (fun k k' hkk hres => separatedByUnit_of_latticeResidue8 hL1 hρ
      (fun h => hkk (Subtype.ext h)) hres)
    (X := fun k a => ∫ x, w k.1 x * X.field r a x) (θ := fun _ => θ) (fun k => hloc k.1)
    (fun k => hW k.1)
  have hcard : (Fintype.card (Fin d → ZMod 8) : ℝ) = 8 ^ d := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  have hθ0 : 0 ≤ θ := by positivity
  have hsumθ : Real.sqrt (∑ _k : T, θ ^ 2) = Real.sqrt T.card * θ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hθ0]
  have e : (fun a => ∑ k : T, ∫ x, w k.1 x * X.field r a x) =
      fun a => ∑ k ∈ T, ∫ x, w k x * X.field r a x :=
    funext fun a => Finset.sum_coe_sort T (fun k => ∫ x, w k x * X.field r a x)
  rw [hcard, hsumθ, e] at hsum
  have h2 := hsum.const_mul (Real.rpow_pos_of_pos hR0 (-(d : ℝ)))
  have hfi := integrable_of_abs_le_one_of_closedCube hf hf1 hR0.le (fun x hx => by
    by_contra h
    exact hx (cube_subset_closedCube z R (hfsupp x h).1))
  refine (h2.congr_ae (measurable_block X r hf _) (Filter.Eventually.of_forall fun a => ?_)).mono_scale ?_
  · have hpt : (fun x => f x * X.field r a x) = fun x => ∑ k ∈ T, w k x * X.field r a x := by
      funext x
      rw [← Finset.sum_mul]
      congr 1
      simp only [hwdef]
      rw [sum_indicator_cellAt_finset z hL0 T f x]
      by_cases hfx : f x = 0
      · simp [hfx]
      · simp only [cellIndex_mem_layerCells hL0 hN1 (hfsupp x hfx), ↓reduceIte]
    have hik : ∀ k, Integrable fun x => w k x * X.field r a x := fun k =>
      X.integrable_mul r a (hfi.indicator (measurableSet_cellAt z L k))
    show R ^ (-(d : ℝ)) * ∑ k ∈ T, ∫ x, w k x * X.field r a x =
      R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x
    rw [hpt, integral_finsetSum _ fun k _ => hik k]
  · have hcardT : (T.card : ℝ) ≤ 8 * d * 6 ^ (d - 1) * R ^ ((1 - b) * ((d - 1 : ℕ) : ℝ)) := by
      have h1 : (T.card : ℝ) ≤ ((8 * d * (2 * N + 1) ^ (d - 1) : ℕ) : ℝ) := by
        exact_mod_cast card_layerCells_le hN2
      refine h1.trans ?_
      have hRL : R / L = R ^ (1 - b) := by
        rw [hLdef, Real.rpow_sub hR0, Real.rpow_one]
      have hRL1 : 1 ≤ R ^ (1 - b) := Real.one_le_rpow hR (by linarith)
      have h2N : (2 * (N : ℝ) + 1) ≤ 6 * R ^ (1 - b) := by
        have : R / (2 * L) = R ^ (1 - b) / 2 := by rw [← hRL]; ring
        rw [this] at hN2
        linarith
      push_cast
      have h3 : (2 * (N : ℝ) + 1) ^ (d - 1) ≤ (6 * R ^ (1 - b)) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) h2N _
      rw [mul_pow, ← Real.rpow_natCast (R ^ (1 - b)), ← Real.rpow_mul hR0.le] at h3
      calc 8 * (d : ℝ) * (2 * (N : ℝ) + 1) ^ (d - 1)
          ≤ 8 * d * (6 ^ (d - 1) * R ^ ((1 - b) * ((d - 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 8 * d * 6 ^ (d - 1) * R ^ ((1 - b) * ((d - 1 : ℕ) : ℝ)) := by ring
    have h3 := scale_layer_le hd hR hCb.le hcardT
    have hpos : 0 ≤ R ^ (-(d : ℝ) / 2 - (1 - b) / 2) := Real.rpow_nonneg hR0.le _
    calc R ^ (-(d : ℝ)) * (Real.sqrt (2 * 8 ^ d) * (Real.sqrt T.card * θ))
        ≤ layerConst d * Cb * R ^ (-(d : ℝ) / 2 - (1 - b) / 2) := h3
      _ ≤ (layerConst d * Cb + 1) * R ^ (-(d : ℝ) / 2 - (1 - b) / 2) := by nlinarith

end QSH
