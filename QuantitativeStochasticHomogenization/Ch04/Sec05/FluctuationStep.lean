import QuantitativeStochasticHomogenization.Ch04.Sec05.FluctuationCubes

/-!
# The induction step in the proof of Proposition 4.12

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Section 4.5, (4.118)–(4.119). For `R ∈ (R₁, 2R₁]` the block
`R^{-d} ∫ f X(r)` is split, after Step 1, into the `2^d` large cubes, the cells of the frame and
the far part. This file proves the splitting of the weight `g` (`heat_weight_decomposition`) and
the bound of the block under explicit conditions on the scales (`centeredOsBound_block_step`).

The inner scale is `r₁ = (R/2)^{η₁}`. The book takes `r₁ = R^{η₁}/2`, which lies below
`(R/2)^{η₁}`, the smallest scale allowed by the induction hypothesis at the side `R/2`; with
`r₁ = (R/2)^{η₁}` all the other constraints of the proof still hold for `R` large.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

/-- The cell `z + L k + [-L/2, L/2)^d`. -/
def cellAt (z : Vec d) (L : ℝ) (k : LatticeIndex d) : Set (Vec d) := {y | y - z ∈ latticeCell L k}

theorem measurableSet_cellAt (z : Vec d) (L : ℝ) (k : LatticeIndex d) :
    MeasurableSet (cellAt z L k) :=
  (measurableSet_latticeCell L k).preimage (measurable_id.sub measurable_const)

theorem cellAt_subset_closedCube (z : Vec d) (L : ℝ) (k : LatticeIndex d) :
    cellAt z L k ⊆ closedCube (z + L • latticeShift k) L := by
  intro y hy i
  have h := latticeCell_subset_closedCube L k hy i
  simp only [Pi.sub_apply, Pi.add_apply] at h ⊢
  rwa [show y i - (z i + (L • latticeShift k) i) = y i - z i - (L • latticeShift k) i by ring]

/-- The union of the cells with index in the box `|k| ≤ N`. -/
def boxAt (z : Vec d) (L : ℝ) (N : ℕ) : Set (Vec d) :=
  {y | cellIndex L (y - z) ∈ latticeBox d N}

theorem measurableSet_boxAt (z : Vec d) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    MeasurableSet (boxAt z L N) := by
  have e : boxAt z L N = ⋃ k ∈ latticeBox d N, cellAt z L k := by
    ext y
    simp only [boxAt, cellAt, Set.mem_ofPred_eq, Set.mem_iUnion, mem_latticeCell_iff hL,
      exists_prop, exists_eq_right']
  rw [e]
  exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_cellAt z L k

/-- The union of the large cubes. -/
def bigCubesAt (z : Vec d) (R R' : ℝ) : Set (Vec d) := ⋃ σ, bigCubeAt z R R' σ

theorem measurableSet_bigCubesAt (z : Vec d) (R R' : ℝ) : MeasurableSet (bigCubesAt z R R') :=
  MeasurableSet.iUnion fun _ => measurableSet_closedCube _ _

theorem bigCubeAt_subset_boxAt {z : Vec d} {R R' : ℝ} (hR' : 0 < R') {n : ℕ}
    (hn : R / 2 < ((n : ℝ) + 1) * R') (σ : Fin d → Bool) :
    bigCubeAt z R R' σ ⊆ boxAt z R' (n + 2) := by
  intro y hy
  by_contra h
  obtain ⟨i, hi⟩ := exists_le_abs_of_cellIndex_notMem hR' h
  have hc := bigCube_coord (sub_mem_bigCube_of_mem_bigCubeAt hy) i
  have hb : |(y - z) i| ≤ R / 2 + R' / 2 := by
    rw [abs_le]
    cases hσ : σ i
    · obtain ⟨h1, h2⟩ := hc.2 hσ
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hc.1 hσ
      constructor <;> linarith
  push_cast at hi
  nlinarith

/-- **The decomposition of the weight** in Step 2: for `n R' ≤ R/2 < (n+1) R'` and `N = n + 2`,
every function is the sum of its restrictions to the `2^d` large cubes, to the frame cells outside
them, and to the complement of the box of cells. -/
theorem heat_weight_decomposition {z : Vec d} {R R' : ℝ} (hR' : 0 < R') {n : ℕ}
    (hn : (n : ℝ) * R' ≤ R / 2) (hn' : R / 2 < ((n : ℝ) + 1) * R') (g : Vec d → ℝ) (y : Vec d) :
    g y = ∑ σ : Fin d → Bool, (bigCubeAt z R R' σ).indicator g y +
      ∑ k ∈ latticeFrame d (n + 2) n, (cellAt z R' k \ bigCubesAt z R R').indicator g y +
      (boxAt z R' (n + 2))ᶜ.indicator g y := by
  classical
  by_cases hU : y ∈ bigCubesAt z R R'
  · obtain ⟨σ₀, hσ₀⟩ := Set.mem_iUnion.mp hU
    have h1 : ∑ σ : Fin d → Bool, (bigCubeAt z R R' σ).indicator g y = g y := by
      rw [Finset.sum_eq_single σ₀]
      · exact Set.indicator_of_mem hσ₀ _
      · intro σ _ hσ
        refine Set.indicator_of_notMem (fun hy => ?_) _
        exact Set.disjoint_left.mp (bigCube_disjoint hR' hσ) (sub_mem_bigCube_of_mem_bigCubeAt hy)
          (sub_mem_bigCube_of_mem_bigCubeAt hσ₀)
      · intro h
        exact absurd (Finset.mem_univ σ₀) h
    have h2 : ∑ k ∈ latticeFrame d (n + 2) n,
        (cellAt z R' k \ bigCubesAt z R R').indicator g y = 0 :=
      Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (fun hy => hy.2 hU) _
    have h3 : (boxAt z R' (n + 2))ᶜ.indicator g y = 0 :=
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (bigCubeAt_subset_boxAt hR' hn' σ₀ hσ₀)) _
    rw [h1, h2, h3, add_zero, add_zero]
  · have h1 : ∑ σ : Fin d → Bool, (bigCubeAt z R R' σ).indicator g y = 0 :=
      Finset.sum_eq_zero fun σ _ =>
        Set.indicator_of_notMem (fun hy => hU (Set.mem_iUnion.mpr ⟨σ, hy⟩)) _
    have h2 : ∑ k ∈ latticeFrame d (n + 2) n,
        (cellAt z R' k \ bigCubesAt z R R').indicator g y =
        if cellIndex R' (y - z) ∈ latticeFrame d (n + 2) n then g y else 0 := by
      have e : ∀ k, (cellAt z R' k \ bigCubesAt z R R').indicator g y =
          if cellIndex R' (y - z) = k then g y else 0 := by
        intro k
        simp only [Set.indicator_apply, Set.mem_sdiff, cellAt, Set.mem_ofPred_eq,
          mem_latticeCell_iff hR', hU, not_false_eq_true, and_true]
      simp only [e]
      exact Finset.sum_ite_eq _ _ _
    rw [h1, h2, zero_add]
    by_cases hD : y ∈ boxAt z R' (n + 2)
    · have hfr : cellIndex R' (y - z) ∈ latticeFrame d (n + 2) n := by
        by_contra hk
        have hsub := latticeCell_subset_bigCube_of_notMem_frame (R := R) hn hR' hD hk
        have hmem : y - z ∈ latticeCell R' (cellIndex R' (y - z)) := (mem_latticeCell_iff hR').2 rfl
        refine hU (Set.mem_iUnion.mpr ⟨fun i => decide (0 < cellIndex R' (y - z) i), ?_⟩)
        have h := hsub hmem
        intro i
        have := h i
        simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
        rwa [show y i - (z i + bigCubeCenter R R' (fun i => decide (0 < cellIndex R' (y - z) i)) i)
          = y i - z i - bigCubeCenter R R' (fun i => decide (0 < cellIndex R' (y - z) i)) i by ring]
      simp only [hfr, ↓reduceIte]
      rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hD), add_zero]
    · have hfr : cellIndex R' (y - z) ∉ latticeFrame d (n + 2) n := fun h =>
        hD (Finset.mem_filter.mp h).1
      simp only [hfr, ↓reduceIte]
      rw [Set.indicator_of_mem hD, zero_add]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}
  {s δ α B A : ℝ}

theorem CenteredLocalFields.integrable_mul (X : CenteredLocalFields P F s δ α B A) (r : ℝ) (a : Ω)
    {w : Vec d → ℝ} (hw : Integrable w) : Integrable fun y => w y * X.field r a y :=
  hw.mul_bdd ((X.measurable r).comp measurable_prodMk_left).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact X.abs_le r a y)

theorem CenteredLocalFields.abs_heatAverage_le (X : CenteredLocalFields P F s δ α B A) (r : ℝ)
    (a : Ω) (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    |∫ y, heatKernel x ρ y * X.field r a y| ≤ B := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |heatKernel x ρ y * X.field r a y| ≤ ∫ y, heatKernel x ρ y * B := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
          ((integrable_heatKernel x hρ).mul_const _) (Filter.Eventually.of_forall fun y => ?_)
        show |heatKernel x ρ y * X.field r a y| ≤ heatKernel x ρ y * B
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg x ρ y)]
        exact mul_le_mul_of_nonneg_left (X.abs_le r a y) (heatKernel_nonneg x ρ y)
    _ = B := by rw [integral_mul_const, integral_heatKernel x hρ, one_mul]

/-- **The induction step** (4.119), for `R/2 ∈ [1, R₁]`, `r₁ = (R/2)^{η₁} < r`, an auxiliary side
`R'` with `n R' ≤ R/2 < (n+1) R'`, and the conditions on `r₁` and `R'` that make the induction
hypothesis applicable at the sides `R/2` and `R'` and the neighbourhoods of radius `r₁^{1+δ}` of
the large cubes separated. The scale is the sum of the four contributions: Step 1, the large
cubes, the frame cells and the far part. -/
theorem centeredOsBound_block_step [IsProbabilityMeasure P] (hd : 1 ≤ d) (hF : HasUnitRange P F)
    (hmono : Monotone F) (X : CenteredLocalFields P F s δ α B A) {η₁ η₂ β R₁ C : ℝ}
    (hA : BlockBound X η₁ η₂ β R₁ C) (hβ : β ≤ (d : ℝ) / 2) (hC : 0 ≤ C) {C₀ : ℝ}
    (hfar : ∀ (r₁ : ℝ) {z : Vec d} {R ρ t : ℝ}, 0 < R → 0 < ρ → 0 ≤ t → ∀ {f : Vec d → ℝ},
      Measurable f → (∀ x, |f x| ≤ 1) → (∀ x ∉ closedCube z R, f x = 0) →
      ∀ {S : Set (Vec d)}, MeasurableSet S →
      (∀ x ∈ closedCube z R, ∀ y ∈ S, t ≤ euclideanNorm (y - x)) →
      CenteredOsBound P (fun a => R ^ (-(d : ℝ)) *
        ∫ y, S.indicator (heatSmooth f ρ) y * X.field r₁ a y) s
        (C₀ * (B * 2 ^ ((d : ℝ) / 2) * Real.exp (-(t ^ 2 / (8 * ρ ^ 2))))))
    {R r r₁ R' : ℝ} {n : ℕ} (hR2 : 1 ≤ R / 2) (hRR₁ : R / 2 ≤ R₁) (hr₁ : 1 ≤ r₁)
    (hr₁r : r₁ < r) (hr₁lo : (R / 2) ^ η₁ ≤ r₁) (hr₁hi : r₁ ≤ (R / 2) ^ η₂)
    (hsep : 1 < R' - 2 * r₁ ^ (1 + δ)) (hR'1 : 1 ≤ R') (hR'R₁ : R' ≤ R₁)
    (hr₁lo' : R' ^ η₁ ≤ r₁) (hr₁hi' : r₁ ≤ R' ^ η₂) (hρ₁ : r₁ ^ (1 + δ) ≤ R' / 2)
    (hn : (n : ℝ) * R' ≤ R / 2) (hn' : R / 2 < ((n : ℝ) + 1) * R') (z : Vec d)
    {f : Vec d → ℝ} (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1)
    (hfz : ∀ x ∉ closedCube z R, f x = 0) :
    CenteredOsBound P (fun a => R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x) s
      (A * r₁ ^ (-α) + C * R ^ (-β) +
        R ^ (-(d : ℝ)) * (Real.sqrt (2 * 4 ^ d) * (Real.sqrt (latticeFrame d (n + 2) n).card *
          (R' ^ d * (C * R' ^ (-β))))) +
        C₀ * (B * 2 ^ ((d : ℝ) / 2) *
          Real.exp (-(R' ^ 2 / (8 * Real.sqrt (r ^ 2 - r₁ ^ 2) ^ 2))))) := by
  classical
  have hR0 : 0 < R := by linarith
  have hR'0 : 0 < R' := zero_lt_one.trans_le hR'1
  set ρ : ℝ := Real.sqrt (r ^ 2 - r₁ ^ 2) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (by nlinarith)
  set g : Vec d → ℝ := heatSmooth f ρ with hgdef
  have hfi := integrable_of_abs_le_one_of_closedCube hf hf1 hR0.le hfz
  have hgm : Measurable g := measurable_heatSmooth hf ρ
  have hgi : Integrable g := integrable_heatSmooth hfi hf hρ
  have hg1 : ∀ y, |g y| ≤ 1 := abs_heatSmooth_le_one hf1 hρ
  set U : Set (Vec d) := bigCubesAt z R R' with hUdef
  set T : Finset (LatticeIndex d) := latticeFrame d (n + 2) n with hTdef
  set S : Set (Vec d) := (boxAt z R' (n + 2))ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_boxAt z hR'0 _).compl
  have hT : T.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨mem_latticeBox.mpr fun i => by
      simp only [Pi.zero_apply, abs_zero]; positivity, ⟨0, hd⟩, Or.inl rfl⟩⟩
  have hT1 := centeredOsBound_block_additivity_defect X hr₁ hr₁r hR0 hf hf1 hfz
  have hT2 := centeredOsBound_sum_bigCubes hF hmono X hA hβ hC hR2 hRR₁ hr₁ hr₁lo hr₁hi hsep z
    hgm hg1
  have hcm : ∀ k, Measurable ((cellAt z R' k \ U).indicator g) := fun k =>
    hgm.indicator ((measurableSet_cellAt z R' k).diff (measurableSet_bigCubesAt z R R'))
  have hc1 : ∀ k y, |(cellAt z R' k \ U).indicator g y| ≤ 1 := by
    intro k y
    by_cases hy : y ∈ cellAt z R' k \ U
    · rw [Set.indicator_of_mem hy]; exact hg1 y
    · rw [Set.indicator_of_notMem hy, abs_zero]; exact zero_le_one
  have hcz : ∀ k y, y ∉ closedCube (z + R' • latticeShift k) R' →
      (cellAt z R' k \ U).indicator g y = 0 := fun k y hy =>
    Set.indicator_of_notMem (fun h => hy (cellAt_subset_closedCube z R' k h.1)) _
  have hT3 := (centeredOsBound_sum_cells hF hmono X hA hC hR'1 hR'R₁ hr₁ hr₁lo' hr₁hi' hρ₁ z T
    hT hcm hc1 hcz).const_mul (Real.rpow_pos_of_pos hR0 (-(d : ℝ)))
  have hfarS : ∀ x ∈ closedCube z R, ∀ y ∈ S, R' ≤ euclideanNorm (y - x) := by
    intro x hx y hy
    obtain ⟨i, hi⟩ := exists_le_abs_of_cellIndex_notMem hR'0 hy
    have hxi := hx i
    have h1 : |y i - x i| ≤ euclideanNorm (y - x) := by
      simpa using abs_apply_le_euclideanNorm' (y - x) i
    have h2 : |(y - z) i| ≤ |y i - x i| + |x i - z i| := by
      simp only [Pi.sub_apply]
      calc |y i - z i| = |(y i - x i) + (x i - z i)| := by ring_nf
        _ ≤ |y i - x i| + |x i - z i| := abs_add_le _ _
    push_cast at hi
    nlinarith
  have hT4 := hfar r₁ hR0 hρ hR'0.le hf hf1 hfz hSm hfarS
  rw [← hgdef] at hT4
  have hsum := ((hT1.add hT2).add hT3).add hT4
  refine hsum.congr_ae (measurable_block X r hf _) (Filter.Eventually.of_forall fun a => ?_)
  have hDint : Integrable fun x => f x * (X.field r a x -
      ∫ y, heatKernel x ρ y * X.field r₁ a y) := by
    refine hfi.mul_bdd (c := 2 * B) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((X.measurable r).comp measurable_prodMk_left).sub
        ((measurable_heatAverage _ (X.measurable r₁) ρ).comp measurable_prodMk_left)).aestronglyMeasurable
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
  have hpoint : (fun y => g y * X.field r₁ a y) = fun y =>
      (∑ σ : Fin d → Bool, (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y) +
      (∑ k ∈ T, (cellAt z R' k \ U).indicator g y * X.field r₁ a y) +
      S.indicator g y * X.field r₁ a y := by
    funext y
    rw [heat_weight_decomposition hR'0 hn hn' g y, add_mul, add_mul, Finset.sum_mul,
      Finset.sum_mul]
  have hiσ : ∀ σ, Integrable fun y => (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y :=
    fun σ => X.integrable_mul r₁ a (hgi.indicator (measurableSet_closedCube _ _))
  have hik : ∀ k, Integrable fun y => (cellAt z R' k \ U).indicator g y * X.field r₁ a y :=
    fun k => X.integrable_mul r₁ a (hgi.indicator ((measurableSet_cellAt z R' k).diff
      (measurableSet_bigCubesAt z R R')))
  have hiS : Integrable fun y => S.indicator g y * X.field r₁ a y :=
    X.integrable_mul r₁ a (hgi.indicator hSm)
  have hsplit2 : ∫ y, g y * X.field r₁ a y =
      (∑ σ : Fin d → Bool, ∫ y, (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y) +
      (∑ k ∈ T, ∫ y, (cellAt z R' k \ U).indicator g y * X.field r₁ a y) +
      ∫ y, S.indicator g y * X.field r₁ a y := by
    have hA1 : Integrable fun y => ∑ σ : Fin d → Bool,
        (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y :=
      integrable_finsetSum _ fun σ _ => hiσ σ
    have hA2 : Integrable fun y => ∑ k ∈ T, (cellAt z R' k \ U).indicator g y * X.field r₁ a y :=
      integrable_finsetSum _ fun k _ => hik k
    rw [hpoint]
    calc ∫ y, ((∑ σ : Fin d → Bool, (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y) +
          (∑ k ∈ T, (cellAt z R' k \ U).indicator g y * X.field r₁ a y) +
          S.indicator g y * X.field r₁ a y)
        = (∫ y, ((∑ σ : Fin d → Bool, (bigCubeAt z R R' σ).indicator g y * X.field r₁ a y) +
          (∑ k ∈ T, (cellAt z R' k \ U).indicator g y * X.field r₁ a y))) +
          ∫ y, S.indicator g y * X.field r₁ a y := integral_add (hA1.add hA2) hiS
      _ = _ := by
        rw [integral_add hA1 hA2, integral_finsetSum _ fun σ _ => hiσ σ,
          integral_finsetSum _ fun k _ => hik k]
  show _ = R ^ (-(d : ℝ)) * ∫ x, f x * X.field r a x
  beta_reduce
  rw [hsplit1, hfub, hsplit2]
  ring

end QSH
