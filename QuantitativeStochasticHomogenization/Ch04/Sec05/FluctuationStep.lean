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

end QSH
