import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Cube decompositions for the fluctuation estimates

The proof of Proposition 4.12 of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Section 4.5, Step 2, cuts a neighbourhood of the cube
`□_R` into `2^d` cubes of side `R/2` at mutual distance `R'`, and cells of side `R'` covering the
rest. This file provides that decomposition in the form used there:

* closed cubes `closedCube z R` and half-open lattice cells `latticeCell L k`, which partition
  `ℝ^d` (`mem_latticeCell_iff`, `sum_indicator_latticeCell`);
* the `2^d` closed cubes `bigCube R R' σ` of side `R/2` centered at `±(R/4 + R'/2)` in each
  coordinate, at mutual coordinate distance at least `R'` (`exists_le_abs_sub_of_mem_bigCube`);
* every cell `latticeCell R' k` with `1 ≤ |kᵢ| ≤ n` for all `i`, where `n R' ≤ R/2`, lies in one of
  these cubes (`latticeCell_subset_bigCube`), so only the cells of the frame `latticeFrame`
  meet the complement, and there are at most `5 d (2N+1)^{d-1}` of them for `N = n + 2`
  (`card_latticeFrame_le`);
* Euclidean neighbourhoods of separated sets are separated (`le_euclideanNorm_sub_of_near`).
-/

open MeasureTheory

namespace QSH

variable {d : ℕ}

/-! ### Euclidean norm -/

theorem euclideanSq_eq_sum_sq (x : Vec d) : euclideanSq x = ∑ i, x i ^ 2 := by
  simp only [euclideanSq, dot, sq]

theorem euclideanNorm_eq_norm (x : Vec d) :
    euclideanNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, euclideanNorm, euclideanSq_eq_sum_sq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem euclideanNorm_nonneg' (x : Vec d) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

theorem euclideanNorm_sub_le_add (x y z : Vec d) :
    euclideanNorm (x - z) ≤ euclideanNorm (x - y) + euclideanNorm (y - z) := by
  simp only [euclideanNorm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem euclideanNorm_sub_comm' (x y : Vec d) : euclideanNorm (x - y) = euclideanNorm (y - x) := by
  simp only [euclideanNorm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_rev _ _

theorem abs_apply_le_euclideanNorm' (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  rw [euclideanNorm, euclideanSq_eq_sum_sq]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- Points within Euclidean distance `ρ` of two sets whose points differ by at least `g` in some
coordinate are at Euclidean distance at least `g - 2ρ`. -/
theorem le_euclideanNorm_sub_of_near {U W : Set (Vec d)} {g ρ : ℝ}
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ∃ i, g ≤ |u i - w i|) {x y : Vec d}
    (hx : ∃ u ∈ U, euclideanNorm (x - u) < ρ) (hy : ∃ w ∈ W, euclideanNorm (y - w) < ρ) :
    g - 2 * ρ ≤ euclideanNorm (x - y) := by
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨w, hw, hyw⟩ := hy
  obtain ⟨i, hi⟩ := hUW u hu w hw
  have h1 : |u i - w i| ≤ euclideanNorm (u - w) := by
    simpa using abs_apply_le_euclideanNorm' (u - w) i
  have h2 := euclideanNorm_sub_le_add u x w
  have h3 := euclideanNorm_sub_le_add x y w
  rw [euclideanNorm_sub_comm' u x] at h2
  linarith

/-! ### Closed cubes and lattice cells -/

/-- The closed cube of side `R` centered at `z`. -/
def closedCube (z : Vec d) (R : ℝ) : Set (Vec d) := {x | ∀ i, |x i - z i| ≤ R / 2}

theorem measurableSet_closedCube (z : Vec d) (R : ℝ) : MeasurableSet (closedCube z R) := by
  have e : closedCube z R = ⋂ i, {x : Vec d | |x i - z i| ≤ R / 2} := by
    ext x
    simp [closedCube]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

theorem cube_subset_closedCube (z : Vec d) (R : ℝ) : cube z R ⊆ closedCube z R :=
  fun _ hx i => (hx i).le

/-- The half-open cell `L k + [-L/2, L/2)^d` of the lattice `L ℤ^d`. -/
def latticeCell (L : ℝ) (k : LatticeIndex d) : Set (Vec d) :=
  {x | ∀ i, L * k i - L / 2 ≤ x i ∧ x i < L * k i + L / 2}

theorem measurableSet_latticeCell (L : ℝ) (k : LatticeIndex d) :
    MeasurableSet (latticeCell L k) := by
  have e : latticeCell L k = ⋂ i, ({x : Vec d | L * k i - L / 2 ≤ x i} ∩
      {x : Vec d | x i < L * k i + L / 2}) := by
    ext x
    simp [latticeCell]
  rw [e]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_le measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)

/-- The index of the cell of `L ℤ^d` containing `x`. -/
noncomputable def cellIndex (L : ℝ) (x : Vec d) : LatticeIndex d := fun i => ⌊x i / L + 1 / 2⌋

theorem mem_latticeCell_iff {L : ℝ} (hL : 0 < L) {x : Vec d} {k : LatticeIndex d} :
    x ∈ latticeCell L k ↔ cellIndex L x = k := by
  simp only [latticeCell, cellIndex, Set.mem_ofPred_eq, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Int.floor_eq_iff]
  have e1 : ((k i : ℝ) ≤ x i / L + 1 / 2) ↔ L * k i - L / 2 ≤ x i := by
    rw [← sub_le_iff_le_add, le_div_iff₀ hL]
    constructor <;> intro h <;> linarith
  have e2 : (x i / L + 1 / 2 < (k i : ℝ) + 1) ↔ x i < L * k i + L / 2 := by
    rw [← lt_sub_iff_add_lt, div_lt_iff₀ hL]
    constructor <;> intro h <;> linarith
  rw [e1, e2]

theorem latticeCell_subset_closedCube (L : ℝ) (k : LatticeIndex d) :
    latticeCell L k ⊆ closedCube (L • latticeShift k) L := by
  intro x hx i
  obtain ⟨h1, h2⟩ := hx i
  simp only [Pi.smul_apply, latticeShift, smul_eq_mul]
  rw [abs_le]
  constructor <;> linarith

/-- The cells of `L ℤ^d` partition `ℝ^d`: summing the restrictions of `h` to the cells with
index in `I` gives `h` on the union of these cells and `0` elsewhere. -/
theorem sum_indicator_latticeCell {L : ℝ} (hL : 0 < L) (I : Finset (LatticeIndex d))
    (h : Vec d → ℝ) (x : Vec d) :
    ∑ k ∈ I, (latticeCell L k).indicator h x = if cellIndex L x ∈ I then h x else 0 := by
  classical
  simp only [Set.indicator_apply, mem_latticeCell_iff hL]
  exact Finset.sum_ite_eq I (cellIndex L x) (fun _ => h x)

/-- The indices `k` with `|kᵢ| ≤ N` for every `i`. -/
def latticeBox (d N : ℕ) : Finset (LatticeIndex d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem mem_latticeBox {N : ℕ} {k : LatticeIndex d} :
    k ∈ latticeBox d N ↔ ∀ i, |k i| ≤ N := by
  simp only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- A point outside the union of the cells of the box `|k| ≤ N` has a coordinate of modulus at
least `(N + 1/2) L`. -/
theorem exists_le_abs_of_cellIndex_notMem {L : ℝ} (hL : 0 < L) {N : ℕ} {x : Vec d}
    (hx : cellIndex L x ∉ latticeBox d N) : ∃ i, ((N : ℝ) + 1 / 2) * L ≤ |x i| := by
  rw [mem_latticeBox] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  simp only [cellIndex] at hi
  rcases lt_abs.mp hi with h | h
  · have h1 : (N : ℤ) + 1 ≤ ⌊x i / L + 1 / 2⌋ := h
    have h2 : ((N : ℝ) + 1) ≤ x i / L + 1 / 2 := by
      have := (Int.le_floor.mp h1)
      push_cast at this
      exact this
    have h3 : ((N : ℝ) + 1 / 2) * L ≤ x i := by
      have : (N : ℝ) + 1 / 2 ≤ x i / L := by linarith
      rwa [le_div_iff₀ hL] at this
    exact h3.trans (le_abs_self _)
  · have h1 : ⌊x i / L + 1 / 2⌋ < -(N : ℤ) := by linarith
    have h2 : x i / L + 1 / 2 < -(N : ℝ) := by
      have := Int.floor_lt.mp h1
      push_cast at this
      exact this
    have h3 : x i < -(((N : ℝ) + 1 / 2) * L) := by
      have : x i / L < -((N : ℝ) + 1 / 2) := by linarith
      rw [div_lt_iff₀ hL] at this
      linarith
    exact (by linarith : ((N : ℝ) + 1 / 2) * L ≤ -x i).trans (neg_le_abs _)

/-! ### The `2^d` large cubes -/

/-- The center `±(R/4 + R'/2)` in each coordinate, with the signs given by `σ`. -/
noncomputable def bigCubeCenter (R R' : ℝ) (σ : Fin d → Bool) : Vec d :=
  fun i => (if σ i then 1 else -1) * (R / 4 + R' / 2)

/-- The closed cube of side `R/2` centered at `bigCubeCenter R R' σ`. -/
def bigCube (R R' : ℝ) (σ : Fin d → Bool) : Set (Vec d) := closedCube (bigCubeCenter R R' σ) (R / 2)

theorem measurableSet_bigCube (R R' : ℝ) (σ : Fin d → Bool) : MeasurableSet (bigCube R R' σ) :=
  measurableSet_closedCube _ _

theorem bigCube_coord {R R' : ℝ} {σ : Fin d → Bool} {x : Vec d} (hx : x ∈ bigCube R R' σ)
    (i : Fin d) :
    (σ i = true → R' / 2 ≤ x i ∧ x i ≤ R / 2 + R' / 2) ∧
      (σ i = false → -(R / 2 + R' / 2) ≤ x i ∧ x i ≤ -(R' / 2)) := by
  have h := abs_le.mp (hx i)
  simp only [bigCubeCenter] at h
  refine ⟨fun hσ => ?_, fun hσ => ?_⟩
  · simp only [hσ, ite_true, one_mul] at h
    constructor <;> linarith [h.1, h.2]
  · simp only [hσ, Bool.false_eq_true, ite_false, neg_mul, one_mul] at h
    constructor <;> linarith [h.1, h.2]

/-- Distinct large cubes are at coordinate distance at least `R'`. -/
theorem exists_le_abs_sub_of_mem_bigCube {R R' : ℝ} {σ σ' : Fin d → Bool} (hσ : σ ≠ σ')
    {x y : Vec d} (hx : x ∈ bigCube R R' σ) (hy : y ∈ bigCube R R' σ') :
    ∃ i, R' ≤ |x i - y i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hσ
  refine ⟨i, ?_⟩
  have hx' := bigCube_coord hx i
  have hy' := bigCube_coord hy i
  cases h1 : σ i <;> cases h2 : σ' i
  · exact absurd (h1.trans h2.symm) hi
  · have a := hx'.2 h1
    have b := hy'.1 h2
    rw [abs_sub_comm]
    exact (by linarith : R' ≤ y i - x i).trans (le_abs_self _)
  · have a := hx'.1 h1
    have b := hy'.2 h2
    exact (by linarith : R' ≤ x i - y i).trans (le_abs_self _)
  · exact absurd (h1.trans h2.symm) hi

theorem bigCube_disjoint {R R' : ℝ} (hR' : 0 < R') {σ σ' : Fin d → Bool} (hσ : σ ≠ σ') :
    Disjoint (bigCube R R' σ) (bigCube R R' σ') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ := exists_le_abs_sub_of_mem_bigCube hσ hx hx'
  simp at hi
  linarith

/-- A cell with `1 ≤ |kᵢ| ≤ n` in every coordinate, where `n R' ≤ R/2`, lies in the large cube
with the signs of `k`. -/
theorem latticeCell_subset_bigCube {R R' : ℝ} {n : ℕ} (hn : (n : ℝ) * R' ≤ R / 2)
    (hR' : 0 < R') {k : LatticeIndex d} (hk : ∀ i, k i ≠ 0 ∧ |k i| ≤ n) :
    latticeCell R' k ⊆ bigCube R R' (fun i => decide (0 < k i)) := by
  intro x hx i
  obtain ⟨h1, h2⟩ := hx i
  obtain ⟨hk0, hkn⟩ := hk i
  have hkn' : |(k i : ℝ)| ≤ n := by exact_mod_cast hkn
  simp only [bigCubeCenter]
  rw [abs_le]
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · have hd : decide (0 < k i) = false := by simp; omega
    have hk1 : (k i : ℝ) ≤ -1 := by exact_mod_cast (show k i ≤ -1 by omega)
    have hkn'' : -(n : ℝ) ≤ k i := (abs_le.mp hkn').1
    simp only [hd, Bool.false_eq_true, ite_false, neg_mul, one_mul]
    constructor <;> nlinarith
  · have hd : decide (0 < k i) = true := by simp; omega
    have hk1 : (1 : ℝ) ≤ k i := by exact_mod_cast (show 1 ≤ k i by omega)
    have hkn'' : (k i : ℝ) ≤ n := (abs_le.mp hkn').2
    simp only [hd, ite_true, one_mul]
    constructor <;> nlinarith

/-! ### The frame -/

/-- The cells of the box `|k| ≤ N` having a coordinate `0` or of modulus larger than `n`. -/
def latticeFrame (d N n : ℕ) : Finset (LatticeIndex d) :=
  (latticeBox d N).filter fun k => ∃ i, k i = 0 ∨ (n : ℤ) < |k i|

theorem latticeCell_subset_bigCube_of_notMem_frame {R R' : ℝ} {N n : ℕ}
    (hn : (n : ℝ) * R' ≤ R / 2) (hR' : 0 < R') {k : LatticeIndex d} (hk : k ∈ latticeBox d N)
    (hkf : k ∉ latticeFrame d N n) :
    latticeCell R' k ⊆ bigCube R R' (fun i => decide (0 < k i)) := by
  refine latticeCell_subset_bigCube hn hR' fun i => ?_
  simp only [latticeFrame, Finset.mem_filter, hk, true_and, not_exists, not_or, not_lt] at hkf
  exact hkf i

theorem card_filter_coord_le {N : ℕ} (B : Finset ℤ) (i : Fin d) :
    ((latticeBox d N).filter fun k => k i ∈ B).card ≤ B.card * (2 * N + 1) ^ (d - 1) := by
  classical
  have hsub : (latticeBox d N).filter (fun k => k i ∈ B) ⊆
      Fintype.piFinset fun j => if j = i then B else Finset.Icc (-(N : ℤ)) N := by
    intro k hk
    simp only [Finset.mem_filter, latticeBox, Fintype.mem_piFinset] at hk
    simp only [Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hk.2
    · simpa [hj] using hk.1 j
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset, Fintype.prod_eq_mul_prod_compl i]
  simp only [ite_true]
  have hrest : ∏ j ∈ ({i} : Finset (Fin d))ᶜ,
      (if j = i then B else Finset.Icc (-(N : ℤ)) N).card = (2 * N + 1) ^ (d - 1) := by
    rw [Finset.prod_congr rfl (g := fun _ => 2 * N + 1)]
    · rw [Finset.prod_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    · intro j hj
      have hji : j ≠ i := by simpa using hj
      simp only [hji, ite_false, Int.card_Icc]
      omega
  rw [hrest]

/-- **The number of frame cells**: for `N = n + 2`, at most `5 d (2N+1)^{d-1}`. -/
theorem card_latticeFrame_le (n : ℕ) :
    (latticeFrame d (n + 2) n).card ≤ 5 * d * (2 * (n + 2) + 1) ^ (d - 1) := by
  classical
  set B : Finset ℤ := ([0, (n : ℤ) + 1, n + 2, -((n : ℤ) + 1), -((n : ℤ) + 2)] : List ℤ).toFinset
  have hB : B.card ≤ 5 := List.toFinset_card_le _
  have hsub : latticeFrame d (n + 2) n ⊆
      Finset.univ.biUnion fun i => (latticeBox d (n + 2)).filter fun k => k i ∈ B := by
    intro k hk
    simp only [latticeFrame, Finset.mem_filter] at hk
    obtain ⟨hkb, i, hi⟩ := hk
    have hki : |k i| ≤ ((n + 2 : ℕ) : ℤ) := mem_latticeBox.mp hkb i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    refine ⟨i, hkb, ?_⟩
    simp only [B, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    push_cast at hki
    rcases hi with h | h
    · exact Or.inl h
    · rcases abs_le.mp hki with ⟨h1, h2⟩
      rcases lt_abs.mp h with h3 | h3 <;> omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ i : Fin d, ((latticeBox d (n + 2)).filter fun k => k i ∈ B).card
      ≤ ∑ _i : Fin d, B.card * (2 * (n + 2) + 1) ^ (d - 1) :=
        Finset.sum_le_sum fun i _ => card_filter_coord_le B i
    _ = d * (B.card * (2 * (n + 2) + 1) ^ (d - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ d * (5 * (2 * (n + 2) + 1) ^ (d - 1)) := by gcongr
    _ = 5 * d * (2 * (n + 2) + 1) ^ (d - 1) := by ring

end QSH
