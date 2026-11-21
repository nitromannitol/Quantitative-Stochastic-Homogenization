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

end QSH
