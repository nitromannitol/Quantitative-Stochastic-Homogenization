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

end QSH
