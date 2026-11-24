import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma22

/-!
# Lemma 2.7: the matrices `a(U)` and `a*(U)` are controlled by `J(U, p, ā p)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, Lemma 2.7, (2.25): there is `C(d, Λ) < ∞` such that, for every symmetric matrix `ā`
with `Id ≤ ā ≤ Λ Id` and every `U`,
`|a(U) - ā| + |a*(U) - ā| ≤ C sup_{p ∈ B₁} J(U, p, ā p)^{1/2}` (`lemma_2_7`), for the Frobenius
norm and a bounded open convex nonempty `U` (see `lemma_2_1`).

The proof is the book's. By (2.12), `J(U, p, q) = ½ p·(a(U) - a*(U))p + ½ (q - a*(U)p)·a*⁻¹(U)(q - a*(U)p)`
(`dualityDefect_eq_completedSquare`), and both terms are nonnegative by (2.11). With `q = ā p` and
`a*⁻¹(U) ≥ Λ⁻¹`, the second term bounds `|(ā - a*(U))p|²`; the first bounds the diagonal of the
nonnegative matrix `a(U) - a*(U)`, whose entries are then bounded by the Cauchy–Schwarz
inequality and the bound `a(U) - a*(U) ≤ Λ`. The book's minimization in `p` for `a(U)` is replaced by
this bound of `a(U) - a*(U)`. The bound uses no property of the matrix in `J(U, p, A p)`
(`frobeniusNorm_sub_add_le_of_dualityDefect_le`); the bounds of `ā` only give the bound of `J`
(`dualityDefect_le_of_bounds`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The completed square**: `J(U, p, q) = ½ p·(a(U) - a*(U))p + ½ (q - a*(U)p)·a*⁻¹(U)(q - a*(U)p)`. -/
theorem dualityDefect_eq_completedSquare [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (p q : Vec d) :
    dualityDefect a U p q = (1 / 2 : ℝ) * (dot p ((coarseMatrix a U).mulVec p) -
        dot p ((coarseDualMatrix a U).mulVec p)) +
      (1 / 2 : ℝ) * dot (q - (coarseDualMatrix a U).mulVec p)
        ((coarseDualInvMatrix a U).mulVec (q - (coarseDualMatrix a U).mulVec p)) := by
  set M := coarseDualInvMatrix a U
  set B := coarseDualMatrix a U
  have hMB : M.mulVec (B.mulVec p) = p :=
    coarseDualInvMatrix_mulVec_coarseDualMatrix_mulVec a hUo hUb hUc hne p
  have hMt : M.transpose = M := coarseDualInvMatrix_transpose a hUo hUb hUc hne
  have h1 : dot (B.mulVec p) (M.mulVec q) = dot q p := by
    rw [dot_mulVec_comm_of_symm hMt, hMB]
  have h2 : dot (B.mulVec p) (M.mulVec (B.mulVec p)) = dot p (B.mulVec p) := by
    rw [hMB, dot_comm']
  have h3 : dot q (M.mulVec (B.mulVec p)) = dot q p := by rw [hMB]
  have e : dot (q - B.mulVec p) (M.mulVec (q - B.mulVec p)) = dot q (M.mulVec q) -
      dot q (M.mulVec (B.mulVec p)) - dot (B.mulVec p) (M.mulVec q) +
        dot (B.mulVec p) (M.mulVec (B.mulVec p)) := by
    simp only [dot_eq_dotProduct, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    ring
  rw [dualityDefect_eq_coarseMatrix a hUo hUb hUc hne, e, h1, h2, h3, dot_comm' q p]
  ring

/-- `p·(a(U) - a*(U))p ≤ 2 J(U, p, q)`. -/
theorem dot_sub_mulVec_le_dualityDefect [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (p q : Vec d) :
    dot p ((coarseMatrix a U - coarseDualMatrix a U).mulVec p) ≤ 2 * dualityDefect a U p q := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  have hJ := dualityDefect_eq_completedSquare a hUo hUb hUc hne p q
  have hq := inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne
    (q - (coarseDualMatrix a U).mulVec p)
  have hq0 : 0 ≤ Λ⁻¹ * euclideanSq (q - (coarseDualMatrix a U).mulVec p) :=
    mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg _)
  rw [Matrix.sub_mulVec, dot_sub_right_eq]
  linarith

/-- `|q - a*(U)p|² ≤ 2Λ J(U, p, q)`. -/
theorem euclideanSq_sub_le_dualityDefect [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (p q : Vec d) :
    euclideanSq (q - (coarseDualMatrix a U).mulVec p) ≤ 2 * Λ * dualityDefect a U p q := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  have hJ := dualityDefect_eq_completedSquare a hUo hUb hUc hne p q
  have hq := inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne
    (q - (coarseDualMatrix a U).mulVec p)
  have hd := coarseDualMatrix_le_coarseMatrix a hUo hUb hUc hne p
  have hL : Λ * (Λ⁻¹ * euclideanSq (q - (coarseDualMatrix a U).mulVec p)) =
      euclideanSq (q - (coarseDualMatrix a U).mulVec p) := by
    field_simp
  nlinarith

theorem abs_le_of_sq_le {x c : ℝ} (hc : 0 ≤ c) (h : x ^ 2 ≤ c ^ 2) : |x| ≤ c := by
  have := Real.abs_le_sqrt h
  rwa [Real.sqrt_sq hc] at this

theorem euclideanSq_smul_eq (c : ℝ) (v : Vec d) : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `J(U, p, A p) ≤ ½ Λ + ½ Λ²` for `p ∈ B₁` and a symmetric matrix `A` with `0 ≤ A ≤ Λ Id`. -/
theorem dualityDefect_le_of_bounds [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    {A : Mat d} (hAt : A.transpose = A) (hA0 : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v))
    (hA : ∀ v : Vec d, dot v (A.mulVec v) ≤ Λ * euclideanSq v) {p : Vec d}
    (hp : p ∈ originBall d 1) :
    dualityDefect a U p (A.mulVec p) ≤ (1 / 2 : ℝ) * Λ + (1 / 2 : ℝ) * Λ ^ 2 := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  have hp1 : euclideanSq p ≤ 1 := euclideanSq_le_one_of_mem_originBall hp
  have hJ := dualityDefect_eq_coarseMatrix a hUo hUb hUc hne p (A.mulVec p)
  have h1 := (coarseMatrix_bounds a hU0 hU hΛ.le p).2
  have h2 := dot_coarseDualInvMatrix_le a hUo hUb hUc hne (A.mulVec p)
  have h3 := euclideanSq_mulVec_le_of_dot_le hAt hA0 hA p
  have h4 := hA0 p
  have h5 := mul_le_mul_of_nonneg_left hp1 hΛ.le
  have h6 := mul_le_mul_of_nonneg_left hp1 (sq_nonneg Λ)
  rw [hJ]
  nlinarith

/-- **The matrices `a(U)` and `a*(U)` from `J(U, p, A p)`**, for any matrix `A`: if
`J(U, p, A p) ≤ δ²` for every `p ∈ B₁`, then `|a(U) - A| + |a*(U) - A| ≤ 3 d² √(32 Λ) δ`, for the
Frobenius norm. This is the bound of the proof of Lemma 2.7, which uses no property of `A`. -/
theorem frobeniusNorm_sub_add_le_of_dualityDefect_le [NeZero d] (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) (A : Mat d) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδJ : ∀ p ∈ originBall d 1, dualityDefect a U p (A.mulVec p) ≤ δ ^ 2) :
    frobeniusNorm (coarseMatrix a U - A) + frobeniusNorm (coarseDualMatrix a U - A) ≤
      3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) * δ := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  -- the test vectors `¼ e_k`
  have hmem : ∀ k : Fin d, (1 / 4 : ℝ) • unitVector k ∈ originBall d 1 := fun k => by
    simpa using mem_originBall_quarter k k 0 (by simp)
  -- the matrix `a(U) - a*(U)`
  have hD0 : ∀ v : Vec d, 0 ≤ dot v ((coarseMatrix a U - coarseDualMatrix a U).mulVec v) :=
    fun v => by
      rw [Matrix.sub_mulVec, dot_sub_right_eq]
      linarith [coarseDualMatrix_le_coarseMatrix a hUo hUb hUc hne v]
  have hDt : (coarseMatrix a U - coarseDualMatrix a U).transpose =
      coarseMatrix a U - coarseDualMatrix a U := by
    rw [Matrix.transpose_sub, coarseMatrix_transpose a hU,
      coarseDualMatrix_transpose a hUo hUb hUc hne]
  have hDdiag : ∀ k : Fin d,
      dot (unitVector k) ((coarseMatrix a U - coarseDualMatrix a U).mulVec (unitVector k)) ≤
        32 * δ ^ 2 ∧
      dot (unitVector k) ((coarseMatrix a U - coarseDualMatrix a U).mulVec (unitVector k)) ≤ Λ :=
    fun k => by
      have h := dot_sub_mulVec_le_dualityDefect a hUo hUb hUc hne ((1 / 4 : ℝ) • unitVector k)
        (A.mulVec ((1 / 4 : ℝ) • unitVector k))
      have hδk := hδJ _ (hmem k)
      have hp : dot ((1 / 4 : ℝ) • unitVector k)
          ((coarseMatrix a U - coarseDualMatrix a U).mulVec ((1 / 4 : ℝ) • unitVector k)) =
          (1 / 16 : ℝ) *
            dot (unitVector k) ((coarseMatrix a U - coarseDualMatrix a U).mulVec (unitVector k)) := by
        simp only [dot_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
          smul_eq_mul]
        ring
      rw [hp] at h
      refine ⟨by linarith, ?_⟩
      have h1 := (coarseMatrix_bounds a hU0 hU hΛ.le (unitVector k)).2
      have h2 := le_coarseDualMatrix a hUo hUb hUc hne (unitVector k)
      rw [Matrix.sub_mulVec, dot_sub_right_eq]
      rw [euclideanSq_unitVector] at h1 h2
      linarith
  have hAB : ∀ k : Fin d,
      euclideanSq ((A - coarseDualMatrix a U).mulVec (unitVector k)) ≤ 32 * Λ * δ ^ 2 := fun k => by
    have h := euclideanSq_sub_le_dualityDefect a hUo hUb hUc hne ((1 / 4 : ℝ) • unitVector k)
      (A.mulVec ((1 / 4 : ℝ) • unitVector k))
    have hδk := hδJ _ (hmem k)
    have hv : A.mulVec ((1 / 4 : ℝ) • unitVector k) -
        (coarseDualMatrix a U).mulVec ((1 / 4 : ℝ) • unitVector k) =
        (1 / 4 : ℝ) • (A - coarseDualMatrix a U).mulVec (unitVector k) := by
      simp only [Matrix.mulVec_smul, Matrix.sub_mulVec, smul_sub]
    rw [hv, euclideanSq_smul_eq] at h
    nlinarith
  -- the entries
  obtain ⟨c, hc⟩ : ∃ c, c = Real.sqrt (32 * Λ) * δ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ mul_nonneg (Real.sqrt_nonneg _) hδ0
  have hcsq : c ^ 2 = 32 * Λ * δ ^ 2 := by
    rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
  have hentry1 : ∀ i j : Fin d, |(coarseDualMatrix a U - A) i j| ≤ c := fun i j => by
    refine abs_le_of_sq_le hc0 ?_
    have h := sq_apply_le_euclideanSq ((A - coarseDualMatrix a U).mulVec (unitVector j)) i
    rw [mulVec_unitVector_apply] at h
    have e : (coarseDualMatrix a U - A) i j ^ 2 = (A - coarseDualMatrix a U) i j ^ 2 := by
      simp only [Matrix.sub_apply]
      ring
    rw [e, hcsq]
    exact h.trans (hAB j)
  have hentry2 : ∀ i j : Fin d, |(coarseMatrix a U - coarseDualMatrix a U) i j| ≤ c := fun i j => by
    refine abs_le_of_sq_le hc0 ?_
    have hcs := sq_dot_mulVec_le hDt hD0 (unitVector j) (unitVector i)
    rw [dot_unitVector_left, mulVec_unitVector_apply] at hcs
    have hi := hDdiag i
    have hj := hDdiag j
    have hj0 := hD0 (unitVector j)
    rw [hcsq]
    calc (coarseMatrix a U - coarseDualMatrix a U) i j ^ 2
        ≤ dot (unitVector i) ((coarseMatrix a U - coarseDualMatrix a U).mulVec (unitVector i)) *
          dot (unitVector j) ((coarseMatrix a U - coarseDualMatrix a U).mulVec (unitVector j)) :=
          hcs
      _ ≤ (32 * δ ^ 2) * Λ := mul_le_mul hi.1 hj.2 hj0 (by positivity)
      _ = 32 * Λ * δ ^ 2 := by ring
  have hentry3 : ∀ i j : Fin d, |(coarseMatrix a U - A) i j| ≤ 2 * c := fun i j => by
    have e : (coarseMatrix a U - A) i j =
        (coarseMatrix a U - coarseDualMatrix a U) i j + (coarseDualMatrix a U - A) i j := by
      simp only [Matrix.sub_apply]
      ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith [hentry1 i j, hentry2 i j])
  have hsum : ∀ (N : Mat d) (b : ℝ), (∀ i j, |N i j| ≤ b) → frobeniusNorm N ≤ (d : ℝ) ^ 2 * b :=
    fun N b hN => (frobeniusNorm_le_sum_abs N).trans (by
      calc ∑ i, ∑ j, |N i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, b :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hN i j
        _ = (d : ℝ) ^ 2 * b := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring)
  have hB := hsum _ _ hentry1
  have hĀ := hsum _ _ hentry3
  calc frobeniusNorm (coarseMatrix a U - A) + frobeniusNorm (coarseDualMatrix a U - A)
      ≤ (d : ℝ) ^ 2 * (2 * c) + (d : ℝ) ^ 2 * c := add_le_add hĀ hB
    _ = 3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ) * δ := by rw [hc]; ring

/-- **Lemma 2.7.** There is `C(d, Λ) < ∞` such that, for every symmetric matrix `ā` with
`Id ≤ ā ≤ Λ Id` and every bounded open convex nonempty `U ⊆ ℝ^d`,
`|a(U) - ā| + |a*(U) - ā| ≤ C sup_{p ∈ B₁} J(U, p, ā p)^{1/2}` (2.25), the supremum of a set bounded
above, for the Frobenius norm. -/
theorem lemma_2_7 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Mat d, A.transpose = A →
      (∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (A.mulVec ξ) ∧ dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) →
      ∀ (a : CoefficientField d Λ) (U : Set (Vec d)), IsOpen U → Bornology.IsBounded U →
        Convex ℝ U → U.Nonempty →
        BddAbove ((fun p => Real.sqrt (dualityDefect a U p (A.mulVec p))) '' originBall d 1) ∧
        frobeniusNorm (coarseMatrix a U - A) + frobeniusNorm (coarseDualMatrix a U - A) ≤
          C * sSup ((fun p => Real.sqrt (dualityDefect a U p (A.mulVec p))) '' originBall d 1) := by
  refine ⟨3 * (d : ℝ) ^ 2 * Real.sqrt (32 * Λ), by positivity, fun A hAt hA a U hUo hUb hUc hne => ?_⟩
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hA0 : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v) := fun v =>
    (euclideanSq_nonneg v).trans (hA v).1
  have hJ0 : ∀ p : Vec d, 0 ≤ dualityDefect a U p (A.mulVec p) := fun p => by
    have := dot_le_dirichletEnergy_add_dualEnergy a hUb hU0 p (A.mulVec p)
    unfold dualityDefect
    linarith
  have hbdd : BddAbove ((fun p => Real.sqrt (dualityDefect a U p (A.mulVec p))) '' originBall d 1) := by
    refine ⟨Real.sqrt ((1 / 2 : ℝ) * Λ + (1 / 2 : ℝ) * Λ ^ 2), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact Real.sqrt_le_sqrt
      (dualityDefect_le_of_bounds a hUo hUb hUc hne hAt hA0 (fun v => (hA v).2) hp)
  refine ⟨hbdd, ?_⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = sSup ((fun p => Real.sqrt (dualityDefect a U p (A.mulVec p))) ''
      originBall d 1) := ⟨_, rfl⟩
  rw [← hδ]
  have hδJ : ∀ p ∈ originBall d 1, dualityDefect a U p (A.mulVec p) ≤ δ ^ 2 := fun p hp => by
    have h := le_csSup hbdd ⟨p, hp, rfl⟩
    rw [← hδ] at h
    rw [← Real.sq_sqrt (hJ0 p)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact (Real.sqrt_nonneg _).trans (le_csSup hbdd ⟨0, zero_mem_originBall, rfl⟩)
  exact frobeniusNorm_sub_add_le_of_dualityDefect_le a hUo hUb hUc hne A hδ0 hδJ

end QSH
