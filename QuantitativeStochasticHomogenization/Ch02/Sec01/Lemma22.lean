import QuantitativeStochasticHomogenization.Ch02.Sec01.DefectMaximizer

/-!
# Lemma 2.2: basic properties of `J`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, Lemma 2.2, (2.11)–(2.17), for a bounded open convex nonempty set `U` (see
`lemma_2_1` for the domains).

* `coarseDualInvMatrix a U`: the symmetric matrix `a*⁻¹(U)` with `μ*(U, q) = ½ q·a*⁻¹(U)q`, the
  polarization matrix of `q ↦ μ*(U, q)` (`dualEnergy_eq_coarseDualInvMatrix`), and
  `coarseDualMatrix a U = a*(U)`, its inverse. The book obtains the quadratic form (2.20) from (2.18)
  and (2.19); here the parallelogram identity of `μ*(U, ·) = J(U, 0, ·)` comes from the same two
  facts (`dualEnergy_parallelogram`).
* (2.11): `Id ≤ a*(U) ≤ a(U) ≤ Λ Id` (`le_coarseDualMatrix`, `coarseDualMatrix_le_coarseMatrix`),
  with the book's Step 3: the bound `μ*(U, q) ≤ ½|q|²` and (2.4) at `q = a*(U)p`.
* (2.12) `dualityDefect_eq_coarseMatrix`, (2.13) `coarseMatrix_mulVec_eq`, (2.14)
  `coarseDualInvMatrix_mulVec_eq`, (2.15) `dualityDefect_le_sum_of_partition`; (2.16) and (2.17)
  are in `DefectMaximizer.lean`.
* `lemma_2_2`: the four properties of the lemma.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem dirichletEnergy_zero (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) : dirichletEnergy a U 0 = 0 := by
  have h := dirichletEnergy_le a hU0 hU hΛ 0
  simp only [euclideanSq, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  exact le_antisymm h (dirichletEnergy_nonneg a U 0)

/-- `J(U, 0, q) = μ*(U, q)`. -/
theorem dualityDefect_zero_left (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (q : Vec d) : dualityDefect a U 0 q = dualEnergy a U q := by
  rw [dualityDefect, dirichletEnergy_zero a hU0 hU hΛ, dot_zero_left']
  ring

theorem integral_parallelogram (a : CoefficientField d Λ) {U : Set (Vec d)} {g₁ g₂ : Vec d → Vec d}
    (hg₁ : MemLp g₁ 2 (volume.restrict U)) (hg₂ : MemLp g₂ 2 (volume.restrict U)) :
    (∫ x in U, (1 / 2 : ℝ) * dot (g₁ x + g₂ x) ((a x).mulVec (g₁ x + g₂ x))) +
        ∫ x in U, (1 / 2 : ℝ) * dot (g₁ x - g₂ x) ((a x).mulVec (g₁ x - g₂ x)) =
      2 * (∫ x in U, (1 / 2 : ℝ) * dot (g₁ x) ((a x).mulVec (g₁ x))) +
        2 * ∫ x in U, (1 / 2 : ℝ) * dot (g₂ x) ((a x).mulVec (g₂ x)) := by
  have ip : Integrable (fun x => (1 / 2 : ℝ) * dot (g₁ x + g₂ x) ((a x).mulVec (g₁ x + g₂ x)))
      (volume.restrict U) := (integrable_dot_mulVec a U (hg₁.add hg₂)).const_mul _
  have im : Integrable (fun x => (1 / 2 : ℝ) * dot (g₁ x - g₂ x) ((a x).mulVec (g₁ x - g₂ x)))
      (volume.restrict U) := (integrable_dot_mulVec a U (hg₁.sub hg₂)).const_mul _
  have i1 := ((integrable_dot_mulVec a U hg₁).const_mul (1 / 2 : ℝ)).const_mul (2 : ℝ)
  have i2 := ((integrable_dot_mulVec a U hg₂).const_mul (1 / 2 : ℝ)).const_mul (2 : ℝ)
  rw [← integral_add ip im, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h := dot_parallelogram (a x) (g₁ x) (g₂ x)
  simp only
  linarith

/-- **The parallelogram identity of `μ*(U, ·)`**, from the linearity (2.18) and the identity
(2.19) for `J(U, 0, ·) = μ*(U, ·)`. -/
theorem dualEnergy_parallelogram [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (q₁ q₂ : Vec d) :
    dualEnergy a U (q₁ + q₂) + dualEnergy a U (q₁ - q₂) =
      2 * dualEnergy a U q₁ + 2 * dualEnergy a U q₂ := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  obtain ⟨v₁, g₁, h₁⟩ := exists_isDefectMaximizer a hUo hUb hUc hne 0 q₁
  obtain ⟨v₂, g₂, h₂⟩ := exists_isDefectMaximizer a hUo hUb hUc hne 0 q₂
  have hs := h₁.linearCombination hUo hUb hUc hne h₂ 1 1
  have hd := h₁.linearCombination hUo hUb hUc hne h₂ 1 (-1)
  simp only [one_smul, one_mul, smul_zero, add_zero] at hs
  simp only [one_smul, one_mul, smul_zero, add_zero, neg_smul, neg_one_mul,
    ← sub_eq_add_neg] at hd
  rw [← dualityDefect_zero_left a hU0 hU hΛ, ← dualityDefect_zero_left a hU0 hU hΛ,
    ← dualityDefect_zero_left a hU0 hU hΛ, ← dualityDefect_zero_left a hU0 hU hΛ,
    hs.dualityDefect_eq hUb hU0, hd.dualityDefect_eq hUb hU0, h₁.dualityDefect_eq hUb hU0,
    h₂.dualityDefect_eq hUb hU0]
  simp only [setAverage_eq, smul_eq_mul]
  rw [← mul_add, integral_parallelogram a h₁.1.1.2.1 h₂.1.1.2.1]
  ring

/-! ## The matrices `a*⁻¹(U)` and `a*(U)` -/

/-- **The matrix `a*⁻¹(U)`**: the symmetric matrix with `μ*(U, q) = ½ q·a*⁻¹(U)q`. -/
def coarseDualInvMatrix (a : CoefficientField d Λ) (U : Set (Vec d)) : Mat d :=
  polarizationMatrix (dualEnergy a U)

/-- **The coarse-grained matrix `a*(U)`** of Lemma 2.2 and Remark 2.3. -/
def coarseDualMatrix (a : CoefficientField d Λ) (U : Set (Vec d)) : Mat d :=
  (coarseDualInvMatrix a U)⁻¹

theorem dot_unitVector_left (i : Fin d) (v : Vec d) : dot (unitVector i) v = v i := by
  simp [dot, unitVector, Pi.single_apply]

/-- `(0, 0)` is a maximizer of `μ*(U, 0)`. -/
theorem isDualMaximizer_zero (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hne : U.Nonempty) :
    IsDualMaximizer a U 0 (fun _ => 0) (fun _ => 0) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  refine ⟨H1_zero U, ?_⟩
  rw [dualTrialEnergy_zero]
  have h := dualEnergy_le a hU0 hU 0
  simp only [euclideanSq, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  exact le_antisymm (dualEnergy_nonneg a hU0 hU 0) h

section Matrices

variable [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
  (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
include hUo hUb hUc hne

theorem coarseDualInvMatrix_transpose :
    (coarseDualInvMatrix a U).transpose = coarseDualInvMatrix a U :=
  polarizationMatrix_transpose (dualEnergy_parallelogram a hUo hUb hUc hne)

/-- **`μ*(U, q) = ½ q·a*⁻¹(U)q`** (Remark 2.3). -/
theorem dualEnergy_eq_coarseDualInvMatrix (q : Vec d) :
    dualEnergy a U q = (1 / 2 : ℝ) * dot q ((coarseDualInvMatrix a U).mulVec q) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  refine eq_half_dot_polarizationMatrix (dualEnergy_parallelogram a hUo hUb hUc hne)
    (M := 1 / 2) (by norm_num) (fun q => ?_) q
  rw [abs_of_nonneg (dualEnergy_nonneg a hU0 hU q)]
  exact dualEnergy_le a hU0 hU q

theorem dot_coarseDualInvMatrix_le (q : Vec d) :
    dot q ((coarseDualInvMatrix a U).mulVec q) ≤ euclideanSq q := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have h := dualEnergy_le a hU0 hU q
  rw [dualEnergy_eq_coarseDualInvMatrix a hUo hUb hUc hne] at h
  linarith

/-- `q·a*⁻¹(U)q ≥ Λ⁻¹|q|²`, from (2.4) at `p = Λ⁻¹q` and `μ(U, p) ≤ ½Λ|p|²`. -/
theorem inv_mul_le_dot_coarseDualInvMatrix (q : Vec d) :
    Λ⁻¹ * euclideanSq q ≤ dot q ((coarseDualInvMatrix a U).mulVec q) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ1 : 1 ≤ Λ := one_le_of_coefficientField a
  have hΛ : 0 < Λ := zero_lt_one.trans_le hΛ1
  have h4 := dot_le_dirichletEnergy_add_dualEnergy a hUb hU0 (Λ⁻¹ • q) q
  have hD := dirichletEnergy_le a hU0 hU hΛ.le (Λ⁻¹ • q)
  rw [dualEnergy_eq_coarseDualInvMatrix a hUo hUb hUc hne] at h4
  have e1 : dot (Λ⁻¹ • q) q = Λ⁻¹ * euclideanSq q := by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have e2 : euclideanSq (Λ⁻¹ • q) = Λ⁻¹ ^ 2 * euclideanSq q := by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1] at h4
  rw [e2] at hD
  have hq := euclideanSq_nonneg q
  have e3 : (1 / 2 : ℝ) * Λ * (Λ⁻¹ ^ 2 * euclideanSq q) = (1 / 2 : ℝ) * (Λ⁻¹ * euclideanSq q) := by
    field_simp
  linarith

theorem isUnit_det_coarseDualInvMatrix : IsUnit (coarseDualInvMatrix a U).det := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  refine (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp ?_)
  intro x y hxy
  have h := inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self] at h
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have h0 : euclideanSq (x - y) = 0 :=
    le_antisymm (by nlinarith [inv_pos.mpr hΛ]) (euclideanSq_nonneg _)
  exact sub_eq_zero.mp (_root_.Homogenization.vecNormSq_eq_zero h0)

theorem coarseDualInvMatrix_mulVec_coarseDualMatrix_mulVec (p : Vec d) :
    (coarseDualInvMatrix a U).mulVec ((coarseDualMatrix a U).mulVec p) = p := by
  rw [coarseDualMatrix, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_det_coarseDualInvMatrix a hUo hUb hUc hne), Matrix.one_mulVec]

theorem coarseDualMatrix_transpose : (coarseDualMatrix a U).transpose = coarseDualMatrix a U := by
  rw [coarseDualMatrix, Matrix.transpose_nonsing_inv,
    coarseDualInvMatrix_transpose a hUo hUb hUc hne]

theorem inv_coarseDualMatrix : (coarseDualMatrix a U)⁻¹ = coarseDualInvMatrix a U :=
  Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_coarseDualInvMatrix a hUo hUb hUc hne)

/-- **`Id ≤ a*(U)`**, (2.11). -/
theorem le_coarseDualMatrix (p : Vec d) :
    euclideanSq p ≤ dot p ((coarseDualMatrix a U).mulVec p) := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  set M := coarseDualInvMatrix a U
  set s := (coarseDualMatrix a U).mulVec p
  have hMs : M.mulVec s = p := coarseDualInvMatrix_mulVec_coarseDualMatrix_mulVec a hUo hUb hUc hne p
  have h0 := inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne (p - s)
  have hnn : 0 ≤ Λ⁻¹ * euclideanSq (p - s) :=
    mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg _)
  have e : dot (p - s) (M.mulVec (p - s)) = dot p (M.mulVec p) - dot p (M.mulVec s) -
      dot s (M.mulVec p) + dot s (M.mulVec s) := by
    simp only [dot_eq_dotProduct, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    ring
  have hsym := dot_mulVec_comm_of_symm (coarseDualInvMatrix_transpose a hUo hUb hUc hne) s p
  rw [e, hsym, hMs] at h0
  have hle := dot_coarseDualInvMatrix_le a hUo hUb hUc hne p
  have hc : dot s p = dot p s := dot_comm' s p
  change dot p p ≤ dot p s
  change dot p (M.mulVec p) ≤ dot p p at hle
  linarith

/-- **`a*(U) ≤ a(U)`**, (2.11): (2.4) at `q = a*(U)p`. -/
theorem coarseDualMatrix_le_coarseMatrix (p : Vec d) :
    dot p ((coarseDualMatrix a U).mulVec p) ≤ dot p ((coarseMatrix a U).mulVec p) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  set s := (coarseDualMatrix a U).mulVec p
  have h4 := dot_le_dirichletEnergy_add_dualEnergy a hUb hU0 p s
  rw [dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ, dualEnergy_eq_coarseDualInvMatrix a hUo hUb hUc hne,
    coarseDualInvMatrix_mulVec_coarseDualMatrix_mulVec a hUo hUb hUc hne, dot_comm' s p] at h4
  linarith

/-- **(2.12)**: `J(U, p, q) = ½ p·a(U)p + ½ q·a*⁻¹(U)q - p·q`. -/
theorem dualityDefect_eq_coarseMatrix (p q : Vec d) :
    dualityDefect a U p q = (1 / 2 : ℝ) * dot p ((coarseMatrix a U).mulVec p) +
      (1 / 2 : ℝ) * dot q ((coarseDualInvMatrix a U).mulVec q) - dot p q := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  rw [dualityDefect, dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ,
    dualEnergy_eq_coarseDualInvMatrix a hUo hUb hUc hne]

/-- **(2.14)**: `a*⁻¹(U)q = ⨍_U ∇v(·, U, 0, q)` for the maximizer `v(·, U, 0, q)` of (2.9). -/
theorem coarseDualInvMatrix_mulVec_eq {q : Vec d} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hmax : IsDefectMaximizer a U 0 q v g) :
    (coarseDualInvMatrix a U).mulVec q = fun i => ⨍ x in U, g x i := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  funext i
  set e : Vec d := unitVector i
  set M := coarseDualInvMatrix a U
  obtain ⟨v', g', h'⟩ := exists_isDefectMaximizer a hUo hUb hUc hne 0 e
  have hs := hmax.linearCombination hUo hUb hUc hne h' 1 1
  have hd := hmax.linearCombination hUo hUb hUc hne h' 1 (-1)
  simp only [one_smul, one_mul, smul_zero, add_zero] at hs
  simp only [one_smul, one_mul, smul_zero, add_zero, neg_smul, neg_one_mul,
    ← sub_eq_add_neg] at hd
  have hg := hmax.1.1.2.1
  have hg' := h'.1.1.2.1
  -- the quadratic form
  have hq : dualEnergy a U (q + e) - dualEnergy a U (q - e) = 2 * dot e (M.mulVec q) := by
    rw [dualEnergy_eq_coarseDualInvMatrix a hUo hUb hUc hne,
      dualEnergy_eq_coarseDualInvMatrix a hUo hUb hUc hne]
    have hsym := dot_mulVec_comm_of_symm (coarseDualInvMatrix_transpose a hUo hUb hUc hne) q e
    simp only [dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add,
      add_dotProduct, dotProduct_sub, sub_dotProduct] at hsym ⊢
    linarith
  -- the maximizers
  have hJ : dualEnergy a U (q + e) - dualEnergy a U (q - e) = 2 * ⨍ x in U, g x i := by
    rw [← dualityDefect_zero_left a hU0 hU hΛ, ← dualityDefect_zero_left a hU0 hU hΛ,
      hs.dualityDefect_eq hUb hU0, hd.dualityDefect_eq hUb hU0]
    have hfv := h'.setIntegral_dot_eq hUb hU0 hmax.1
    simp only [dot_zero_left', neg_zero, zero_add] at hfv
    have ip : Integrable (fun x => (1 / 2 : ℝ) * dot (g x + g' x) ((a x).mulVec (g x + g' x)))
        (volume.restrict U) := (integrable_dot_mulVec a U (hg.add hg')).const_mul _
    have im : Integrable (fun x => (1 / 2 : ℝ) * dot (g x - g' x) ((a x).mulVec (g x - g' x)))
        (volume.restrict U) := (integrable_dot_mulVec a U (hg.sub hg')).const_mul _
    have i2 := (integrable_dot_mulVec_of_memLp a hg hg').const_mul (2 : ℝ)
    have key : (∫ x in U, (1 / 2 : ℝ) * dot (g x + g' x) ((a x).mulVec (g x + g' x))) -
        ∫ x in U, (1 / 2 : ℝ) * dot (g x - g' x) ((a x).mulVec (g x - g' x)) =
        2 * ∫ x in U, dot (g x) ((a x).mulVec (g' x)) := by
      rw [← integral_sub ip im, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hsym := dot_mulVec_comm_of_symm (a.symmetric x) (g x) (g' x)
      simp only [dot_eq_dotProduct, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add,
        add_dotProduct, dotProduct_sub, sub_dotProduct] at hsym ⊢
      linarith
    have hi : ∫ x in U, dot e (g x) = ∫ x in U, g x i :=
      integral_congr_ae (Eventually.of_forall fun x => dot_unitVector_left i (g x))
    simp only [setAverage_eq, smul_eq_mul]
    rw [← mul_sub, key, hfv, hi]
    ring
  have h2 : dot e (M.mulVec q) = ⨍ x in U, g x i := by linarith
  rw [← h2]
  exact (dot_unitVector_left i _).symm

omit hUc in
/-- **(2.13)**: `a(U)p = -⨍_U a∇v(·, U, p, 0)` for the maximizer `v(·, U, p, 0)` of (2.9), from
Lemma 2.1 (it is minus the minimizer of `μ(U, p)`) and (1.49). -/
theorem coarseMatrix_mulVec_eq {p : Vec d} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hmax : IsDefectMaximizer a U p 0 v g) :
    (coarseMatrix a U).mulVec p = fun i => -⨍ x in U, (a x).mulVec (g x) i := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  obtain ⟨u, gD, hD⟩ := exists_isDirichletMinimizer a hUb hU0 p
  have hM := (isDualMaximizer_zero a hUo hUb hne).isDefectMaximizer_sub hUb hU0 hD
  have hae := hmax.ae_eq hUb hU0 hM
  funext i
  have hflux := hD.setAverage_flux_eq hU0 hU (unitVector i)
  rw [dot_unitVector_left] at hflux
  rw [← hflux]
  have hc : ⨍ x in U, (a x).mulVec (g x) i = ⨍ x in U, -dot (unitVector i) ((a x).mulVec (p + gD x)) := by
    simp only [setAverage_eq, smul_eq_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, dot_unitVector_left, zero_sub, Matrix.mulVec_neg, Pi.neg_apply]
  rw [hc]
  simp only [setAverage_eq, smul_eq_mul, integral_neg, mul_neg, neg_neg]

end Matrices

/-! ## Subadditivity (2.15) -/

/-- **Subadditivity (2.15)** for a partition of `U`, up to a null set, by pairwise disjoint open
sets: `J(U, p, q) ≤ Σᵢ |Uᵢ|/|U| J(Uᵢ, p, q)`. -/
theorem dualityDefect_le_sum_of_partition [NeZero d] (a : CoefficientField d Λ) {ι : Type*}
    [Fintype ι] {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : Convex ℝ U) (hne : U.Nonempty) {Q : ι → Set (Vec d)} (hQo : ∀ k, IsOpen (Q k))
    (hdisj : Pairwise (Function.onFun Disjoint Q)) (hsub : ∀ k, Q k ⊆ U)
    (hcover : volume (U \ ⋃ k, Q k) = 0) (p q : Vec d) :
    dualityDefect a U p q ≤ ∑ k, (volume.real (Q k) / volume.real U) * dualityDefect a (Q k) p q := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  obtain ⟨v, g, hmax⟩ := exists_isDefectMaximizer a hUo hUb hUc hne p q
  have hint := integrable_defectIntegrand a hU p q hmax.1.1.2.1
  have hae : U =ᵐ[volume] ⋃ k, Q k := by
    refine ae_eq_set.mpr ⟨hcover, ?_⟩
    rw [sdiff_eq_empty.mpr (iUnion_subset hsub), measure_empty]
  have hsplit : ∫ x in U, (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x)) =
      ∑ k, ∫ x in Q k, (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
        dot p ((a x).mulVec (g x)) + dot q (g x)) := by
    rw [setIntegral_congr_set hae, integral_iUnion_fintype (fun k => (hQo k).measurableSet) hdisj
      fun k => IntegrableOn.mono_set hint (hsub k)]
  rw [← hmax.2, defectTrialEnergy, setAverage_eq, smul_eq_mul, hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hQ : volume (Q k) ≠ ⊤ := ne_top_of_le_ne_top hU (measure_mono (hsub k))
  rcases eq_or_ne (volume (Q k)) 0 with h0 | h0
  · rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
    simp [Measure.real, h0]
  · have hle := defectTrialEnergy_le_dualityDefect a (hUb.subset (hsub k)) h0
      (hmax.1.mono (hsub k)) p q
    have hpos : 0 < volume.real (Q k) := ENNReal.toReal_pos h0 hQ
    rw [defectTrialEnergy, setAverage_eq, smul_eq_mul] at hle
    calc (volume.real U)⁻¹ * ∫ x in Q k, (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
          dot p ((a x).mulVec (g x)) + dot q (g x))
        = (volume.real (Q k) / volume.real U) * ((volume.real (Q k))⁻¹ *
            ∫ x in Q k, (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
              dot p ((a x).mulVec (g x)) + dot q (g x))) := by
          field_simp
      _ ≤ (volume.real (Q k) / volume.real U) * dualityDefect a (Q k) p q :=
          mul_le_mul_of_nonneg_left hle (div_nonneg measureReal_nonneg measureReal_nonneg)

/-! ## Lemma 2.2 -/

/-- **Lemma 2.2 (Basic properties of `J`).** For a bounded open convex nonempty set `U ⊆ ℝ^d`:

* *representation as a quadratic form*: `a*(U)` is symmetric with inverse `a*⁻¹(U)`,
  `Id ≤ a*(U) ≤ a(U) ≤ Λ Id` (2.11), `J(U, p, q) = ½ p·a(U)p + ½ q·a*⁻¹(U)q - p·q` (2.12),
  `a(U)p = -⨍_U a∇v(·, U, p, 0)` (2.13) and `a*⁻¹(U)q = ⨍_U ∇v(·, U, 0, q)` (2.14) for the
  maximizers of (2.9);
* *subadditivity* (2.15): for open, pairwise disjoint `U₁, …, U_N ⊆ U` with `|U \ ⋃ Uᵢ| = 0`,
  `J(U, p, q) ≤ Σᵢ |Uᵢ|/|U| J(Uᵢ, p, q)`;
* *first variation*: the maximizer `v(·, U, p, q)` of (2.9) exists, its gradient is unique up to
  null sets, and the maximizers are exactly the `v ∈ A(U)` with
  `⨍_U ∇w·a∇v = ⨍_U (-p·a∇w + q·∇w)` for every `w ∈ A(U)` (2.16);
* *quadratic response* (2.17): for every `w ∈ A(U)`,
  `⨍_U ½ (∇w - ∇v)·a(∇w - ∇v) = J(U, p, q) - ⨍_U (-½ ∇w·a∇w - p·a∇w + q·∇w)`. -/
theorem lemma_2_2 [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) :
    ((coarseDualMatrix a U).transpose = coarseDualMatrix a U ∧
      (coarseDualMatrix a U)⁻¹ = coarseDualInvMatrix a U ∧
      (∀ p : Vec d, euclideanSq p ≤ dot p ((coarseDualMatrix a U).mulVec p) ∧
        dot p ((coarseDualMatrix a U).mulVec p) ≤ dot p ((coarseMatrix a U).mulVec p) ∧
        dot p ((coarseMatrix a U).mulVec p) ≤ Λ * euclideanSq p) ∧
      (∀ p q : Vec d, dualityDefect a U p q = (1 / 2 : ℝ) * dot p ((coarseMatrix a U).mulVec p) +
        (1 / 2 : ℝ) * dot q ((coarseDualInvMatrix a U).mulVec q) - dot p q) ∧
      (∀ (p : Vec d) (v : Vec d → ℝ) (g : Vec d → Vec d), IsDefectMaximizer a U p 0 v g →
        (coarseMatrix a U).mulVec p = fun i => -⨍ x in U, (a x).mulVec (g x) i) ∧
      ∀ (q : Vec d) (v : Vec d → ℝ) (g : Vec d → Vec d), IsDefectMaximizer a U 0 q v g →
        (coarseDualInvMatrix a U).mulVec q = fun i => ⨍ x in U, g x i) ∧
    (∀ (ι : Type) [Fintype ι] (Q : ι → Set (Vec d)), (∀ k, IsOpen (Q k)) →
      Pairwise (Function.onFun Disjoint Q) → (∀ k, Q k ⊆ U) → volume (U \ ⋃ k, Q k) = 0 →
      ∀ p q : Vec d, dualityDefect a U p q ≤
        ∑ k, (volume.real (Q k) / volume.real U) * dualityDefect a (Q k) p q) ∧
    (∀ p q : Vec d, (∃ (v : Vec d → ℝ) (g : Vec d → Vec d), IsDefectMaximizer a U p q v g) ∧
      (∀ (v₁ v₂ : Vec d → ℝ) (g₁ g₂ : Vec d → Vec d), IsDefectMaximizer a U p q v₁ g₁ →
        IsDefectMaximizer a U p q v₂ g₂ → g₁ =ᵐ[volume.restrict U] g₂) ∧
      ∀ (v : Vec d → ℝ) (g : Vec d → Vec d), IsAHarmonic a U v g →
        (IsDefectMaximizer a U p q v g ↔ ∀ (w : Vec d → ℝ) (h : Vec d → Vec d),
          IsAHarmonic a U w h → ⨍ x in U, dot (h x) ((a x).mulVec (g x)) =
            ⨍ x in U, (-dot p ((a x).mulVec (h x)) + dot q (h x)))) ∧
    (∀ (p q : Vec d) (v w : Vec d → ℝ) (g h : Vec d → Vec d), IsDefectMaximizer a U p q v g →
      IsAHarmonic a U w h →
      ⨍ x in U, (1 / 2 : ℝ) * dot (h x - g x) ((a x).mulVec (h x - g x)) =
        dualityDefect a U p q - defectTrialEnergy a U p q h) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  refine ⟨⟨coarseDualMatrix_transpose a hUo hUb hUc hne, inv_coarseDualMatrix a hUo hUb hUc hne,
    fun p => ⟨le_coarseDualMatrix a hUo hUb hUc hne p,
      coarseDualMatrix_le_coarseMatrix a hUo hUb hUc hne p,
      (coarseMatrix_bounds a hU0 hU hΛ p).2⟩, dualityDefect_eq_coarseMatrix a hUo hUb hUc hne,
    fun p v g h => coarseMatrix_mulVec_eq a hUo hUb hne h,
    fun q v g h => coarseDualInvMatrix_mulVec_eq a hUo hUb hUc hne h⟩,
    fun ι _ Q hQo hdisj hsub hcover p q =>
      dualityDefect_le_sum_of_partition a hUo hUb hUc hne hQo hdisj hsub hcover p q,
    fun p q => ⟨exists_isDefectMaximizer a hUo hUb hUc hne p q,
      fun v₁ v₂ g₁ g₂ h₁ h₂ => h₁.ae_eq hUb hU0 h₂, fun v g hv => ⟨fun hmax w h hw => ?_,
        fun hfv => isDefectMaximizer_of_setIntegral_dot_eq hUo hUb hUc hne hv fun w h hw => ?_⟩⟩,
    fun p q v w g h hmax hw => hmax.setAverage_sub_eq hUb hU0 hw⟩
  · simp only [setAverage_eq, smul_eq_mul]
    rw [hmax.setIntegral_dot_eq hUb hU0 hw]
  · have h := hfv w h hw
    simp only [setAverage_eq, smul_eq_mul] at h
    exact mul_left_cancel₀ (inv_ne_zero hV.ne') h

end QSH
