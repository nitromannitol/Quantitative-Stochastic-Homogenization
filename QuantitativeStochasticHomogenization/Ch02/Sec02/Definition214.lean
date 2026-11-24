import QuantitativeStochasticHomogenization.Ch02.Sec01.Lemma22
import QuantitativeStochasticHomogenization.Ch02.Sec01.DualEnergyMeasurability

/-!
# Definition 2.14: the deterministic matrix `ā_U`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Definition 2.14, (2.41)–(2.42): `ā_U := E[a*⁻¹(U)]⁻¹` (`averagedDualMatrix`), the
expectation taken entrywise (`expectedDualInvMatrix`), and `Id ≤ ā_U ≤ Λ Id`
(`averagedDualMatrix_bounds`), for a bounded open convex nonempty set `U` and a probability
measure on the coefficient fields.

The entries of `a*⁻¹(U)` are measurable, as polarizations of the measurable function
`a ↦ μ*(U, ·)` (`measurable_coarseDualInvMatrix_apply`), and bounded by `1`, since
`Λ⁻¹ Id ≤ a*⁻¹(U) ≤ Id`; so `Λ⁻¹ Id ≤ E[a*⁻¹(U)] ≤ Id`, and the inverse of a symmetric matrix with
`c Id ≤ M ≤ C Id` satisfies `C⁻¹ Id ≤ M⁻¹ ≤ c⁻¹ Id` (`inv_mulVec_bounds`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The inverse of a symmetric positive definite matrix -/

/-- **Bounds of the inverse**: a symmetric matrix with `c|p|² ≤ p·Mp ≤ C|p|²`, `0 < c ≤ C`, is
invertible and `C⁻¹|p|² ≤ p·M⁻¹p ≤ c⁻¹|p|²`. -/
theorem inv_mulVec_bounds {M : Mat d} (hM : M.transpose = M) {c C : ℝ} (hc : 0 < c)
    (hcC : c ≤ C) (h1 : ∀ p : Vec d, c * euclideanSq p ≤ dot p (M.mulVec p))
    (h2 : ∀ p : Vec d, dot p (M.mulVec p) ≤ C * euclideanSq p) :
    IsUnit M.det ∧ ∀ p : Vec d, C⁻¹ * euclideanSq p ≤ dot p (M⁻¹.mulVec p) ∧
      dot p (M⁻¹.mulVec p) ≤ c⁻¹ * euclideanSq p := by
  have hC : 0 < C := hc.trans_le hcC
  have hdet : IsUnit M.det := by
    refine (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp ?_)
    intro x y hxy
    have h := h1 (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self] at h
    simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
    have h0 : euclideanSq (x - y) = 0 :=
      le_antisymm (by nlinarith [euclideanSq_nonneg (x - y)]) (euclideanSq_nonneg _)
    exact sub_eq_zero.mp (_root_.Homogenization.vecNormSq_eq_zero h0)
  refine ⟨hdet, fun p => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s : Vec d, s = M⁻¹.mulVec p := ⟨_, rfl⟩
  have hMs : M.mulVec s = p := by
    rw [hsdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  rw [← hsdef]
  have hps : dot p s = dot s (M.mulVec s) := by rw [hMs, dot_comm']
  constructor
  · obtain ⟨r, hrdef⟩ : ∃ r : Vec d, r = C⁻¹ • p := ⟨_, rfl⟩
    have h0 := h1 (r - s)
    have hn := euclideanSq_nonneg (r - s)
    have e : dot (r - s) (M.mulVec (r - s)) = dot r (M.mulVec r) - dot r (M.mulVec s) -
        dot s (M.mulVec r) + dot s (M.mulVec s) := by
      simp only [dot_eq_dotProduct, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
      ring
    have hsym := dot_mulVec_comm_of_symm hM s r
    rw [e, hsym, hMs] at h0
    have hr := h2 r
    have er : euclideanSq r = C⁻¹ ^ 2 * euclideanSq p := by
      rw [hrdef]
      simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have erp : dot r p = C⁻¹ * euclideanSq p := by
      rw [hrdef]
      simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [er] at hr
    rw [erp] at h0
    have hsp : dot s p = dot p s := dot_comm' s p
    have eC : C * (C⁻¹ ^ 2 * euclideanSq p) = C⁻¹ * euclideanSq p := by
      field_simp
    have hcn : 0 ≤ c * euclideanSq (r - s) := mul_nonneg hc.le hn
    rw [eC] at hr
    linarith
  · have hcs : dot p s ^ 2 ≤ euclideanSq p * euclideanSq s := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p s
      simpa only [euclideanSq, dot, pow_two] using this
    have hlow := h1 s
    rw [← hps] at hlow
    have hX0 : 0 ≤ dot p s := (mul_nonneg hc.le (euclideanSq_nonneg s)).trans hlow
    have hp0 := euclideanSq_nonneg p
    have key : c * dot p s ≤ euclideanSq p := by
      rcases hX0.eq_or_lt with h | h
      · rw [← h, mul_zero]
        exact hp0
      · have h3 : c * dot p s ^ 2 ≤ euclideanSq p * dot p s := by
          calc c * dot p s ^ 2 ≤ c * (euclideanSq p * euclideanSq s) :=
                mul_le_mul_of_nonneg_left hcs hc.le
            _ = euclideanSq p * (c * euclideanSq s) := by ring
            _ ≤ euclideanSq p * dot p s := mul_le_mul_of_nonneg_left hlow hp0
        have h4 : (c * dot p s) * dot p s ≤ euclideanSq p * dot p s := by nlinarith
        exact le_of_mul_le_mul_right h4 h
    rw [le_inv_mul_iff₀ hc]
    exact key

/-! ## The entries of `a*⁻¹(U)` -/

/-- **The entries of `a*⁻¹(U)` are measurable** in the coefficient field. -/
theorem measurable_coarseDualInvMatrix_apply {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (i j : Fin d) :
    Measurable (fun a : CoefficientField d Λ => coarseDualInvMatrix a U i j) := by
  unfold coarseDualInvMatrix polarizationMatrix polarization
  simp only [Matrix.of_apply]
  exact measurable_const.mul (((measurable_dualEnergy hU0 hU hΛ _).sub
    (measurable_dualEnergy hU0 hU hΛ _)).div_const 4)

theorem abs_coarseDualInvMatrix_apply_le [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (i j : Fin d) : |coarseDualInvMatrix a U i j| ≤ 1 := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  refine abs_apply_le_of_dot_le (coarseDualInvMatrix_transpose a hUo hUb hUc hne) zero_le_one
    (fun v => ?_) (fun v => by simpa using dot_coarseDualInvMatrix_le a hUo hUb hUc hne v) i j
  exact (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg v)).trans
    (inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne v)

/-! ## Definition 2.14 -/

/-- The expectation `E[a*⁻¹(U)]`, entrywise. -/
def expectedDualInvMatrix (P : Measure (CoefficientField d Λ)) (U : Set (Vec d)) : Mat d :=
  Matrix.of fun i j => ∫ a, coarseDualInvMatrix a U i j ∂P

/-- **Definition 2.14**, (2.41): the deterministic matrix `ā_U := E[a*⁻¹(U)]⁻¹`. -/
def averagedDualMatrix (P : Measure (CoefficientField d Λ)) (U : Set (Vec d)) : Mat d :=
  (expectedDualInvMatrix P U)⁻¹

section Bounds

variable [NeZero d] (P : Measure (CoefficientField d Λ)) [IsProbabilityMeasure P]
  {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U)
  (hne : U.Nonempty)
include hUo hUb hUc hne

theorem integrable_coarseDualInvMatrix_apply (hΛ : 1 ≤ Λ) (i j : Fin d) :
    Integrable (fun a : CoefficientField d Λ => coarseDualInvMatrix a U i j) P := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_coarseDualInvMatrix_apply hU0 hU (zero_le_one.trans hΛ) i j).aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]
  exact abs_coarseDualInvMatrix_apply_le a hUo hUb hUc hne i j

theorem dot_expectedDualInvMatrix_mulVec (hΛ : 1 ≤ Λ) (p : Vec d) :
    dot p ((expectedDualInvMatrix P U).mulVec p) =
      ∫ a, dot p ((coarseDualInvMatrix a U).mulVec p) ∂P := by
  have hint := integrable_coarseDualInvMatrix_apply P hUo hUb hUc hne hΛ
  simp only [dot, Matrix.mulVec, dotProduct, expectedDualInvMatrix, Matrix.of_apply]
  rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
    (hint i j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const _]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm

theorem expectedDualInvMatrix_bounds (hΛ : 1 ≤ Λ) (p : Vec d) :
    Λ⁻¹ * euclideanSq p ≤ dot p ((expectedDualInvMatrix P U).mulVec p) ∧
      dot p ((expectedDualInvMatrix P U).mulVec p) ≤ euclideanSq p := by
  have hint := integrable_coarseDualInvMatrix_apply P hUo hUb hUc hne hΛ
  have hq : Integrable (fun a : CoefficientField d Λ =>
      dot p ((coarseDualInvMatrix a U).mulVec p)) P := by
    simp only [dot, Matrix.mulVec, dotProduct]
    exact integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      (hint i j).mul_const _).const_mul _
  rw [dot_expectedDualInvMatrix_mulVec P hUo hUb hUc hne hΛ]
  constructor
  · calc Λ⁻¹ * euclideanSq p = ∫ _a : CoefficientField d Λ, Λ⁻¹ * euclideanSq p ∂P := by
          simp
      _ ≤ _ := integral_mono (integrable_const _) hq fun a =>
          inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne p
  · calc ∫ a, dot p ((coarseDualInvMatrix a U).mulVec p) ∂P ≤
          ∫ _a : CoefficientField d Λ, euclideanSq p ∂P :=
          integral_mono hq (integrable_const _) fun a =>
            dot_coarseDualInvMatrix_le a hUo hUb hUc hne p
      _ = euclideanSq p := by simp

theorem expectedDualInvMatrix_transpose :
    (expectedDualInvMatrix P U).transpose = expectedDualInvMatrix P U := by
  ext i j
  simp only [expectedDualInvMatrix, Matrix.transpose_apply, Matrix.of_apply]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  have h := coarseDualInvMatrix_transpose a hUo hUb hUc hne
  exact congrFun (congrFun h i) j

/-- **(2.42)**: `Id ≤ ā_U ≤ Λ Id`, and `ā_U` is symmetric. -/
theorem averagedDualMatrix_bounds (hΛ : 1 ≤ Λ) :
    (averagedDualMatrix P U).transpose = averagedDualMatrix P U ∧
      ∀ p : Vec d, euclideanSq p ≤ dot p ((averagedDualMatrix P U).mulVec p) ∧
        dot p ((averagedDualMatrix P U).mulVec p) ≤ Λ * euclideanSq p := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hb := expectedDualInvMatrix_bounds P hUo hUb hUc hne hΛ
  obtain ⟨-, hinv⟩ := inv_mulVec_bounds (expectedDualInvMatrix_transpose P hUo hUb hUc hne)
    (inv_pos.mpr hΛ0) (inv_le_one_of_one_le₀ hΛ) (fun p => (hb p).1)
    (fun p => by simpa using (hb p).2)
  refine ⟨?_, fun p => ?_⟩
  · rw [averagedDualMatrix, Matrix.transpose_nonsing_inv,
      expectedDualInvMatrix_transpose P hUo hUb hUc hne]
  · have h := hinv p
    rw [inv_one, one_mul, inv_inv] at h
    exact h

end Bounds

end QSH
