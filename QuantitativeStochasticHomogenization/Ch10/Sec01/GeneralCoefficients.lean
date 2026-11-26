import QuantitativeStochasticHomogenization.Ch10.Sec01.VariationalRepresentation
import QuantitativeStochasticHomogenization.Ch01.Sec04.FluxAverage
import Homogenization.CoarseGraining.HilbertMinimizationMeasurability

/-!
# The coefficient fields of Chapter 10

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the opening of Chapter 10, (10.2), and the quadratic form (10.7) of Section 10.1 with its matrix
`A(x)` of Section 10.2.

* `GeneralCoefficientField d Λ`: the enlarged set `Ω` of Chapter 10, the Lebesgue measurable maps
  `a : ℝ^d → ℝ^{d×d}`, not necessarily symmetric, with `|ξ|² ≤ ξ·a(x)ξ` and `|a(x)ξ| ≤ Λ|ξ|`
  for every `ξ ∈ ℝ^d`, (10.2).
* `representativePairing a p' q' p q = p'·s p + (q' - m p')·s⁻¹(q - m p)`: the bilinear form
  `X'·A X` of the quadratic form (10.7), with `X = (p, q)`, `X' = (p', q')` and `s`, `m` the
  symmetric and antisymmetric parts of `a`; `linearRepresentative a p q = ½ X·A X`.
* For the symmetric part `s(x)`: `|ξ|² ≤ ξ·s(x)ξ ≤ Λ|ξ|²` and
  `(max Λ 1)⁻¹ |ξ|² ≤ ξ·s(x)⁻¹ξ ≤ |ξ|²`.
* `GeneralCoefficientField.symmetricPartField`: the symmetric part `s` as a coefficient field
  satisfying (0.6) with the same `Λ`; it equals `a` where `a` is symmetric.
-/

open MeasureTheory Matrix

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The set `Ω` of Chapter 10**, (10.2): Lebesgue measurable fields `a : ℝ^d → ℝ^{d×d}`, not
necessarily symmetric, with `|ξ|² ≤ ξ·a(x)ξ` and `|a(x)ξ| ≤ Λ|ξ|` for every `x, ξ ∈ ℝ^d`. -/
structure GeneralCoefficientField (d : ℕ) (Λ : ℝ) where
  field : Vec d → Mat d
  aestronglyMeasurable : ∀ i j, AEStronglyMeasurable (fun x => field x i j) volume
  elliptic : ∀ x ξ, euclideanSq ξ ≤ dot ξ ((field x).mulVec ξ) ∧
    euclideanNorm ((field x).mulVec ξ) ≤ Λ * euclideanNorm ξ

instance instCoeFunGeneralCoefficientFieldForallVecMat :
    CoeFun (GeneralCoefficientField d Λ) (fun _ => Vec d → Mat d) :=
  ⟨GeneralCoefficientField.field⟩

/-- The bilinear form `X'·A X` of the quadratic form (10.7), for `X = (p, q)` and `X' = (p', q')`:
`p'·s p + (q' - m p')·s⁻¹(q - m p)`, with `s` and `m` the symmetric and antisymmetric parts of
`a`. In block form, `A = [[s - m s⁻¹ m, m s⁻¹], [-s⁻¹ m, s⁻¹]]`. -/
def representativePairing (a : Mat d) (p' q' p q : Vec d) : ℝ :=
  dot p' ((symmetricPart a).mulVec p) +
    dot (q' - (antisymmetricPart a).mulVec p')
      ((symmetricPart a)⁻¹.mulVec (q - (antisymmetricPart a).mulVec p))

/-! ## Elementary bounds -/

private theorem dot_eq_dotProduct' (x y : Vec d) : dot x y = x ⬝ᵥ y := rfl

theorem euclideanNorm_mul_self (x : Vec d) : euclideanNorm x * euclideanNorm x = euclideanSq x :=
  Real.mul_self_sqrt (euclideanSq_nonneg x)

/-- **The Cauchy–Schwarz inequality** `x·y ≤ |x| |y|`. -/
theorem dot_le_euclideanNorm_mul (x y : Vec d) : dot x y ≤ euclideanNorm x * euclideanNorm y := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  simpa only [euclideanNorm, euclideanSq, dot, sq] using h

theorem euclideanSq_pos_of_ne_zero {x : Vec d} (hx : x ≠ 0) : 0 < euclideanSq x := by
  rcases (euclideanSq_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have h0 : ∀ i ∈ Finset.univ, x i * x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).mp h.symm
    funext i
    exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ i))

/-- A symmetric matrix `S` with `|ξ|² ≤ ξ·Sξ` is invertible. -/
theorem isUnit_det_of_euclideanSq_le {S : Mat d} (hlow : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (S.mulVec ξ)) :
    IsUnit S.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hsv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := (euclideanSq_pos_of_ne_zero hv).trans_le (hlow v)
  rw [hsv, dot_eq_dotProduct', dotProduct_zero] at h
  exact lt_irrefl 0 h

/-- **Bounds for the inverse of a symmetric matrix** with `|ξ|² ≤ ξ·Sξ ≤ L|ξ|²` and `L > 0`:
`L⁻¹|ξ|² ≤ ξ·S⁻¹ξ ≤ |ξ|²`. -/
theorem dot_inv_mulVec_bounds {S : Mat d} (hS : S.transpose = S)
    (hlow : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (S.mulVec ξ)) {L : ℝ} (hL : 0 < L)
    (hup : ∀ ξ : Vec d, dot ξ (S.mulVec ξ) ≤ L * euclideanSq ξ) (ξ : Vec d) :
    L⁻¹ * euclideanSq ξ ≤ dot ξ (S⁻¹.mulVec ξ) ∧ dot ξ (S⁻¹.mulVec ξ) ≤ euclideanSq ξ := by
  have hdet := isUnit_det_of_euclideanSq_le hlow
  set η := S⁻¹.mulVec ξ with hη
  have hSη : S.mulVec η = ξ := by
    rw [hη, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hdet, Matrix.one_mulVec]
  have hpos : ∀ v : Vec d, 0 ≤ dot v (S.mulVec v) := fun v =>
    (euclideanSq_nonneg v).trans (hlow v)
  have ht : dot ξ η = dot η (S.mulVec η) := by
    rw [hSη, dot_eq_dotProduct', dot_eq_dotProduct', dotProduct_comm]
  have hηlow := hlow η
  rw [← ht] at hηlow
  have hcs := dot_le_euclideanNorm_mul η ξ
  have hcomm : dot η ξ = dot ξ η := by
    rw [dot_eq_dotProduct', dot_eq_dotProduct', dotProduct_comm]
  rw [hcomm] at hcs
  have hnη : 0 ≤ euclideanNorm η := Real.sqrt_nonneg _
  have hnξ : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _
  have hsqη := euclideanNorm_mul_self η
  have hsqξ := euclideanNorm_mul_self ξ
  have hdξη : 0 ≤ dot ξ η := (euclideanSq_nonneg η).trans hηlow
  have hupper : dot ξ η ≤ euclideanSq ξ := by
    have h1 : euclideanNorm η ≤ euclideanNorm ξ := by
      by_contra hlt
      push Not at hlt
      have hpos' : 0 < euclideanNorm η := hnξ.trans_lt hlt
      have h2 : euclideanNorm η * euclideanNorm ξ < euclideanNorm η * euclideanNorm η :=
        mul_lt_mul_of_pos_left hlt hpos'
      linarith
    have h2 : euclideanNorm η * euclideanNorm ξ ≤ euclideanNorm ξ * euclideanNorm ξ :=
      mul_le_mul_of_nonneg_right h1 hnξ
    linarith
  refine ⟨?_, hupper⟩
  have hcs2 := sq_dot_mulVec_le hS hpos ξ η
  have hηSξ : dot η (S.mulVec ξ) = euclideanSq ξ := by
    rw [dot_mulVec_comm_of_symm hS, hSη]
    rfl
  rw [hηSξ, hSη, hcomm] at hcs2
  have h3 : dot ξ (S.mulVec ξ) ≤ L * euclideanSq ξ := hup ξ
  rcases (euclideanSq_nonneg ξ).lt_or_eq with hξ | hξ
  · have h4 : euclideanSq ξ ^ 2 ≤ dot ξ η * (L * euclideanSq ξ) :=
      hcs2.trans (mul_le_mul_of_nonneg_left h3 hdξη)
    have h5 : euclideanSq ξ ≤ L * dot ξ η := by nlinarith
    rw [inv_mul_le_iff₀ hL]
    exact h5
  · rw [← hξ, mul_zero]
    exact hdξη

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ)

/-- `ξ·a(x)ξ ≤ Λ|ξ|²`. -/
theorem dot_mulVec_le (x ξ : Vec d) : dot ξ ((a x).mulVec ξ) ≤ Λ * euclideanSq ξ := by
  have h1 := dot_le_euclideanNorm_mul ξ ((a x).mulVec ξ)
  have h2 := (a.elliptic x ξ).2
  have h0 : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _
  calc dot ξ ((a x).mulVec ξ) ≤ euclideanNorm ξ * euclideanNorm ((a x).mulVec ξ) := h1
    _ ≤ euclideanNorm ξ * (Λ * euclideanNorm ξ) := mul_le_mul_of_nonneg_left h2 h0
    _ = Λ * euclideanSq ξ := by rw [← euclideanNorm_mul_self]; ring

/-- `|a(x)ξ|² ≤ Λ²|ξ|²`. -/
theorem euclideanSq_mulVec_le (x ξ : Vec d) :
    euclideanSq ((a x).mulVec ξ) ≤ Λ ^ 2 * euclideanSq ξ := by
  have h2 := (a.elliptic x ξ).2
  have h0 : 0 ≤ euclideanNorm ((a x).mulVec ξ) := Real.sqrt_nonneg _
  rw [← euclideanNorm_mul_self, ← euclideanNorm_mul_self]
  calc euclideanNorm ((a x).mulVec ξ) * euclideanNorm ((a x).mulVec ξ)
      ≤ (Λ * euclideanNorm ξ) * (Λ * euclideanNorm ξ) := mul_self_le_mul_self h0 h2
    _ = Λ ^ 2 * (euclideanNorm ξ * euclideanNorm ξ) := by ring

theorem dot_symmetricPart (x ξ : Vec d) :
    dot ξ ((symmetricPart (a x)).mulVec ξ) = dot ξ ((a x).mulVec ξ) :=
  dotProduct_symmetricPart_self (a x) ξ

/-- `|ξ|² ≤ ξ·s(x)ξ`. -/
theorem euclideanSq_le_dot_symmetricPart (x ξ : Vec d) :
    euclideanSq ξ ≤ dot ξ ((symmetricPart (a x)).mulVec ξ) := by
  rw [dot_symmetricPart]
  exact (a.elliptic x ξ).1

/-- `ξ·s(x)ξ ≤ max Λ 1 |ξ|²`. -/
theorem dot_symmetricPart_le (x ξ : Vec d) :
    dot ξ ((symmetricPart (a x)).mulVec ξ) ≤ max Λ 1 * euclideanSq ξ := by
  rw [dot_symmetricPart]
  exact (a.dot_mulVec_le x ξ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (euclideanSq_nonneg ξ))

theorem isUnit_det_symmetricPart' (x : Vec d) : IsUnit (symmetricPart (a x)).det :=
  isUnit_det_of_euclideanSq_le (a.euclideanSq_le_dot_symmetricPart x)

/-- **`(max Λ 1)⁻¹|ξ|² ≤ ξ·s(x)⁻¹ξ ≤ |ξ|²`.** -/
theorem dot_inv_symmetricPart_bounds (x ξ : Vec d) :
    (max Λ 1)⁻¹ * euclideanSq ξ ≤ dot ξ ((symmetricPart (a x))⁻¹.mulVec ξ) ∧
      dot ξ ((symmetricPart (a x))⁻¹.mulVec ξ) ≤ euclideanSq ξ :=
  dot_inv_mulVec_bounds (symmetricPart_transpose (a x)) (a.euclideanSq_le_dot_symmetricPart x)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (a.dot_symmetricPart_le x) ξ

/-- The entries of a coefficient field are bounded by `Λ`. -/
theorem abs_apply_le (x : Vec d) (i j : Fin d) : |a x i j| ≤ Λ := by
  have h := abs_apply_le_euclideanNorm ((a x).mulVec (unitVector j)) i
  have h2 := (a.elliptic x (unitVector j)).2
  have hu : euclideanNorm (unitVector j : Vec d) = 1 := by
    unfold euclideanNorm euclideanSq dot unitVector
    simp [Pi.single_apply]
  have he : (a x).mulVec (unitVector j) i = a x i j := by
    simp [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [he] at h
  rw [hu, mul_one] at h2
  exact h.trans h2

/-- The entries of the inverse of a matrix field with a.e. strongly measurable entries are a.e.
strongly measurable. -/
theorem aestronglyMeasurable_inv_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {M : α → Mat d} (hM : ∀ i j, AEStronglyMeasurable (fun x => M x i j) μ) (i j : Fin d) :
    AEStronglyMeasurable (fun x => (M x)⁻¹ i j) μ := by
  set M' : α → Fin d → Fin d → ℝ := fun x k l => (hM k l).mk _ x with hM'
  have hmeas : Measurable M' := measurable_pi_iff.2 fun k =>
    measurable_pi_iff.2 fun l => (hM k l).stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ x ∂μ, M' x = M x := by
    have h : ∀ᵐ x ∂μ, ∀ k l, M' x k l = M x k l := by
      rw [ae_all_iff]
      intro k
      rw [ae_all_iff]
      intro l
      exact (hM k l).ae_eq_mk.symm
    filter_upwards [h] with x hx
    funext k l
    exact hx k l
  refine (_root_.Homogenization.measurable_matrix_inv_entry hmeas i j).aestronglyMeasurable.congr ?_
  filter_upwards [hae] with x hx
  exact congrArg (fun N : Mat d => N⁻¹ i j) hx

theorem aestronglyMeasurable_symmetricPart_apply {μ : Measure (Vec d)} (hμ : μ ≪ volume)
    (i j : Fin d) : AEStronglyMeasurable (fun x => symmetricPart (a x) i j) μ := by
  have h1 := ((a.aestronglyMeasurable i j).mono_ac hμ)
  have h2 := ((a.aestronglyMeasurable j i).mono_ac hμ)
  refine ((h1.add h2).const_mul (1 / 2 : ℝ)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [symmetricPart, Matrix.transpose_apply]

theorem aestronglyMeasurable_antisymmetricPart_apply {μ : Measure (Vec d)} (hμ : μ ≪ volume)
    (i j : Fin d) : AEStronglyMeasurable (fun x => antisymmetricPart (a x) i j) μ := by
  have h1 := ((a.aestronglyMeasurable i j).mono_ac hμ)
  have h2 := ((a.aestronglyMeasurable j i).mono_ac hμ)
  refine ((h1.sub h2).const_mul (1 / 2 : ℝ)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [antisymmetricPart, Matrix.transpose_apply]

theorem aestronglyMeasurable_inv_symmetricPart_apply {μ : Measure (Vec d)} (hμ : μ ≪ volume)
    (i j : Fin d) : AEStronglyMeasurable (fun x => (symmetricPart (a x))⁻¹ i j) μ :=
  aestronglyMeasurable_inv_apply (a.aestronglyMeasurable_symmetricPart_apply hμ) i j

theorem aestronglyMeasurable_apply {μ : Measure (Vec d)} (hμ : μ ≪ volume) (i j : Fin d) :
    AEStronglyMeasurable (fun x => a x i j) μ :=
  (a.aestronglyMeasurable i j).mono_ac hμ

/-- **The symmetric part of a field of `Ω`** is a coefficient field satisfying (0.6) with the same
constant `Λ`. -/
def symmetricPartField : CoefficientField d Λ where
  field x := symmetricPart (a x)
  locally_integrable i j := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hfin : volume K < ⊤ := hK.measure_lt_top
    have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hfin.ne
    refine Integrable.of_bound (C := Λ)
      (a.aestronglyMeasurable_symmetricPart_apply Measure.restrict_le_self.absolutelyContinuous i j)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := a.abs_apply_le x i j
    have h2 := a.abs_apply_le x j i
    simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_add_le (a x i j) (a x j i)
    linarith
  symmetric x := symmetricPart_transpose (a x)
  elliptic x ξ := ⟨a.euclideanSq_le_dot_symmetricPart x ξ, by
    rw [a.dot_symmetricPart]
    exact a.dot_mulVec_le x ξ⟩

@[simp] theorem symmetricPartField_apply (x : Vec d) :
    a.symmetricPartField x = symmetricPart (a x) := rfl

end GeneralCoefficientField

/-! ## The bilinear form of (10.7) -/

theorem linearRepresentative_eq_half_representativePairing (a : Mat d) (p q : Vec d) :
    linearRepresentative a p q = (1 / 2) * representativePairing a p q p q := by
  unfold linearRepresentative representativePairing
  ring

end QSH
