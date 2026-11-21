import Mathlib

/-!
# Section 5.3: the linear algebra of the coarsened coefficients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, Definition 5.23 and Lemma 5.24.

Let `H` be a finite-dimensional real inner product space and let `U, V : H → E` be two bounded
linear maps. In the application `H` is the space of gradients of `A₁` with the inner product
`⟨v, w⟩ = ∫ Φ_{z,r} v · a w`, `U v = ∫ Φ_{z,r} v` and `V v = ∫ Φ_{z,r} a v`, so that
`J₁(Φ_{z,r}, p, q) = ½ |U^* q - V^* p|²`, and the coarsened coefficient `b_r(z)` of (5.62) is the
matrix of the operator `b = V V^* - D U V^*` below, with `D = ā`.

This file proves `b = (V - D U) V^*`, the factorization `V - (D + b) U = (V - D U) (I - V^* U)`, the
bound `‖b‖ ≤ (1 + ‖D‖) (‖V V^* - D‖ + ‖U V^* - I‖)`, and, when `dim H ≤ dim E`, the quadratic bound
`‖V - (D + b) U‖ ≤ C (‖b‖ + ‖U V^* - I‖)²`: if `‖U V^* - I‖ ≤ 1/2`, then `U V^*` is invertible,
`V^*` is onto, and `(V - (D + b) U) V^* = b (I - U V^*)`.
-/

open scoped InnerProduct InnerProductSpace

noncomputable section

namespace QSH

open ContinuousLinearMap

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The coarsened operator `b = V V^* - D U V^*` of (5.62), written with the maps `U` and `V`. -/
def coarsenedOperator (U V : H →L[ℝ] E) (D : E →L[ℝ] E) : E →L[ℝ] E :=
  V ∘L V† - D ∘L U ∘L V†

/-- The first-order defect `T = ‖V V^* - D‖ + ‖U V^* - I‖`. -/
def firstOrderDefect (U V : H →L[ℝ] E) (D : E →L[ℝ] E) : ℝ :=
  ‖V ∘L V† - D‖ + ‖U ∘L V† - 1‖

theorem firstOrderDefect_nonneg (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    0 ≤ firstOrderDefect U V D :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- `b = (V - D U) V^*`. -/
theorem coarsenedOperator_eq_comp (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    coarsenedOperator U V D = (V - D ∘L U) ∘L V† := by
  ext x
  simp [coarsenedOperator]

/-- `b = (V V^* - D) + D (I - U V^*)`. -/
theorem coarsenedOperator_eq_add (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    coarsenedOperator U V D = (V ∘L V† - D) + D ∘L (1 - U ∘L V†) := by
  ext x
  simp [coarsenedOperator]

/-- **The factorization** `V - (D + b) U = (V - D U) (I - V^* U)`. -/
theorem sub_add_coarsenedOperator_comp (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    V - (D + coarsenedOperator U V D) ∘L U = (V - D ∘L U) ∘L (1 - V† ∘L U) := by
  ext x
  simp only [coarsenedOperator, sub_apply, add_apply, comp_apply,
    one_apply_eq_self, map_sub]
  abel

/-- **`‖b‖ ≤ (1 + ‖D‖) T`.** -/
theorem norm_coarsenedOperator_le (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    ‖coarsenedOperator U V D‖ ≤ (1 + ‖D‖) * firstOrderDefect U V D := by
  rw [coarsenedOperator_eq_add]
  have h1 := norm_add_le (V ∘L V† - D) (D ∘L (1 - U ∘L V†))
  have h2 := opNorm_comp_le D (1 - U ∘L V†)
  have h3 : ‖(1 : E →L[ℝ] E) - U ∘L V†‖ = ‖U ∘L V† - 1‖ := norm_sub_rev _ _
  have hA := norm_nonneg (V ∘L V† - D)
  have hB := norm_nonneg (U ∘L V† - 1)
  have hD := norm_nonneg D
  have hDA : 0 ≤ ‖D‖ * ‖V ∘L V† - D‖ := mul_nonneg hD hA
  unfold firstOrderDefect
  rw [h3] at h2
  linarith

/-- If `‖U V^* - I‖ ≤ 1/2`, then `‖x‖ ≤ 2 ‖U V^* x‖`. -/
theorem norm_le_two_mul_norm_comp_adjoint {U V : H →L[ℝ] E} (hC : ‖U ∘L V† - 1‖ ≤ 1 / 2)
    (x : E) : ‖x‖ ≤ 2 * ‖(U ∘L V†) x‖ := by
  have h1 : ‖(U ∘L V† - 1) x‖ ≤ 1 / 2 * ‖x‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg x))
  have h2 : (U ∘L V† - 1) x = (U ∘L V†) x - x := by
    rw [sub_apply, one_apply_eq_self]
  rw [h2] at h1
  have h3 := norm_sub_norm_le x ((U ∘L V†) x)
  rw [norm_sub_rev] at h3
  linarith

/-- If `dim H ≤ dim E` and `‖U V^* - I‖ ≤ 1/2`, every `h ∈ H` is `V^* x` with
`‖x‖ ≤ 2 ‖U‖ ‖h‖`. -/
theorem exists_adjoint_eq_of_finrank_le [FiniteDimensional ℝ H] [FiniteDimensional ℝ E]
    {U V : H →L[ℝ] E} (hdim : Module.finrank ℝ H ≤ Module.finrank ℝ E)
    (hC : ‖U ∘L V† - 1‖ ≤ 1 / 2) (h : H) :
    ∃ x : E, (V†) x = h ∧ ‖x‖ ≤ 2 * ‖U‖ * ‖h‖ := by
  have hinj : Function.Injective ((V† : E →L[ℝ] H) : E →ₗ[ℝ] H) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (V†) x = 0 := hx
    have h1 := norm_le_two_mul_norm_comp_adjoint hC x
    rw [comp_apply, hx', map_zero, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hsurj : Function.Surjective ((V† : E →L[ℝ] H) : E →ₗ[ℝ] H) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle hdim)).mp hinj
  obtain ⟨x, hx⟩ := hsurj h
  have hx' : (V†) x = h := hx
  refine ⟨x, hx', ?_⟩
  have h1 := norm_le_two_mul_norm_comp_adjoint hC x
  rw [comp_apply, hx'] at h1
  calc ‖x‖ ≤ 2 * ‖U h‖ := h1
    _ ≤ 2 * (‖U‖ * ‖h‖) := by gcongr; exact le_opNorm _ _
    _ = 2 * ‖U‖ * ‖h‖ := by ring

/-- **The quadratic error for small mixed defect**: if `dim H ≤ dim E` and `‖U V^* - I‖ ≤ 1/2`,
then `‖V - (D + b) U‖ ≤ 2 ‖U‖ ‖b‖ ‖U V^* - I‖`, since `(V - (D + b) U) V^* = b (I - U V^*)` and
`V^*` is onto. -/
theorem norm_sub_add_coarsenedOperator_comp_le_of_le_half [FiniteDimensional ℝ H]
    [FiniteDimensional ℝ E] {U V : H →L[ℝ] E} (D : E →L[ℝ] E)
    (hdim : Module.finrank ℝ H ≤ Module.finrank ℝ E) (hC : ‖U ∘L V† - 1‖ ≤ 1 / 2) :
    ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤
      2 * ‖U‖ * ‖coarsenedOperator U V D‖ * ‖U ∘L V† - 1‖ := by
  have hb := norm_nonneg (coarsenedOperator U V D)
  have hU := norm_nonneg U
  have hS := norm_nonneg (U ∘L V† - 1)
  refine opNorm_le_bound _ (by positivity) fun h => ?_
  obtain ⟨x, rfl, hx⟩ := exists_adjoint_eq_of_finrank_le hdim hC h
  have hval : (V - (D + coarsenedOperator U V D) ∘L U) ((V†) x) =
      coarsenedOperator U V D ((1 - U ∘L V†) x) := by
    simp only [coarsenedOperator, sub_apply, add_apply, comp_apply, one_apply_eq_self, map_sub]
    abel
  rw [hval]
  have hI : ‖(1 : E →L[ℝ] E) - U ∘L V†‖ = ‖U ∘L V† - 1‖ := norm_sub_rev _ _
  calc ‖coarsenedOperator U V D ((1 - U ∘L V†) x)‖
      ≤ ‖coarsenedOperator U V D‖ * ‖(1 - U ∘L V†) x‖ := le_opNorm _ _
    _ ≤ ‖coarsenedOperator U V D‖ * (‖U ∘L V† - 1‖ * ‖x‖) := by
        gcongr; rw [← hI]; exact le_opNorm _ _
    _ ≤ ‖coarsenedOperator U V D‖ * (‖U ∘L V† - 1‖ * (2 * ‖U‖ * ‖(V†) x‖)) := by
        gcongr
    _ = 2 * ‖U‖ * ‖coarsenedOperator U V D‖ * ‖U ∘L V† - 1‖ * ‖(V†) x‖ := by ring

/-- The crude bound `‖V - (D + b) U‖ ≤ ‖V‖ + (‖D‖ + ‖b‖) ‖U‖`. -/
theorem norm_sub_add_coarsenedOperator_comp_le (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤
      ‖V‖ + (‖D‖ + ‖coarsenedOperator U V D‖) * ‖U‖ := by
  calc ‖V - (D + coarsenedOperator U V D) ∘L U‖
      ≤ ‖V‖ + ‖(D + coarsenedOperator U V D) ∘L U‖ := norm_sub_le _ _
    _ ≤ ‖V‖ + ‖D + coarsenedOperator U V D‖ * ‖U‖ := by gcongr; exact opNorm_comp_le _ _
    _ ≤ ‖V‖ + (‖D‖ + ‖coarsenedOperator U V D‖) * ‖U‖ := by
        gcongr; exact norm_add_le _ _

/-- **The quadratic error**: if `dim H ≤ dim E`, `‖U‖ ≤ α`, `‖V‖ ≤ β` and `‖D‖ ≤ δ`, then
`‖V - (D + b) U‖ ≤ 4 (α + β + δ α) (‖b‖ + ‖U V^* - I‖)²`. -/
theorem norm_sub_add_coarsenedOperator_comp_le_sq [FiniteDimensional ℝ H]
    [FiniteDimensional ℝ E] {U V : H →L[ℝ] E} {D : E →L[ℝ] E}
    (hdim : Module.finrank ℝ H ≤ Module.finrank ℝ E) {α β δ : ℝ} (hU : ‖U‖ ≤ α) (hV : ‖V‖ ≤ β)
    (hDδ : ‖D‖ ≤ δ) :
    ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤
      4 * (α + β + δ * α) * (‖coarsenedOperator U V D‖ + ‖U ∘L V† - 1‖) ^ 2 := by
  set b := ‖coarsenedOperator U V D‖ with hbdef
  set S := ‖U ∘L V† - 1‖ with hSdef
  have hb0 : 0 ≤ b := norm_nonneg _
  have hS0 : 0 ≤ S := norm_nonneg _
  have hα : 0 ≤ α := (norm_nonneg U).trans hU
  have hβ : 0 ≤ β := (norm_nonneg V).trans hV
  have hδ : 0 ≤ δ := (norm_nonneg D).trans hDδ
  have hδα : 0 ≤ δ * α := mul_nonneg hδ hα
  have hT2 : 0 ≤ (b + S) ^ 2 := sq_nonneg _
  rcases le_or_gt S (1 / 2) with hsmall | hlarge
  · have h1 := norm_sub_add_coarsenedOperator_comp_le_of_le_half D hdim hsmall
    have h2 : 2 * ‖U‖ * b * S ≤ 2 * α * (b + S) ^ 2 := by
      have hbS : b * S ≤ (b + S) ^ 2 := by nlinarith
      calc 2 * ‖U‖ * b * S = 2 * ‖U‖ * (b * S) := by ring
        _ ≤ 2 * α * (b + S) ^ 2 := by gcongr
    have h3 : 2 * α * (b + S) ^ 2 ≤ 4 * (α + β + δ * α) * (b + S) ^ 2 := by
      gcongr <;> linarith
    exact h1.trans (h2.trans h3)
  · have h1 := norm_sub_add_coarsenedOperator_comp_le U V D
    have h2 : ‖V‖ + (‖D‖ + b) * ‖U‖ ≤ β + (δ + b) * α := by gcongr
    have hT : 1 / 2 < b + S := by linarith
    have h4 : 1 ≤ 4 * (b + S) ^ 2 := by nlinarith
    have h5 : b ≤ 2 * (b + S) ^ 2 := by nlinarith
    calc ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤ β + (δ + b) * α := h1.trans h2
      _ = (β + δ * α) * 1 + α * b := by ring
      _ ≤ (β + δ * α) * (4 * (b + S) ^ 2) + α * (2 * (b + S) ^ 2) := by gcongr
      _ ≤ 4 * (α + β + δ * α) * (b + S) ^ 2 := by nlinarith

/-! ## Polarization -/

/-- The quadratic form `J(p, q) = ½ ‖U^* q - V^* p‖²`, the form of `J₁(Φ_{z,r}, p, q)` on the
space of gradients of `A₁`. -/
def gramEnergy (U V : H →L[ℝ] E) (p q : E) : ℝ := (1 / 2 : ℝ) * ‖(U†) q - (V†) p‖ ^ 2

theorem gramEnergy_smul (U V : H →L[ℝ] E) (t : ℝ) (p q : E) :
    gramEnergy U V (t • p) (t • q) = t ^ 2 * gramEnergy U V p q := by
  unfold gramEnergy
  rw [map_smul, map_smul, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The mixed block: `q · U V^* p = J(p, 0) + J(0, q) - J(p, q)`. -/
theorem inner_comp_adjoint_eq_gramEnergy (U V : H →L[ℝ] E) (p q : E) :
    ⟪q, (U ∘L V†) p⟫_ℝ = gramEnergy U V p 0 + gramEnergy U V 0 q - gramEnergy U V p q := by
  unfold gramEnergy
  rw [map_zero, map_zero, zero_sub, sub_zero, norm_neg, norm_sub_sq_real, comp_apply,
    ← adjoint_inner_left]
  ring

/-- The coarsened coefficient by polarization, (5.62): if `D` is symmetric, then
`p · b k = ½ (J(p + k, D p) - J(p - k, D p))`. -/
theorem inner_coarsenedOperator_eq_gramEnergy (U V : H →L[ℝ] E) {D : E →L[ℝ] E}
    (hD : ∀ x y : E, ⟪x, D y⟫_ℝ = ⟪D x, y⟫_ℝ) (p k : E) :
    ⟪p, coarsenedOperator U V D k⟫_ℝ =
      (gramEnergy U V (p + k) (D p) - gramEnergy U V (p - k) (D p)) / 2 := by
  set A := (U†) (D p) - (V†) p with hA
  set B := (V†) k with hB
  have h1 : (U†) (D p) - (V†) (p + k) = A - B := by rw [map_add, hA, hB]; abel
  have h2 : (U†) (D p) - (V†) (p - k) = A + B := by rw [map_sub, hA, hB]; abel
  unfold gramEnergy
  rw [h1, h2, norm_sub_sq_real, norm_add_sq_real]
  have h3 : ⟪A, B⟫_ℝ = ⟪(U†) (D p), B⟫_ℝ - ⟪(V†) p, B⟫_ℝ := by rw [hA, inner_sub_left]
  have h4 : ⟪p, coarsenedOperator U V D k⟫_ℝ = ⟪(V†) p, B⟫_ℝ - ⟪(U†) (D p), B⟫_ℝ := by
    rw [coarsenedOperator, sub_apply, inner_sub_right, comp_apply, comp_apply, comp_apply, hD,
      ← adjoint_inner_left V ((V†) k) p, ← adjoint_inner_left U ((V†) k) (D p), hB]
  rw [h4, h3]
  ring

omit [CompleteSpace E] in
/-- An operator norm is at most the sum of the absolute values of the matrix entries in an
orthonormal basis. -/
theorem opNorm_le_sum_abs_inner {ι : Type*} [Fintype ι] (ob : OrthonormalBasis ι ℝ E)
    (M : E →L[ℝ] E) : ‖M‖ ≤ ∑ j, ∑ k, |⟪ob j, M (ob k)⟫_ℝ| := by
  have hvec : ∀ y : E, ‖y‖ ≤ ∑ j, |⟪ob j, y⟫_ℝ| := fun y => by
    conv_lhs => rw [← ob.sum_repr' y]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_smul, ob.orthonormal.1 j, mul_one, Real.norm_eq_abs]
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  have hx : M x = ∑ k, ⟪ob k, x⟫_ℝ • M (ob k) := by
    conv_lhs => rw [← ob.sum_repr' x]
    rw [map_sum]
    simp only [map_smul]
  have hcoef : ∀ k, |⟪ob k, x⟫_ℝ| ≤ ‖x‖ := fun k => by
    have := abs_real_inner_le_norm (ob k) x
    rwa [ob.orthonormal.1 k, one_mul] at this
  calc ‖M x‖ ≤ ∑ k, ‖⟪ob k, x⟫_ℝ • M (ob k)‖ := by rw [hx]; exact norm_sum_le _ _
    _ ≤ ∑ k, ‖x‖ * ∑ j, |⟪ob j, M (ob k)⟫_ℝ| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hcoef k) (hvec _) (norm_nonneg _) (norm_nonneg _)
    _ = (∑ j, ∑ k, |⟪ob j, M (ob k)⟫_ℝ|) * ‖x‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm, mul_comm]

end QSH
