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

With `T = ‖V V^* - D‖ + ‖U V^* - I‖` this file proves the factorization
`V - (D + b) U = (V - D U) (I - V^* U)`, the bound `‖b‖ ≤ (1 + ‖D‖) T`, and, when
`dim H ≤ dim E` and `D ≥ I`, the quadratic bound `‖V - (D + b) U‖ ≤ C T²`.
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

/-- If `‖V V^* - D‖ ≤ 1/2` and `D ≥ I`, then `|x|² ≤ 2 ‖V^* x‖²`. -/
theorem sq_norm_le_two_mul_sq_norm_adjoint {U V : H →L[ℝ] E} {D : E →L[ℝ] E}
    (hD : ∀ x : E, ‖x‖ ^ 2 ≤ ⟪D x, x⟫_ℝ) (hT : firstOrderDefect U V D ≤ 1 / 2) (x : E) :
    ‖x‖ ^ 2 ≤ 2 * ‖(V†) x‖ ^ 2 := by
  have hVV : ‖(V†) x‖ ^ 2 = ⟪(V ∘L V†) x, x⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, comp_apply, adjoint_inner_left, real_inner_comm]
  have hsplit : ⟪(V ∘L V†) x, x⟫_ℝ = ⟪D x, x⟫_ℝ + ⟪(V ∘L V† - D) x, x⟫_ℝ := by
    rw [sub_apply, inner_sub_left]
    ring
  have hM : |⟪(V ∘L V† - D) x, x⟫_ℝ| ≤ ‖V ∘L V† - D‖ * ‖x‖ ^ 2 := by
    calc |⟪(V ∘L V† - D) x, x⟫_ℝ| ≤ ‖(V ∘L V† - D) x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖V ∘L V† - D‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
      _ = ‖V ∘L V† - D‖ * ‖x‖ ^ 2 := by ring
  have hA : ‖V ∘L V† - D‖ ≤ 1 / 2 := by
    have := norm_nonneg (U ∘L V† - 1)
    unfold firstOrderDefect at hT
    linarith
  have hx2 := sq_nonneg ‖x‖
  have hAx : ‖V ∘L V† - D‖ * ‖x‖ ^ 2 ≤ 1 / 2 * ‖x‖ ^ 2 := by gcongr
  have := neg_abs_le ⟪(V ∘L V† - D) x, x⟫_ℝ
  have := hD x
  linarith

/-- If `dim H ≤ dim E`, `D ≥ I` and `T ≤ 1/2`, every `h ∈ H` is `V^* x` with `‖x‖ ≤ 2 ‖h‖`. -/
theorem exists_adjoint_eq_of_finrank_le [FiniteDimensional ℝ H] [FiniteDimensional ℝ E]
    {U V : H →L[ℝ] E} {D : E →L[ℝ] E}
    (hdim : Module.finrank ℝ H ≤ Module.finrank ℝ E)
    (hD : ∀ x : E, ‖x‖ ^ 2 ≤ ⟪D x, x⟫_ℝ) (hT : firstOrderDefect U V D ≤ 1 / 2) (h : H) :
    ∃ x : E, (V†) x = h ∧ ‖x‖ ≤ 2 * ‖h‖ := by
  have hinj : Function.Injective ((V† : E →L[ℝ] H) : E →ₗ[ℝ] H) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := sq_norm_le_two_mul_sq_norm_adjoint hD hT x
    have hx' : (V†) x = 0 := hx
    rw [hx', norm_zero] at h1
    have : ‖x‖ ^ 2 ≤ 0 := by linarith
    have h0 : ‖x‖ = 0 := by
      have := sq_nonneg ‖x‖
      nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp h0
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hsurj : Function.Surjective ((V† : E →L[ℝ] H) : E →ₗ[ℝ] H) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle hdim)).mp hinj
  obtain ⟨x, hx⟩ := hsurj h
  have hx' : (V†) x = h := hx
  refine ⟨x, hx', ?_⟩
  have h1 := sq_norm_le_two_mul_sq_norm_adjoint hD hT x
  rw [hx'] at h1
  have h2 : ‖x‖ ^ 2 ≤ (2 * ‖h‖) ^ 2 := by
    have := sq_nonneg ‖h‖
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg x) (by positivity) (by norm_num)).mp h2

/-- **The quadratic error for small defect**: if `dim H ≤ dim E`, `D ≥ I` and `T ≤ 1/2`, then
`‖V - (D + b) U‖ ≤ 2 ‖b‖ T`. -/
theorem norm_sub_add_coarsenedOperator_comp_le_of_le_half [FiniteDimensional ℝ H]
    [FiniteDimensional ℝ E] {U V : H →L[ℝ] E} {D : E →L[ℝ] E}
    (hdim : Module.finrank ℝ H ≤ Module.finrank ℝ E)
    (hD : ∀ x : E, ‖x‖ ^ 2 ≤ ⟪D x, x⟫_ℝ) (hT : firstOrderDefect U V D ≤ 1 / 2) :
    ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤
      2 * ‖coarsenedOperator U V D‖ * firstOrderDefect U V D := by
  rw [sub_add_coarsenedOperator_comp]
  have hb := norm_nonneg (coarsenedOperator U V D)
  have hT0 := firstOrderDefect_nonneg U V D
  refine opNorm_le_bound _ (by positivity) fun h => ?_
  obtain ⟨x, rfl, hx⟩ := exists_adjoint_eq_of_finrank_le hdim hD hT h
  have hval : ((V - D ∘L U) ∘L (1 - V† ∘L U)) ((V†) x) =
      coarsenedOperator U V D ((1 - U ∘L V†) x) := by
    rw [coarsenedOperator_eq_comp]
    simp only [comp_apply, sub_apply, one_apply_eq_self, map_sub]
  rw [hval]
  have hI : ‖(1 : E →L[ℝ] E) - U ∘L V†‖ ≤ firstOrderDefect U V D := by
    rw [norm_sub_rev]
    unfold firstOrderDefect
    linarith [norm_nonneg (V ∘L V† - D)]
  calc ‖coarsenedOperator U V D ((1 - U ∘L V†) x)‖
      ≤ ‖coarsenedOperator U V D‖ * ‖(1 - U ∘L V†) x‖ := le_opNorm _ _
    _ ≤ ‖coarsenedOperator U V D‖ * (‖(1 : E →L[ℝ] E) - U ∘L V†‖ * ‖x‖) := by
        gcongr; exact le_opNorm _ _
    _ ≤ ‖coarsenedOperator U V D‖ * (firstOrderDefect U V D * (2 * ‖(V†) x‖)) := by
        gcongr
    _ = 2 * ‖coarsenedOperator U V D‖ * firstOrderDefect U V D * ‖(V†) x‖ := by ring

/-- The crude bound `‖V - (D + b) U‖ ≤ ‖V‖ + (‖D‖ + ‖b‖) ‖U‖`. -/
theorem norm_sub_add_coarsenedOperator_comp_le (U V : H →L[ℝ] E) (D : E →L[ℝ] E) :
    ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤
      ‖V‖ + (‖D‖ + ‖coarsenedOperator U V D‖) * ‖U‖ := by
  calc ‖V - (D + coarsenedOperator U V D) ∘L U‖
      ≤ ‖V‖ + ‖(D + coarsenedOperator U V D) ∘L U‖ := norm_sub_le _ _
    _ ≤ ‖V‖ + ‖D + coarsenedOperator U V D‖ * ‖U‖ := by gcongr; exact opNorm_comp_le _ _
    _ ≤ ‖V‖ + (‖D‖ + ‖coarsenedOperator U V D‖) * ‖U‖ := by
        gcongr; exact norm_add_le _ _

/-- **The quadratic error**: if `dim H ≤ dim E`, `D ≥ I`, `‖U‖ ≤ α`, `‖V‖ ≤ β` and `‖D‖ ≤ δ`, then
`‖V - (D + b) U‖ ≤ (2 (1 + δ) (1 + α) + 4 (β + δ α)) T²`. -/
theorem norm_sub_add_coarsenedOperator_comp_le_sq [FiniteDimensional ℝ H]
    [FiniteDimensional ℝ E] {U V : H →L[ℝ] E} {D : E →L[ℝ] E}
    (hdim : Module.finrank ℝ H ≤ Module.finrank ℝ E)
    (hD : ∀ x : E, ‖x‖ ^ 2 ≤ ⟪D x, x⟫_ℝ) {α β δ : ℝ} (hU : ‖U‖ ≤ α) (hV : ‖V‖ ≤ β)
    (hDδ : ‖D‖ ≤ δ) :
    ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤
      (2 * (1 + δ) * (1 + α) + 4 * (β + δ * α)) * firstOrderDefect U V D ^ 2 := by
  set T := firstOrderDefect U V D with hTdef
  have hT0 : 0 ≤ T := firstOrderDefect_nonneg U V D
  have hα : 0 ≤ α := (norm_nonneg U).trans hU
  have hβ : 0 ≤ β := (norm_nonneg V).trans hV
  have hδ : 0 ≤ δ := (norm_nonneg D).trans hDδ
  have hb := norm_coarsenedOperator_le U V D
  have hbδ : ‖coarsenedOperator U V D‖ ≤ (1 + δ) * T :=
    hb.trans (by gcongr)
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  have hrest : 0 ≤ 2 * (1 + δ) * α * T ^ 2 + 4 * (β + δ * α) * T ^ 2 := by positivity
  rcases le_or_gt T (1 / 2) with hsmall | hlarge
  · have h1 := norm_sub_add_coarsenedOperator_comp_le_of_le_half hdim hD hsmall
    have h2 : 2 * ‖coarsenedOperator U V D‖ * T ≤ 2 * ((1 + δ) * T) * T := by gcongr
    have h3 : 2 * ((1 + δ) * T) * T = 2 * (1 + δ) * T ^ 2 := by ring
    calc ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤ 2 * (1 + δ) * T ^ 2 := by linarith
      _ ≤ (2 * (1 + δ) * (1 + α) + 4 * (β + δ * α)) * T ^ 2 := by nlinarith
  · have h1 := norm_sub_add_coarsenedOperator_comp_le U V D
    have h2 : ‖V‖ + (‖D‖ + ‖coarsenedOperator U V D‖) * ‖U‖ ≤ β + (δ + (1 + δ) * T) * α := by
      gcongr
    have h4 : β + δ * α ≤ 4 * (β + δ * α) * T ^ 2 := by
      have : 1 ≤ 4 * T ^ 2 := by nlinarith
      have hβδ : 0 ≤ β + δ * α := by positivity
      nlinarith
    have h5 : (1 + δ) * T * α ≤ 2 * (1 + δ) * α * T ^ 2 := by
      have : T ≤ 2 * T ^ 2 := by nlinarith
      have h1δα : 0 ≤ (1 + δ) * α := by positivity
      nlinarith
    calc ‖V - (D + coarsenedOperator U V D) ∘L U‖ ≤ β + (δ + (1 + δ) * T) * α := h1.trans h2
      _ = (β + δ * α) + (1 + δ) * T * α := by ring
      _ ≤ 4 * (β + δ * α) * T ^ 2 + 2 * (1 + δ) * α * T ^ 2 := add_le_add h4 h5
      _ ≤ (2 * (1 + δ) * (1 + α) + 4 * (β + δ * α)) * T ^ 2 := by nlinarith

end QSH
