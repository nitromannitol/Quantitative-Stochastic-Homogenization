import QuantitativeStochasticHomogenization.Ch04.Sec01.EnergyQuantityBounds
import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientAlgebra

/-!
# The Gram space of a linear family of gradients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, (4.8) and (4.12).

Let `Ψ ≥ 0` be a mask of mass at most one and `ξ ↦ G ξ` a linear family of gradient fields with
`∫ Ψ |G ξ|² < ∞`. The form `⟨ξ, η⟩ = ∫ Ψ G ξ · a G η` is a positive semidefinite inner product on
`ℝ^d`; its separation quotient `H` is a finite-dimensional real inner product space of dimension at
most `d`. The averages `U ξ = ∫ Ψ G ξ` and `V ξ = ∫ Ψ a G ξ` define bounded linear maps
`U, V : H → ℝ^d` with `‖U‖ ≤ 1` and `‖V‖ ≤ Λ`.

When the gradients of `A₁` are exactly the fields `G ξ` up to null sets ((4.12), from Theorem 3.8),
completing the square in (4.8) gives `J₁(Ψ, p, q) = ½ ‖U^* q - V^* p‖²` (`J1_eq_gramEnergy`).
-/

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Pointwise bounds and measurability -/

theorem aemeasurable_mulVec (a : CoefficientField d Λ) {g : Vec d → Vec d}
    (hg : AEMeasurable g volume) : AEMeasurable (fun x => (a x).mulVec (g x)) volume := by
  have hgi : ∀ i, AEMeasurable (fun x => g x i) volume := fun i => aemeasurable_pi_iff.mp hg i
  have ha : ∀ i j, AEMeasurable (fun x => a.field x i j) volume := fun i j =>
    (a.locally_integrable i j).aestronglyMeasurable.aemeasurable
  refine aemeasurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.aemeasurable_fun_sum _ fun j _ => (ha i j).mul (hgi j)

theorem aemeasurable_dot {g h : Vec d → Vec d} (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) : AEMeasurable (fun x => dot (g x) (h x)) volume := by
  have hgi : ∀ i, AEMeasurable (fun x => g x i) volume := fun i => aemeasurable_pi_iff.mp hg i
  have hhi : ∀ i, AEMeasurable (fun x => h x i) volume := fun i => aemeasurable_pi_iff.mp hh i
  simp only [dot]
  exact Finset.aemeasurable_fun_sum _ fun i _ => (hgi i).mul (hhi i)

theorem form_nonneg (a : CoefficientField d Λ) (x g : Vec d) : 0 ≤ dot g ((a x).mulVec g) :=
  (euclideanSq_nonneg g).trans (a.elliptic x g).1

/-- `|g · a h| ≤ Λ/2 (|g|² + |h|²)`. -/
theorem abs_dot_mulVec_le (a : CoefficientField d Λ) (x g h : Vec d) :
    |dot g ((a x).mulVec h)| ≤ Λ / 2 * (euclideanSq g + euclideanSq h) := by
  have hcs := dot_mulVec_sq_le (a.symmetric x) (fun ξ => (a.elliptic x ξ).1) g h
  have hg := (a.elliptic x g).2
  have hh := (a.elliptic x h).2
  have hg0 := form_nonneg a x g
  have hh0 := form_nonneg a x h
  have hA : 0 ≤ Λ * euclideanSq g := hg0.trans hg
  have hB : 0 ≤ Λ * euclideanSq h := hh0.trans hh
  have h1 : dot g ((a x).mulVec h) ^ 2 ≤ (Λ * euclideanSq g) * (Λ * euclideanSq h) :=
    hcs.trans (mul_le_mul hg hh hh0 hA)
  have h2 : dot g ((a x).mulVec h) ^ 2 ≤ ((Λ * euclideanSq g + Λ * euclideanSq h) / 2) ^ 2 := by
    nlinarith [sq_nonneg (Λ * euclideanSq g - Λ * euclideanSq h)]
  have h3 := abs_le_of_sq_le_sq h2 (by positivity)
  calc |dot g ((a x).mulVec h)| ≤ (Λ * euclideanSq g + Λ * euclideanSq h) / 2 := h3
    _ = Λ / 2 * (euclideanSq g + euclideanSq h) := by ring

/-- `|a g|² ≤ Λ² |g|²`. -/
theorem euclideanSq_mulVec_le (a : CoefficientField d Λ) (x g : Vec d) :
    euclideanSq ((a x).mulVec g) ≤ Λ ^ 2 * euclideanSq g := by
  set p := (a x).mulVec g with hp
  have hcs := dot_mulVec_sq_le (a.symmetric x) (fun ξ => (a.elliptic x ξ).1) p g
  have hpp := (a.elliptic x p).2
  have hgg := (a.elliptic x g).2
  have hp0 := form_nonneg a x p
  have hg0 := form_nonneg a x g
  have hS : euclideanSq p = dot p ((a x).mulVec g) := rfl
  rw [← hS] at hcs
  have hS0 := euclideanSq_nonneg p
  have hG0 := euclideanSq_nonneg g
  have h1 : euclideanSq p ^ 2 ≤ (Λ * euclideanSq p) * (Λ * euclideanSq g) :=
    hcs.trans (mul_le_mul hpp hgg hg0 (hp0.trans hpp))
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h2 : euclideanSq p * euclideanSq p ≤ euclideanSq p * (Λ ^ 2 * euclideanSq g) := by
      nlinarith
    exact le_of_mul_le_mul_left h2 hpos

theorem norm_le_euclideanNorm (v : Vec d) : ‖v‖ ≤ euclideanNorm v :=
  (pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg v)).mpr fun i => by
    rw [Real.norm_eq_abs]
    unfold euclideanNorm euclideanSq dot
    apply Real.abs_le_sqrt
    rw [sq]
    exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)

theorem euclideanNorm_le_one_add_sq (v : Vec d) : euclideanNorm v ≤ (1 + euclideanSq v) / 2 := by
  have h := euclideanNorm_sq v
  have h0 := euclideanNorm_nonneg v
  nlinarith [sq_nonneg (euclideanNorm v - 1)]

/-! ## Integrability against a mask -/

section Mask

variable {mask : Vec d → ℝ}

theorem integrable_mask_smul (hmask0 : ∀ x, 0 ≤ mask x) (hmask : Integrable mask)
    {F : Vec d → Vec d} (hF : AEMeasurable F volume)
    (hF2 : Integrable (fun x => mask x * euclideanSq (F x))) :
    Integrable (fun x => mask x • F x) := by
  refine Integrable.mono' ((hmask.add hF2).div_const 2)
    ((hmask.aestronglyMeasurable.aemeasurable.smul hF).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hmask0 x)]
  calc mask x * ‖F x‖ ≤ mask x * ((1 + euclideanSq (F x)) / 2) :=
        mul_le_mul_of_nonneg_left ((norm_le_euclideanNorm _).trans
          (euclideanNorm_le_one_add_sq _)) (hmask0 x)
    _ = (mask x + mask x * euclideanSq (F x)) / 2 := by ring

theorem integrable_mask_mul_dot_mulVec (a : CoefficientField d Λ) (hmask0 : ∀ x, 0 ≤ mask x)
    (hmask : Integrable mask) {g h : Vec d → Vec d} (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) (hg2 : Integrable (fun x => mask x * euclideanSq (g x)))
    (hh2 : Integrable (fun x => mask x * euclideanSq (h x))) :
    Integrable (fun x => mask x * dot (g x) ((a x).mulVec (h x))) := by
  refine Integrable.mono' ((hg2.add hh2).const_mul (Λ / 2))
    ((hmask.aestronglyMeasurable.aemeasurable.mul
      (aemeasurable_dot hg (aemeasurable_mulVec a hh))).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hmask0 x)]
  calc mask x * |dot (g x) ((a x).mulVec (h x))|
      ≤ mask x * (Λ / 2 * (euclideanSq (g x) + euclideanSq (h x))) :=
        mul_le_mul_of_nonneg_left (abs_dot_mulVec_le a x _ _) (hmask0 x)
    _ = Λ / 2 * (mask x * euclideanSq (g x) + mask x * euclideanSq (h x)) := by ring

theorem integrable_mask_mul_euclideanSq_mulVec (a : CoefficientField d Λ)
    (hmask0 : ∀ x, 0 ≤ mask x) (hmask : Integrable mask) {g : Vec d → Vec d}
    (hg : AEMeasurable g volume) (hg2 : Integrable (fun x => mask x * euclideanSq (g x))) :
    Integrable (fun x => mask x * euclideanSq ((a x).mulVec (g x))) := by
  have hm := aemeasurable_mulVec a hg
  refine Integrable.mono' (hg2.const_mul (Λ ^ 2))
    ((hmask.aestronglyMeasurable.aemeasurable.mul (aemeasurable_dot hm hm)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hmask0 x), abs_of_nonneg (euclideanSq_nonneg _)]
  calc mask x * euclideanSq ((a x).mulVec (g x)) ≤ mask x * (Λ ^ 2 * euclideanSq (g x)) :=
        mul_le_mul_of_nonneg_left (euclideanSq_mulVec_le a x _) (hmask0 x)
    _ = Λ ^ 2 * (mask x * euclideanSq (g x)) := by ring

/-- Jensen's inequality for a mask of mass at most one: `|∫ Ψ F|² ≤ ∫ Ψ |F|²`. -/
theorem euclideanSq_integral_le (hmask0 : ∀ x, 0 ≤ mask x) (hmask : Integrable mask)
    (hmass : ∫ x, mask x ≤ 1) {F : Vec d → Vec d} (hF : AEMeasurable F volume)
    (hF2 : Integrable (fun x => mask x * euclideanSq (F x))) :
    euclideanSq (∫ x, mask x • F x) ≤ ∫ x, mask x * euclideanSq (F x) := by
  set v := ∫ x, mask x • F x with hv
  have hint := integrable_mask_smul hmask0 hmask hF hF2
  have h1 : euclideanSq v = ∫ x, dot v (mask x • F x) := dot_integral v hint
  have hpt : ∀ x, dot v (mask x • F x) ≤ (mask x * euclideanSq v + mask x * euclideanSq (F x)) / 2 :=
    fun x => by
      have hsq := euclideanSq_nonneg (v - F x)
      have hexp : euclideanSq (v - F x) = euclideanSq v - 2 * dot v (F x) + euclideanSq (F x) := by
        simp only [euclideanSq, dot, Pi.sub_apply, ← Finset.sum_sub_distrib, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hsm : dot v (mask x • F x) = mask x * dot v (F x) := by
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsm]
      have := hmask0 x
      nlinarith
  have h2 : ∫ x, dot v (mask x • F x) ≤
      ∫ x, (mask x * euclideanSq v + mask x * euclideanSq (F x)) / 2 :=
    integral_mono (integrable_dot_left v hint)
      (((hmask.mul_const _).add hF2).div_const 2) hpt
  have h3 : ∫ x, (mask x * euclideanSq v + mask x * euclideanSq (F x)) / 2 =
      ((∫ x, mask x) * euclideanSq v + ∫ x, mask x * euclideanSq (F x)) / 2 := by
    rw [integral_div, integral_add (hmask.mul_const _) hF2, integral_mul_const]
  have hS := euclideanSq_nonneg v
  have h4 : (∫ x, mask x) * euclideanSq v ≤ euclideanSq v := by
    nlinarith
  rw [h1] at hS ⊢
  linarith

end Mask

/-! ## Euclidean vectors -/

theorem inner_toLp_toLp_eq_dot (x y : Vec d) :
    ⟪WithLp.toLp 2 x, WithLp.toLp 2 y⟫_ℝ = dot x y := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dot, dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_toLp_sq (x : Vec d) : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 =
    euclideanSq x := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_toLp_eq_dot]
  rfl

theorem norm_toLp (x : Vec d) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ = euclideanNorm x := by
  rw [euclideanNorm, ← norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ## The Gram family -/

/-- A coefficient field, a nonnegative mask `Ψ` of mass at most one and a linear family `ξ ↦ G ξ`
of gradient fields with `∫ Ψ |G ξ|² < ∞`. -/
structure GramFamily (d : ℕ) (Λ : ℝ) where
  /-- The coefficient field. -/
  coeff : CoefficientField d Λ
  /-- The mask `Ψ`. -/
  mask : Vec d → ℝ
  /-- The family `ξ ↦ G ξ`. -/
  field : Vec d →ₗ[ℝ] Vec d → Vec d
  mask_nonneg : ∀ x, 0 ≤ mask x
  integrable_mask : Integrable mask
  integral_mask_le : ∫ x, mask x ≤ 1
  aemeasurable_field : ∀ ξ, AEMeasurable (field ξ) volume
  integrable_sq : ∀ ξ, Integrable (fun x => mask x * euclideanSq (field ξ x))

namespace GramFamily

variable (F : GramFamily d Λ)

/-- The form `⟨ξ, η⟩ = ∫ Ψ G ξ · a G η`. -/
def form (ξ η : Vec d) : ℝ :=
  ∫ x, F.mask x * dot (F.field ξ x) ((F.coeff x).mulVec (F.field η x))

theorem integrable_form (ξ η : Vec d) :
    Integrable (fun x => F.mask x * dot (F.field ξ x) ((F.coeff x).mulVec (F.field η x))) :=
  integrable_mask_mul_dot_mulVec F.coeff F.mask_nonneg F.integrable_mask (F.aemeasurable_field ξ)
    (F.aemeasurable_field η) (F.integrable_sq ξ) (F.integrable_sq η)

theorem integrable_gradient (ξ : Vec d) : Integrable (fun x => F.mask x • F.field ξ x) :=
  integrable_mask_smul F.mask_nonneg F.integrable_mask (F.aemeasurable_field ξ) (F.integrable_sq ξ)

theorem integrable_sq_flux (ξ : Vec d) :
    Integrable (fun x => F.mask x * euclideanSq ((F.coeff x).mulVec (F.field ξ x))) :=
  integrable_mask_mul_euclideanSq_mulVec F.coeff F.mask_nonneg F.integrable_mask
    (F.aemeasurable_field ξ) (F.integrable_sq ξ)

theorem integrable_flux (ξ : Vec d) :
    Integrable (fun x => F.mask x • (F.coeff x).mulVec (F.field ξ x)) :=
  integrable_mask_smul F.mask_nonneg F.integrable_mask
    (aemeasurable_mulVec F.coeff (F.aemeasurable_field ξ)) (F.integrable_sq_flux ξ)

theorem form_add_left (ξ ξ' η : Vec d) : F.form (ξ + ξ') η = F.form ξ η + F.form ξ' η := by
  unfold form
  rw [← integral_add (F.integrable_form ξ η) (F.integrable_form ξ' η)]
  congr 1
  funext x
  rw [map_add, Pi.add_apply]
  simp only [dot_eq_dotProduct, add_dotProduct]
  ring

theorem form_smul_left (c : ℝ) (ξ η : Vec d) : F.form (c • ξ) η = c * F.form ξ η := by
  unfold form
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [map_smul, Pi.smul_apply]
  simp only [dot_eq_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

theorem form_comm (ξ η : Vec d) : F.form ξ η = F.form η ξ := by
  unfold form
  congr 1
  funext x
  rw [dot_mulVec_comm (F.coeff.symmetric x)]

theorem energy_le_form (ξ : Vec d) : ∫ x, F.mask x * euclideanSq (F.field ξ x) ≤ F.form ξ ξ :=
  integral_mono (F.integrable_sq ξ) (F.integrable_form ξ ξ) fun x =>
    mul_le_mul_of_nonneg_left (F.coeff.elliptic x _).1 (F.mask_nonneg x)

theorem form_le_energy (ξ : Vec d) :
    F.form ξ ξ ≤ Λ * ∫ x, F.mask x * euclideanSq (F.field ξ x) := by
  rw [← integral_const_mul]
  refine integral_mono (F.integrable_form ξ ξ) ((F.integrable_sq ξ).const_mul Λ) fun x => ?_
  have h := mul_le_mul_of_nonneg_left (F.coeff.elliptic x (F.field ξ x)).2 (F.mask_nonneg x)
  calc F.mask x * dot (F.field ξ x) ((F.coeff x).mulVec (F.field ξ x))
      ≤ F.mask x * (Λ * euclideanSq (F.field ξ x)) := h
    _ = Λ * (F.mask x * euclideanSq (F.field ξ x)) := by ring

theorem form_self_nonneg (ξ : Vec d) : 0 ≤ F.form ξ ξ :=
  (integral_nonneg fun x => mul_nonneg (F.mask_nonneg x) (euclideanSq_nonneg _)).trans
    (F.energy_le_form ξ)

/-! ## The semi-inner product space and its separation quotient -/

/-- `ℝ^d` with the semi-inner product `F.form`. -/
structure Space (_F : GramFamily d Λ) where
  /-- The underlying vector. -/
  vec : Vec d

/-- The identification of `F.Space` with `ℝ^d`. -/
def spaceEquiv : F.Space ≃ Vec d where
  toFun ξ := ξ.vec
  invFun ξ := ⟨ξ⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup F.Space := F.spaceEquiv.addCommGroup

/-- The additive identification of `F.Space` with `ℝ^d`. -/
def spaceAddEquiv : F.Space ≃+ Vec d where
  __ := F.spaceEquiv
  map_add' _ _ := rfl

instance : Module ℝ F.Space := F.spaceAddEquiv.module ℝ

/-- A vector of `ℝ^d` as an element of `F.Space`. -/
def toSpace (ξ : Vec d) : F.Space := ⟨ξ⟩

/-- An element of `F.Space` as a vector of `ℝ^d`. -/
def ofSpace : F.Space →ₗ[ℝ] Vec d where
  toFun ξ := ξ.vec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear identification of `F.Space` with `ℝ^d`. -/
def spaceLinearEquiv : F.Space ≃ₗ[ℝ] Vec d := F.spaceAddEquiv.linearEquiv ℝ

/-- The semi-inner product `F.form`. -/
@[instance_reducible]
def core : PreInnerProductSpace.Core ℝ F.Space where
  inner ξ η := F.form ξ.vec η.vec
  conj_inner_symm ξ η := by
    rw [conj_trivial]
    exact F.form_comm η.vec ξ.vec
  re_inner_nonneg ξ := by
    rw [RCLike.re_to_real]
    exact F.form_self_nonneg ξ.vec
  add_left ξ ξ' η := F.form_add_left ξ.vec ξ'.vec η.vec
  smul_left ξ η c := by
    rw [conj_trivial]
    exact F.form_smul_left c ξ.vec η.vec

instance : SeminormedAddCommGroup F.Space :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ F.Space _ _ _ F.core

instance : InnerProductSpace ℝ F.Space := InnerProductSpace.ofCore F.core

instance : FiniteDimensional ℝ F.Space := LinearEquiv.finiteDimensional F.spaceLinearEquiv.symm

theorem inner_toSpace (ξ η : Vec d) : ⟪F.toSpace ξ, F.toSpace η⟫_ℝ = F.form ξ η := rfl

theorem norm_toSpace_sq (ξ : Vec d) : ‖F.toSpace ξ‖ ^ 2 = F.form ξ ξ := by
  rw [← real_inner_self_eq_norm_sq, inner_toSpace]

/-- The Gram space: the separation quotient of `F.Space`. -/
abbrev H := SeparationQuotient F.Space

instance : FiniteDimensional ℝ F.H :=
  Module.Finite.of_surjective (SeparationQuotient.mkCLM ℝ F.Space).toLinearMap
    SeparationQuotient.surjective_mk

instance : CompleteSpace F.H := FiniteDimensional.complete ℝ F.H

/-- The class of `ξ` in the Gram space. -/
def toH (ξ : Vec d) : F.H := SeparationQuotient.mk (F.toSpace ξ)

theorem toH_surjective : Function.Surjective F.toH := fun h => by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk h
  exact ⟨x.vec, rfl⟩

theorem norm_toH_sq (ξ : Vec d) : ‖F.toH ξ‖ ^ 2 = F.form ξ ξ := by
  rw [toH, SeparationQuotient.norm_mk, norm_toSpace_sq]

theorem finrank_H_le : Module.finrank ℝ F.H ≤ d := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (SeparationQuotient.mkCLM ℝ F.Space).toLinearMap) SeparationQuotient.surjective_mk
  have hd : Module.finrank ℝ F.Space = d :=
    (LinearEquiv.finrank_eq F.spaceLinearEquiv).trans (Module.finrank_fin_fun ℝ)
  calc Module.finrank ℝ F.H ≤ Module.finrank ℝ F.Space := h
    _ = d := hd

/-! ## The averages of the gradient and of the flux -/

/-- `ξ ↦ ∫ Ψ G ξ`. -/
def gradientAverage : F.Space →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun ξ := WithLp.toLp 2 (∫ x, F.mask x • F.field (F.ofSpace ξ) x)
  map_add' ξ η := by
    rw [← WithLp.toLp_add]
    congr 1
    rw [← integral_add (F.integrable_gradient _) (F.integrable_gradient _)]
    congr 1
    funext x
    rw [map_add, map_add, Pi.add_apply, smul_add]
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]
    congr 1
    rw [← integral_smul]
    congr 1
    funext x
    rw [map_smul, map_smul, Pi.smul_apply, smul_comm]

/-- `ξ ↦ ∫ Ψ a G ξ`. -/
def fluxAverage : F.Space →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun ξ := WithLp.toLp 2 (∫ x, F.mask x • (F.coeff x).mulVec (F.field (F.ofSpace ξ) x))
  map_add' ξ η := by
    rw [← WithLp.toLp_add]
    congr 1
    rw [← integral_add (F.integrable_flux _) (F.integrable_flux _)]
    congr 1
    funext x
    rw [map_add, map_add, Pi.add_apply, Matrix.mulVec_add, smul_add]
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]
    congr 1
    rw [← integral_smul]
    congr 1
    funext x
    rw [map_smul, map_smul, Pi.smul_apply, Matrix.mulVec_smul, smul_comm]

theorem norm_gradientAverage_le (ξ : F.Space) : ‖F.gradientAverage ξ‖ ≤ 1 * ‖ξ‖ := by
  rcases ξ with ⟨ξ⟩
  change ‖F.gradientAverage (F.toSpace ξ)‖ ≤ 1 * ‖F.toSpace ξ‖
  rw [one_mul]
  have h1 : ‖F.gradientAverage (F.toSpace ξ)‖ ^ 2 ≤ ‖F.toSpace ξ‖ ^ 2 := by
    rw [show ‖F.gradientAverage (F.toSpace ξ)‖ ^ 2 = euclideanSq (∫ x, F.mask x • F.field ξ x)
      from norm_toLp_sq _, F.norm_toSpace_sq ξ]
    exact (euclideanSq_integral_le F.mask_nonneg F.integrable_mask F.integral_mask_le
      (F.aemeasurable_field ξ) (F.integrable_sq ξ)).trans (F.energy_le_form ξ)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

theorem norm_fluxAverage_le (ξ : F.Space) : ‖F.fluxAverage ξ‖ ≤ |Λ| * ‖ξ‖ := by
  rcases ξ with ⟨ξ⟩
  change ‖F.fluxAverage (F.toSpace ξ)‖ ≤ |Λ| * ‖F.toSpace ξ‖
  have h1 : ‖F.fluxAverage (F.toSpace ξ)‖ ^ 2 ≤ (|Λ| * ‖F.toSpace ξ‖) ^ 2 := by
    rw [show ‖F.fluxAverage (F.toSpace ξ)‖ ^ 2 =
        euclideanSq (∫ x, F.mask x • (F.coeff x).mulVec (F.field ξ x)) from norm_toLp_sq _,
      mul_pow, sq_abs, F.norm_toSpace_sq ξ]
    refine (euclideanSq_integral_le F.mask_nonneg F.integrable_mask F.integral_mask_le
      (aemeasurable_mulVec F.coeff (F.aemeasurable_field ξ)) (F.integrable_sq_flux ξ)).trans ?_
    calc ∫ x, F.mask x * euclideanSq ((F.coeff x).mulVec (F.field ξ x))
        ≤ ∫ x, Λ ^ 2 * (F.mask x * euclideanSq (F.field ξ x)) :=
          integral_mono (F.integrable_sq_flux ξ) ((F.integrable_sq ξ).const_mul _) fun x => by
            have := mul_le_mul_of_nonneg_left (euclideanSq_mulVec_le F.coeff x (F.field ξ x))
              (F.mask_nonneg x)
            linarith
      _ = Λ ^ 2 * ∫ x, F.mask x * euclideanSq (F.field ξ x) := integral_const_mul _ _
      _ ≤ Λ ^ 2 * F.form ξ ξ := by gcongr; exact F.energy_le_form ξ
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

/-- The map `U` on the Gram space. -/
def U : F.H →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  SeparationQuotient.liftCLM (F.gradientAverage.mkContinuous 1 F.norm_gradientAverage_le)
    fun ξ η h => by
      rw [Metric.inseparable_iff, dist_eq_norm] at h
      rw [← sub_eq_zero, ← map_sub, ← norm_le_zero_iff]
      calc _ ≤ 1 * ‖ξ - η‖ := F.norm_gradientAverage_le (ξ - η)
        _ = 0 := by rw [h, mul_zero]

/-- The map `V` on the Gram space. -/
def V : F.H →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  SeparationQuotient.liftCLM (F.fluxAverage.mkContinuous |Λ| F.norm_fluxAverage_le)
    fun ξ η h => by
      rw [Metric.inseparable_iff, dist_eq_norm] at h
      rw [← sub_eq_zero, ← map_sub, ← norm_le_zero_iff]
      calc _ ≤ |Λ| * ‖ξ - η‖ := F.norm_fluxAverage_le (ξ - η)
        _ = 0 := by rw [h, mul_zero]

theorem U_toH (ξ : Vec d) : F.U (F.toH ξ) = WithLp.toLp 2 (∫ x, F.mask x • F.field ξ x) := rfl

theorem V_toH (ξ : Vec d) :
    F.V (F.toH ξ) = WithLp.toLp 2 (∫ x, F.mask x • (F.coeff x).mulVec (F.field ξ x)) := rfl

theorem norm_U_le : ‖F.U‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
  obtain ⟨ξ, rfl⟩ := F.toH_surjective h
  rw [U_toH, toH, SeparationQuotient.norm_mk]
  exact F.norm_gradientAverage_le (F.toSpace ξ)

theorem norm_V_le : ‖F.V‖ ≤ |Λ| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg Λ) fun h => ?_
  obtain ⟨ξ, rfl⟩ := F.toH_surjective h
  rw [V_toH, toH, SeparationQuotient.norm_mk]
  exact F.norm_fluxAverage_le (F.toSpace ξ)

end GramFamily

end QSH
