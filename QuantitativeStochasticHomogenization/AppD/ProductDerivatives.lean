import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Appendix D: derivatives of functions of product form

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D (Sobolev norms and heat flow), preliminaries.

For smooth one-dimensional functions `hᵢ`, the iterated coordinate derivative `∂^β` of the
product `x ↦ ∏ᵢ hᵢ(xᵢ)`, in the form `multiIndexDerivative` of the normalized Sobolev norms
(0.26), is the product `∏ᵢ hᵢ^{(βᵢ)}(xᵢ)` of the one-dimensional derivatives
(`multiIndexDerivative_prod`). The heat kernel is of this form.
-/

open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The product `x ↦ ∏ᵢ hᵢ(xᵢ)`. -/
def prodFun (h : Fin d → ℝ → ℝ) (x : Vec d) : ℝ := ∏ i, h i (x i)

theorem coordinateDerivative_prodFun {h : Fin d → ℝ → ℝ} (hh : ∀ i, Differentiable ℝ (h i))
    (j : Fin d) (x : Vec d) :
    coordinateDerivative j (prodFun h) x =
      prodFun (Function.update h j (deriv (h j))) x := by
  classical
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin d)), HasFDerivAt (fun y : Vec d => h i (y i))
      ((deriv (h i) (x i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x :=
    fun i _ => ((hh i) (x i)).hasDerivAt.comp_hasFDerivAt x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt
  have hprod := HasFDerivAt.finsetProd hd
  unfold coordinateDerivative prodFun
  rw [hprod.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, unitVector, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one, ← Finset.mul_prod_erase Finset.univ
      (fun i => Function.update h j (deriv (h j)) i (x i)) (Finset.mem_univ j),
      Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem foldr_coordinateDerivative_prodFun {h : Fin d → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ ∞ (h i))
    (l : List (Fin d)) :
    l.foldr coordinateDerivative (prodFun h) =
      prodFun (fun i => iteratedDeriv (l.count i) (h i)) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, ih]
    funext x
    have hdiff : ∀ i, Differentiable ℝ (iteratedDeriv (l.count i) (h i)) := fun i => by
      rw [iteratedDeriv_eq_iterate]
      exact ((hh i).iterate_deriv (l.count i)).differentiable (by simp)
    rw [coordinateDerivative_prodFun hdiff j x]
    unfold prodFun
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, List.count_cons_self, iteratedDeriv_succ]
    · rw [Function.update_of_ne hij, List.count_cons_of_ne (Ne.symm hij)]

theorem count_multiIndexList {m : ℕ} (β : Fin d → Fin (m + 1)) (i : Fin d) :
    ((List.finRange d).flatMap fun j => List.replicate (β j).val j).count i = (β i).val := by
  rw [List.count_flatMap]
  have : (List.map (List.count i ∘ fun j => List.replicate (β j).val j) (List.finRange d)) =
      List.map (fun j => if j = i then (β j).val else 0) (List.finRange d) := by
    refine List.map_congr_left fun j _ => ?_
    simp [List.count_replicate]
  rw [this, ← List.sum_toFinset _ (List.nodup_finRange d)]
  · simp

/-- **Iterated derivatives of products**: `∂^β ∏ᵢ hᵢ(xᵢ) = ∏ᵢ hᵢ^{(βᵢ)}(xᵢ)`. -/
theorem multiIndexDerivative_prodFun {m : ℕ} {h : Fin d → ℝ → ℝ}
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (β : Fin d → Fin (m + 1)) :
    multiIndexDerivative β (prodFun h) = prodFun (fun i => iteratedDeriv (β i).val (h i)) := by
  unfold multiIndexDerivative
  rw [foldr_coordinateDerivative_prodFun hh]
  simp only [count_multiIndexList]

end QSH
