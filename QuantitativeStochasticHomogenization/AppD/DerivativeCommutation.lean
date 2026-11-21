import QuantitativeStochasticHomogenization.AppD.HeatSmoothing

/-!
# Appendix D: coordinate derivatives commute

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: for a smooth function, the iterated coordinate derivative along a list of coordinates
depends only on the number of occurrences of each coordinate
(`foldr_coordinateDerivative_perm`, `foldr_coordinateDerivative_eq_multiIndexDerivative`), by the
symmetry of second derivatives.
-/

open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

theorem coordinateDerivative_comm {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Fin d) :
    coordinateDerivative a (coordinateDerivative b f) =
      coordinateDerivative b (coordinateDerivative a f) := by
  funext x
  have hsymm := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hd1 : Differentiable ℝ (fderiv ℝ f) := hf.fderiv_right (m := ∞) le_rfl |>.differentiable
    (by simp)
  have key : ∀ u v : Fin d, coordinateDerivative u (coordinateDerivative v f) x =
      fderiv ℝ (fderiv ℝ f) x (unitVector u) (unitVector v) := fun u v => by
    unfold coordinateDerivative
    rw [fderiv_clm_apply (hd1 x) (differentiableAt_const _)]
    simp
  rw [key, key, hsymm]

theorem foldr_coordinateDerivative_perm {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f)
    {l₁ l₂ : List (Fin d)} (h : l₁.Perm l₂) :
    l₁.foldr coordinateDerivative f = l₂.foldr coordinateDerivative f := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [List.foldr_cons, List.foldr_cons, ih]
  | swap a b l =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, List.foldr_cons]
    exact (coordinateDerivative_comm (foldr_coordinateDerivative_contDiff hf l) b a)
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **A list derivative is a multi-index derivative**: if the coordinate `i` occurs `βᵢ` times in
`l`, then `∂^l f = ∂^β f`. -/
theorem foldr_coordinateDerivative_eq_multiIndexDerivative {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f)
    {m : ℕ} (β : Fin d → Fin (m + 1)) {l : List (Fin d)} (hl : ∀ i, l.count i = (β i).val) :
    l.foldr coordinateDerivative f = multiIndexDerivative β f := by
  unfold multiIndexDerivative
  refine foldr_coordinateDerivative_perm hf (List.perm_iff_count.mpr fun i => ?_)
  rw [hl i, count_multiIndexList]

end QSH
