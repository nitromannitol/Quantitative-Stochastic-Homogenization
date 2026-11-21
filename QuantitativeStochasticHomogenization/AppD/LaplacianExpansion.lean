import QuantitativeStochasticHomogenization.AppD.HeatTaylor
import QuantitativeStochasticHomogenization.AppD.DerivativeCommutation

/-!
# Appendix D: expansion of the powers of the Laplacian

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: `Δ^k χ = ∑_{w : Fin k → Fin d} ∂_{w₁}∂_{w₁} ⋯ ∂_{w_k}∂_{w_k} χ`
(`iterLaplacian_eq_sum`), and each term is `∂^{L} ∂^{L} χ` with `L = (w₁, …, w_k)`
(`foldr_doubled_eq`), so that half of the derivatives can be moved onto a convolution kernel.
-/

open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The list `(w₁, w₁, …, w_k, w_k)`. -/
def doubledList {k : ℕ} (w : Fin k → Fin d) : List (Fin d) :=
  (List.ofFn w).flatMap fun j => [j, j]

theorem coordinateDerivative_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (j : Fin d) :
    coordinateDerivative j (fun x => ∑ i ∈ s, f i x) =
      fun x => ∑ i ∈ s, coordinateDerivative j (f i) x := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_fun_sum fun i hi => ((hf i hi).differentiable (by simp)) x]
  simp

theorem iterLaplacian_eq_sum {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ) (k : ℕ) :
    iterLaplacian k χ = fun x => ∑ w : Fin k → Fin d, (doubledList w).foldr coordinateDerivative χ x := by
  induction k with
  | zero =>
    funext x
    simp [iterLaplacian, doubledList]
  | succ k ih =>
    rw [iterLaplacian_succ, ih]
    funext x
    have hsm : ∀ w : Fin k → Fin d,
        ContDiff ℝ ∞ ((doubledList w).foldr coordinateDerivative χ) := fun w =>
      foldr_coordinateDerivative_contDiff hχ _
    simp only [coordLaplacian]
    simp only [coordinateDerivative_finsetSum Finset.univ (fun w _ => hsm w)]
    simp only [coordinateDerivative_finsetSum Finset.univ
      (fun w _ => contDiff_coordinateDerivative (hsm w) _)]
    rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin d)).symm _
      (fun p => (doubledList (Fin.cons p.1 p.2 : Fin (k + 1) → Fin d)).foldr
        coordinateDerivative χ x) (fun w => by simp)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    simp [doubledList, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

theorem foldr_doubled_eq {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ) {k : ℕ} (w : Fin k → Fin d) :
    (doubledList w).foldr coordinateDerivative χ =
      (List.ofFn w).foldr coordinateDerivative ((List.ofFn w).foldr coordinateDerivative χ) := by
  rw [← List.foldr_append]
  refine foldr_coordinateDerivative_perm hχ (List.perm_iff_count.mpr fun i => ?_)
  rw [doubledList, List.count_flatMap, List.count_append]
  induction (List.ofFn w) with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp, List.count_cons]
    rw [ih]
    split_ifs <;> (simp_all; try omega)

end QSH
