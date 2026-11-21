import QuantitativeStochasticHomogenization.AppD.HeatTaylor
import QuantitativeStochasticHomogenization.AppD.DerivativeCommutation

/-!
# Appendix D: expansion of the powers of the Laplacian

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D: `Δ^k χ = ∑_{w : Fin k → Fin d} ∂_{w₁}∂_{w₁} ⋯ ∂_{w_k}∂_{w_k} χ`
(`iterLaplacian_eq_sum`), and each term is `∂^{L} ∂^{L} χ` with `L = (w₁, …, w_k)`
(`foldr_doubled_eq`), so that half of the derivatives can be moved onto a convolution kernel.
-/

open MeasureTheory
open scoped ContDiff Convolution

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

/-- The multi-index of the counts of the coordinates of `w`. -/
def countIndex {k : ℕ} (w : Fin k → Fin d) : Fin d → Fin (k + 1) := fun i =>
  ⟨(List.ofFn w).count i, Nat.lt_succ_of_le (List.count_le_length.trans (by simp))⟩

theorem heatSmooth_finsetSum {ι : Type*} (s : Finset ι) {t : ℝ} {f : ι → Vec d → ℝ}
    (hf : ∀ i ∈ s, Continuous (f i) ∧ HasCompactSupport (f i)) (x : Vec d) :
    heatSmooth t (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, heatSmooth t (f i) x := by
  simp only [heatSmooth, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_mul_comp_sub_of_compact
    (contDiff_euclideanHeatKernel t).continuous (hf i hi).1 (hf i hi).2 x

/-- **Half of the derivatives on the kernel**: `Φ(s) ∗ Δ^k χ = ∑_w ∂^{β_w} Φ(s) ∗ ∂^{β_w} χ`, where
`β_w` counts the coordinates of `w`. -/
theorem heatSmooth_iterLaplacian {s : ℝ} (hs : 0 < s) {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (k : ℕ) (x : Vec d) :
    heatSmooth s (iterLaplacian k χ) x = ∑ w : Fin k → Fin d,
      (multiIndexDerivative (countIndex w) (euclideanHeatKernel (d := d) s) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] multiIndexDerivative (countIndex w) χ) x := by
  rw [iterLaplacian_eq_sum hχ k]
  have hsm : ∀ w : Fin k → Fin d, ContDiff ℝ ∞ ((doubledList w).foldr coordinateDerivative χ) ∧
      HasCompactSupport ((doubledList w).foldr coordinateDerivative χ) := fun w =>
    foldr_coordinateDerivative_smooth hχ hcχ _
  rw [heatSmooth_finsetSum Finset.univ (fun w _ => ⟨(hsm w).1.continuous, (hsm w).2⟩) x]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hL := foldr_coordinateDerivative_smooth hχ hcχ (List.ofFn w)
  rw [foldr_doubled_eq hχ w]
  unfold heatSmooth
  rw [convolution_foldr_coordinateDerivative hL.1 hL.2 (List.ofFn w)
    (contDiff_euclideanHeatKernel s),
    foldr_coordinateDerivative_eq_multiIndexDerivative (contDiff_euclideanHeatKernel s)
      (countIndex w) (fun i => by simp [countIndex]),
    foldr_coordinateDerivative_eq_multiIndexDerivative hχ (countIndex w)
      (fun i => by simp [countIndex])]

theorem sum_count_eq_length (l : List (Fin d)) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons, beq_iff_eq]
    rw [Finset.sum_add_distrib, ih]
    simp [Finset.sum_ite_eq']

theorem sum_countIndex {k : ℕ} (w : Fin k → Fin d) : ∑ i, (countIndex w i).val = k := by
  simp only [countIndex]
  rw [sum_count_eq_length, List.length_ofFn]

end QSH
