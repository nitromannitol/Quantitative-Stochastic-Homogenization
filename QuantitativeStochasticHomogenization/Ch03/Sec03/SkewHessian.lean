import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Contraction of a skew family with second derivatives

Second coordinate derivatives of a `C²` function commute, so for a family `Ξ_{jk}` of `C²`
functions with `Ξ_{kj} = -Ξ_{jk}` the contraction `∑_{j,k} ∂ⱼ∂ₖ Ξ_{jk}` vanishes. This is the
cancellation behind the tensor identity of the harmonic approximation (2).
-/

noncomputable section

namespace QSH

variable {d : ℕ}

theorem coordinateDerivative_coordinateDerivative_eq {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (j k : Fin d) (x : Vec d) :
    coordinateDerivative j (coordinateDerivative k f) x =
      fderiv ℝ (fderiv ℝ f) x (unitVector j) (unitVector k) := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) x
  unfold coordinateDerivative
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp

theorem coordinateDerivative_comm_of_contDiff_two {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (j k : Fin d)
    (x : Vec d) :
    coordinateDerivative j (coordinateDerivative k f) x =
      coordinateDerivative k (coordinateDerivative j f) x := by
  rw [coordinateDerivative_coordinateDerivative_eq hf, coordinateDerivative_coordinateDerivative_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem coordinateDerivative_fun_neg (f : Vec d → ℝ) (j : Fin d) :
    coordinateDerivative j (fun x => -f x) = fun x => -coordinateDerivative j f x := by
  funext x
  unfold coordinateDerivative
  rw [show (fun x => -f x) = -f from rfl, fderiv_neg]
  rfl

/-- **`∑_{j,k} ∂ⱼ∂ₖ Ξ_{jk} = 0` for a skew family of `C²` functions.** -/
theorem sum_coordinateDerivative_skew_eq_zero {Ξ : Fin d → Fin d → Vec d → ℝ}
    (hΞ : ∀ j k, ContDiff ℝ 2 (Ξ j k)) (hskew : ∀ j k, Ξ k j = fun x => -Ξ j k x)
    (x : Vec d) :
    ∑ j, ∑ k, coordinateDerivative j (coordinateDerivative k (Ξ j k)) x = 0 := by
  set S := ∑ j, ∑ k, coordinateDerivative j (coordinateDerivative k (Ξ j k)) x with hS
  have h : S = -S := by
    calc S = ∑ k, ∑ j, coordinateDerivative j (coordinateDerivative k (Ξ j k)) x := by
          rw [hS, Finset.sum_comm]
      _ = ∑ k, ∑ j, coordinateDerivative k (coordinateDerivative j (Ξ j k)) x := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          exact coordinateDerivative_comm_of_contDiff_two (hΞ j k) j k x
      _ = ∑ k, ∑ j, -coordinateDerivative k (coordinateDerivative j (Ξ k j)) x := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hskew k j, coordinateDerivative_fun_neg, coordinateDerivative_fun_neg]
      _ = -S := by
          rw [hS]
          simp only [Finset.sum_neg_distrib]
  linarith

end QSH
