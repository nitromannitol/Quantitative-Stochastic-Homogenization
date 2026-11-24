import QuantitativeStochasticHomogenization.Ch02.Sec01.DefectTrials
import QuantitativeStochasticHomogenization.Ch03.Sec04.CutoffTestIdentity
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientCentering
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectorTensorIdentity
import QuantitativeStochasticHomogenization.Ch03.Sec03.WeakRestriction

/-!
# The cutoff of a skew field as a skew family of `H¹₀(U)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
toward Theorem 2.4: the dual trial `F = q + div(η(σ - c))` of the finite-cube argument from
first-order correctors. For a skew field `σ` (`σₖⱼ = -σⱼₖ`) with entries in `H¹(U)`, a skew matrix
`c` and a smooth cutoff `η` compactly supported in a bounded open convex `U`, the functions
`Θⱼₖ = η (σⱼₖ - cⱼₖ)` are in `H¹₀(U)`, with the gradients
`η ½(∇σⱼₖ - ∇σₖⱼ) + (σⱼₖ - cⱼₖ)∇η`, which are skew at every point (`skewCutoffFamily`,
`skewCutoffFamily_grad`, `skewCutoffFamily_skew`). The antisymmetrized gradient `½(∇σⱼₖ - ∇σₖⱼ)` is
a weak gradient of `σⱼₖ = ½(σⱼₖ - σₖⱼ)`, and its row divergence is almost everywhere the weak
divergence of the rows of `σ` (`ae_sum_skewGrad_eq`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

section Skew

variable {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
  {σ : Fin d → Fin d → Vec d → ℝ} {gσ : Fin d → Fin d → Vec d → Vec d}
  (hσ : ∀ j k, MemLp (σ j k) 2 (volume.restrict U))
  (hgσ : ∀ j k i, MemLp (fun x => gσ j k x i) 2 (volume.restrict U))
  (hw : ∀ j k, HasWeakGradient U (σ j k) (gσ j k))
  (hskew : ∀ j k x, σ k j x = -σ j k x) (c : Fin d → Fin d → ℝ)
  {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
  (hηU : tsupport η ⊆ U)

/-- The antisymmetrized gradient `½(∇σⱼₖ - ∇σₖⱼ)`. -/
def skewGrad (gσ : Fin d → Fin d → Vec d → Vec d) (j k : Fin d) (x : Vec d) : Vec d :=
  (1 / 2 : ℝ) • (gσ j k x - gσ k j x)

include hU hσ in
theorem memLp_sub_const_of_skew (j k : Fin d) :
    MemLp (fun x => σ j k x - c j k) 2 (volume.restrict U) := by
  have := isFiniteMeasure_restrict.mpr (volume_lt_top_of_isBoundedDomain hU.2.1).ne
  exact (hσ j k).sub (memLp_const _)

include hgσ in
theorem memLp_skewGrad (j k i : Fin d) :
    MemLp (fun x => skewGrad gσ j k x i) 2 (volume.restrict U) := by
  simp only [skewGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact ((hgσ j k i).sub (hgσ k j i)).const_mul _

include hw hskew in
theorem hasWeakGradient_sub_const_skewGrad (j k : Fin d) :
    HasWeakGradient U (fun x => σ j k x - c j k) (skewGrad gσ j k) := by
  have h1 := hasWeakGradient_sub (hw j k) (hw k j)
  have h2 : HasWeakGradient U (fun x => (1 / 2 : ℝ) * (σ j k x - σ k j x)) (skewGrad gσ j k) :=
    fun i => by
      simpa only [skewGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using
        hasWeakPartialDerivative_const_mul (h1 i) (1 / 2 : ℝ)
  have e : (fun x => (1 / 2 : ℝ) * (σ j k x - σ k j x)) = σ j k := by
    funext x
    rw [hskew j k x]
    ring
  rw [e] at h2
  exact hasWeakGradient_sub_const U h2 (c j k)

/-- **The family `Θⱼₖ = η (σⱼₖ - cⱼₖ)` of `H¹₀(U)`.** -/
def skewCutoffFamily (j k : Fin d) : PDE.H10Function U :=
  cutoffH10 hU (memLp_sub_const_of_skew hU hσ c j k) (memLp_skewGrad hgσ j k)
    (hasWeakGradient_sub_const_skewGrad hw hskew c j k) hη hηc hηU

theorem skewCutoffFamily_toFun (j k : Fin d) :
    (skewCutoffFamily hU hσ hgσ hw hskew c hη hηc hηU j k).toH1Function.toFun =
      fun x => η x * (σ j k x - c j k) :=
  cutoffH10_toFun hU _ _ _ hη hηc hηU

theorem skewCutoffFamily_grad (j k : Fin d) :
    (skewCutoffFamily hU hσ hgσ hw hskew c hη hηc hηU j k).toH1Function.grad =
      fun x => η x • skewGrad gσ j k x + (σ j k x - c j k) • gradient η x :=
  cutoffH10_grad hU _ _ _ hη hηc hηU

/-- **The gradients of `Θ` are skew at every point**, for a skew matrix `c`. -/
theorem skewCutoffFamily_skew (hc : ∀ j k, c k j = -c j k) (j k : Fin d) (x : Vec d) :
    (skewCutoffFamily hU hσ hgσ hw hskew c hη hηc hηU k j).toH1Function.grad x =
      -(skewCutoffFamily hU hσ hgσ hw hskew c hη hηc hηU j k).toH1Function.grad x := by
  rw [skewCutoffFamily_grad, skewCutoffFamily_grad]
  simp only [skewGrad, hskew j k x, hc j k]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

end Skew

/-- **The row divergence of the antisymmetrized gradient**: if the rows of a skew field `σ` on
`ℝ^d` have weak divergences `fⱼ`, then `Σₖ ½(∂ₖσⱼₖ - ∂ₖσₖⱼ) = fⱼ` almost everywhere. -/
theorem ae_sum_skewGrad_eq {σ : Fin d → Fin d → Vec d → ℝ} {gσ : Fin d → Fin d → Vec d → Vec d}
    (hw : ∀ j k, HasWeakGradient Set.univ (σ j k) (gσ j k))
    (hskew : ∀ j k x, σ k j x = -σ j k x) {f : Fin d → Vec d → ℝ}
    (hdiv : ∀ j, HasWeakDivergence Set.univ (fun x k => σ j k x) (f j)) (j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ k, skewGrad gσ j k x k = f j x := by
  have h1 := hasWeakDivergence_of_hasWeakGradient (F := fun x k => σ j k x) fun k => hw j k
  have h2 := hasWeakDivergence_of_hasWeakGradient (F := fun x k => σ k j x) fun k => hw k j
  have h3 : HasWeakDivergence Set.univ (fun x k => σ k j x) (fun x => -f j x) := by
    have h := hasWeakDivergence_const_smul (hdiv j) (-1)
    have e1 : (fun x => (-1 : ℝ) • fun k => σ j k x) = fun x k => σ k j x := by
      funext x k
      simp [hskew j k x]
    have e2 : (fun x => (-1 : ℝ) * f j x) = fun x => -f j x := by
      funext x
      ring
    rw [e1, e2] at h
    exact h
  have a1 := h1.ae_eq isOpen_univ (hdiv j)
  have a2 := h2.ae_eq isOpen_univ h3
  filter_upwards [a1, a2] with x hx1 hx2
  have e1 := hx1 (Set.mem_univ x)
  have e2 := hx2 (Set.mem_univ x)
  simp only [skewGrad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [e1, e2]
  ring

end QSH
