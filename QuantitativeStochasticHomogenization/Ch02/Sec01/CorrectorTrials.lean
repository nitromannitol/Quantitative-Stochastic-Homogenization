import QuantitativeStochasticHomogenization.Ch02.Sec01.SkewCutoff

/-!
# The bound of `J(U, p, Dp)` by a corrector and a flux corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
toward Theorem 2.4: the first step of the finite-cube argument for (2.21) from first-order
correctors. Let `φ ∈ H¹(U)` with gradient `∇φ`, and let `σ` be a skew field with entries in
`H¹(U)` whose antisymmetrized gradient has row divergence `a(p + ∇φ) - Dp` almost everywhere in
`U`. For a smooth cutoff `η` compactly supported in `U`, constants `m` and a skew matrix `c`, the
trials `E = p + ∇(η(φ - m))` and `F = Dp + div(η(σ - c))` give
`J(U, p, Dp) ≤ ½ ⨍_U |(1 - η)(a - D)p + (φ - m) a∇η - (σ - c)∇η|²` (`dualityDefect_le_of_correctors`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The bound of `J(U, p, Dp)` by a corrector `φ` and a flux corrector `σ`.** -/
theorem dualityDefect_le_of_correctors [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    (hU : PDE.IsOpenBoundedConvexDomain U) (D : Mat d) (p : Vec d)
    {φ : Vec d → ℝ} {gφ : Vec d → Vec d} (hφ : MemLp φ 2 (volume.restrict U))
    (hgφ : ∀ i, MemLp (fun x => gφ x i) 2 (volume.restrict U)) (hwφ : HasWeakGradient U φ gφ)
    (m : ℝ) {σ : Fin d → Fin d → Vec d → ℝ} {gσ : Fin d → Fin d → Vec d → Vec d}
    (hσ : ∀ j k, MemLp (σ j k) 2 (volume.restrict U))
    (hgσ : ∀ j k i, MemLp (fun x => gσ j k x i) 2 (volume.restrict U))
    (hwσ : ∀ j k, HasWeakGradient U (σ j k) (gσ j k)) (hskew : ∀ j k x, σ k j x = -σ j k x)
    (c : Fin d → Fin d → ℝ) (hc : ∀ j k, c k j = -c j k)
    (hflux : ∀ j, ∀ᵐ x ∂(volume.restrict U),
      ∑ k, skewGrad gσ j k x k = (a x).mulVec (p + gφ x) j - D.mulVec p j)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    dualityDefect a U p (D.mulVec p) ≤ (1 / 2 : ℝ) * ⨍ x in U, euclideanSq (fun j =>
      (1 - η x) * ((a x).mulVec p j - D.mulVec p j) +
        (φ x - m) * (a x).mulVec (gradient η x) j - ∑ k, (σ j k x - c j k) * gradient η x k) := by
  have hum : MemLp (fun x => φ x - m) 2 (volume.restrict U) := by
    have := isFiniteMeasure_restrict.mpr (volume_lt_top_of_isBoundedDomain hU.2.1).ne
    exact hφ.sub (memLp_const m)
  have hu := h01_cutoff_mul hU hum hgφ (hasWeakGradient_sub_const U hwφ m) hη hηc hηU
  set Θ := skewCutoffFamily hU hσ hgσ hwσ hskew c hη hηc hηU with hΘ
  have hΘs : ∀ j k x, (Θ k j).toH1Function.grad x = -(Θ j k).toH1Function.grad x :=
    skewCutoffFamily_skew hU hσ hgσ hwσ hskew c hη hηc hηU hc
  refine (dualityDefect_le_of_skew a hUo hUb hUc hne p (D.mulVec p) hu Θ hΘs).trans (le_of_eq ?_)
  congr 1
  refine average_congr ?_
  filter_upwards [ae_all_iff.mpr hflux] with x hx
  congr 1
  funext j
  have hg : ∀ k, (Θ j k).toH1Function.grad x k =
      η x * skewGrad gσ j k x k + (σ j k x - c j k) * gradient η x k := fun k => by
    rw [hΘ, skewCutoffFamily_grad]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.sub_apply, Pi.add_apply, hg, Finset.sum_add_distrib, ← Finset.mul_sum, hx j,
    Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

end QSH
