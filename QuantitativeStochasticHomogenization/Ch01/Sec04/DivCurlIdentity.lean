import QuantitativeStochasticHomogenization.AppB.NegativeSobolevTwo
import QuantitativeStochasticHomogenization.Ch01.Sec04.HatNegativeSobolev
import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# Solenoidal fields and the identity of the div-curl lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the space `L²_sol(U)` of (0.34) and the first identity in the proof of Lemma 1.16: for
`u ∈ H¹(U)`, `g ∈ L²_sol(U)` and `φ ∈ C_c^∞(U)`, `∫_U φ ∇u · g = -∫_U u ∇φ · g`.

The proof tests `∇ · g = 0` with `φ u ∈ H¹₀(U)` (the multiplier of the elliptic regularity
library, `PDE.H1Function.mulContDiffHasCompactSupportToH10`, on bounded convex domains), through
the extension of the pairing of `∇ · g` to `H¹₀(U)` of Appendix C
(`abs_integral_pairing_le_of_h10`).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `g ∈ L²_sol(U)`, (0.34): `g ∈ L²(U; ℝ^d)` and `∇ · g = 0` in the sense of distributions. -/
def IsL2Sol (U : Set (Vec d)) (g : Vec d → Vec d) : Prop :=
  MemLp g 2 (volume.restrict U) ∧ HasWeakDivergence U g (fun _ => 0)

/-- The `H¹(U)` function of the elliptic regularity library with value `u` and gradient `G`. -/
def H1.toPDEH1Function {U : Set (Vec d)} {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : H1 U u G) :
    PDE.H1Function U where
  toFun := u
  grad := G
  memL2 := hu.1
  gradMemL2 := fun i => hu.2.1.eval i
  hasWeakGradient := fun i φ h1 h2 h3 => (hu.2.2 i).2.2 φ ⟨h1, h2, h3⟩

theorem negativeSobolevOneNorm_zero_eq_zero_of_isL2Sol {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : IsL2Sol U g) : negativeSobolevOneNorm 2 U 0 g = 0 := by
  refine le_antisymm (iSup_le fun ψ => ?_) zero_le
  have h := hg.2.2.2 ψ.1 ψ.2.1
  simp only [zero_mul, integral_zero, neg_zero] at h
  have hp : distributionPairing U 0 g ψ.1 = 0 := by
    unfold distributionPairing
    simp only [Pi.zero_apply, zero_mul, zero_sub]
    rw [setAverage_eq, integral_neg, h, neg_zero, smul_zero]
  rw [hp, abs_zero, ENNReal.ofReal_zero]

/-- A solenoidal field is orthogonal to the gradients of `H¹₀(U)`. -/
theorem setIntegral_vecDot_grad_eq_zero_of_isL2Sol {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {g : Vec d → Vec d} (hg : IsL2Sol U g) (v : PDE.H10Function U) :
    ∫ x in U, PDE.vecDot (g x) (v.toH1Function.grad x) = 0 := by
  have h := abs_integral_pairing_le_of_h10 hU (f := 0) (F := g) MemLp.zero
    (fun i => hg.1.eval i) le_rfl
    (by rw [negativeSobolevOneNorm_zero_eq_zero_of_isL2Sol hg, ENNReal.ofReal_zero]) v
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub, abs_neg, mul_zero] at h
  exact abs_nonpos_iff.1 h

theorem exists_bound_of_isSpatialTest {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) : ∃ C, ∀ x, ‖φ x‖ ≤ C :=
  hφ.2.1.exists_bound_of_continuous hφ.1.continuous

theorem isSpatialTest_coordinateDerivative {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) : IsSpatialTest U (coordinateDerivative i φ) := by
  refine ⟨?_, hφ.2.1.fderiv_apply ℝ (unitVector i), ?_⟩
  · exact ((contDiff_infty_iff_fderiv.mp hφ.1).2).clm_apply contDiff_const
  · refine (tsupport_fderiv_apply_subset ℝ (unitVector i)).trans hφ.2.2

theorem integrable_dot_of_memLp {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U)) :
    Integrable (fun x => dot (F x) (G x)) (volume.restrict U) :=
  integrable_finsetSum _ fun i _ => (hF.eval i).integrable_mul (hG.eval i)

/-- **The identity of the div-curl lemma**: for `u ∈ H¹(U)` with gradient `G`, `g ∈ L²_sol(U)`
and a test `φ` on a bounded open convex `U`, `∫_U φ G · g = -∫_U u ∇φ · g`. -/
theorem setIntegral_mul_dot_eq_neg {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (hUt : volume U ≠ ⊤) {u : Vec d → ℝ} {G g : Vec d → Vec d} (hu : H1 U u G)
    (hg : IsL2Sol U g) {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∫ x in U, φ x * dot (G x) (g x) = -∫ x in U, u x * dot (gradient φ x) (g x) := by
  have h0 := setIntegral_vecDot_grad_eq_zero_of_isL2Sol hUt hg
    ((hu.toPDEH1Function).mulContDiffHasCompactSupportToH10 hU hφ.1 hφ.2.1 hφ.2.2)
  rw [PDE.H1Function.mulContDiffHasCompactSupportToH10_grad] at h0
  have hpt : ∀ x, PDE.vecDot (g x) (φ x • hu.toPDEH1Function.grad x +
      hu.toPDEH1Function.toFun x • PDE.classicalGradient φ x) =
      φ x * dot (G x) (g x) + u x * dot (gradient φ x) (g x) := by
    intro x
    simp only [PDE.vecDot, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, H1.toPDEH1Function,
      PDE.classicalGradient, gradient, coordinateDerivative, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show PDE.basisVec i = unitVector i from rfl]
    ring
  simp only [hpt] at h0
  obtain ⟨Cφ, hCφ⟩ := exists_bound_of_isSpatialTest hφ
  have hI1 : Integrable (fun x => φ x * dot (G x) (g x)) (volume.restrict U) :=
    (integrable_dot_of_memLp hu.2.1 hg.1).bdd_mul hφ.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hCφ)
  have hI2 : Integrable (fun x => u x * dot (gradient φ x) (g x)) (volume.restrict U) := by
    have hs : Integrable (fun x => ∑ i, coordinateDerivative i φ x * (u x * g x i))
        (volume.restrict U) := by
      refine integrable_finsetSum _ fun i _ => ?_
      obtain ⟨Ci, hCi⟩ := exists_bound_of_isSpatialTest (isSpatialTest_coordinateDerivative hφ i)
      exact (hu.1.integrable_mul (hg.1.eval i)).bdd_mul
        (isSpatialTest_coordinateDerivative hφ i).1.continuous.aestronglyMeasurable
        (Eventually.of_forall hCi)
    refine hs.congr (Eventually.of_forall fun x => ?_)
    simp only [dot, gradient, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_add hI1 hI2] at h0
  linarith

end QSH
