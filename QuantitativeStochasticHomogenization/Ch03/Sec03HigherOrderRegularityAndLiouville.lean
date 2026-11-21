import QuantitativeStochasticHomogenization.Front.Assumptions

/-!
# Section 3.3: Higher-Order Regularity Theory and Liouville Theorems

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 3 (Regularity on Large Scales), Section 3.3. Numbered results of this section: Theorem 3.8;
Lemma 3.9; Corollary 3.10.

Defined here: the class `A₁` of (3.38).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

/-- **The class `A₁`**, (3.38): whole-space `a`-harmonic functions with subquadratic growth. -/
structure HarmonicA1 {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) where
  potential : Vec d → ℝ
  grad : Vec d → Vec d
  weak_gradient : HasWeakGradient Set.univ potential grad
  local_energy : ∀ R : ℝ, 0 < R →
    MemLp potential 2 (volume.restrict (ball 0 R)) ∧
    MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict (ball 0 R))
  harmonic : HasWeakDivergence Set.univ (fun x => (a x).mulVec (grad x)) (fun _ => 0)
  growth : Tendsto
    (fun R : ℝ => R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |potential x| ^ 2))
    atTop (𝓝 0)

end QSH
