import QuantitativeStochasticHomogenization.Ch02.Sec02.Lemma215
import QuantitativeStochasticHomogenization.Ch04.Sec04.BallCaccioppoli

/-!
# The Caccioppoli inequality on triadic cubes

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, the
Caccioppoli inequality (Lemma C.2) in the form used in the proof of Lemma 2.16: for a solution `v`
of `-∇·a∇v = 0` in `□_{n+1}` and every `k`,
`∫_{□_n} |∇v|² ≤ C(d, Λ) 3^{-2n} ∫_{□_{n+1}} |v - k|²` (`caccioppoli_triadicCube`). The cutoff is the
inner cube cutoff of `□_{n+1}` of relative width `¼`, which equals one on `□_n`
(`triadicCubeCutoff`), and the inequality is the Caccioppoli inequality of the elliptic regularity
library for a quantitative cutoff (`PDE.caccioppoli_coefficient_energy_on_inner`), as for balls in
`caccioppoli_ball`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

open _root_.Homogenization

variable {d : ℕ}

theorem triadicCube_subset_scaledClosedCubeSet (n : ℕ) :
    triadicCube d n ⊆ scaledClosedCubeSet (originCube d ((n + 1 : ℕ) : ℤ)) (1 - 2 * (1 / 4)) := by
  intro x hx i
  have h := (mem_triadicCube_iff.mp hx) i
  have hc : cubeCenter (originCube d ((n + 1 : ℕ) : ℤ)) i = 0 := by simp [cubeCenter, originCube]
  have hr : cubeRadius (originCube d ((n + 1 : ℕ) : ℤ)) = (1 / 2 : ℝ) * (3 * (3 : ℝ) ^ n) := by
    rw [cubeRadius, cubeScaleFactor_originCube]
    norm_num [pow_succ]
    ring
  show |x i - cubeCenter (originCube d ((n + 1 : ℕ) : ℤ)) i| ≤
    (1 - 2 * (1 / 4)) * cubeRadius (originCube d ((n + 1 : ℕ) : ℤ))
  rw [hc, hr, sub_zero]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  linarith

/-- The cutoff of `□_n` in `□_{n+1}`: the inner cube cutoff of `□_{n+1}` of relative width `¼`, with
`|∇η| ≤ 4 √(c_d) 3^{-(n+1)}`, `c_d = cutoffGradConst d`. -/
def triadicCubeCutoff (n : ℕ) :
    PDE.QuantitativeSmoothCutoff (triadicCube d n) (triadicCube d (n + 1))
      (Real.sqrt (cutoffGradConst d / (1 / 4 : ℝ) ^ 2 / ((3 : ℝ) ^ (n + 1)) ^ 2)) where
  toFun := innerCubeCutoff (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4)
  smooth := innerCubeCutoff_smooth _ (by norm_num) (by norm_num)
  hasCompactSupport := innerCubeCutoff_hasCompactSupport _ (by norm_num) (by norm_num)
  tsupport_subset := tsupport_innerCubeCutoff_subset_triadicCube (n + 1) (by norm_num) (by norm_num)
  nonneg := innerCubeCutoff_nonneg _ _
  le_one := innerCubeCutoff_le_one _ _
  eq_one_on_inner := fun x hx =>
    QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner (by norm_num) (by norm_num)
      (triadicCube_subset_scaledClosedCubeSet n hx)
  gradient_bound := fun x => by
    have h := euclideanSq_gradient_innerCubeCutoff_le (d := d) (n + 1) (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) x
    show Real.sqrt (euclideanSq (gradient (innerCubeCutoff (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4)) x)) ≤ _
    exact Real.sqrt_le_sqrt h

/-- **The Caccioppoli inequality on triadic cubes**: for `v ∈ H¹(□_{n+1})` with gradient `g` and
`∇·(a g) = 0` in `□_{n+1}`, `∫_{□_n} |g|² ≤ 4 Λ K² ∫_{□_{n+1}} |v - k|²`,
`K² = 16 c_d 3^{-2(n+1)}`. -/
theorem caccioppoli_triadicCube {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) (n : ℕ)
    {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (triadicCube d (n + 1))))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (triadicCube d (n + 1))))
    (hw : HasWeakGradient (triadicCube d (n + 1)) v g)
    (hdiv : HasWeakDivergence (triadicCube d (n + 1)) (fun x => (a x).mulVec (g x)) (fun _ => 0))
    (k : ℝ) :
    ∫ x in triadicCube d n, euclideanSq (g x) ≤
      4 * Λ * (cutoffGradConst d / (1 / 4 : ℝ) ^ 2 / ((3 : ℝ) ^ (n + 1)) ^ 2) *
        ∫ x in triadicCube d (n + 1), (v x - k) ^ 2 := by
  have hU := isOpenBoundedConvexDomain_triadicCube (d := d) (n + 1)
  have hUm : MeasurableSet (triadicCube d (n + 1)) := hU.1.measurableSet
  have hrm : MeasurableSet (triadicCube d n) := (isOpen_triadicCube n).measurableSet
  have hsol := isWeakDivergenceFormHarmonicOn_toH1FunctionOn hΛ a hUm hv hg hw hdiv
  have hEll := isEllipticFieldOn_ellipticFieldOf hΛ a hUm
  have h := PDE.caccioppoli_coefficient_energy_on_inner (k := k) hU hrm hUm hEll one_pos
    (by linarith) hsol (triadicCubeCutoff (d := d) n) subset_rfl
  simp only [div_one] at h
  have hK0 : 0 ≤ cutoffGradConst d / (1 / 4 : ℝ) ^ 2 / ((3 : ℝ) ^ (n + 1)) ^ 2 := by
    unfold cutoffGradConst
    positivity
  rw [Real.sq_sqrt hK0] at h
  have hsub : triadicCube d n ⊆ triadicCube d (n + 1) := by
    intro x hx
    rw [mem_triadicCube_iff] at hx ⊢
    intro i
    have := hx i
    have h3 : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hint : IntegrableOn (fun x => PDE.vecDot (g x) (PDE.matVecMul (ellipticFieldOf a x) (g x)))
      (triadicCube d n) :=
    (PDE.integrableOn_vecDot_of_memVectorL2On hg
      (PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hg)).mono_set hsub
  have hle : ∫ x in triadicCube d n, euclideanSq (g x) ≤
      ∫ x in triadicCube d n, PDE.vecDot (g x) (PDE.matVecMul (ellipticFieldOf a x) (g x)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => euclideanSq_nonneg _) hint
      (Eventually.of_forall fun x => ?_)
    have h1 := (isEllipticMatrix_ellipticFieldOf hΛ a x).2.2.1 (g x)
    rw [one_mul] at h1
    exact h1
  exact hle.trans h

end QSH
