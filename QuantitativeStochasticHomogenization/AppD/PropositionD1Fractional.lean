import QuantitativeStochasticHomogenization.AppD.HeatFlowLp
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests

/-!
# Appendix D: Proposition D.1 for non-integer orders

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Proposition D.1, (D.2): for `p ∈ (1, ∞)` and `α ∈ (0, ∞) \ ℕ`,
`‖u‖_{W^{-α,p}(ℝ^d)} ≤ C (∫_0^1 (t^{α/2} ‖u ∗ Φ(t, ·)‖_{L^p(ℝ^d)})^p dt/t)^{1/p}`.

This file defines the norm (B.3) of `W^{m+β,q}(ℝ^d)` on smooth functions (`fractionalSobolevNorm`)
and the norm (B.4) of `W^{-(m+β),p}(ℝ^d)` (`negativeFractionalSobolevNorm`), and proves the bounds on
the heat flow of the Laplacian used in the book's proof: `|Φ(t) ∗ Δ^K g| ≤ d^K |∇^{2K} Φ(t, ·) ∗ g|`
(`abs_heatSmooth_iterLaplacian_le`), and `W^{m,q}(ℝ^d)` for smooth compactly supported functions
(`isSobolevFamilyLp_of_smooth`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff Convolution Nat

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The norm (B.3) of `W^{m+β,q}(ℝ^d)` of a smooth function, with the derivatives along lists of
coordinates: `∑_{j ≤ m} ∑_{|w| = j} ‖∂_w g‖_{L^q(ℝ^d)} + ∑_{|w| = m} [∂_w g]_{W^{β,q}(ℝ^d)}`. -/
def fractionalSobolevNorm (m : ℕ) (β q : ℝ) (g : Vec d → ℝ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (m + 1), ∑ w : Fin j → Fin d,
      eLpNorm ((List.ofFn w).foldr coordinateDerivative g) (ENNReal.ofReal q) volume) +
    fractionalSobolevSeminorm m β q (fun l => l.foldr coordinateDerivative g)

/-- The norm (B.4) of `W^{-(m+β),p}(ℝ^d)`: the supremum of `|∫ u g|` over `g ∈ C_c^∞(ℝ^d)` with
`‖g‖_{W^{m+β,p/(p-1)}(ℝ^d)} ≤ 1`. -/
def negativeFractionalSobolevNorm (m : ℕ) (β p : ℝ) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ g : {g : Vec d → ℝ // ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      fractionalSobolevNorm m β (p / (p - 1)) g ≤ 1},
    ENNReal.ofReal |∫ x, u x * g.1 x|

theorem hasCompactSupport_foldr_coordinateDerivative {g : Vec d → ℝ} (hcg : HasCompactSupport g) :
    ∀ l : List (Fin d), HasCompactSupport (l.foldr coordinateDerivative g)
  | [] => hcg
  | i :: l => hasCompactSupport_coordinateDerivative
      (hasCompactSupport_foldr_coordinateDerivative hcg l) i

/-- A smooth compactly supported function with its classical derivatives is in `W^{m,q}(ℝ^d)`. -/
theorem isSobolevFamilyLp_of_smooth (q : ℝ) (m : ℕ) {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) :
    IsSobolevFamilyLp q m g (fun l => l.foldr coordinateDerivative g) where
  nil := rfl
  memLp := fun l _ => (foldr_coordinateDerivative_contDiff hg l).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_foldr_coordinateDerivative hcg l)
  weak := fun l i _ => by
    have hv : IsSpatialTest univ (l.foldr coordinateDerivative g) :=
      ⟨foldr_coordinateDerivative_contDiff hg l, hasCompactSupport_foldr_coordinateDerivative hcg l,
        subset_univ _⟩
    refine ⟨hv.1.continuous.locallyIntegrable.locallyIntegrableOn _,
      (contDiff_coordinateDerivative hv.1 i).continuous.locallyIntegrable.locallyIntegrableOn _,
      fun ψ hψ => ?_⟩
    exact IsSpatialTest.integral_mul_coordinateDerivative hv hψ i

theorem sq_kconv_heatKernelDeriv_le_heatGradSq (t : ℝ) (g : Vec d → ℝ) (l : List (Fin d))
    (x : Vec d) : kconv (heatKernelDeriv t l) g x ^ 2 ≤ heatGradSq l.length t g x := by
  unfold heatGradSq
  conv_lhs => rw [← List.ofFn_get l]
  exact Finset.single_le_sum (f := fun w : Fin l.length → Fin d =>
    kconv (heatKernelDeriv t (List.ofFn w)) g x ^ 2) (fun w _ => sq_nonneg _) (Finset.mem_univ l.get)

theorem length_doubledList {k : ℕ} (w : Fin k → Fin d) : (doubledList w).length = 2 * k := by
  unfold doubledList
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.flatMap_cons, List.length_append, ih (fun i => w i.succ)]
    simp
    ring

/-- `|Φ(t) ∗ Δ^K g| ≤ d^K |∇^{2K} Φ(t, ·) ∗ g|`. -/
theorem abs_heatSmooth_iterLaplacian_le {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) {t : ℝ} (ht : 0 < t) (K : ℕ) (x : Vec d) :
    |heatSmooth t (iterLaplacian K g) x| ≤ (d : ℝ) ^ K * Real.sqrt (heatGradSq (2 * K) t g x) := by
  rw [iterLaplacian_eq_sum hg K]
  have hterm : ∀ w : Fin K → Fin d, heatSmooth t ((doubledList w).foldr coordinateDerivative g) x =
      kconv (heatKernelDeriv t (doubledList w).reverse) g x := fun w => by
    rw [kconv_heatKernelDeriv_eq_heatSmooth hg hcg, List.reverse_reverse]
  have hsum : heatSmooth t (fun y => ∑ w : Fin K → Fin d, (doubledList w).foldr coordinateDerivative g y) x =
      ∑ w : Fin K → Fin d, heatSmooth t ((doubledList w).foldr coordinateDerivative g) x := by
    change kconv _ _ x = ∑ w : Fin K → Fin d, kconv _ _ x
    simp_rw [kconv_apply, Finset.mul_sum]
    refine integral_finsetSum _ fun w _ => ?_
    exact integrable_mul_of_bound_of_memLp (K := fun y => euclideanHeatKernel t (x - y)) le_rfl
      ((integrable_euclideanHeatKernel ht).comp_sub_left x)
      ((continuous_euclideanHeatKernel t).comp (continuous_const.sub continuous_id))
      (fun z => by
        rw [abs_of_nonneg (euclideanHeatKernel_nonneg ht.le _)]
        exact euclideanHeatKernel_le_const ht _)
      ((foldr_coordinateDerivative_contDiff hg _).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_foldr_coordinateDerivative hcg _))
  rw [hsum]
  have hb : ∀ w : Fin K → Fin d, |heatSmooth t ((doubledList w).foldr coordinateDerivative g) x| ≤
      Real.sqrt (heatGradSq (2 * K) t g x) := fun w => by
    rw [hterm, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have h := sq_kconv_heatKernelDeriv_le_heatGradSq t g (doubledList w).reverse x
    rwa [List.length_reverse, length_doubledList] at h
  calc |∑ w : Fin K → Fin d, heatSmooth t ((doubledList w).foldr coordinateDerivative g) x|
      ≤ ∑ w : Fin K → Fin d, |heatSmooth t ((doubledList w).foldr coordinateDerivative g) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w : Fin K → Fin d, Real.sqrt (heatGradSq (2 * K) t g x) := Finset.sum_le_sum fun w _ => hb w
    _ = (d : ℝ) ^ K * Real.sqrt (heatGradSq (2 * K) t g x) := by
        simp [Finset.card_univ]

end QSH
