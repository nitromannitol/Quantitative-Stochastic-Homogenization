import QuantitativeStochasticHomogenization.AppD.HeatFlowLp
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests

/-!
# Appendix D: Proposition D.1 for non-integer orders

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Proposition D.1, (D.2): for `p ∈ (1, ∞)` and `α ∈ (0, ∞) \ ℕ`,
`‖u‖_{W^{-α,p}(ℝ^d)} ≤ C (∫_0^1 (t^{α/2} ‖u ∗ Φ(t, ·)‖_{L^p(ℝ^d)})^p dt/t)^{1/p}`.

This file defines the norm (B.3) of `W^{m+β,q}(ℝ^d)` on smooth functions (`fractionalSobolevNorm`)
and the norm (B.4) of `W^{-(m+β),p}(ℝ^d)` (`negativeFractionalSobolevNorm`), and proves the first
inequality of (D.2) for `u ∈ L^p(ℝ^d)` (`propositionD1_fractional`) along the book's proof (Step 1):
with `q = p/(p-1)`, a test `g` and `K = ⌊m/2⌋ + 1` (so that `2K > α`), the Taylor formula (D.21) of
the heat semigroup paired with `u` (`integral_mul_heatTaylor_ball`) gives the terms
`∫ u (Φ(1) ∗ Δ^j g)`, `j < K`, bounded by `‖u ∗ Φ(1, ·)‖_{L^p} ‖Δ^j g‖_{L^q}` and the contraction of
`L^p` norms by the heat flow (`enorm_integral_mul_heatSmooth_one_le`), and the remainder
`∫_0^1 s^{K-1} ∫ u (Φ(s) ∗ Δ^K g)`, bounded by
`|Φ(s) ∗ Δ^K g| ≤ d^K |∇^{2K} Φ(s, ·) ∗ g|` (`abs_heatSmooth_iterLaplacian_le`), Hölder's inequality
in space and in time (`lintegral_Ioc_mul_rpow_le`) and Proposition D.2 (`propositionD2_fractional`)
for `g ∈ W^{α,q}(ℝ^d)` (`isSobolevFamilyLp_of_smooth`).
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

/-! ## The first inequality of (D.2) -/

theorem euclideanSq_le_succ_mul_norm_sq (x : Vec d) : euclideanSq x ≤ (d + 1) * ‖x‖ ^ 2 := by
  have h : euclideanSq x ≤ d * ‖x‖ ^ 2 := by
    unfold euclideanSq dot
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at h
          nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
      _ = d * ‖x‖ ^ 2 := by simp
  nlinarith [sq_nonneg ‖x‖]

/-- `exp(-‖x‖²/16) ≤ (4π t)^{d/2} Φ(t, x)` for `t = 4(d + 1)`. -/
theorem exp_neg_norm_sq_le_euclideanHeatKernel (x : Vec d) :
    Real.exp (-(‖x‖ ^ 2) / 16) ≤
      (4 * Real.pi * (4 * (d + 1))) ^ ((d : ℝ) / 2) * euclideanHeatKernel (4 * (d + 1)) x := by
  have hpos : (0 : ℝ) < 4 * Real.pi * (4 * (d + 1)) := by positivity
  unfold euclideanHeatKernel
  rw [← mul_assoc, ← Real.rpow_add hpos, show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
    Real.rpow_zero, one_mul]
  refine Real.exp_le_exp.mpr ?_
  have h := euclideanSq_le_succ_mul_norm_sq x
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- A function in `L^p(ℝ^d)` times the Gaussian `exp(-‖x‖²/16)` is integrable. -/
theorem integrable_mul_exp_neg_norm_sq_of_memLp {p : ℝ} (hp : 1 ≤ p) {u : Vec d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) :
    Integrable (fun x => u x * Real.exp (-(‖x‖ ^ 2) / 16)) := by
  have ht : (0 : ℝ) < 4 * (d + 1) := by positivity
  have hc : (0 : ℝ) ≤ (4 * Real.pi * (4 * (d + 1))) ^ ((d : ℝ) / 2) := by positivity
  refine ((integrable_mul_euclideanHeatKernel_of_memLp ht hp hu).const_mul
    ((4 * Real.pi * (4 * (d + 1))) ^ ((d : ℝ) / 2))).norm.mono'
    (hu.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : Vec d =>
      Real.exp (-(‖x‖ ^ 2) / 16)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hc, abs_of_nonneg (euclideanHeatKernel_nonneg ht.le x)]
  calc |u x| * Real.exp (-(‖x‖ ^ 2) / 16)
      ≤ |u x| * ((4 * Real.pi * (4 * (d + 1))) ^ ((d : ℝ) / 2) *
          euclideanHeatKernel (4 * (d + 1)) x) :=
        mul_le_mul_of_nonneg_left (exp_neg_norm_sq_le_euclideanHeatKernel x) (abs_nonneg _)
    _ = _ := by ring

/-- The heat flow maps `L^p(ℝ^d)` into itself with norm at most one. -/
theorem memLp_heatSmooth_of_memLp {t : ℝ} (ht : 0 < t) {p : ℝ} (hp : 1 < p) {u : Vec d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) :
    MemLp (heatSmooth t u) (ENNReal.ofReal p) volume ∧
      eLpNorm (heatSmooth t u) (ENNReal.ofReal p) volume ≤ eLpNorm u (ENNReal.ofReal p) volume := by
  have h := memLp_kconv_of_memLp (K := euclideanHeatKernel t) hp (integrable_euclideanHeatKernel ht)
    (continuous_euclideanHeatKernel t).measurable hu
  rw [lintegral_enorm_euclideanHeatKernel ht, one_mul] at h
  exact h

/-- `‖Φ(1) ∗ u‖_{L^p} ≤ ‖Φ(t) ∗ u‖_{L^p}` for `t ∈ (0, 1)`. -/
theorem eLpNorm_heatSmooth_one_le {t : ℝ} (ht : 0 < t) (ht1 : t < 1) {p : ℝ} (hp : 1 < p)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) :
    eLpNorm (heatSmooth 1 u) (ENNReal.ofReal p) volume ≤
      eLpNorm (heatSmooth t u) (ENNReal.ofReal p) volume := by
  have h1 : heatSmooth 1 u = heatSmooth (1 - t) (heatSmooth t u) := by
    funext x
    rw [← heatSmooth_add_of_memLp (sub_pos.mpr ht1) ht hp.le hu x, sub_add_cancel]
  rw [h1]
  exact (memLp_heatSmooth_of_memLp (sub_pos.mpr ht1) hp (memLp_heatSmooth_of_memLp ht hp hu).1).2

/-- **Hölder's inequality** `|∫ f g| ≤ ‖f‖_{L^p} ‖g‖_{L^q}`. -/
theorem enorm_integral_mul_le_eLpNorm_mul {p q : ℝ} (hpq : p.HolderConjugate q) {f g : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    ‖∫ x, f x * g x‖ₑ ≤
      eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal q) volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hpq.nonneg, ENNReal.toReal_ofReal hpq.symm.nonneg]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hf.enorm hg.enorm
  simp only [Pi.mul_apply] at h
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp_rw [enorm_mul]
  exact h

/-- A derivative of order at most `m` is bounded in `L^q` by the norm of `W^{m+β,q}(ℝ^d)`. -/
theorem eLpNorm_foldr_le_fractionalSobolevNorm {m : ℕ} {β q : ℝ} (g : Vec d → ℝ)
    (l : List (Fin d)) (hl : l.length ≤ m) :
    eLpNorm (l.foldr coordinateDerivative g) (ENNReal.ofReal q) volume ≤
      fractionalSobolevNorm m β q g := by
  unfold fractionalSobolevNorm
  refine le_add_right ?_
  calc eLpNorm (l.foldr coordinateDerivative g) (ENNReal.ofReal q) volume
      = eLpNorm ((List.ofFn l.get).foldr coordinateDerivative g) (ENNReal.ofReal q) volume := by
        rw [List.ofFn_get]
    _ ≤ ∑ w : Fin l.length → Fin d,
          eLpNorm ((List.ofFn w).foldr coordinateDerivative g) (ENNReal.ofReal q) volume :=
        Finset.single_le_sum (f := fun w : Fin l.length → Fin d =>
          eLpNorm ((List.ofFn w).foldr coordinateDerivative g) (ENNReal.ofReal q) volume)
          (fun w _ => zero_le) (Finset.mem_univ l.get)
    _ ≤ ∑ j ∈ Finset.range (m + 1), ∑ w : Fin j → Fin d,
          eLpNorm ((List.ofFn w).foldr coordinateDerivative g) (ENNReal.ofReal q) volume :=
        Finset.single_le_sum (f := fun j => ∑ w : Fin j → Fin d,
          eLpNorm ((List.ofFn w).foldr coordinateDerivative g) (ENNReal.ofReal q) volume)
          (fun j _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

/-- `‖Δ^j g‖_{L^q} ≤ d^j ‖g‖_{W^{m+β,q}}` for `2j ≤ m`. -/
theorem eLpNorm_iterLaplacian_le {m : ℕ} (β : ℝ) {q : ℝ} (hq : 1 ≤ q) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) {j : ℕ} (hj : 2 * j ≤ m) :
    eLpNorm (iterLaplacian j g) (ENNReal.ofReal q) volume ≤
      (d : ℝ≥0∞) ^ j * fractionalSobolevNorm m β q g := by
  have hsum : iterLaplacian j g =
      ∑ w : Fin j → Fin d, (doubledList w).foldr coordinateDerivative g := by
    rw [iterLaplacian_eq_sum hg j]
    funext x
    rw [Finset.sum_apply]
  rw [hsum]
  calc eLpNorm (∑ w : Fin j → Fin d, (doubledList w).foldr coordinateDerivative g)
        (ENNReal.ofReal q) volume
      ≤ ∑ w : Fin j → Fin d,
          eLpNorm ((doubledList w).foldr coordinateDerivative g) (ENNReal.ofReal q) volume :=
        eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hq)
    _ ≤ ∑ _w : Fin j → Fin d, fractionalSobolevNorm m β q g :=
        Finset.sum_le_sum fun w _ => eLpNorm_foldr_le_fractionalSobolevNorm g _
          (by rw [length_doubledList]; exact hj)
    _ = (d : ℝ≥0∞) ^ j * fractionalSobolevNorm m β q g := by
        simp [Finset.card_univ]

/-- **The step `τ ∈ (1/2, 1)`**: `‖Φ(1) ∗ u‖_{L^p} ≤ C (∫_0^1 t^{a} ‖Φ(t) ∗ u‖^p_{L^p} dt/t)^{1/p}`,
from the contraction of `L^p` norms by the heat flow. -/
theorem eLpNorm_heatSmooth_one_le_lintegral {p : ℝ} (hp : 1 < p) {u : Vec d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) {a : ℝ} (ha : 0 < a) :
    eLpNorm (heatSmooth 1 u) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (2 ^ (a + 1)) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) *
        ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hp0' : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have heq : ∀ t : ℝ, 0 < t → eLpNorm (heatSmooth t u) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p) ^ (1 / p) := fun t ht => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0' ENNReal.ofReal_ne_top
      (memLp_heatSmooth_of_memLp ht hp hu).1.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  have hmono : ∀ t ∈ Ioo (1 / 2 : ℝ) 1,
      ∫⁻ x, ‖heatSmooth 1 u x‖ₑ ^ p ≤ ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h := eLpNorm_heatSmooth_one_le ht0 ht.2 hp hu
    rw [heq 1 one_pos, heq t ht0] at h
    exact (ENNReal.rpow_le_rpow_iff (by positivity)).mp h
  have hlow : ENNReal.ofReal ((1 / 2) ^ a * (1 / 2)) * ∫⁻ x, ‖heatSmooth 1 u x‖ₑ ^ p ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) * ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p := by
    calc ENNReal.ofReal ((1 / 2) ^ a * (1 / 2)) * ∫⁻ x, ‖heatSmooth 1 u x‖ₑ ^ p
        = ∫⁻ _t in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal ((1 / 2) ^ a) *
            ∫⁻ x, ‖heatSmooth 1 u x‖ₑ ^ p := by
          rw [setLIntegral_const, Real.volume_Ioo, ENNReal.ofReal_mul (by positivity),
            show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
          ring
      _ ≤ ∫⁻ t in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal (t ^ a / t) *
            ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht =>
            mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (hmono t ht)
          have ht0 : 0 < t := by linarith [ht.1]
          calc (1 / 2 : ℝ) ^ a ≤ t ^ a := Real.rpow_le_rpow (by norm_num) ht.1.le ha.le
            _ ≤ t ^ a / t := le_div_self (Real.rpow_nonneg ht0.le a) ht0 ht.2.le
      _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioc_self.trans
          (Ioc_subset_Ioc_left (by norm_num)))
  have hc : ENNReal.ofReal (2 ^ (a + 1)) * ENNReal.ofReal ((1 / 2) ^ a * (1 / 2)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
    congr 1
    have h2a : (0 : ℝ) < 2 ^ a := by positivity
    rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), Real.div_rpow (by norm_num) (by norm_num),
      Real.one_rpow]
    field_simp
  rw [heq 1 one_pos]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc ∫⁻ x, ‖heatSmooth 1 u x‖ₑ ^ p
      = ENNReal.ofReal (2 ^ (a + 1)) * (ENNReal.ofReal ((1 / 2) ^ a * (1 / 2)) *
          ∫⁻ x, ‖heatSmooth 1 u x‖ₑ ^ p) := by
        rw [← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hlow

/-- **The terms `ρ^{(j)}(1)` of (D.21)**: for `2j ≤ m` and `‖g‖_{W^{m+β,q}} ≤ 1`,
`|∫ u (Φ(1) ∗ Δ^j g)| ≤ C (∫_0^1 t^{a} ‖Φ(t) ∗ u‖^p_{L^p} dt/t)^{1/p}`. -/
theorem enorm_integral_mul_heatSmooth_one_le {m : ℕ} {β p q : ℝ} (hpq : p.HolderConjugate q)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (hgn : fractionalSobolevNorm m β q g ≤ 1)
    {j : ℕ} (hj : 2 * j ≤ m) {a : ℝ} (ha : 0 < a) :
    ‖∫ x, u x * heatSmooth 1 (iterLaplacian j g) x‖ₑ ≤
      ENNReal.ofReal ((d : ℝ) ^ j * (2 ^ (a + 1)) ^ (1 / p)) *
        (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) *
          ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p) ^ (1 / p) := by
  have hp := hpq.lt
  have hsm := iterLaplacian_smooth hg hcg j
  rw [integral_mul_heatSmooth_comm one_pos hu.aestronglyMeasurable
    (integrable_mul_euclideanHeatKernel_of_memLp (by norm_num) hp.le hu) hsm.1.continuous hsm.2]
  calc ‖∫ y, heatSmooth 1 u y * iterLaplacian j g y‖ₑ
      ≤ eLpNorm (heatSmooth 1 u) (ENNReal.ofReal p) volume *
          eLpNorm (iterLaplacian j g) (ENNReal.ofReal q) volume :=
        enorm_integral_mul_le_eLpNorm_mul hpq
          (memLp_heatSmooth_of_memLp one_pos hp hu).1.aestronglyMeasurable
          hsm.1.continuous.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (2 ^ (a + 1)) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) *
          ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p) ^ (1 / p) * ((d : ℝ≥0∞) ^ j * 1) :=
        mul_le_mul' (eLpNorm_heatSmooth_one_le_lintegral hp hu ha)
          ((eLpNorm_iterLaplacian_le β hpq.symm.lt.le hg hj).trans (mul_le_mul' le_rfl hgn))
    _ = _ := by
        rw [mul_one, ENNReal.mul_rpow_of_nonneg _ _ hpq.one_div_nonneg,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hpq.one_div_nonneg,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg d),
          ENNReal.ofReal_natCast]
        ring

/-- **The remainder of (D.21) at time `s`**:
`|∫ u (Φ(s) ∗ Δ^K g)| ≤ d^K ‖Φ(s/2) ∗ u‖_{L^p} ‖∇^{2K} Φ(s/2, ·) ∗ g‖_{L^q}`. -/
theorem enorm_integral_mul_heatSmooth_iterLaplacian_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {u : Vec d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) {s : ℝ} (hs : 0 < s) (K : ℕ) :
    ‖∫ x, u x * heatSmooth s (iterLaplacian K g) x‖ₑ ≤
      ENNReal.ofReal ((d : ℝ) ^ K) * (∫⁻ x, ‖heatSmooth (s / 2) u x‖ₑ ^ p) ^ (1 / p) *
        (∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * K) (s / 2) g x)) ^ q) ^ (1 / q) := by
  have hp : 1 < p := hpq.lt
  have hs2 : 0 < s / 2 := half_pos hs
  have hsm := iterLaplacian_smooth hg hcg K
  rw [integral_mul_heatSmooth_split hs hp hu hsm.1.continuous hsm.2]
  have hA : AEMeasurable (fun x => ‖heatSmooth (s / 2) u x‖ₑ) volume :=
    (memLp_heatSmooth_of_memLp hs2 hp hu).1.aestronglyMeasurable.enorm
  obtain ⟨H, hHm, hH⟩ := exists_measurable_heatGradSq (2 * K) hg.continuous.aestronglyMeasurable
  have hB : AEMeasurable
      (fun x => ENNReal.ofReal (Real.sqrt (heatGradSq (2 * K) (s / 2) g x))) volume := by
    refine ((hHm.comp (measurable_prodMk_left (x := s / 2))).sqrt.ennreal_ofReal).aemeasurable.congr
      (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, hH (s / 2) hs2 x]
  have hH2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hA hB
  simp only [Pi.mul_apply] at hH2
  calc ‖∫ x, heatSmooth (s / 2) u x * heatSmooth (s / 2) (iterLaplacian K g) x‖ₑ
      ≤ ∫⁻ x, ‖heatSmooth (s / 2) u x‖ₑ * ‖heatSmooth (s / 2) (iterLaplacian K g) x‖ₑ := by
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        simp_rw [enorm_mul]
    _ ≤ ∫⁻ x, ‖heatSmooth (s / 2) u x‖ₑ * (ENNReal.ofReal ((d : ℝ) ^ K) *
          ENNReal.ofReal (Real.sqrt (heatGradSq (2 * K) (s / 2) g x))) := by
        refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (abs_heatSmooth_iterLaplacian_le hg hcg hs2 K x)
    _ = ENNReal.ofReal ((d : ℝ) ^ K) * ∫⁻ x, ‖heatSmooth (s / 2) u x‖ₑ *
          ENNReal.ofReal (Real.sqrt (heatGradSq (2 * K) (s / 2) g x)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        ring
    _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl hH2

/-- The change of variables `t = 2 s` on `(0, 1]`. -/
theorem lintegral_Ioc_comp_half (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioc (0 : ℝ) 1, f (t / 2) = 2 * ∫⁻ s in Ioc (0 : ℝ) (1 / 2), f s := by
  have h := lintegral_Ioi_comp_half ((Ioc (0 : ℝ) (1 / 2)).indicator f)
  have h1 : ∀ t : ℝ, (Ioc (0 : ℝ) (1 / 2)).indicator f (t / 2) =
      (Ioc (0 : ℝ) 1).indicator (fun t => f (t / 2)) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · have ht2 : t / 2 ∈ Ioc (0 : ℝ) (1 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [indicator_of_mem ht2, indicator_of_mem ht]
    · have ht2 : t / 2 ∉ Ioc (0 : ℝ) (1 / 2) := fun h =>
        ht ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [indicator_of_notMem ht2, indicator_of_notMem ht]
  simp only [h1] at h
  rw [setLIntegral_indicator measurableSet_Ioc, setLIntegral_indicator measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self, inter_eq_left.mpr Ioc_subset_Ioi_self] at h
  exact h

theorem ofReal_two_mul_rpow_div {r : ℝ} (hr : 0 < r) (c : ℝ) :
    ENNReal.ofReal ((2 * r) ^ c / (2 * r)) =
      ENNReal.ofReal (2 ^ c / 2) * ENNReal.ofReal (r ^ c / r) := by
  rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by norm_num) hr.le]
  congr 1
  exact mul_div_mul_comm _ _ _ _

theorem two_mul_ofReal_rpow_div (c : ℝ) :
    2 * ENNReal.ofReal (2 ^ c / 2) = ENNReal.ofReal (2 ^ c) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- `∫_0^1 s^c A(s/2) ds/s ≤ 2^c ∫_0^1 t^c A(t) dt/t`. -/
theorem lintegral_Ioc_weight_comp_half_le (c : ℝ) (A : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ c / s) * A (s / 2) ≤
      ENNReal.ofReal (2 ^ c) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ c / t) * A t := by
  have h2 : ∀ t : ℝ, 2 * (t / 2) = t := fun t => by ring
  have hc := lintegral_Ioc_comp_half (fun r => ENNReal.ofReal ((2 * r) ^ c / (2 * r)) * A r)
  simp only [h2] at hc
  rw [hc]
  calc 2 * ∫⁻ r in Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal ((2 * r) ^ c / (2 * r)) * A r
      ≤ 2 * ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal ((2 * r) ^ c / (2 * r)) * A r :=
        mul_le_mul' le_rfl (lintegral_mono_set (Ioc_subset_Ioc_right (by norm_num)))
    _ = 2 * ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (2 ^ c / 2) * (ENNReal.ofReal (r ^ c / r) * A r) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        rw [ofReal_two_mul_rpow_div hr.1, mul_assoc]
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, two_mul_ofReal_rpow_div]

/-- `∫_0^∞ s^c B(s/2) ds/s = 2^c ∫_0^∞ t^c B(t) dt/t`. -/
theorem lintegral_Ioi_weight_comp_half (c : ℝ) (B : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ c / s) * B (s / 2) =
      ENNReal.ofReal (2 ^ c) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ c / t) * B t := by
  have h2 : ∀ t : ℝ, 2 * (t / 2) = t := fun t => by ring
  have hc := lintegral_Ioi_comp_half (fun r => ENNReal.ofReal ((2 * r) ^ c / (2 * r)) * B r)
  simp only [h2] at hc
  rw [hc]
  calc 2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((2 * r) ^ c / (2 * r)) * B r
      = 2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 ^ c / 2) * (ENNReal.ofReal (r ^ c / r) * B r) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
        rw [ofReal_two_mul_rpow_div hr, mul_assoc]
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, two_mul_ofReal_rpow_div]

/-- **Hölder's inequality in time, (D.23)**: for `a/p + b/q = n + 1`,
`∫_0^1 s^n A(s/2)^{1/p} B(s/2)^{1/q} ds ≤ (2^a ∫_0^1 t^a A(t) dt/t)^{1/p} (2^b ∫_0^∞ t^b B(t) dt/t)^{1/q}`. -/
theorem lintegral_Ioc_mul_rpow_le {p q : ℝ} (hpq : p.HolderConjugate q) {a b : ℝ} {n : ℕ}
    (hab : a / p + b / q = n + 1) {A B : ℝ → ℝ≥0∞}
    (hA : AEMeasurable (fun s => A (s / 2)) (volume.restrict (Ioc (0 : ℝ) 1)))
    (hB : AEMeasurable (fun s => B (s / 2)) (volume.restrict (Ioc (0 : ℝ) 1))) :
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ n) * A (s / 2) ^ (1 / p) * B (s / 2) ^ (1 / q) ≤
      (ENNReal.ofReal (2 ^ a) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) * A t) ^ (1 / p) *
        (ENNReal.ofReal (2 ^ b) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ b / t) * B t) ^
          (1 / q) := by
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have hW : ∀ c : ℝ, Measurable (fun s : ℝ => ENNReal.ofReal (s ^ c / s)) := fun c =>
    ((measurable_id.pow_const c).div measurable_id).ennreal_ofReal
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (s ^ n) * A (s / 2) ^ (1 / p) * B (s / 2) ^ (1 / q) =
        (ENNReal.ofReal (s ^ a / s) * A (s / 2)) ^ (1 / p) *
          (ENNReal.ofReal (s ^ b / s) * B (s / 2)) ^ (1 / q) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hreal : s ^ n = (s ^ a / s) ^ (1 / p) * (s ^ b / s) ^ (1 / q) := by
      rw [← Real.rpow_sub_one hs0.ne', ← Real.rpow_sub_one hs0.ne', ← Real.rpow_mul hs0.le,
        ← Real.rpow_mul hs0.le, ← Real.rpow_add hs0, ← Real.rpow_natCast]
      congr 1
      have h1 := hpq.inv_add_inv_eq_one
      calc (n : ℝ) = (a / p + b / q) - (p⁻¹ + q⁻¹) := by rw [hab, h1]; ring
        _ = (a - 1) * (1 / p) + (b - 1) * (1 / q) := by ring
    have ha0 : 0 ≤ s ^ a / s := div_nonneg (Real.rpow_nonneg hs0.le a) hs0.le
    have hb0 : 0 ≤ s ^ b / s := div_nonneg (Real.rpow_nonneg hs0.le b) hs0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.one_div_nonneg,
      ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.one_div_nonneg,
      ENNReal.ofReal_rpow_of_nonneg ha0 hpq.one_div_nonneg,
      ENNReal.ofReal_rpow_of_nonneg hb0 hpq.symm.one_div_nonneg, hreal,
      ENNReal.ofReal_mul (Real.rpow_nonneg ha0 _)]
    ring
  have hf1 : AEMeasurable (fun s => (ENNReal.ofReal (s ^ a / s) * A (s / 2)) ^ (1 / p))
      (volume.restrict (Ioc (0 : ℝ) 1)) := (((hW a).aemeasurable).mul hA).pow_const _
  have hf2 : AEMeasurable (fun s => (ENNReal.ofReal (s ^ b / s) * B (s / 2)) ^ (1 / q))
      (volume.restrict (Ioc (0 : ℝ) 1)) := (((hW b).aemeasurable).mul hB).pow_const _
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0 : ℝ) 1)) hpq hf1 hf2
  simp only [Pi.mul_apply] at hH
  have e1 : ∀ s : ℝ, ((ENNReal.ofReal (s ^ a / s) * A (s / 2)) ^ (1 / p)) ^ p =
      ENNReal.ofReal (s ^ a / s) * A (s / 2) := fun s => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have e2 : ∀ s : ℝ, ((ENNReal.ofReal (s ^ b / s) * B (s / 2)) ^ (1 / q)) ^ q =
      ENNReal.ofReal (s ^ b / s) * B (s / 2) := fun s => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  simp only [e1, e2] at hH
  calc ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ n) * A (s / 2) ^ (1 / p) * B (s / 2) ^ (1 / q)
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal (s ^ a / s) * A (s / 2)) ^ (1 / p) *
          (ENNReal.ofReal (s ^ b / s) * B (s / 2)) ^ (1 / q) :=
        setLIntegral_mono' measurableSet_Ioc fun s hs => (hpt s hs).le
    _ ≤ _ := hH
    _ ≤ _ := mul_le_mul'
        (ENNReal.rpow_le_rpow (lintegral_Ioc_weight_comp_half_le a A) hpq.one_div_nonneg)
        (ENNReal.rpow_le_rpow ((lintegral_mono_set Ioc_subset_Ioi_self).trans
          (lintegral_Ioi_weight_comp_half b B).le) hpq.symm.one_div_nonneg)

/-- **Proposition D.1, the first inequality of (D.2)**: for `p ∈ (1, ∞)` and `α = m + β` with
`m ∈ ℕ` and `β ∈ (0, 1)`, there is `C(α, p, d)` such that, for every `u ∈ L^p(ℝ^d)`,
`‖u‖_{W^{-α,p}(ℝ^d)} ≤ C (∫_0^1 (t^{α/2} ‖u ∗ Φ(t, ·)‖_{L^p(ℝ^d)})^p dt/t)^{1/p}`. -/
theorem propositionD1_fractional (m : ℕ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {p : ℝ}
    (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Vec d → ℝ, MemLp u (ENNReal.ofReal p) volume →
      negativeFractionalSobolevNorm m β p u ≤ ENNReal.ofReal C *
        (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (p * (m + β) / 2) / t) *
          ∫⁻ x, ‖heatSmooth t u x‖ₑ ^ p) ^ (1 / p) := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  set q := p / (p - 1) with hq
  have hq1 : 1 < q := hpq.symm.lt
  have hp0 : 0 < p := hpq.pos
  set n := m / 2 with hn
  have hmn : m < 2 * (n + 1) := by omega
  obtain ⟨C₂, hC₂, hD2⟩ := propositionD2_fractional (d := d) m hβ hβ1 hmn hq1
  have ha : 0 < p * (m + β) / 2 := by positivity
  set a := p * (m + β) / 2 with ha_def
  set b := q * (((2 * (n + 1) : ℕ) : ℝ) - (m + β)) / 2 with hb_def
  have hab : a / p + b / q = n + 1 := by
    rw [ha_def, hb_def, div_add_div _ _ hp0.ne' hpq.symm.ne_zero,
      div_eq_iff (mul_ne_zero hp0.ne' hpq.symm.ne_zero)]
    push_cast
    ring
  set C₁ : ℝ := ∑ j ∈ Finset.range (n + 1),
    1 / (j ! : ℝ) * ((d : ℝ) ^ j * (2 ^ (a + 1)) ^ (1 / p)) with hC₁_def
  set C₃ : ℝ := 1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1) * (2 ^ a) ^ (1 / p) * (2 ^ b) ^ (1 / q) * C₂
    with hC₃_def
  have hC₁ : 0 ≤ C₁ := by
    rw [hC₁_def]
    exact Finset.sum_nonneg fun j _ => by positivity
  have hC₃ : 0 ≤ C₃ := by
    rw [hC₃_def]
    positivity
  refine ⟨C₁ + C₃, add_nonneg hC₁ hC₃, fun u hu => ?_⟩
  set u' := hu.aestronglyMeasurable.mk u with hu'
  have hu'm : Measurable u' := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have huu' : u =ᵐ[volume] u' := hu.aestronglyMeasurable.ae_eq_mk
  have hu'L : MemLp u' (ENNReal.ofReal p) volume := hu.ae_eq huu'
  have hheat : ∀ t, heatSmooth t u = heatSmooth t u' := fun t => by
    funext x
    rw [heatSmooth_eq_kconv, heatSmooth_eq_kconv, kconv_apply, kconv_apply]
    refine integral_congr_ae ?_
    filter_upwards [huu'] with y hy
    rw [hy]
  simp only [hheat]
  unfold negativeFractionalSobolevNorm
  refine iSup_le ?_
  rintro ⟨g, hg, hcg, hgn⟩
  dsimp only
  rw [show ∫ x, u x * g x = ∫ x, u' x * g x from
    integral_congr_ae (huu'.mono fun x hx => by simp only [hx]), ← Real.enorm_eq_ofReal_abs]
  obtain ⟨R, hR⟩ := hcg.isCompact.isBounded.exists_norm_le
  have hsupp : ∀ z ∈ tsupport g, ‖z‖ ≤ max R 0 := fun z hz => (hR z hz).trans (le_max_left _ _)
  rw [integral_mul_heatTaylor_ball (le_max_right R 0) hu'L.aestronglyMeasurable
    (integrable_mul_exp_neg_norm_sq_of_memLp hp.le hu'L) hg hcg hsupp n]
  set P := (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) *
    ∫⁻ x, ‖heatSmooth t u' x‖ₑ ^ p) ^ (1 / p) with hP
  have hT : ∀ j ∈ Finset.range (n + 1),
      ‖(-1) ^ j / (j ! : ℝ) * ∫ x, u' x * heatSmooth 1 (iterLaplacian j g) x‖ₑ ≤
        ENNReal.ofReal (1 / (j ! : ℝ) * ((d : ℝ) ^ j * (2 ^ (a + 1)) ^ (1 / p))) * P := by
    intro j hj
    have h2j : 2 * j ≤ m := by rw [Finset.mem_range] at hj; omega
    have hc : ‖(-1) ^ j / (j ! : ℝ)‖ₑ = ENNReal.ofReal (1 / (j ! : ℝ)) := by
      rw [Real.enorm_eq_ofReal_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    calc ‖(-1) ^ j / (j ! : ℝ) * ∫ x, u' x * heatSmooth 1 (iterLaplacian j g) x‖ₑ
        = ‖(-1) ^ j / (j ! : ℝ)‖ₑ * ‖∫ x, u' x * heatSmooth 1 (iterLaplacian j g) x‖ₑ :=
          enorm_mul _ _
      _ ≤ ENNReal.ofReal (1 / (j ! : ℝ)) *
          (ENNReal.ofReal ((d : ℝ) ^ j * (2 ^ (a + 1)) ^ (1 / p)) * P) :=
          mul_le_mul' hc.le (enorm_integral_mul_heatSmooth_one_le hpq hu'L hg hcg hgn h2j ha)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (j ! : ℝ)), mul_assoc]
  have hRem : ‖∫ s in (0 : ℝ)..1, (-s) ^ n / (n ! : ℝ) *
      ∫ x, u' x * heatSmooth s (iterLaplacian (n + 1) g) x‖ₑ ≤ ENNReal.ofReal C₃ * P := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    obtain ⟨H, hHm, hH⟩ :=
      exists_measurable_heatGradSq (2 * (n + 1)) hg.continuous.aestronglyMeasurable
    have hAm : AEMeasurable (fun s => ∫⁻ x, ‖heatSmooth (s / 2) u' x‖ₑ ^ p)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have hF : Measurable (fun z : ℝ × Vec d => ‖heatSmooth z.1 u' z.2‖ₑ ^ p) :=
        ((stronglyMeasurable_heatSmooth_uncurry hu'm).measurable.comp measurable_swap).enorm.pow_const p
      exact (hF.lintegral_prod_right'.comp (measurable_id.div_const 2)).aemeasurable
    have hBm : AEMeasurable (fun s => ∫⁻ x,
        ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) (s / 2) g x)) ^ q)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have hF : Measurable (fun z : ℝ × Vec d => ENNReal.ofReal (Real.sqrt (H z)) ^ q) :=
        (hHm.sqrt.ennreal_ofReal).pow_const q
      refine ((Measurable.lintegral_prod_right' (ν := volume) hF).comp
        (measurable_id.div_const 2)).aemeasurable.congr
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_))
      simp only [Function.comp_apply, id]
      refine lintegral_congr fun x => ?_
      rw [hH (s / 2) (half_pos hs.1) x]
    have hL2 := lintegral_Ioc_mul_rpow_le hpq hab
      (A := fun r => ∫⁻ x, ‖heatSmooth r u' x‖ₑ ^ p)
      (B := fun r => ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) r g x)) ^ q) hAm hBm
    have hD : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ b / t) *
        ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) t g x)) ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C₂ := by
      refine (hD2 g _ (isSobolevFamilyLp_of_smooth q m hg hcg)).trans ?_
      calc ENNReal.ofReal C₂ * fractionalSobolevSeminorm m β q
            (fun l => l.foldr coordinateDerivative g)
          ≤ ENNReal.ofReal C₂ * 1 := mul_le_mul' le_rfl ((le_add_left le_rfl).trans hgn)
        _ = _ := mul_one _
    have e1 : (0 : ℝ) ≤ 1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1) := by positivity
    have e2 : (0 : ℝ) ≤ 1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1) * (2 ^ a) ^ (1 / p) := by positivity
    have e3 : (0 : ℝ) ≤ 1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1) * (2 ^ a) ^ (1 / p) *
        (2 ^ b) ^ (1 / q) := by positivity
    calc ∫⁻ s in Ioc (0 : ℝ) 1, ‖(-s) ^ n / (n ! : ℝ) *
          ∫ x, u' x * heatSmooth s (iterLaplacian (n + 1) g) x‖ₑ
        ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1)) *
            (ENNReal.ofReal (s ^ n) * (∫⁻ x, ‖heatSmooth (s / 2) u' x‖ₑ ^ p) ^ (1 / p) *
              (∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) (s / 2) g x)) ^ q) ^
                (1 / q)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          have hc : ‖(-s) ^ n / (n ! : ℝ)‖ₑ =
              ENNReal.ofReal (s ^ n) * ENNReal.ofReal (1 / (n ! : ℝ)) := by
            rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (pow_nonneg hs.1.le n)]
            congr 1
            rw [abs_div, abs_pow, abs_neg, abs_of_pos hs.1, Nat.abs_cast, mul_one_div]
          rw [enorm_mul, hc]
          calc ENNReal.ofReal (s ^ n) * ENNReal.ofReal (1 / (n ! : ℝ)) *
                ‖∫ x, u' x * heatSmooth s (iterLaplacian (n + 1) g) x‖ₑ
              ≤ ENNReal.ofReal (s ^ n) * ENNReal.ofReal (1 / (n ! : ℝ)) *
                  (ENNReal.ofReal ((d : ℝ) ^ (n + 1)) *
                    (∫⁻ x, ‖heatSmooth (s / 2) u' x‖ₑ ^ p) ^ (1 / p) *
                    (∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) (s / 2) g x)) ^ q) ^
                      (1 / q)) :=
                mul_le_mul' le_rfl
                  (enorm_integral_mul_heatSmooth_iterLaplacian_le hpq hu'L hg hcg hs.1 (n + 1))
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (n ! : ℝ))]
                ring
      _ = ENNReal.ofReal (1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1)) *
            ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ n) *
              (∫⁻ x, ‖heatSmooth (s / 2) u' x‖ₑ ^ p) ^ (1 / p) *
              (∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) (s / 2) g x)) ^ q) ^
                (1 / q) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1)) *
            ((ENNReal.ofReal (2 ^ a) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ a / t) *
              ∫⁻ x, ‖heatSmooth t u' x‖ₑ ^ p) ^ (1 / p) *
            (ENNReal.ofReal (2 ^ b) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ b / t) *
              ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (2 * (n + 1)) t g x)) ^ q) ^ (1 / q)) :=
          mul_le_mul' le_rfl hL2
      _ ≤ ENNReal.ofReal (1 / (n ! : ℝ) * (d : ℝ) ^ (n + 1)) *
            ((ENNReal.ofReal ((2 ^ a) ^ (1 / p)) * P) *
              (ENNReal.ofReal ((2 ^ b) ^ (1 / q)) * ENNReal.ofReal C₂)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.one_div_nonneg,
            ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.one_div_nonneg,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hpq.one_div_nonneg,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hpq.symm.one_div_nonneg]
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hD))
      _ = ENNReal.ofReal C₃ * P := by
          rw [hC₃_def, ENNReal.ofReal_mul e3, ENNReal.ofReal_mul e2, ENNReal.ofReal_mul e1]
          ring
  refine (enorm_sub_le).trans ?_
  refine (add_le_add (enorm_sum_le _ _) le_rfl).trans ?_
  refine (add_le_add (Finset.sum_le_sum hT) hRem).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity),
    ENNReal.ofReal_add hC₁ hC₃, add_mul, hC₁_def]

end QSH
