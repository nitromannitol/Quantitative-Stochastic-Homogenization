import QuantitativeStochasticHomogenization.AppD.LemmaD3
import QuantitativeStochasticHomogenization.AppD.HeatKernelMajorant

/-!
# Appendix D: Proposition D.2 for fractional orders

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Proposition D.2, (D.4): for `α ∈ (0, ∞) \ ℕ`, `k ∈ ℕ ∩ (α, ∞)` and `q ∈ (1, ∞)`,
`(∫_0^∞ (t^{(k-α)/2} ‖∇^k Φ(t, ·) ∗ u‖_{L^q(ℝ^d)})^q dt/t)^{1/q} ≤ C [u]_{W^{α,q}(ℝ^d)}`.

This file proves it as `propositionD2_fractional`, with the seminorm (B.2)–(B.3) on `ℝ^d`
(`fractionalSeminorm`, `fractionalSobolevSeminorm`) and `u ∈ W^{m,q}(ℝ^d)` given with its weak
derivatives (`IsSobolevFamilyLp`), `α = m + β`, `β ∈ (0, 1)`. The case `α ∈ (0, 1)`
(`propositionD2_fractional_lt_one`) is the book's estimate (D.7), proved for every order `k ≥ 1`
at once:
* `∂^w Φ(t, ·)` has integral zero (`integral_heatKernelDeriv_ofFn_eq_zero`), so
  `∂^w Φ(t, ·) ∗ u (x) = ∫ ∂^w Φ(t, x - y) (u(y) - u(x)) dy`, and the Gaussian majorant
  `|∂^w Φ(t, z)| ≤ C (2t)^{-k/2} Φ(2t, z)` gives the pointwise bound `ofReal_sqrt_heatGradSq_le`;
* Jensen's inequality for the probability density `Φ(2t, x - ·)` (`lintegral_mul_rpow_le`);
* Tonelli's theorem and the time integral
  `∫_0^∞ t^{-a-1} Φ(2t, z) dt = K |z|^{-d-2a}` (`lintegral_heatKernel_two_mul_eq`, a Gamma
  integral) give `∫∫ |u(x) - u(y)|^q / |x - y|^{d+αq}` (`lintegral_heatGradSq_le_fractional`).
The book reduces to `k = 1` by the semigroup property and Young's inequality; the Gaussian majorant
handles every `k` directly. The constant depends on `q`, see the notes on (D.4) in
CORRESPONDENCE.md. For `m ≥ 1` the `m` derivatives are moved from the heat kernel onto `u` by the weak derivative
identity against smooth functions with integrable products
(`integral_mul_coordinateDerivative_of_hasWeakPartialDerivative_of_integrable`,
`kconv_heatKernelDeriv_append_eq_of_memLp`), so that
`|∇^{m+n} Φ(t, ·) ∗ u|² = ∑_{|w| = m} |∇^n Φ(t, ·) ∗ ∂_w u|²` (`heatGradSq_add_eq_of_memLp`), as the
book does when it considers `∇^{k-1} u` in place of `u`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `∫_0^∞ t^{-c-1} e^{-b/t} dt = Γ(c) b^{-c}`, with the integrand integrable. -/
theorem integrableOn_rpow_neg_mul_exp_neg_div {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (-c - 1) * Real.exp (-(b / t))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ (-c - 1) * Real.exp (-(b / t)) = Real.Gamma c * b ^ (-c) := by
  set g : ℝ → ℝ := fun y => y ^ (c - 1) * Real.exp (-(b * y)) with hg
  have heq : EqOn (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ)))
      (fun t : ℝ => t ^ (-c - 1) * Real.exp (-(b / t))) (Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    simp only [hg, smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [Real.rpow_neg_one, ← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le, div_eq_mul_inv b x,
      ← Real.rpow_neg_one x, ← mul_assoc, ← Real.rpow_add hx0]
    congr 2
    ring
  have hgi : IntegrableOn g (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := c - 1) (b := b)
      (by linarith) one_pos hb
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hg, Real.rpow_one, neg_mul]
  have hint := (integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)).mpr hgi
  refine ⟨hint.congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_comp_rpow_Ioi g (by norm_num),
    hg, Real.integral_rpow_mul_exp_neg_mul_Ioi hc hb, Real.div_rpow zero_le_one hb.le,
    Real.one_rpow, Real.rpow_neg hb.le]
  ring

/-- Jensen's inequality for a weighted lower integral: `(∫ w f)^q ≤ (∫ w)^{q-1} ∫ w f^q`. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ}
    (hq : 1 < q) {w f : α → ℝ≥0∞} (hw : AEMeasurable w μ) (hf : AEMeasurable f μ) :
    (∫⁻ a, w a * f a ∂μ) ^ q ≤ (∫⁻ a, w a ∂μ) ^ (q - 1) * ∫⁻ a, w a * f a ^ q ∂μ := by
  have hq0 : 0 < q := by linarith
  set q' := q / (q - 1) with hq'
  have hq'0 : 0 < q' := div_pos hq0 (by linarith)
  have hpq : q'.HolderConjugate q := (Real.HolderConjugate.conjExponent hq).symm
  have hsplit : ∀ a, w a * f a = w a ^ (1 / q') * (w a ^ (1 / q) * f a) := fun a => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (one_div_nonneg.mpr hq'0.le)
      (one_div_nonneg.mpr hq0.le)]
    rw [show 1 / q' + 1 / q = 1 by rw [hq']; field_simp; ring, ENNReal.rpow_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hw.pow_const (1 / q'))
    ((hw.pow_const (1 / q)).mul hf)
  simp only [Pi.mul_apply] at hH
  simp_rw [← hsplit] at hH
  have e1 : ∀ a, (w a ^ (1 / q')) ^ q' = w a := fun a => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq'0.ne', ENNReal.rpow_one]
  have e2 : ∀ a, (w a ^ (1 / q) * f a) ^ q = w a * f a ^ q := fun a => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne',
      ENNReal.rpow_one]
  simp_rw [e1, e2] at hH
  calc (∫⁻ a, w a * f a ∂μ) ^ q
      ≤ ((∫⁻ a, w a ∂μ) ^ (1 / q') * (∫⁻ a, w a * f a ^ q ∂μ) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow hH hq0.le
    _ = (∫⁻ a, w a ∂μ) ^ (q - 1) * ∫⁻ a, w a * f a ^ q ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
        congr 2
        rw [hq']
        field_simp

theorem abs_le_one_add_abs_rpow {q : ℝ} (hq : 1 ≤ q) (a : ℝ) : |a| ≤ 1 + |a| ^ q := by
  rcases le_or_gt |a| 1 with h | h
  · have := Real.rpow_nonneg (abs_nonneg a) q
    linarith
  · have := Real.self_le_rpow_of_one_le h.le hq
    linarith

/-- A bounded integrable continuous kernel times an `L^q` function is integrable. -/
theorem integrable_mul_of_bound_of_memLp {K v : Vec d → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hK : Integrable K) (hKc : Continuous K) {C : ℝ} (hKC : ∀ z, |K z| ≤ C)
    (hv : MemLp v (ENNReal.ofReal q) volume) :
    Integrable (fun y => K y * v y) := by
  have hvq : Integrable (fun y => ‖v y‖ ^ q) := by
    have h := hv.integrable_norm_rpow (by simp; linarith) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at h
  refine (hK.abs.add (hvq.const_mul C)).mono'
    (hKc.aestronglyMeasurable.mul hv.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hKC y)
  have h1 := abs_le_one_add_abs_rpow hq (v y)
  simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
  calc |K y| * |v y| ≤ |K y| * (1 + |v y| ^ q) := by gcongr
    _ = |K y| + |K y| * |v y| ^ q := by ring
    _ ≤ |K y| + C * |v y| ^ q := by gcongr; exact hKC y

/-- The fractional seminorm (B.2) on `ℝ^d`:
`[v]_{W^{β,q}(ℝ^d)} = ((1 - β) ∫∫ |v(x) - v(y)|^q / |x - y|^{d+βq} dx dy)^{1/q}`. -/
def fractionalSeminorm (β q : ℝ) (v : Vec d → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - β) * ∫⁻ x, ∫⁻ y,
    ENNReal.ofReal (|v x - v y| ^ q / euclideanNorm (x - y) ^ ((d : ℝ) + β * q))) ^ (1 / q)

/-- **The weak derivative identity against a smooth function**: if `g` is the weak `i`-th
derivative of `f` on `ℝ^d` and `f ∂ᵢφ`, `f φ`, `g φ` are integrable, then `∫ f ∂ᵢφ = -∫ g φ`. -/
theorem integral_mul_coordinateDerivative_of_hasWeakPartialDerivative_of_integrable {i : Fin d}
    {f g : Vec d → ℝ} (hw : HasWeakPartialDerivative univ i f g)
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hfdφi : Integrable (fun x => f x * coordinateDerivative i φ x))
    (hfφi : Integrable (fun x => f x * φ x)) (hgφi : Integrable (fun x => g x * φ x)) :
    ∫ x, f x * coordinateDerivative i φ x = -∫ x, g x * φ x := by
  obtain ⟨M, hM⟩ := PDE.exists_abs_coord_deriv_wholeSpaceCutoff_le (d := d) i
  set χ : ℕ → Vec d → ℝ := fun n => PDE.wholeSpaceCutoff ((n : ℝ) + 1) with hχ
  have hχs : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => PDE.contDiff_wholeSpaceCutoff _
  have hχc : ∀ n, HasCompactSupport (χ n) := fun n =>
    PDE.hasCompactSupport_wholeSpaceCutoff (by positivity)
  have hdχ : ∀ (n : ℕ) x, |coordinateDerivative i (χ n) x| ≤ M / ((n : ℝ) + 1) := fun n x =>
    hM _ (by positivity) x
  have hM0 : 0 ≤ M := by
    have := (abs_nonneg _).trans (hdχ 0 0)
    simpa using this
  have hχ01 : ∀ n x, |χ n x| ≤ 1 := fun n x => by
    rw [abs_of_nonneg (PDE.wholeSpaceCutoff_nonneg _ _)]
    exact PDE.wholeSpaceCutoff_le_one _ _
  have hprod : ∀ n x, coordinateDerivative i (fun y => χ n y * φ y) x =
      χ n x * coordinateDerivative i φ x + coordinateDerivative i (χ n) x * φ x := by
    intro n x
    unfold coordinateDerivative
    rw [fderiv_fun_mul ((hχs n).differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    change χ n x * fderiv ℝ φ x (unitVector i) + φ x * fderiv ℝ (χ n) x (unitVector i) = _
    ring
  have htest : ∀ n, ∫ x, f x * coordinateDerivative i (fun y => χ n y * φ y) x =
      -∫ x, g x * (χ n x * φ x) := by
    intro n
    have h := hw.2.2 (fun y => χ n y * φ y) ⟨(hχs n).mul hφ, (hχc n).mul_right, subset_univ _⟩
    simpa only [Measure.restrict_univ] using h
  have hχ1 : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (2 * ‖x‖)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    refine (PDE.wholeSpaceCutoff_eq_one (by positivity) ?_).symm
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdχ0 : ∀ x, Tendsto (fun n => coordinateDerivative i (χ n) x) atTop (𝓝 0) := by
    intro x
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (Real.norm_eq_abs _).trans_le
      (hdχ n x)) ?_
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
    rw [mul_zero] at h
    exact h.congr fun n => by ring
  have hfdφ : Integrable (fun x => |f x| * |coordinateDerivative i φ x|) := by
    simpa only [abs_mul] using hfdφi.abs
  have hfφ : Integrable (fun x => |f x| * |φ x|) := by
    simpa only [abs_mul] using hfφi.abs
  have hgφ : Integrable (fun x => |g x| * |φ x|) := by
    simpa only [abs_mul] using hgφi.abs
  have hL : Tendsto (fun n => ∫ x, f x * coordinateDerivative i (fun y => χ n y * φ y) x) atTop
      (𝓝 (∫ x, f x * coordinateDerivative i φ x)) := by
    simp_rw [hprod]
    refine tendsto_integral_of_dominated_convergence
      (fun x => |f x| * |coordinateDerivative i φ x| + M * (|f x| * |φ x|)) (fun n => ?_)
      (hfdφ.add (hfφ.const_mul M)) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · have hc : Continuous fun x => χ n x * coordinateDerivative i φ x +
          coordinateDerivative i (χ n) x * φ x :=
        ((hχs n).continuous.mul (contDiff_coordinateDerivative hφ i).continuous).add
          ((contDiff_coordinateDerivative (hχs n) i).continuous.mul hφ.continuous)
      exact hfm.mul hc.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |χ n x * coordinateDerivative i φ x + coordinateDerivative i (χ n) x * φ x| ≤
          |coordinateDerivative i φ x| + M * |φ x| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 n x)
        · rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ((hdχ n x).trans ?_) (abs_nonneg _)
          exact div_le_self hM0 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      calc |f x| * |χ n x * coordinateDerivative i φ x + coordinateDerivative i (χ n) x * φ x|
          ≤ |f x| * (|coordinateDerivative i φ x| + M * |φ x|) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = _ := by ring
    · have h := ((hχ1 x).mul_const (coordinateDerivative i φ x)).add
        ((hdχ0 x).mul_const (φ x))
      rw [one_mul, zero_mul, add_zero] at h
      exact h.const_mul (f x)
  have hR : Tendsto (fun n => ∫ x, g x * (χ n x * φ x)) atTop (𝓝 (∫ x, g x * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |g x| * |φ x|) (fun n => ?_) hgφ
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact hgm.mul ((hχs n).continuous.mul hφ.continuous).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) (hχ01 n x))
        (abs_nonneg _)
    · have h := (hχ1 x).mul_const (φ x)
      rw [one_mul] at h
      exact h.const_mul (g x)
  have heq : (fun n => ∫ x, f x * coordinateDerivative i (fun y => χ n y * φ y) x) =
      fun n => -∫ x, g x * (χ n x * φ x) := funext htest
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR.neg

/-! ## Derivatives of every order -/

/-- `∫ ∂^β Φ(t, ·) = 0` for `|β| ≥ 1`. -/
theorem integral_multiIndexDerivative_euclideanHeatKernel_eq_zero {m : ℕ} {t : ℝ} (ht : 0 < t)
    (β : Fin d → Fin (m + 1)) (hβ : ∃ i, (β i).val ≠ 0) :
    ∫ z, multiIndexDerivative β (euclideanHeatKernel (d := d) t) z = 0 := by
  rw [euclideanHeatKernel_eq_prodFun ht, multiIndexDerivative_prodFun
    (fun _ => contDiff_heatKernel1 t)]
  simp only [prodFun]
  rw [integral_fintype_prod_volume_eq_prod (fun i y => iteratedDeriv (β i).val (heatKernel1 t) y)]
  obtain ⟨i, hi⟩ := hβ
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [hc]
  refine integral_eq_zero_of_hasDerivAt_of_integrable (f := iteratedDeriv c (heatKernel1 t))
    (fun y => ?_) (integrable_iteratedDeriv_heatKernel1 ht (c + 1))
    (integrable_iteratedDeriv_heatKernel1 ht c)
  rw [iteratedDeriv_succ]
  have hdiff : Differentiable ℝ (iteratedDeriv c (heatKernel1 t)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ((contDiff_heatKernel1 t).iterate_deriv c).differentiable (by simp)
  exact (hdiff y).hasDerivAt

theorem integral_heatKernelDeriv_ofFn_eq_zero {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (w : Fin k → Fin d) :
    ∫ z, heatKernelDeriv t (List.ofFn w) z = 0 := by
  rw [heatKernelDeriv_ofFn_eq]
  refine integral_multiIndexDerivative_euclideanHeatKernel_eq_zero ht _ ?_
  by_contra h
  push Not at h
  have := sum_countIndex w
  simp [h] at this
  omega

/-- **The Gaussian majorant along a list**: `|∂_w Φ(t, z)| ≤ C_w (2t)^{-k/2} Φ(2t, z)`. -/
theorem abs_heatKernelDeriv_ofFn_le {k : ℕ} (w : Fin k → Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ z : Vec d,
      |heatKernelDeriv t (List.ofFn w) z| ≤
        C * (Real.sqrt (2 * t))⁻¹ ^ k * euclideanHeatKernel (2 * t) z := by
  obtain ⟨C, hC, h⟩ := abs_multiIndexDerivative_euclideanHeatKernel_le (d := d) (countIndex w)
  refine ⟨C, hC, fun t ht z => ?_⟩
  rw [heatKernelDeriv_ofFn_eq]
  have := h t ht z
  rwa [sum_countIndex] at this

/-- `K ∗ v (x) = ∫ K(x - y) (v y - v x) dy` for a kernel of integral zero. -/
theorem kconv_eq_integral_sub_of_integral_eq_zero {K v : Vec d → ℝ} (hK : Integrable K)
    (hK0 : ∫ z, K z = 0) (x : Vec d) (hv : Integrable (fun y => K (x - y) * v y)) :
    kconv K v x = ∫ y, K (x - y) * (v y - v x) := by
  have hKx : Integrable (fun y => K (x - y)) := hK.comp_sub_left x
  have hK0' : ∫ y, K (x - y) = 0 := by rw [integral_sub_left_eq_self K volume x]; exact hK0
  rw [kconv_apply]
  simp_rw [mul_sub]
  rw [integral_sub hv (hKx.mul_const _), integral_mul_const, hK0', zero_mul, sub_zero]

theorem sqrt_sum_sq_le_sum_abs {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, a i ^ 2) ≤ ∑ i ∈ s, |a i| := by
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  calc ∑ i ∈ s, a i ^ 2 = ∑ i ∈ s, |a i| ^ 2 := by simp_rw [sq_abs]
    _ ≤ (∑ i ∈ s, |a i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- **The pointwise bound for `k ≥ 1` derivatives**:
`|∇^k Φ(t, ·) ∗ v|(x) ≤ C (2t)^{-k/2} ∫ Φ(2t, x - y) |v y - v x| dy`. -/
theorem ofReal_sqrt_heatGradSq_le {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ (v : Vec d → ℝ) (x : Vec d),
      (∀ w : Fin k → Fin d, Integrable (fun y => heatKernelDeriv t (List.ofFn w) (x - y) * v y)) →
      ENNReal.ofReal (Real.sqrt (heatGradSq k t v x)) ≤
        ENNReal.ofReal (C * (Real.sqrt (2 * t))⁻¹ ^ k) *
          ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) * ENNReal.ofReal |v y - v x| := by
  have hb := fun w : Fin k → Fin d => abs_heatKernelDeriv_ofFn_le (d := d) w
  choose Cw hCw hCwb using hb
  refine ⟨∑ w, Cw w, Finset.sum_nonneg fun w _ => hCw w, fun t ht v x hv => ?_⟩
  set A := ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
    ENNReal.ofReal |v y - v x| with hA
  set s := (Real.sqrt (2 * t))⁻¹ ^ k with hs
  have hs0 : 0 ≤ s := by positivity
  have hcoord : ∀ w : Fin k → Fin d,
      ENNReal.ofReal |kconv (heatKernelDeriv t (List.ofFn w)) v x| ≤
        ENNReal.ofReal (Cw w * s) * A := by
    intro w
    have hK0 := integral_heatKernelDeriv_ofFn_eq_zero hk ht w
    rw [kconv_eq_integral_sub_of_integral_eq_zero (integrable_heatKernelDeriv ht _) hK0 x (hv w),
      ← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (hCw w) hs0),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hCw w) hs0)
        (euclideanHeatKernel_nonneg (by linarith) _))]
    gcongr
    exact hCwb w t ht (x - y)
  calc ENNReal.ofReal (Real.sqrt (heatGradSq k t v x))
      ≤ ENNReal.ofReal (∑ w : Fin k → Fin d, |kconv (heatKernelDeriv t (List.ofFn w)) v x|) :=
        ENNReal.ofReal_le_ofReal (sqrt_sum_sq_le_sum_abs _ _)
    _ = ∑ w : Fin k → Fin d, ENNReal.ofReal |kconv (heatKernelDeriv t (List.ofFn w)) v x| :=
        ENNReal.ofReal_sum_of_nonneg fun w _ => abs_nonneg _
    _ ≤ ∑ w : Fin k → Fin d, ENNReal.ofReal (Cw w * s) * A := Finset.sum_le_sum fun w _ => hcoord w
    _ = ENNReal.ofReal ((∑ w, Cw w) * s) * A := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun w _ => mul_nonneg (hCw w) hs0,
          Finset.sum_mul]

theorem euclideanSq_nonneg_of_vec (z : Vec d) : 0 ≤ euclideanSq z := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem euclideanNorm_pos_of_ne_zero {z : Vec d} (hz : z ≠ 0) : 0 < euclideanNorm z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have h1 : 0 < z i * z i := mul_self_pos.mpr hi
  have h2 : z i * z i ≤ euclideanSq z := by
    unfold euclideanSq dot
    exact Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le h1 h2)

/-- The constant `(8π)^{-d/2} Γ(a + d/2) 8^{a + d/2}` of `lintegral_heatKernel_two_mul_eq`. -/
def heatTimeConstant (d : ℕ) (a : ℝ) : ℝ :=
  (8 * Real.pi) ^ (-(d : ℝ) / 2) * Real.Gamma (a + d / 2) * 8 ^ (a + d / 2)

theorem heatTimeConstant_nonneg (d : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ heatTimeConstant d a := by
  unfold heatTimeConstant
  have := Real.Gamma_nonneg_of_nonneg (by positivity : (0 : ℝ) ≤ a + d / 2)
  positivity

/-- **The time integral of the heat kernel**: for `a > 0` and `z ≠ 0`,
`∫_0^∞ t^{-a-1} Φ(2t, z) dt = K |z|^{-d-2a}`. -/
theorem lintegral_heatKernel_two_mul_eq {a : ℝ} (ha : 0 < a) {z : Vec d} (hz : z ≠ 0) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-a - 1)) *
        ENNReal.ofReal (euclideanHeatKernel (2 * t) z) =
      ENNReal.ofReal (heatTimeConstant d a * euclideanNorm z ^ (-(d : ℝ) - 2 * a)) := by
  set r := euclideanNorm z with hr
  have hrpos : 0 < r := euclideanNorm_pos_of_ne_zero hz
  set c := a + d / 2 with hc
  have hcpos : 0 < c := by positivity
  set b := r ^ 2 / 8 with hb
  have hbpos : 0 < b := by positivity
  have hsq : euclideanSq z = r ^ 2 := by
    rw [hr, euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_of_vec z)]
  set A := (8 * Real.pi) ^ (-(d : ℝ) / 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-a - 1)) *
      ENNReal.ofReal (euclideanHeatKernel (2 * t) z) =
        ENNReal.ofReal A * ENNReal.ofReal (t ^ (-c - 1) * Real.exp (-(b / t))) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← ENNReal.ofReal_mul hA0]
    congr 1
    rw [euclideanHeatKernel, hsq, show 4 * Real.pi * (2 * t) = (8 * Real.pi) * t by ring,
      Real.mul_rpow (by positivity) ht0.le]
    have h1 : t ^ (-c - 1) = t ^ (-a - 1) * t ^ (-(d : ℝ) / 2) := by
      rw [← Real.rpow_add ht0, hc]
      congr 1
      ring
    rw [h1, hA, hb, show -(r ^ 2) / (4 * (2 * t)) = -(r ^ 2 / 8 / t) by field_simp; ring]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  obtain ⟨hint, hval⟩ := integrableOn_rpow_neg_mul_exp_neg_div hbpos hcpos
  rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t (ht : 0 < t) =>
      mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)), hval, ← ENNReal.ofReal_mul hA0]
  congr 1
  have h4 : (r ^ 2 / 8) ^ (-c) = (8 : ℝ) ^ c * r ^ (-2 * c) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      ← Real.rpow_natCast r 2, ← Real.rpow_mul hrpos.le, div_eq_mul_inv, inv_inv]
    push_cast
    ring_nf
  rw [hb, h4, heatTimeConstant, ← hc, show -(d : ℝ) - 2 * a = -2 * c by rw [hc]; ring]
  ring

/-- `∫ Φ(2t, x - y) dy = 1` as a lower integral. -/
theorem lintegral_euclideanHeatKernel_sub_left {t : ℝ} (ht : 0 < t) (x : Vec d) :
    ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel t (x - y)) = 1 := by
  rw [lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (euclideanHeatKernel t z)) x,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_euclideanHeatKernel ht)
      (Eventually.of_forall fun z => euclideanHeatKernel_nonneg ht.le z),
    integral_euclideanHeatKernel ht, ENNReal.ofReal_one]

/-- For `v ∈ L^q` measurable and `t > 0`:
`∫ |∇^k Φ(t, ·) ∗ v|^q ≤ (C (2t)^{-k/2})^q ∫∫ Φ(2t, x - y) |v y - v x|^q`. -/
theorem lintegral_heatGradSq_rpow_le {k : ℕ} {q : ℝ} (hq : 1 < q) {C : ℝ}
    (hC : ∀ t : ℝ, 0 < t → ∀ (v : Vec d → ℝ) (x : Vec d),
      (∀ w : Fin k → Fin d, Integrable (fun y => heatKernelDeriv t (List.ofFn w) (x - y) * v y)) →
      ENNReal.ofReal (Real.sqrt (heatGradSq k t v x)) ≤
        ENNReal.ofReal (C * (Real.sqrt (2 * t))⁻¹ ^ k) *
          ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) * ENNReal.ofReal |v y - v x|)
    {v : Vec d → ℝ} (hvm : Measurable v) (hv : MemLp v (ENNReal.ofReal q) volume)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t v x)) ^ q ≤
      ENNReal.ofReal (C * (Real.sqrt (2 * t))⁻¹ ^ k) ^ q *
        ∫⁻ x, ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
          ENNReal.ofReal |v y - v x| ^ q := by
  have hq0 : 0 < q := by linarith
  have ht2 : 0 < 2 * t := by linarith
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun x => ?_
  have hint : ∀ w : Fin k → Fin d,
      Integrable (fun y => heatKernelDeriv t (List.ofFn w) (x - y) * v y) := by
    intro w
    obtain ⟨CK, -, hCK⟩ := abs_foldr_euclideanHeatKernel_le (d := d) ht (List.ofFn w)
    exact integrable_mul_of_bound_of_memLp (K := fun y => heatKernelDeriv t (List.ofFn w) (x - y))
      hq.le ((integrable_heatKernelDeriv ht _).comp_sub_left x)
      ((continuous_heatKernelDeriv t _).comp (continuous_const.sub continuous_id))
      (fun z => hCK (x - z)) hv
  have hwm : AEMeasurable (fun y => ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y))) volume :=
    ((continuous_euclideanHeatKernel (2 * t)).comp
      (continuous_const.sub continuous_id)).measurable.ennreal_ofReal.aemeasurable
  have hfm : AEMeasurable (fun y => ENNReal.ofReal |v y - v x|) volume :=
    (continuous_abs.measurable.comp (hvm.sub measurable_const)).ennreal_ofReal.aemeasurable
  have hJ := lintegral_mul_rpow_le hq hwm hfm
  rw [lintegral_euclideanHeatKernel_sub_left ht2 x, ENNReal.one_rpow, one_mul] at hJ
  calc ENNReal.ofReal (Real.sqrt (heatGradSq k t v x)) ^ q
      ≤ (ENNReal.ofReal (C * (Real.sqrt (2 * t))⁻¹ ^ k) *
          ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
            ENNReal.ofReal |v y - v x|) ^ q := ENNReal.rpow_le_rpow (hC t ht v x hint) hq0.le
    _ = ENNReal.ofReal (C * (Real.sqrt (2 * t))⁻¹ ^ k) ^ q *
          (∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
            ENNReal.ofReal |v y - v x|) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ ≤ _ := mul_le_mul' le_rfl hJ

/-- **(D.7) for every order `k ≥ 1`**: for `β > 0`, `q > 1` and `v ∈ L^q(ℝ^d)`,
`∫_0^∞ t^{q(k-β)/2} ‖∇^k Φ(t, ·) ∗ v‖^q_{L^q(ℝ^d)} dt/t ≤ C ∫∫ |v(x) - v(y)|^q / |x - y|^{d+βq}`
with `C(k, β, q, d)`. -/
theorem lintegral_heatGradSq_le_fractional {k : ℕ} (hk : 0 < k) {β q : ℝ} (hβ : 0 < β)
    (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Vec d → ℝ, MemLp v (ENNReal.ofReal q) volume →
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q * (k - β) / 2) / t) *
          ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t v x)) ^ q ≤
        ENNReal.ofReal C * ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (|v x - v y| ^ q / euclideanNorm (x - y) ^ ((d : ℝ) + β * q)) := by
  obtain ⟨C₁, hC₁, hpt⟩ := ofReal_sqrt_heatGradSq_le (d := d) hk
  have hq0 : 0 < q := by linarith
  set a := q * β / 2 with ha
  have ha0 : 0 < a := by positivity
  set A := C₁ ^ q * (2 : ℝ) ^ (-(q * k / 2)) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hK0 := heatTimeConstant_nonneg d ha0.le
  refine ⟨A * heatTimeConstant d a, mul_nonneg hA0 hK0, fun v hv => ?_⟩
  set v' := hv.aestronglyMeasurable.mk v with hv'
  have hv'm : Measurable v' := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hvv' : v =ᵐ[volume] v' := hv.aestronglyMeasurable.ae_eq_mk
  have hv'L : MemLp v' (ENNReal.ofReal q) volume := hv.ae_eq hvv'
  have hgrad : ∀ t x, heatGradSq k t v x = heatGradSq k t v' x := fun t x => by
    unfold heatGradSq
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [kconv_apply, kconv_apply]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hvv'] with y hy
    rw [hy]
  have hsem : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|v x - v y| ^ q /
        euclideanNorm (x - y) ^ ((d : ℝ) + β * q)) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|v' x - v' y| ^ q /
        euclideanNorm (x - y) ^ ((d : ℝ) + β * q)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hvv'] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hvv'] with y hy
    rw [hx, hy]
  simp_rw [hgrad]
  rw [hsem]
  set F : ℝ → Vec d → Vec d → ℝ≥0∞ := fun t x y =>
    ENNReal.ofReal (t ^ (-a - 1)) * (ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
      ENNReal.ofReal |v' y - v' x| ^ q) with hF
  have hFm : Measurable (fun p : (ℝ × Vec d) × Vec d => F p.1.1 p.1.2 p.2) := by
    have h1 : Measurable (fun p : (ℝ × Vec d) × Vec d =>
        euclideanHeatKernel (2 * p.1.1) (p.1.2 - p.2)) := by
      unfold euclideanHeatKernel euclideanSq dot
      fun_prop
    have h2 : Measurable (fun p : (ℝ × Vec d) × Vec d => |v' p.2 - v' p.1.2|) :=
      continuous_abs.measurable.comp ((hv'm.comp measurable_snd).sub
        (hv'm.comp (measurable_snd.comp measurable_fst)))
    have h3 : Measurable (fun p : (ℝ × Vec d) × Vec d => p.1.1 ^ (-a - 1)) :=
      (measurable_fst.comp measurable_fst).pow_const _
    simp only [hF]
    exact h3.ennreal_ofReal.mul (h1.ennreal_ofReal.mul (h2.ennreal_ofReal.pow_const _))
  have hkey : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t ^ (q * (k - β) / 2) / t) *
      ENNReal.ofReal (C₁ * (Real.sqrt (2 * t))⁻¹ ^ k) ^ q =
      ENNReal.ofReal A * ENNReal.ofReal (t ^ (-a - 1)) := by
    intro t ht0
    have hs : 0 ≤ C₁ * (Real.sqrt (2 * t))⁻¹ ^ k := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg hs hq0.le,
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg ht0.le _) ht0.le),
      ← ENNReal.ofReal_mul hA0]
    congr 1
    have hsq : (Real.sqrt (2 * t))⁻¹ ^ k = (2 * t) ^ (-(k : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [hsq, Real.mul_rpow hC₁ (by positivity), ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) ht0.le, div_eq_mul_inv, ← Real.rpow_neg_one t, hAdef]
    have e3 : t ^ (q * (k - β) / 2) * t ^ (-1 : ℝ) * t ^ (-(k : ℝ) / 2 * q) = t ^ (-a - 1) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0, ha]
      congr 1
      ring
    rw [show (2 : ℝ) ^ (-(k : ℝ) / 2 * q) = (2 : ℝ) ^ (-(q * k / 2)) by congr 1; ring]
    calc t ^ (q * (k - β) / 2) * t ^ (-1 : ℝ) *
          (C₁ ^ q * ((2 : ℝ) ^ (-(q * k / 2)) * t ^ (-(k : ℝ) / 2 * q)))
        = C₁ ^ q * (2 : ℝ) ^ (-(q * k / 2)) *
          (t ^ (q * (k - β) / 2) * t ^ (-1 : ℝ) * t ^ (-(k : ℝ) / 2 * q)) := by ring
      _ = _ := by rw [e3]
  have hstep : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q * (k - β) / 2) / t) *
      ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t v' x)) ^ q ≤
        ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, F t x y := by
    intro t ht
    have ht0 : 0 < t := ht
    calc ENNReal.ofReal (t ^ (q * (k - β) / 2) / t) *
          ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t v' x)) ^ q
        ≤ ENNReal.ofReal (t ^ (q * (k - β) / 2) / t) *
          (ENNReal.ofReal (C₁ * (Real.sqrt (2 * t))⁻¹ ^ k) ^ q *
            ∫⁻ x, ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
              ENNReal.ofReal |v' y - v' x| ^ q) :=
          mul_le_mul' le_rfl (lintegral_heatGradSq_rpow_le hq hpt hv'm hv'L ht0)
      _ = ENNReal.ofReal A * (ENNReal.ofReal (t ^ (-a - 1)) *
            ∫⁻ x, ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
              ENNReal.ofReal |v' y - v' x| ^ q) := by
          rw [← mul_assoc, hkey t ht0, mul_assoc]
      _ = ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, F t x y := by
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q * (k - β) / 2) / t) *
          ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t v' x)) ^ q
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, F t x y :=
        setLIntegral_mono' measurableSet_Ioi hstep
    _ = ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, ∫⁻ t in Ioi (0 : ℝ), F t x y := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_lintegral_swap hFm.lintegral_prod_right'.aemeasurable]
        refine lintegral_congr fun x => ?_
        refine lintegral_lintegral_swap ?_
        exact (hFm.comp ((measurable_fst.prodMk measurable_const).prodMk
          measurable_snd)).aemeasurable
    _ = ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (heatTimeConstant d a) *
          ENNReal.ofReal (|v' x - v' y| ^ q / euclideanNorm (x - y) ^ ((d : ℝ) + β * q)) := by
        congr 1
        refine lintegral_congr fun x => lintegral_congr fun y => ?_
        have hc : ENNReal.ofReal |v' y - v' x| ^ q ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top
        simp only [hF]
        simp_rw [← mul_assoc]
        rw [lintegral_mul_const' _ _ hc]
        rcases eq_or_ne x y with rfl | hxy
        · simp [Real.zero_rpow hq0.ne', hq0]
        have hn : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
        rw [lintegral_heatKernel_two_mul_eq ha0 (sub_ne_zero.mpr hxy),
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le, ← ENNReal.ofReal_mul
          (mul_nonneg hK0 (Real.rpow_nonneg hn _)), ← ENNReal.ofReal_mul hK0]
        congr 1
        rw [abs_sub_comm (v' y), show -(d : ℝ) - 2 * a = -((d : ℝ) + β * q) by rw [ha]; ring,
          Real.rpow_neg hn]
        ring
    _ = ENNReal.ofReal (A * heatTimeConstant d a) * ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (|v' x - v' y| ^ q / euclideanNorm (x - y) ^ ((d : ℝ) + β * q)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [← mul_assoc, ← ENNReal.ofReal_mul hA0]

/-- **Proposition D.2, (D.4), for `α ∈ (0, 1)`**: for `k ∈ ℕ ∩ (α, ∞)` and `q ∈ (1, ∞)` there is
`C(k, α, q, d)` such that, for every `u ∈ L^q(ℝ^d)`,
`(∫_0^∞ (t^{(k-α)/2} ‖∇^k Φ(t, ·) ∗ u‖_{L^q(ℝ^d)})^q dt/t)^{1/q} ≤ C [u]_{W^{α,q}(ℝ^d)}`. -/
theorem propositionD2_fractional_lt_one {α q : ℝ} (hα : 0 < α) (hα1 : α < 1) {k : ℕ}
    (hk : 0 < k) (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Vec d → ℝ, MemLp u (ENNReal.ofReal q) volume →
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q * (k - α) / 2) / t) *
          ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t u x)) ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C * fractionalSeminorm α q u := by
  obtain ⟨C, hC, h⟩ := lintegral_heatGradSq_le_fractional (d := d) hk hα hq
  have hq0 : 0 < q := by linarith
  have h1α : 0 < 1 - α := by linarith
  refine ⟨(C / (1 - α)) ^ (1 / q), Real.rpow_nonneg (div_nonneg hC h1α.le) _, fun u hu => ?_⟩
  rw [fractionalSeminorm, ← ENNReal.ofReal_rpow_of_nonneg (div_nonneg hC h1α.le)
    (one_div_nonneg.mpr hq0.le), ← ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le)]
  refine ENNReal.rpow_le_rpow ((h u hu).trans (le_of_eq ?_)) (one_div_nonneg.mpr hq0.le)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hC h1α.le), div_mul_cancel₀ _ h1α.ne']

/-! ## Derivatives moved onto `u ∈ W^{m,q}(ℝ^d)` -/

/-- `u ∈ W^{m,q}(ℝ^d)` with its weak derivatives `g l = ∂_{l₁} ⋯ ∂_{l_j} u` along the lists of
coordinates of length `j ≤ m`, all in `L^q(ℝ^d)`. -/
structure IsSobolevFamilyLp (q : ℝ) (m : ℕ) (u : Vec d → ℝ) (g : List (Fin d) → Vec d → ℝ) :
    Prop where
  nil : g [] = u
  memLp : ∀ l : List (Fin d), l.length ≤ m → MemLp (g l) (ENNReal.ofReal q) volume
  weak : ∀ (l : List (Fin d)) (i : Fin d), l.length < m →
    HasWeakPartialDerivative univ i (g l) (g (i :: l))

/-- **One derivative moved onto the weak derivative**, for `f, g ∈ L^q`. -/
theorem kconv_heatKernelDeriv_cons_eq_of_memLp {t : ℝ} (ht : 0 < t) {i : Fin d}
    {f g : Vec d → ℝ} {q : ℝ} (hq : 1 ≤ q) (hw : HasWeakPartialDerivative univ i f g)
    (hf : MemLp f (ENNReal.ofReal q) volume) (hg : MemLp g (ENNReal.ofReal q) volume)
    (l : List (Fin d)) (x : Vec d) :
    kconv (heatKernelDeriv t (i :: l)) f x = kconv (heatKernelDeriv t l) g x := by
  set K := heatKernelDeriv t l with hK
  have hKs : ContDiff ℝ ∞ K := contDiff_heatKernelDeriv t l
  have hφ : ContDiff ℝ ∞ (fun y => K (x - y)) := hKs.comp (contDiff_const.sub contDiff_id)
  have hdφ : ∀ y, coordinateDerivative i (fun y => K (x - y)) y =
      -heatKernelDeriv t (i :: l) (x - y) := by
    intro y
    have h1 : HasFDerivAt (fun y : Vec d => x - y) (-ContinuousLinearMap.id ℝ (Vec d)) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 : HasFDerivAt (fun y => K (x - y))
        ((fderiv ℝ K (x - y)).comp (-ContinuousLinearMap.id ℝ (Vec d))) y :=
      ((hKs.differentiable (by simp) (x - y)).hasFDerivAt).comp y h1
    unfold coordinateDerivative
    rw [h2.fderiv, show heatKernelDeriv t (i :: l) = coordinateDerivative i K from rfl]
    simp [coordinateDerivative]
  have hint : ∀ (l' : List (Fin d)) {h : Vec d → ℝ}, MemLp h (ENNReal.ofReal q) volume →
      Integrable (fun y => heatKernelDeriv t l' (x - y) * h y) := by
    intro l' h hh
    obtain ⟨CK, -, hCK⟩ := abs_foldr_euclideanHeatKernel_le (d := d) ht l'
    exact integrable_mul_of_bound_of_memLp (K := fun y => heatKernelDeriv t l' (x - y)) hq
      ((integrable_heatKernelDeriv ht _).comp_sub_left x)
      ((continuous_heatKernelDeriv t _).comp (continuous_const.sub continuous_id))
      (fun z => hCK (x - z)) hh
  have hfdφ : Integrable (fun y => f y * coordinateDerivative i (fun y => K (x - y)) y) := by
    simp_rw [hdφ]
    exact ((hint (i :: l) hf).neg).congr (Eventually.of_forall fun y => by simp [mul_comm])
  have hfφ : Integrable (fun y => f y * K (x - y)) :=
    (hint l hf).congr (Eventually.of_forall fun y => mul_comm _ _)
  have hgφ : Integrable (fun y => g y * K (x - y)) :=
    (hint l hg).congr (Eventually.of_forall fun y => mul_comm _ _)
  have h := integral_mul_coordinateDerivative_of_hasWeakPartialDerivative_of_integrable hw
    hf.aestronglyMeasurable hg.aestronglyMeasurable hφ hfdφ hfφ hgφ
  simp_rw [hdφ, mul_neg, integral_neg, neg_inj] at h
  rw [kconv_apply, kconv_apply]
  calc ∫ y, heatKernelDeriv t (i :: l) (x - y) * f y
      = ∫ y, f y * heatKernelDeriv t (i :: l) (x - y) :=
        integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    _ = ∫ y, g y * K (x - y) := h
    _ = ∫ y, K (x - y) * g y := integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

/-- **All the derivatives moved onto the weak derivatives**, for `u ∈ W^{m,q}(ℝ^d)`. -/
theorem kconv_heatKernelDeriv_append_eq_of_memLp {q : ℝ} (hq : 1 ≤ q) {m : ℕ} {u : Vec d → ℝ}
    {g : List (Fin d) → Vec d → ℝ} (hS : IsSobolevFamilyLp q m u g) {t : ℝ} (ht : 0 < t)
    (p : List (Fin d)) (x : Vec d) :
    ∀ l n : List (Fin d), l.length + n.length ≤ m →
      kconv (heatKernelDeriv t (l ++ p)) (g n) x =
        kconv (heatKernelDeriv t p) (g (l.reverse ++ n)) x := by
  intro l
  induction l with
  | nil => intro n _; simp
  | cons i l ih =>
    intro n hln
    simp only [List.length_cons] at hln
    have hlen : n.length < m := by omega
    rw [List.cons_append, kconv_heatKernelDeriv_cons_eq_of_memLp ht hq (hS.weak n i hlen)
      (hS.memLp n hlen.le) (hS.memLp (i :: n) (by simp only [List.length_cons]; omega)) (l ++ p) x,
      ih (i :: n) (by simp only [List.length_cons]; omega)]
    simp [List.reverse_cons, List.append_assoc]

/-- The seminorm `[u]_{W^{m+β,q}(ℝ^d)} = ∑_{|w| = m} [∂_w u]_{W^{β,q}(ℝ^d)}` of (B.3), the sum over
the lists `w` of `m` coordinates. -/
def fractionalSobolevSeminorm (m : ℕ) (β q : ℝ) (g : List (Fin d) → Vec d → ℝ) : ℝ≥0∞ :=
  ∑ w : Fin m → Fin d, fractionalSeminorm β q (g (List.ofFn w))

/-- **Splitting the derivatives**: `|∇^{m+n} Φ(t, ·) ∗ u|² = ∑_{|w| = m} |∇^n Φ(t, ·) ∗ ∂_w u|²`
for `u ∈ W^{m,q}(ℝ^d)`. -/
theorem heatGradSq_add_eq_of_memLp {q : ℝ} (hq : 1 ≤ q) {m : ℕ} {u : Vec d → ℝ}
    {g : List (Fin d) → Vec d → ℝ} (hS : IsSobolevFamilyLp q m u g) {t : ℝ} (ht : 0 < t) (n : ℕ)
    (x : Vec d) :
    heatGradSq (m + n) t u x = ∑ w : Fin m → Fin d, heatGradSq n t (g (List.ofFn w)) x := by
  unfold heatGradSq
  rw [← (Fin.appendEquiv (α := Fin d) m n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  have hperm : heatKernelDeriv t (List.ofFn (Fin.append v w)) =
      heatKernelDeriv t ((List.ofFn v).reverse ++ List.ofFn w) := by
    rw [List.ofFn_fin_append]
    exact foldr_coordinateDerivative_perm (contDiff_euclideanHeatKernel t)
      ((List.reverse_perm _).symm.append_right _)
  have h := kconv_heatKernelDeriv_append_eq_of_memLp hq hS ht (List.ofFn w) x
    (List.ofFn v).reverse [] (by simp)
  rw [hS.nil, List.reverse_reverse, List.append_nil] at h
  change kconv (heatKernelDeriv t (List.ofFn (Fin.append v w))) u x ^ 2 = _
  rw [hperm, h]

theorem sqrt_sum_le_sum_sqrt {ι : Type*} (s : Finset ι) {h : ι → ℝ} (hh : ∀ i ∈ s, 0 ≤ h i) :
    Real.sqrt (∑ i ∈ s, h i) ≤ ∑ i ∈ s, Real.sqrt (h i) := by
  have h1 := sqrt_sum_sq_le_sum_abs s (fun i => Real.sqrt (h i))
  simp only [abs_of_nonneg (Real.sqrt_nonneg _)] at h1
  calc Real.sqrt (∑ i ∈ s, h i) = Real.sqrt (∑ i ∈ s, Real.sqrt (h i) ^ 2) := by
        congr 1
        exact Finset.sum_congr rfl fun i hi => (Real.sq_sqrt (hh i hi)).symm
    _ ≤ _ := h1

/-- **Proposition D.2, (D.4)**: for `α = m + β` with `m ∈ ℕ` and `β ∈ (0, 1)`, `k ∈ ℕ ∩ (α, ∞)` and
`q ∈ (1, ∞)`, there is `C(k, α, q, d)` such that, for every `u ∈ W^{α,q}(ℝ^d)` (here `u ∈ W^{m,q}(ℝ^d)`
with its weak derivatives `g`; the right-hand side is infinite otherwise),
`(∫_0^∞ (t^{(k-α)/2} ‖∇^k Φ(t, ·) ∗ u‖_{L^q(ℝ^d)})^q dt/t)^{1/q} ≤ C [u]_{W^{α,q}(ℝ^d)}`. -/
theorem propositionD2_fractional (m : ℕ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {k : ℕ}
    (hk : m < k) {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Vec d → ℝ) (g : List (Fin d) → Vec d → ℝ),
      IsSobolevFamilyLp q m u g →
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q * (k - (m + β)) / 2) / t) *
          ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq k t u x)) ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C * fractionalSobolevSeminorm m β q g := by
  obtain ⟨n, rfl⟩ : ∃ n, k = m + n := ⟨k - m, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨C₀, hC₀, h0⟩ := propositionD2_fractional_lt_one (d := d) hβ hβ1 hn hq
  have hq0 : 0 < q := by linarith
  set N : ℝ≥0∞ := ((Fintype.card (Fin m → Fin d) : ℕ) : ℝ≥0∞) with hN
  have hNtop : N ^ (q - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _)
  refine ⟨(Fintype.card (Fin m → Fin d) : ℝ) * C₀, by positivity, fun u g hS => ?_⟩
  have hexp : ∀ t : ℝ, t ^ (q * (((m + n : ℕ) : ℝ) - (m + β)) / 2) = t ^ (q * (n - β) / 2) :=
    fun t => by
      congr 1
      push_cast
      ring
  have hH : ∀ w : Fin m → Fin d, ∃ H : ℝ × Vec d → ℝ, Measurable H ∧
      ∀ t, 0 < t → ∀ x, heatGradSq n t (g (List.ofFn w)) x = H (t, x) := fun w =>
    exists_measurable_heatGradSq n (hS.memLp _ (by simp)).aestronglyMeasurable
  choose H hHm hHeq using hH
  set G : (Fin m → Fin d) → ℝ → Vec d → ℝ≥0∞ := fun w t x =>
    ENNReal.ofReal (Real.sqrt (heatGradSq n t (g (List.ofFn w)) x)) ^ q with hG
  set T : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (q * (n - β) / 2) / t) with hT
  have hpt : ∀ t, 0 < t → ∀ x,
      ENNReal.ofReal (Real.sqrt (heatGradSq (m + n) t u x)) ^ q ≤ N ^ (q - 1) * ∑ w, G w t x := by
    intro t ht x
    rw [heatGradSq_add_eq_of_memLp hq.le hS ht n x]
    have hs := sqrt_sum_le_sum_sqrt Finset.univ
      (h := fun w : Fin m → Fin d => heatGradSq n t (g (List.ofFn w)) x)
      (fun w _ => heatGradSq_nonneg _ _ _ _)
    calc ENNReal.ofReal (Real.sqrt (∑ w, heatGradSq n t (g (List.ofFn w)) x)) ^ q
        ≤ (∑ w, ENNReal.ofReal (Real.sqrt (heatGradSq n t (g (List.ofFn w)) x))) ^ q := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => Real.sqrt_nonneg _]
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hs) hq0.le
      _ ≤ N ^ (q - 1) * ∑ w, G w t x := by
          have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
            (f := fun w : Fin m → Fin d =>
              ENNReal.ofReal (Real.sqrt (heatGradSq n t (g (List.ofFn w)) x))) hq.le
          rw [Finset.card_univ] at h
          exact h
  have hGm : ∀ w, Measurable (fun p : ℝ × Vec d => ENNReal.ofReal (Real.sqrt (H w p)) ^ q) :=
    fun w => ((hHm w).sqrt.ennreal_ofReal).pow_const _
  have hGx : ∀ w t, 0 < t → AEMeasurable (G w t) volume := by
    intro w t ht
    refine ((hGm w).comp (measurable_prodMk_left (x := t))).aemeasurable.congr
      (Eventually.of_forall fun x => ?_)
    simp only [hG, Function.comp_apply, hHeq w t ht x]
  have hIt : ∀ w, AEMeasurable (fun t => T t * ∫⁻ x, G w t x) (volume.restrict (Ioi 0)) := by
    intro w
    have hm : Measurable (fun t => T t * ∫⁻ x, ENNReal.ofReal (Real.sqrt (H w (t, x))) ^ q) :=
      (((measurable_id.pow_const _).div measurable_id).ennreal_ofReal).mul
        (hGm w).lintegral_prod_right'
    refine hm.aemeasurable.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t (ht : 0 < t) => ?_))
    simp only [hG]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [hHeq w t ht x]
  have hterm : ∀ w, ∫⁻ t in Ioi (0 : ℝ), T t * ∫⁻ x, G w t x ≤
      (ENNReal.ofReal C₀ * fractionalSeminorm β q (g (List.ofFn w))) ^ q := by
    intro w
    have h := ENNReal.rpow_le_rpow (h0 (g (List.ofFn w)) (hS.memLp _ (by simp))) hq0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at h
  set S := fractionalSobolevSeminorm m β q g with hSdef
  have hle : ∀ w, ENNReal.ofReal C₀ * fractionalSeminorm β q (g (List.ofFn w)) ≤
      ENNReal.ofReal C₀ * S := fun w =>
    mul_le_mul' le_rfl (Finset.single_le_sum
      (f := fun w => fractionalSeminorm β q (g (List.ofFn w))) (fun w _ => zero_le)
      (Finset.mem_univ w))
  have hmain : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q * (((m + n : ℕ) : ℝ) - (m + β)) / 2) / t) *
        ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (m + n) t u x)) ^ q ≤
      N ^ (q - 1) * (N * (ENNReal.ofReal C₀ * S) ^ q) := by
    calc _ ≤ ∫⁻ t in Ioi (0 : ℝ), N ^ (q - 1) * ∑ w, T t * ∫⁻ x, G w t x := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := ht
          rw [hexp t]
          calc ENNReal.ofReal (t ^ (q * (n - β) / 2) / t) *
                ∫⁻ x, ENNReal.ofReal (Real.sqrt (heatGradSq (m + n) t u x)) ^ q
              ≤ T t * ∫⁻ x, N ^ (q - 1) * ∑ w, G w t x :=
                mul_le_mul' le_rfl (lintegral_mono fun x => hpt t ht0 x)
            _ = N ^ (q - 1) * ∑ w, T t * ∫⁻ x, G w t x := by
                rw [lintegral_const_mul' _ _ hNtop,
                  lintegral_finsetSum' _ fun w _ => hGx w t ht0, ← mul_assoc,
                  mul_comm (T t), mul_assoc, Finset.mul_sum]
      _ = N ^ (q - 1) * ∑ w, ∫⁻ t in Ioi (0 : ℝ), T t * ∫⁻ x, G w t x := by
          rw [lintegral_const_mul' _ _ hNtop, lintegral_finsetSum' _ fun w _ => hIt w]
      _ ≤ N ^ (q - 1) * ∑ _w : Fin m → Fin d, (ENNReal.ofReal C₀ * S) ^ q := by
          gcongr with w
          exact (hterm w).trans (ENNReal.rpow_le_rpow (hle w) hq0.le)
      _ = N ^ (q - 1) * (N * (ENNReal.ofReal C₀ * S) ^ q) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfin : N ^ (q - 1) * (N * (ENNReal.ofReal C₀ * S) ^ q) = (N * (ENNReal.ofReal C₀ * S)) ^ q := by
    have hNq : N ^ (q - 1) * N = N ^ q := by
      conv_rhs => rw [show q = (q - 1) + 1 by ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
    rw [← mul_assoc, hNq, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
  calc _ ≤ ((N * (ENNReal.ofReal C₀ * S)) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (hmain.trans_eq hfin) (one_div_nonneg.mpr hq0.le)
    _ = ENNReal.ofReal ((Fintype.card (Fin m → Fin d) : ℝ) * C₀) * S := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one, ← mul_assoc,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end QSH
