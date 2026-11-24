import QuantitativeStochasticHomogenization.AppD.HeatGradientL2
import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceCutoff

/-!
# Appendix D: Lemma D.3

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Lemma D.3: for `α, k ∈ ℕ` with `α < k` there is `C(α, k, d) < ∞` such that, for every
`u ∈ H^α(ℝ^d)`,
`(∫_0^∞ t^{k-α} ‖∇^k Φ(t, ·) ∗ u‖²_{L²(ℝ^d)} dt/t)^{1/2} ≤ C [u]_{H^α(ℝ^d)}` (D.5) (`lemmaD3`).

Here `u ∈ H^α(ℝ^d)` is given with its weak derivatives `g l = ∂_{l₁} ⋯ ∂_{l_m} u` for the lists `l`
of coordinates of length `m ≤ α`, all in `L²(ℝ^d)` (`IsSobolevFamily`), and
`[u]²_{H^α(ℝ^d)} = ∫ |∇^α u|² = ∫ ∑_{|l| = α} |g l|²`.

The proof follows the book: the `α` derivatives are moved from the heat kernel onto `u`
(`kconv_heatKernelDeriv_append_eq`, by the weak derivative identity, which holds for the
derivatives of the heat kernel as test functions by a cutoff argument,
`integral_mul_coordinateDerivative_of_hasWeakPartialDerivative`), which reduces (D.5) to the case
`α = 0` (`lintegral_heatGradSq_le`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `u ∈ H^α(ℝ^d)`, with the weak derivatives `g l = ∂_{l₁} ⋯ ∂_{l_m} u` for the lists `l` of
coordinates of length `m ≤ α`: `g [] = u`, every `g l` is in `L²(ℝ^d)`, and `g (i :: l)` is the
weak `i`-th derivative of `g l` on `ℝ^d`. -/
structure IsSobolevFamily (α : ℕ) (u : Vec d → ℝ) (g : List (Fin d) → Vec d → ℝ) : Prop where
  nil : g [] = u
  memLp : ∀ l : List (Fin d), l.length ≤ α → MemLp (g l) 2 volume
  weak : ∀ (l : List (Fin d)) (i : Fin d), l.length < α →
    HasWeakPartialDerivative univ i (g l) (g (i :: l))

/-! ## The weak derivative identity against the derivatives of the heat kernel -/

/-- **The weak derivative identity for square integrable test functions**: if `g` is the weak
`i`-th derivative of `f` on `ℝ^d`, with `f, g ∈ L²`, then `∫ f ∂ᵢφ = -∫ g φ` for every smooth `φ`
with `φ, ∂ᵢφ ∈ L²`. The test functions `χ(·/R) φ` converge to `φ`. -/
theorem integral_mul_coordinateDerivative_of_hasWeakPartialDerivative {i : Fin d}
    {f g : Vec d → ℝ} (hw : HasWeakPartialDerivative univ i f g) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {φ : Vec d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφ2 : MemLp φ 2 volume)
    (hdφ2 : MemLp (coordinateDerivative i φ) 2 volume) :
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
    have h := (hf.integrable_mul hdφ2).abs
    simpa only [Pi.mul_apply, abs_mul] using h
  have hfφ : Integrable (fun x => |f x| * |φ x|) := by
    have h := (hf.integrable_mul hφ2).abs
    simpa only [Pi.mul_apply, abs_mul] using h
  have hgφ : Integrable (fun x => |g x| * |φ x|) := by
    have h := (hg.integrable_mul hφ2).abs
    simpa only [Pi.mul_apply, abs_mul] using h
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
      exact hf.aestronglyMeasurable.mul hc.aestronglyMeasurable
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
    · exact hg.aestronglyMeasurable.mul ((hχs n).continuous.mul hφ.continuous).aestronglyMeasurable
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

/-- **One derivative moved onto the weak derivative**:
`∂ᵢ ∂^l Φ(t, ·) ∗ f = ∂^l Φ(t, ·) ∗ g` when `g` is the weak `i`-th derivative of `f`. -/
theorem kconv_heatKernelDeriv_cons_eq {t : ℝ} (ht : 0 < t) {i : Fin d} {f g : Vec d → ℝ}
    (hw : HasWeakPartialDerivative univ i f g) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
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
  have hφ2 : MemLp (fun y => K (x - y)) 2 volume :=
    (memLp_heatKernelDeriv ht l).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hdφ2 : MemLp (coordinateDerivative i (fun y => K (x - y))) 2 volume := by
    rw [show coordinateDerivative i (fun y => K (x - y)) =
      fun y => -heatKernelDeriv t (i :: l) (x - y) from funext hdφ]
    exact ((memLp_heatKernelDeriv ht (i :: l)).comp_measurePreserving
      (Measure.measurePreserving_sub_left volume x)).neg
  have h := integral_mul_coordinateDerivative_of_hasWeakPartialDerivative hw hf hg hφ hφ2 hdφ2
  simp_rw [hdφ, mul_neg, integral_neg, neg_inj] at h
  rw [kconv_apply, kconv_apply]
  calc ∫ y, heatKernelDeriv t (i :: l) (x - y) * f y
      = ∫ y, f y * heatKernelDeriv t (i :: l) (x - y) :=
        integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    _ = ∫ y, g y * K (x - y) := h
    _ = ∫ y, K (x - y) * g y := integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

/-- **All the derivatives moved onto the weak derivatives**: for lists `q`, `m` with
`|q| + |m| ≤ α`, `∂^{q ++ p} Φ(t, ·) ∗ g m = ∂^p Φ(t, ·) ∗ g (q.reverse ++ m)`. -/
theorem kconv_heatKernelDeriv_append_eq {α : ℕ} {u : Vec d → ℝ} {g : List (Fin d) → Vec d → ℝ}
    (hS : IsSobolevFamily α u g) {t : ℝ} (ht : 0 < t) (p : List (Fin d)) (x : Vec d) :
    ∀ q m : List (Fin d), q.length + m.length ≤ α →
      kconv (heatKernelDeriv t (q ++ p)) (g m) x =
        kconv (heatKernelDeriv t p) (g (q.reverse ++ m)) x := by
  intro q
  induction q with
  | nil => intro m _; simp
  | cons i q ih =>
    intro m hqm
    simp only [List.length_cons] at hqm
    have hlen : m.length < α := by omega
    rw [List.cons_append, kconv_heatKernelDeriv_cons_eq ht (hS.weak m i hlen) (hS.memLp m hlen.le)
      (hS.memLp (i :: m) (by simp only [List.length_cons]; omega)) (q ++ p) x,
      ih (i :: m) (by simp only [List.length_cons]; omega)]
    simp [List.reverse_cons, List.append_assoc]

/-! ## Measurability in time -/

/-- The formula `∏ᵢ ∂^{cᵢ} Φ₁(t, zᵢ)` for `∂^l Φ(t, z)`, `cᵢ` the number of occurrences of `i` in
`l`, as a jointly measurable function of `(t, z)`. -/
def heatKernelDerivFormula (l : List (Fin d)) (p : ℝ × Vec d) : ℝ :=
  ∏ i, (4 * Real.pi * p.1) ^ (-(1 : ℝ) / 2) * ((Real.sqrt (2 * p.1))⁻¹ ^ (l.count i) *
    iteratedDeriv (l.count i) stdGaussian1 ((Real.sqrt (2 * p.1))⁻¹ * p.2 i))

theorem measurable_heatKernelDerivFormula (l : List (Fin d)) :
    Measurable (heatKernelDerivFormula (d := d) l) := by
  have hγ : ∀ k : ℕ, Measurable (iteratedDeriv k stdGaussian1) := fun k =>
    (contDiff_stdGaussian1.continuous_iteratedDeriv k (by exact_mod_cast le_top)).measurable
  have h1 : Measurable fun p : ℝ × Vec d => (Real.sqrt (2 * p.1))⁻¹ :=
    (Real.continuous_sqrt.measurable.comp (measurable_const.mul measurable_fst)).inv
  unfold heatKernelDerivFormula
  refine Finset.measurable_prod _ fun i _ => ?_
  exact ((measurable_const.mul measurable_fst).pow_const _).mul ((h1.pow_const _).mul
    ((hγ _).comp (h1.mul ((measurable_pi_apply i).comp measurable_snd))))

theorem heatKernelDeriv_eq_formula {t : ℝ} (ht : 0 < t) (l : List (Fin d)) (z : Vec d) :
    heatKernelDeriv t l z = heatKernelDerivFormula l (t, z) := by
  rw [heatKernelDeriv, euclideanHeatKernel_eq_prodFun ht,
    foldr_coordinateDerivative_prodFun (fun _ => contDiff_heatKernel1 t), prodFun]
  simp only [iteratedDeriv_heatKernel1 ht, heatKernelDerivFormula]

/-- For `g` measurable, `heatGradSq k t g x` agrees for `t > 0` with a jointly measurable function
of `(t, x)`. -/
theorem exists_measurable_heatGradSq (k : ℕ) {g : Vec d → ℝ} (hg : AEStronglyMeasurable g volume) :
    ∃ H : ℝ × Vec d → ℝ, Measurable H ∧ ∀ t, 0 < t → ∀ x, heatGradSq k t g x = H (t, x) := by
  set g' := hg.mk g
  have hg'm : Measurable g' := hg.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[volume] g' := hg.ae_eq_mk
  refine ⟨fun p => ∑ w : Fin k → Fin d,
    (∫ y, heatKernelDerivFormula (List.ofFn w) (p.1, p.2 - y) * g' y) ^ 2, ?_, ?_⟩
  · refine Finset.measurable_sum _ fun w _ => ?_
    have h : StronglyMeasurable (fun p : ℝ × Vec d =>
        ∫ y, heatKernelDerivFormula (List.ofFn w) (p.1, p.2 - y) * g' y) := by
      refine StronglyMeasurable.integral_prod_right' (f := fun q : (ℝ × Vec d) × Vec d =>
        heatKernelDerivFormula (List.ofFn w) (q.1.1, q.1.2 - q.2) * g' q.2) ?_
      exact (((measurable_heatKernelDerivFormula _).comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
        (hg'm.comp measurable_snd)).stronglyMeasurable
    exact h.measurable.pow_const 2
  · intro t ht x
    simp only [heatGradSq, kconv_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hgg'] with y hy
    rw [hy, heatKernelDeriv_eq_formula ht]

/-! ## Lemma D.3 -/

/-- The finite sums over the words of length `a + b`, split into words of lengths `a` and `b`. -/
def finAppendEquiv (a b : ℕ) (β : Type*) : (Fin a → β) × (Fin b → β) ≃ (Fin (a + b) → β) where
  toFun p := Fin.append p.1 p.2
  invFun w := (fun i => w (Fin.castAdd b i), fun i => w (Fin.natAdd a i))
  left_inv _ := Prod.ext (funext fun i => Fin.append_left _ _ i)
    (funext fun i => Fin.append_right _ _ i)
  right_inv _ := Fin.append_castAdd_natAdd

/-- `|∇^{α + k'} Φ(t, ·) ∗ u|² = ∑_{|l| = α} |∇^{k'} Φ(t, ·) ∗ ∂^l u|²` for `u ∈ H^α`. -/
theorem heatGradSq_add_eq {α : ℕ} {u : Vec d → ℝ} {g : List (Fin d) → Vec d → ℝ}
    (hS : IsSobolevFamily α u g) {t : ℝ} (ht : 0 < t) (k' : ℕ) (x : Vec d) :
    heatGradSq (α + k') t u x = ∑ v : Fin α → Fin d, heatGradSq k' t (g (List.ofFn v)) x := by
  unfold heatGradSq
  rw [← (finAppendEquiv α k' (Fin d)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  have hperm : heatKernelDeriv t (List.ofFn (Fin.append v w)) =
      heatKernelDeriv t ((List.ofFn v).reverse ++ List.ofFn w) := by
    rw [List.ofFn_fin_append]
    exact foldr_coordinateDerivative_perm (contDiff_euclideanHeatKernel t)
      ((List.reverse_perm _).symm.append_right _)
  have h := kconv_heatKernelDeriv_append_eq hS ht (List.ofFn w) x (List.ofFn v).reverse []
    (by simp)
  rw [hS.nil, List.reverse_reverse, List.append_nil] at h
  change kconv (heatKernelDeriv t (List.ofFn (Fin.append v w))) u x ^ 2 = _
  rw [hperm, h]

/-- **Lemma D.3.** For `α, k ∈ ℕ` with `α < k` there is `C(α, k, d)` such that for every
`u ∈ H^α(ℝ^d)`, `(∫_0^∞ t^{k-α} ‖∇^k Φ(t, ·) ∗ u‖²_{L²(ℝ^d)} dt/t)^{1/2} ≤ C [u]_{H^α(ℝ^d)}` (D.5),
where `[u]²_{H^α(ℝ^d)} = ∫ ∑_{|l| = α} |∂^l u|²`. -/
theorem lemmaD3 (α k : ℕ) (hαk : α < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Vec d → ℝ) (g : List (Fin d) → Vec d → ℝ),
      IsSobolevFamily α u g →
        (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (k - α) / t) *
            ∫⁻ x, ENNReal.ofReal (heatGradSq k t u x)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal C *
            (∫⁻ x, ENNReal.ofReal (∑ v : Fin α → Fin d, g (List.ofFn v) x ^ 2)) ^ (1 / 2 : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = α + (n + 1) := ⟨k - α - 1, by omega⟩
  obtain ⟨C, hC0, hC⟩ := lintegral_heatGradSq_le (d := d) n
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun u g hS => ?_⟩
  have hgv : ∀ v : Fin α → Fin d, MemLp (g (List.ofFn v)) 2 volume := fun v =>
    hS.memLp _ (by simp)
  have hmeas : ∀ v : Fin α → Fin d, ∃ H : ℝ × Vec d → ℝ, Measurable H ∧
      ∀ t, 0 < t → ∀ x, heatGradSq (n + 1) t (g (List.ofFn v)) x = H (t, x) := fun v =>
    exists_measurable_heatGradSq (n + 1) (hgv v).aestronglyMeasurable
  choose H hHm hH using hmeas
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (α + (n + 1) - α) / t) *
          ∫⁻ x, ENNReal.ofReal (heatGradSq (α + (n + 1)) t u x) =
        ∑ v : Fin α → Fin d, ENNReal.ofReal (t ^ n) * ∫⁻ x, ENNReal.ofReal (H v (t, x)) := by
    intro t ht
    have ht : 0 < t := ht
    have hpow : t ^ (α + (n + 1) - α) / t = t ^ n := by
      rw [Nat.add_sub_cancel_left, pow_succ, mul_div_cancel_right₀ _ ht.ne']
    rw [hpow, ← Finset.mul_sum]
    congr 1
    simp_rw [heatGradSq_add_eq hS ht (n + 1), hH _ t ht]
    rw [← lintegral_finsetSum' (f := fun v x => ENNReal.ofReal (H v (t, x))) _ fun v _ =>
      ((hHm v).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact ENNReal.ofReal_sum_of_nonneg fun v _ => by
      rw [← hH v t ht x]
      exact heatGradSq_nonneg _ _ _ _
  have hsq : ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (α + (n + 1) - α) / t) *
        ∫⁻ x, ENNReal.ofReal (heatGradSq (α + (n + 1)) t u x) ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (∑ v : Fin α → Fin d, g (List.ofFn v) x ^ 2) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_finsetSum'
      (f := fun v t => ENNReal.ofReal (t ^ n) * ∫⁻ x, ENNReal.ofReal (H v (t, x))) _ fun v _ =>
      ((measurable_id.pow_const n).ennreal_ofReal.mul
        (hHm v).ennreal_ofReal.lintegral_prod_right').aemeasurable]
    have hsum : ∫⁻ x, ENNReal.ofReal (∑ v : Fin α → Fin d, g (List.ofFn v) x ^ 2) =
        ∑ v : Fin α → Fin d, ∫⁻ x, ENNReal.ofReal (g (List.ofFn v) x ^ 2) := by
      rw [← lintegral_finsetSum' _ fun v _ =>
        ((hgv v).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal]
      exact lintegral_congr fun x => ENNReal.ofReal_sum_of_nonneg fun v _ => sq_nonneg _
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n) * ∫⁻ x, ENNReal.ofReal (H v (t, x))
        = ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n) *
            ∫⁻ x, ENNReal.ofReal (heatGradSq (n + 1) t (g (List.ofFn v)) x) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          simp_rw [hH v t ht]
      _ ≤ _ := hC _ (hgv v)
  calc (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (α + (n + 1) - α) / t) *
          ∫⁻ x, ENNReal.ofReal (heatGradSq (α + (n + 1)) t u x)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal (∑ v : Fin α → Fin d, g (List.ofFn v) x ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg hC0
          (by norm_num), Real.sqrt_eq_rpow]

end QSH
