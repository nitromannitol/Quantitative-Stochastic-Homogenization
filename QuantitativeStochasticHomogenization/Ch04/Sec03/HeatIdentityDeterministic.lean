import QuantitativeStochasticHomogenization.Ch04.Sec03.AnisotropicGaussian
import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentityGaussianTests
import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentitySublinear

/-!
# The heat identity (H) for a fixed coefficient field

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the heat identity (H) of the route of Proposition 4.10.

Let `ā = Qᵀ diag(λ) Q` with `Q` orthogonal and `1 ≤ λ_k ≤ Λ`, let `g` be the weak gradient of `φ` and
let `a(e + g)` be weakly divergence-free, with `φ`, `g` and `a(e + g)` integrable against every
heat kernel and `φ` sublinear in the sense `∫ Φ_s(x - y) |φ(y)| dy = o(√s)`. Write
`Ξ = (a - ā)(e + g)`. For `r > 0`, `u₀ = r²/2` and `u ≥ u₀` let `B(u) = r² I + 2(u - u₀) ā` and
`E(u) = B(u) - u I`, so that `u I ≤ E(u) ≤ 2Λ u I`. With `G_M` the Gaussian of covariance `2M`,
`F(u) = ∫ G_{B(u)}(z - y) ŵ · g(y) dy` satisfies

* `F(u₀) = ŵ · ∫ Φ_{z,r} g` since `B(u₀) = r² I`;
* `F'(u) = 2 ∑_m λ_m ∫ ∂²_{q_m} G_B (z - y) ŵ · g(y) dy`, by the heat equation in each
  coordinate of the eigenframe of `ā`;
* by the symmetry of the weak second derivatives of `φ`, the equation `∇ · a(e + g) = 0` tested
  against Gaussian tests, and `∫ ā e · ∇ψ = 0`:
  `F'(u) = -2 ∫ ∑_{k,m} (Qŵ)_k (QΞ(y))_m ∂_k ∂_m G_B(Q(z - y)) dy`;
* by the splitting `G_B = G_E ∗ Φ_u` and Fubini's theorem:
  `F'(u) = -2 ∫ ∑_{k,m} (Qŵ)_k ∂_k ∂_m G_E(Q x) (Q C_u(z - x))_m dx` with
  `C_u(w) = ∫ Φ(u, w - y) Ξ(y) dy`, the commutator at scale `√u`;
* the Hessian bound gives `|F'(u)| ≤ ∫ k(u, x) |C_u(z - x)| dx` with
  `k(u, x) = (8Λ + 1) u⁻¹ (4πu)^{-d/2} e^{-|x|²/(16Λu)}`;
* `F(T) → 0` as `T → ∞`: after the weak integration by parts `F(T) = ∫ φ ∂_ŵ G_{B(T)}(z - ·)` and
  the gradient bound, `|F(T)| ≤ C T^{-1/2} ∫ Φ_{4ΛT}(z - y) |φ(y)| dy = o(1)`.

Hence `|∫ Φ_{z,r} g| ≤ ∫⁻_{u > u₀} ∫⁻ K(u, x) |C_u(z - x)| dx du` for every kernel `K` bounding the
Hessian term (`heatIdentity_bound_of_kernel`), in particular for the isotropic kernel `k`
(`heatIdentity_bound`) and for the sharp kernel `u⁻¹(1 + ½ (Qx)·E⁻¹(Qx)) G_E(Qx)` of mass `(d + 1)/u`
(`heatIdentity_bound_sharp`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff Matrix

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Gaussian integrability -/

/-- `f` is integrable against every heat kernel. -/
def GaussianIntegrable (f : Vec d → ℝ) : Prop :=
  AEStronglyMeasurable f volume ∧
    ∀ s : ℝ, 0 < s → ∀ x : Vec d, Integrable (fun y => euclideanHeatKernel s (x - y) * |f y|)

namespace GaussianIntegrable

theorem continuous_heatKernel_comp_sub (s : ℝ) (x : Vec d) :
    Continuous fun y : Vec d => euclideanHeatKernel s (x - y) :=
  (continuous_euclideanHeatKernel s).comp (continuous_const.sub continuous_id)

theorem const (c : ℝ) : GaussianIntegrable (fun _ : Vec d => c) :=
  ⟨aestronglyMeasurable_const, fun _ hs x =>
    ((integrable_euclideanHeatKernel hs).comp_sub_left x).mul_const _⟩

theorem mono {f g : Vec d → ℝ} (hg : GaussianIntegrable g) (hfm : AEStronglyMeasurable f volume)
    (hfg : ∀ y, |f y| ≤ |g y|) : GaussianIntegrable f :=
  ⟨hfm, fun s hs x => integrable_heatKernel_mul_abs_of_le hs (hg.2 s hs x) hfm hfg⟩

theorem add {f g : Vec d → ℝ} (hf : GaussianIntegrable f) (hg : GaussianIntegrable g) :
    GaussianIntegrable (fun y => f y + g y) := by
  refine ⟨hf.1.add hg.1, fun s hs x => ?_⟩
  refine ((hf.2 s hs x).add (hg.2 s hs x)).mono'
    ((continuous_heatKernel_comp_sub s x).aestronglyMeasurable.mul
      (continuous_abs.comp_aestronglyMeasurable (hf.1.add hg.1)))
    (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ euclideanHeatKernel s (x - y) := euclideanHeatKernel_nonneg hs.le _
  show ‖euclideanHeatKernel s (x - y) * |f y + g y|‖ ≤
    euclideanHeatKernel s (x - y) * |f y| + euclideanHeatKernel s (x - y) * |g y|
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg h0, ← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_add_le _ _) h0

theorem const_mul (c : ℝ) {f : Vec d → ℝ} (hf : GaussianIntegrable f) :
    GaussianIntegrable (fun y => c * f y) := by
  refine ⟨hf.1.const_mul c, fun s hs x => ?_⟩
  refine ((hf.2 s hs x).const_mul |c|).congr (Eventually.of_forall fun y => ?_)
  simp only [abs_mul]
  ring

theorem neg {f : Vec d → ℝ} (hf : GaussianIntegrable f) : GaussianIntegrable (fun y => -f y) :=
  mono hf hf.1.neg fun y => by rw [abs_neg]

theorem sub {f g : Vec d → ℝ} (hf : GaussianIntegrable f) (hg : GaussianIntegrable g) :
    GaussianIntegrable (fun y => f y - g y) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sum {ι : Type*} (t : Finset ι) {f : ι → Vec d → ℝ}
    (hf : ∀ i ∈ t, GaussianIntegrable (f i)) : GaussianIntegrable (fun y => ∑ i ∈ t, f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using const (d := d) 0
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i t)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem integrable_mul {f ψ : Vec d → ℝ} (hf : GaussianIntegrable f)
    (hψm : AEStronglyMeasurable ψ volume) {s B : ℝ} {x : Vec d} (hs : 0 < s)
    (hψ : ∀ y, |ψ y| ≤ B * euclideanHeatKernel s (x - y)) :
    Integrable (fun y => f y * ψ y) :=
  integrable_mul_of_gaussian (hf.2 s hs x) hf.1 hψm hψ

theorem integrable_heatKernel_mul {f : Vec d → ℝ} (hf : GaussianIntegrable f) {s : ℝ} (hs : 0 < s)
    (x : Vec d) : Integrable (fun y => euclideanHeatKernel s (x - y) * f y) := by
  have h := hf.integrable_mul (ψ := fun y => euclideanHeatKernel s (x - y))
    (continuous_heatKernel_comp_sub s x).aestronglyMeasurable (B := 1) hs fun y => by
      rw [one_mul, abs_of_nonneg (euclideanHeatKernel_nonneg hs.le _)]
  exact h.congr (Eventually.of_forall fun y => mul_comm _ _)

end GaussianIntegrable

theorem gaussianIntegrable_dot (v : Vec d) {g : Vec d → Vec d}
    (hg : ∀ k, GaussianIntegrable (fun y => g y k)) : GaussianIntegrable (fun y => dot v (g y)) := by
  unfold dot
  exact GaussianIntegrable.sum _ fun k _ => (hg k).const_mul (v k)

theorem gaussianIntegrable_mulVec (M : Mat d) {g : Vec d → Vec d}
    (hg : ∀ k, GaussianIntegrable (fun y => g y k)) (m : Fin d) :
    GaussianIntegrable (fun y => (M *ᵥ g y) m) := by
  simp only [Matrix.mulVec, dotProduct]
  exact GaussianIntegrable.sum _ fun k _ => (hg k).const_mul (M m k)

/-! ## Bounds for the rotated products -/

theorem euclideanNorm_le_sum_abs (v : Vec d) : euclideanNorm v ≤ ∑ i, |v i| := by
  have h0 : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold euclideanNorm euclideanSq dot
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, v i * v i = ∑ i, |v i| ^ 2 := Finset.sum_congr rfl fun i _ => by rw [sq_abs, sq]
    _ ≤ (∑ i, |v i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

theorem measurable_rotKernel (Q : Mat d) (t : Fin d → ℝ) (n : Fin d → ℕ) (z : Vec d) :
    Measurable (rotKernel Q t n z) :=
  (contDiff_rotKernel Q t n z).continuous.measurable

/-- Gaussian majorant of a rotated product. -/
theorem exists_abs_rotKernel_le {Q : Mat d} (hQ : Q.transpose * Q = 1) {τ₁ τ₂ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) {b : Fin d → ℝ} (hb : ∀ k, τ₁ ≤ b k ∧ b k ≤ τ₂)
    (n : Fin d → ℕ) (z : Vec d) :
    ∃ B : ℝ, ∀ y, |rotKernel Q b n z y| ≤ B * euclideanHeatKernel (2 * τ₂) (z - y) := by
  obtain ⟨B, -, hB⟩ := exists_abs_anisoKernel_le n hτ₁ hτ
  refine ⟨B, fun y => ?_⟩
  have h := hB b hb (Q *ᵥ (z - y))
  rwa [euclideanHeatKernel_mulVec_of_orthogonal hQ] at h

/-- Gaussian majorants of a rotated product and of its gradient. -/
theorem exists_rotKernel_bounds {Q : Mat d} (hQ : Q.transpose * Q = 1) {τ₁ τ₂ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) {b : Fin d → ℝ} (hb : ∀ k, τ₁ ≤ b k ∧ b k ≤ τ₂)
    {n : Fin d → ℕ} (hn : ∀ k, n k ≤ 1) (z : Vec d) :
    ∃ B B' : ℝ, (∀ y, |rotKernel Q b n z y| ≤ B * euclideanHeatKernel (2 * τ₂) (z - y)) ∧
      ∀ y, euclideanNorm (gradient (rotKernel Q b n z) y) ≤
        B' * euclideanHeatKernel (2 * τ₂) (z - y) := by
  have hb0 : ∀ k, 0 < b k := fun k => hτ₁.trans_le (hb k).1
  obtain ⟨B, -, hB⟩ := exists_abs_anisoKernel_le n hτ₁ hτ
  have hBj := fun j : Fin d => exists_abs_anisoKernel_le (n + Pi.single j 1) hτ₁ hτ
  choose Bj hBj0 hBjb using hBj
  refine ⟨B, ∑ i, ∑ j, |Q j i| * Bj j, fun y => ?_, fun y => ?_⟩
  · have h := hB b hb (Q *ᵥ (z - y))
    rwa [euclideanHeatKernel_mulVec_of_orthogonal hQ] at h
  · refine (euclideanNorm_le_sum_abs _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [gradient_rotKernel Q hb0 hn z y i, abs_neg, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h := hBjb j b hb (Q *ᵥ (z - y))
    rwa [euclideanHeatKernel_mulVec_of_orthogonal hQ] at h

/-- `dot v ∇ψ = D_v ψ`. -/
theorem dot_gradient_eq_fderiv (ψ : Vec d → ℝ) (y v : Vec d) :
    dot v (gradient ψ y) = fderiv ℝ ψ y v := by
  rw [fderiv_apply_eq_sum_coordinateDerivative (χ := ψ) y v]
  rfl

theorem dot_gradient_rotKernel (Q : Mat d) {t : Fin d → ℝ} (ht : ∀ k, 0 < t k)
    {n : Fin d → ℕ} (hn : ∀ k, n k ≤ 1) (z y v : Vec d) :
    dot v (gradient (rotKernel Q t n z) y) =
      -∑ j, (Q *ᵥ v) j * rotKernel Q t (n + Pi.single j 1) z y := by
  rw [dot_gradient_eq_fderiv, fderiv_rotKernel_apply Q ht hn]

theorem single_le_one (k j : Fin d) : (Pi.single k 1 : Fin d → ℕ) j ≤ 1 := by
  classical
  rw [Pi.single_apply]
  split_ifs <;> simp

/-! ## The time integral of the derivative -/

/-- **The fundamental theorem of calculus in time, integrated in space**: for affine times
`t_k(u) = α_k + β_k u` in `[τ₁, τ₂]` on `[u₀, T]`,
`∫ G_{t(T)}(Q(z - y)) h(y) dy - ∫ G_{t(u₀)}(Q(z - y)) h(y) dy =
  ∫_{u₀}^T ∫ ∑_m β_m ∂²_m G_{t(u)}(Q(z - y)) h(y) dy du`. -/
theorem integral_rotKernel_sub_eq_integral {Q : Mat d} (hQ : Q.transpose * Q = 1)
    {α β : Fin d → ℝ} {u₀ T τ₁ τ₂ : ℝ} (hT : u₀ ≤ T) (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂)
    (hb : ∀ u ∈ Icc u₀ T, ∀ k, τ₁ ≤ α k + β k * u ∧ α k + β k * u ≤ τ₂)
    {h : Vec d → ℝ} (hh : GaussianIntegrable h) (z : Vec d) :
    (∫ y, rotKernel Q (fun k => α k + β k * T) 0 z y * h y) -
        ∫ y, rotKernel Q (fun k => α k + β k * u₀) 0 z y * h y =
      ∫ u in Ioc u₀ T, ∫ y,
        (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) * h y := by
  set t : ℝ → Fin d → ℝ := fun u k => α k + β k * u with ht
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  obtain ⟨B0, -, hB0⟩ := exists_abs_anisoKernel_le (0 : Fin d → ℕ) hτ₁ hτ
  have hB2 := fun m : Fin d => exists_abs_anisoKernel_le (Pi.single m 2 : Fin d → ℕ) hτ₁ hτ
  choose B2 hB20 hB2b using hB2
  set C := ∑ m, |β m| * B2 m with hC
  have hDb : ∀ u ∈ Icc u₀ T, ∀ y, |∑ m, β m * rotKernel Q (t u) (Pi.single m 2) z y| ≤
      C * euclideanHeatKernel (2 * τ₂) (z - y) := by
    intro u hu y
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hC, Finset.sum_mul]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 := hB2b m (t u) (hb u hu) (Q *ᵥ (z - y))
    rwa [euclideanHeatKernel_mulVec_of_orthogonal hQ] at h1
  have htm : Measurable fun p : ℝ × Vec d => t p.1 := by
    show Measurable fun p : ℝ × Vec d => fun k => α k + β k * p.1
    fun_prop
  have hwm : Measurable fun p : ℝ × Vec d => Q *ᵥ (z - p.2) :=
    ((continuous_mulVec Q).comp (continuous_const.sub continuous_snd)).measurable
  have hDm : Measurable fun p : ℝ × Vec d =>
      ∑ m, β m * rotKernel Q (t p.1) (Pi.single m 2) z p.2 :=
    Finset.measurable_sum _ fun m _ => measurable_const.mul
      ((measurable_anisoKernel_uncurry _).comp (htm.prodMk hwm))
  have hftc : ∀ y, rotKernel Q (t T) 0 z y - rotKernel Q (t u₀) 0 z y =
      ∫ u in Ioc u₀ T, ∑ m, β m * rotKernel Q (t u) (Pi.single m 2) z y := by
    intro y
    rw [← intervalIntegral.integral_of_le hT]
    have hder : ∀ u ∈ Icc u₀ T, HasDerivAt (fun u => rotKernel Q (t u) 0 z y)
        (∑ m, β m * rotKernel Q (t u) (Pi.single m 2) z y) u := fun u hu =>
      hasDerivAt_anisoKernel_time (fun k => hτ₁.trans_le (hb u hu k).1) (Q *ᵥ (z - y))
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (fun u hu => (hder u hu).continuousAt.continuousWithinAt)
      (fun u hu => hder u (Ioo_subset_Icc_self hu)) ?_).symm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine (integrable_const (C * euclideanHeatKernel (2 * τ₂) (z - y))).mono'
      (hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_eq_abs]
    exact hDb u (Ioc_subset_Icc_self hu) y
  have hendT : ∀ k, τ₁ ≤ t T k ∧ t T k ≤ τ₂ := hb T ⟨hT, le_rfl⟩
  have hend0 : ∀ k, τ₁ ≤ t u₀ k ∧ t u₀ k ≤ τ₂ := hb u₀ ⟨le_rfl, hT⟩
  have hbd : ∀ u : ℝ, (∀ k, τ₁ ≤ t u k ∧ t u k ≤ τ₂) → ∀ y,
      |rotKernel Q (t u) 0 z y| ≤ B0 * euclideanHeatKernel (2 * τ₂) (z - y) := by
    intro u hu y
    have h1 := hB0 (t u) hu (Q *ᵥ (z - y))
    rwa [euclideanHeatKernel_mulVec_of_orthogonal hQ] at h1
  have hiT : Integrable (fun y => rotKernel Q (t T) 0 z y * h y) := by
    have := hh.integrable_mul (measurable_rotKernel Q (t T) 0 z).aestronglyMeasurable
      (by positivity : (0 : ℝ) < 2 * τ₂) (hbd T hendT)
    simpa [mul_comm] using this
  have hi0 : Integrable (fun y => rotKernel Q (t u₀) 0 z y * h y) := by
    have := hh.integrable_mul (measurable_rotKernel Q (t u₀) 0 z).aestronglyMeasurable
      (by positivity : (0 : ℝ) < 2 * τ₂) (hbd u₀ hend0)
    simpa [mul_comm] using this
  rw [← integral_sub hiT hi0]
  have heq : ∀ y, rotKernel Q (t T) 0 z y * h y - rotKernel Q (t u₀) 0 z y * h y =
      ∫ u in Ioc u₀ T, (∑ m, β m * rotKernel Q (t u) (Pi.single m 2) z y) * h y := by
    intro y
    rw [← sub_mul, hftc y, integral_mul_const]
  rw [integral_congr_ae (Eventually.of_forall heq)]
  refine integral_integral_swap ?_
  have hG : Integrable (fun p : Vec d × ℝ =>
      (C * (euclideanHeatKernel (2 * τ₂) (z - p.1) * |h p.1|)) * 1)
      ((volume : Measure (Vec d)).prod (volume.restrict (Ioc u₀ T))) :=
    ((hh.2 (2 * τ₂) (by positivity) z).const_mul C).mul_prod (integrable_const (1 : ℝ))
  refine hG.mono' ((hDm.comp measurable_swap).aestronglyMeasurable.mul hh.1.comp_fst) ?_
  have hae := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
    (ν := volume.restrict (Ioc u₀ T))).ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with p hp
  change ‖(∑ m, β m * rotKernel Q (t p.2) (Pi.single m 2) z p.1) * h p.1‖ ≤
    C * (euclideanHeatKernel (2 * τ₂) (z - p.1) * |h p.1|) * 1
  rw [Real.norm_eq_abs, abs_mul, mul_one]
  calc |∑ m, β m * rotKernel Q (t p.2) (Pi.single m 2) z p.1| * |h p.1|
      ≤ (C * euclideanHeatKernel (2 * τ₂) (z - p.1)) * |h p.1| :=
        mul_le_mul_of_nonneg_right (hDb p.2 (Ioc_subset_Icc_self hp) p.1) (abs_nonneg _)
    _ = _ := by ring

/-! ## The three steps at a fixed time -/

theorem mulVec_transpose_mulVec_single {Q : Mat d} (hQ : Q.transpose * Q = 1) (m : Fin d) :
    Q *ᵥ (Q.transpose *ᵥ Pi.single m 1) = Pi.single m 1 := by
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hQ, Matrix.one_mulVec]

theorem dot_transpose_mulVec_single (Q : Mat d) (m : Fin d) (v : Vec d) :
    dot (Q.transpose *ᵥ Pi.single m 1) v = (Q *ᵥ v) m := by
  classical
  unfold dot
  change (Q.transpose *ᵥ Pi.single m 1) ⬝ᵥ v = (Q *ᵥ v) m
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    dotProduct_single_one]

theorem sum_single_mul (m : Fin d) (F : Fin d → ℝ) :
    ∑ j, (Pi.single m 1 : Vec d) j * F j = F m := by
  classical
  simp [Pi.single_apply]

theorem single_add_single_self (m : Fin d) :
    (Pi.single m 1 + Pi.single m 1 : Fin d → ℕ) = Pi.single m 2 := by
  rw [← Pi.single_add]

theorem integrable_dot_gradient_of_gaussian {F : Vec d → Vec d} (hF : ∀ k, GaussianIntegrable (fun y => F y k))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {s B' : ℝ} (hs : 0 < s) {x₀ : Vec d}
    (hψg : ∀ y, euclideanNorm (gradient ψ y) ≤ B' * euclideanHeatKernel s (x₀ - y)) :
    Integrable (fun y => dot (F y) (gradient ψ y)) := by
  unfold dot
  refine integrable_finsetSum _ fun k _ => (hF k).integrable_mul (x := x₀) (B := B')
    (contDiff_coordinateDerivative_top hψ k).continuous.aestronglyMeasurable hs fun y => ?_
  exact (abs_component_le_euclideanNorm (gradient ψ y) k).trans (hψg y)

/-- **The symmetry step**:
`∫ ∂²_m G_b(Q(z - ·)) (w · g) = ∫ (∑_k (Qw)_k ∂_m∂_k G_b(Q(z - ·))) (Qg)_m`. -/
theorem integral_rotKernel_two_mul_dot_eq {Q : Mat d} (hQ : Q.transpose * Q = 1)
    {φ : Vec d → ℝ} {g : Vec d → Vec d} (hgrad : HasWeakGradient Set.univ φ g)
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k)) {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂)
    {b : Fin d → ℝ} (hb : ∀ k, τ₁ ≤ b k ∧ b k ≤ τ₂) (z w : Vec d) (m : Fin d) :
    ∫ y, rotKernel Q b (Pi.single m 2) z y * dot w (g y) =
      ∫ y, (∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single m 1 + Pi.single k 1) z y) *
        (Q *ᵥ g y) m := by
  have hb0 : ∀ k, 0 < b k := fun k => hτ₁.trans_le (hb k).1
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  obtain ⟨B, B', hψb, hψg⟩ := exists_rotKernel_bounds hQ hτ₁ hτ hb (single_le_one m) z
  set qm : Vec d := Q.transpose *ᵥ Pi.single m 1 with hqm
  have hfd : ∀ y v, fderiv ℝ (rotKernel Q b (Pi.single m 1) z) y v =
      -∑ j, (Q *ᵥ v) j * rotKernel Q b (Pi.single m 1 + Pi.single j 1) z y := fun y v =>
    fderiv_rotKernel_apply Q hb0 (single_le_one m) z y v
  have hfq : ∀ y, fderiv ℝ (rotKernel Q b (Pi.single m 1) z) y qm =
      -rotKernel Q b (Pi.single m 2) z y := by
    intro y
    rw [hfd, hqm, mulVec_transpose_mulVec_single hQ, sum_single_mul, single_add_single_self]
  have hcomm := hgrad.integral_dot_mul_fderiv_comm (contDiff_rotKernel Q b _ z)
    (by positivity : (0 : ℝ) < 2 * τ₂) hψb hψg (fun k => (hgI k).2 _ (by positivity) z) w qm
  have hL : ∀ y, rotKernel Q b (Pi.single m 2) z y * dot w (g y) =
      -(dot w (g y) * fderiv ℝ (rotKernel Q b (Pi.single m 1) z) y qm) := by
    intro y
    rw [hfq y]
    ring
  have hR : ∀ y, (∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single m 1 + Pi.single k 1) z y) *
      (Q *ᵥ g y) m = -(dot qm (g y) * fderiv ℝ (rotKernel Q b (Pi.single m 1) z) y w) := by
    intro y
    rw [hfd y w, hqm, dot_transpose_mulVec_single]
    ring
  rw [integral_congr_ae (Eventually.of_forall hL), integral_congr_ae (Eventually.of_forall hR),
    integral_neg, integral_neg, hcomm]

/-- **The equation step**: by `∇ · a(e + g) = 0` and `∫ ā e · ∇ψ = 0`,
`∑_m λ_m ∫ (Qg)_m ∂_k∂_m G_b(Q(z - ·)) = -∫ ∑_m (QΞ)_m ∂_k∂_m G_b(Q(z - ·))`. -/
theorem sum_lam_integral_eq {Q : Mat d} (hQ : Q.transpose * Q = 1) {A : Mat d}
    {lam : Fin d → ℝ} (hA : ∀ v, Q *ᵥ (A *ᵥ v) = fun m => lam m * (Q *ᵥ v) m)
    {a : Vec d → Mat d} {e : Vec d} {g : Vec d → Vec d}
    (hdiv : HasWeakDivergence Set.univ (fun x => a x *ᵥ (e + g x)) (fun _ => 0))
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k))
    (hfI : ∀ k, GaussianIntegrable (fun y => (a y *ᵥ (e + g y)) k))
    {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) {b : Fin d → ℝ} (hb : ∀ k, τ₁ ≤ b k ∧ b k ≤ τ₂)
    (z : Vec d) (k : Fin d) :
    ∑ m, lam m * ∫ y, (Q *ᵥ g y) m * rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y =
      -∫ y, ∑ m, (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m *
        rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y := by
  have hb0 : ∀ k, 0 < b k := fun k => hτ₁.trans_le (hb k).1
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have hs : (0 : ℝ) < 2 * τ₂ := by positivity
  have hψs : ContDiff ℝ (⊤ : ℕ∞) (rotKernel Q b (Pi.single k 1) z) := contDiff_rotKernel Q b _ z
  obtain ⟨B, B', hψb, hψg⟩ := exists_rotKernel_bounds hQ hτ₁ hτ hb (single_le_one k) z
  have hdg : ∀ v y, dot v (gradient (rotKernel Q b (Pi.single k 1) z) y) =
      -∑ m, (Q *ᵥ v) m * rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y := fun v y =>
    dot_gradient_rotKernel Q hb0 (single_le_one k) z y v
  set Xi : Vec d → Vec d := fun y => a y *ᵥ (e + g y) - A *ᵥ (e + g y) with hXi
  have hAgI : ∀ j, GaussianIntegrable (fun y => (A *ᵥ g y) j) := gaussianIntegrable_mulVec A hgI
  have hXiI : ∀ j, GaussianIntegrable (fun y => Xi y j) := by
    intro j
    have h1 : GaussianIntegrable (fun y => (a y *ᵥ (e + g y)) j - ((A *ᵥ e) j + (A *ᵥ g y) j)) :=
      (hfI j).sub ((GaussianIntegrable.const _).add (hAgI j))
    refine h1.mono (by simpa [hXi, Matrix.mulVec_add] using h1.1) fun y => ?_
    simp [hXi, Matrix.mulVec_add]
  have hdiv0 : ∫ y, dot (a y *ᵥ (e + g y)) (gradient (rotKernel Q b (Pi.single k 1) z) y) = 0 :=
    hdiv.integral_dot_gradient_eq_zero_of_gaussian hψs hs hψb hψg fun j => (hfI j).2 _ hs z
  have hconst : ∫ y, dot (A *ᵥ e) (gradient (rotKernel Q b (Pi.single k 1) z) y) = 0 :=
    integral_dot_const_gradient_eq_zero _ hψs hs hψb hψg
  have hpt : ∀ y, dot (A *ᵥ g y) (gradient (rotKernel Q b (Pi.single k 1) z) y) = dot (a y *ᵥ (e + g y)) (gradient (rotKernel Q b (Pi.single k 1) z) y) -
      dot (Xi y) (gradient (rotKernel Q b (Pi.single k 1) z) y) - dot (A *ᵥ e) (gradient (rotKernel Q b (Pi.single k 1) z) y) := by
    intro y
    simp only [hXi, dot, Matrix.mulVec_add, Pi.sub_apply, Pi.add_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have i1 := integrable_dot_gradient_of_gaussian hfI hψs hs hψg
  have i2 := integrable_dot_gradient_of_gaussian hXiI hψs hs hψg
  have i12 : Integrable (fun y => dot (a y *ᵥ (e + g y)) (gradient (rotKernel Q b (Pi.single k 1) z) y) -
      dot (Xi y) (gradient (rotKernel Q b (Pi.single k 1) z) y)) := i1.sub i2
  have i3 := integrable_dot_gradient_of_gaussian (fun j => GaussianIntegrable.const (d := d) ((A *ᵥ e) j))
    hψs hs hψg
  have hAg : ∫ y, dot (A *ᵥ g y) (gradient (rotKernel Q b (Pi.single k 1) z) y) = -∫ y, dot (Xi y) (gradient (rotKernel Q b (Pi.single k 1) z) y) := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub i12 i3,
      integral_sub i1 i2, hdiv0, hconst]
    ring
  have hint : ∀ m, Integrable (fun y => lam m * ((Q *ᵥ g y) m *
      rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y)) := by
    intro m
    obtain ⟨Bm, hBm⟩ := exists_abs_rotKernel_le hQ hτ₁ hτ hb (Pi.single k 1 + Pi.single m 1) z
    exact ((gaussianIntegrable_mulVec Q hgI m).integrable_mul
      (measurable_rotKernel Q b _ z).aestronglyMeasurable hs hBm).const_mul _
  calc ∑ m, lam m * ∫ y, (Q *ᵥ g y) m * rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y
      = ∫ y, ∑ m, lam m * ((Q *ᵥ g y) m *
          rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y) := by
        rw [integral_finsetSum _ fun m _ => hint m]
        exact Finset.sum_congr rfl fun m _ => (integral_const_mul _ _).symm
    _ = ∫ y, -dot (A *ᵥ g y) (gradient (rotKernel Q b (Pi.single k 1) z) y) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [hdg (A *ᵥ g y) y, hA (g y), neg_neg]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = ∫ y, dot (Xi y) (gradient (rotKernel Q b (Pi.single k 1) z) y) := by rw [integral_neg, hAg, neg_neg]
    _ = -∫ y, ∑ m, (Q *ᵥ Xi y) m * rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y := by
        rw [← integral_neg]
        exact integral_congr_ae (Eventually.of_forall fun y => hdg (Xi y) y)

/-- **The splitting step**: `G_{e+u} = G_e ∗ Φ_u` and Fubini's theorem give
`∫ ξ(y) G^{(n)}_{e+u}(Q(z - y)) dy = ∫ G^{(n)}_e(Q x) (∫ Φ(u, z - x - y) ξ(y) dy) dx`, and the
right integrand is integrable. -/
theorem integral_mul_rotKernel_split {Q : Mat d} (hQ : Q.transpose * Q = 1) {e b : Fin d → ℝ}
    {u : ℝ} (hu : 0 < u) {n : Fin d → ℕ}
    (hsplit : ∀ w, ∫ y, anisoKernel e n (w - y) * euclideanHeatKernel u y = anisoKernel b n w)
    {s B : ℝ} (hs : 0 < s) (hB : ∀ w, |anisoKernel e n w| ≤ B * euclideanHeatKernel s w)
    {ξ : Vec d → ℝ} (hξ : GaussianIntegrable ξ) (z : Vec d) :
    (∫ y, ξ y * anisoKernel b n (Q *ᵥ (z - y)) =
      ∫ x, anisoKernel e n (Q *ᵥ x) * ∫ y, euclideanHeatKernel u (z - x - y) * ξ y) ∧
    Integrable (fun x => anisoKernel e n (Q *ᵥ x) * ∫ y, euclideanHeatKernel u (z - x - y) * ξ y) := by
  set F : Vec d → Vec d → ℝ := fun y x =>
    ξ y * (anisoKernel e n (Q *ᵥ x) * euclideanHeatKernel u (z - y - x)) with hF
  have hAc : Continuous (anisoKernel e n) := (contDiff_anisoKernel e n).continuous
  have hFm : AEStronglyMeasurable (Function.uncurry F) ((volume : Measure (Vec d)).prod volume) := by
    refine hξ.1.comp_fst.mul (Continuous.aestronglyMeasurable ?_)
    exact (hAc.comp ((continuous_mulVec Q).comp continuous_snd)).mul
      ((continuous_euclideanHeatKernel u).comp ((continuous_const.sub continuous_fst).sub
        continuous_snd))
  have hB0 : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hB 0)
    exact nonneg_of_mul_nonneg_left h (by
      unfold euclideanHeatKernel
      positivity)
  have hMu : ∀ v : Vec d, euclideanHeatKernel u v ≤ (4 * Real.pi * u) ^ (-(d : ℝ) / 2) := by
    intro v
    unfold euclideanHeatKernel
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg (BaseExponent.euclideanSq_nonneg v) (by positivity))
  have hKs : Integrable (fun x : Vec d => euclideanHeatKernel s x) := integrable_euclideanHeatKernel hs
  have hpt : ∀ y x, ‖F y x‖ ≤ |ξ y| * B * (euclideanHeatKernel s x *
      euclideanHeatKernel u (z - y - x)) := by
    intro y x
    rw [hF, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg hu.le _)]
    have h1 := hB (Q *ᵥ x)
    rw [euclideanHeatKernel_mulVec_of_orthogonal hQ] at h1
    calc |ξ y| * (|anisoKernel e n (Q *ᵥ x)| * euclideanHeatKernel u (z - y - x))
        ≤ |ξ y| * ((B * euclideanHeatKernel s x) * euclideanHeatKernel u (z - y - x)) := by
          gcongr
          exact euclideanHeatKernel_nonneg hu.le _
      _ = _ := by ring
  have hconv : ∀ y, ∫ x, euclideanHeatKernel s x * euclideanHeatKernel u (z - y - x) =
      euclideanHeatKernel (u + s) (z - y) := by
    intro y
    have h := integral_euclideanHeatKernel_mul (d := d) hu hs (z - y) 0
    simp only [sub_zero] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hKu : ∀ y, Integrable (fun x => euclideanHeatKernel s x * euclideanHeatKernel u (z - y - x)) := by
    intro y
    refine (hKs.mul_const ((4 * Real.pi * u) ^ (-(d : ℝ) / 2))).mono'
      (Continuous.aestronglyMeasurable ((continuous_euclideanHeatKernel s).mul
        ((continuous_euclideanHeatKernel u).comp (continuous_const.sub continuous_id))))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (euclideanHeatKernel_nonneg hs.le _)
      (euclideanHeatKernel_nonneg hu.le _))]
    exact mul_le_mul_of_nonneg_left (hMu _) (euclideanHeatKernel_nonneg hs.le _)
  have hslice : ∀ y, Integrable (fun x => F y x) := by
    intro y
    refine ((hKu y).const_mul (|ξ y| * B)).mono'
      (Continuous.aestronglyMeasurable (continuous_const.mul ((hAc.comp (continuous_mulVec Q)).mul
        ((continuous_euclideanHeatKernel u).comp (continuous_const.sub continuous_id)))))
      (Eventually.of_forall fun x => hpt y x)
  have hnorm : ∀ y, ∫ x, ‖F y x‖ ≤ B * (euclideanHeatKernel (u + s) (z - y) * |ξ y|) := by
    intro y
    calc ∫ x, ‖F y x‖ ≤ ∫ x, |ξ y| * B *
          (euclideanHeatKernel s x * euclideanHeatKernel u (z - y - x)) :=
          integral_mono (hslice y).norm ((hKu y).const_mul _) (hpt y)
      _ = |ξ y| * B * euclideanHeatKernel (u + s) (z - y) := by rw [integral_const_mul, hconv]
      _ = _ := by ring
  have hFi : Integrable (Function.uncurry F) ((volume : Measure (Vec d)).prod volume) := by
    refine (integrable_prod_iff hFm).mpr ⟨Eventually.of_forall hslice, ?_⟩
    refine ((hξ.2 (u + s) (by positivity) z).const_mul B).mono' hFm.norm.integral_prod_right'
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact hnorm y
  have hL : ∀ y, ξ y * anisoKernel b n (Q *ᵥ (z - y)) = ∫ x, F y x := by
    intro y
    show _ = ∫ x, ξ y * (anisoKernel e n (Q *ᵥ x) * euclideanHeatKernel u (z - y - x))
    rw [integral_const_mul, integral_rotKernel_mul_heatKernel hQ hsplit (z - y)]
  have hR : ∀ x, anisoKernel e n (Q *ᵥ x) * ∫ y, euclideanHeatKernel u (z - x - y) * ξ y =
      ∫ y, F y x := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show _ = ξ y * (anisoKernel e n (Q *ᵥ x) * euclideanHeatKernel u (z - y - x))
    rw [show z - y - x = z - x - y by abel]
    ring
  refine ⟨?_, ?_⟩
  · rw [integral_congr_ae (Eventually.of_forall hL), integral_congr_ae (Eventually.of_forall hR)]
    exact integral_integral_swap hFi
  · exact hFi.integral_prod_right.congr (Eventually.of_forall fun x => (hR x).symm)

/-! ## The derivative at a fixed time -/

theorem mulVec_integral_apply (Q : Mat d) {K : Vec d → ℝ} {Xi : Vec d → Vec d}
    (hint : ∀ j, Integrable (fun y => K y * Xi y j)) (m : Fin d) :
    (Q *ᵥ fun j => ∫ y, K y * Xi y j) m = ∫ y, K y * (Q *ᵥ Xi y) m := by
  simp only [Matrix.mulVec, dotProduct]
  have hpt : ∀ y, K y * ∑ j, Q m j * Xi y j = ∑ j, Q m j * (K y * Xi y j) := fun y => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun j _ => (hint j).const_mul (Q m j)]
  exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

theorem single_add_single_comm (k m : Fin d) :
    (Pi.single m 1 + Pi.single k 1 : Fin d → ℕ) = Pi.single k 1 + Pi.single m 1 := add_comm _ _

/-- **The derivative of `F` at a fixed time**: with `b = E + u`,
`∫ (∑_m 2λ_m ∂²_m G_b(Q(z - y))) w · g(y) dy =
  -2 ∫ ∑_{k,m} (Qw)_k (Q C_u(z - x))_m ∂_k ∂_m G_E(Q x) dx`. -/
theorem integral_time_derivative_eq {Q : Mat d} (hQ : Q.transpose * Q = 1) {A : Mat d}
    {lam : Fin d → ℝ} (hA : ∀ v, Q *ᵥ (A *ᵥ v) = fun m => lam m * (Q *ᵥ v) m)
    {a : Vec d → Mat d} {e : Vec d} {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hgrad : HasWeakGradient Set.univ φ g)
    (hdiv : HasWeakDivergence Set.univ (fun x => a x *ᵥ (e + g x)) (fun _ => 0))
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k))
    (hfI : ∀ k, GaussianIntegrable (fun y => (a y *ᵥ (e + g y)) k))
    {u τ₁ τ₂ σ₁ σ₂ : ℝ} (hu : 0 < u) (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hσ₁ : 0 < σ₁)
    (hσ : σ₁ ≤ σ₂) {E b : Fin d → ℝ} (hEσ : ∀ k, σ₁ ≤ E k ∧ E k ≤ σ₂)
    (hbE : ∀ k, b k = E k + u) (hb : ∀ k, τ₁ ≤ b k ∧ b k ≤ τ₂) {β : Fin d → ℝ}
    (hβ : ∀ m, β m = 2 * lam m) (z w : Vec d) :
    ∫ y, (∑ m, β m * rotKernel Q b (Pi.single m 2) z y) * dot w (g y) =
      -2 * ∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
        (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j) m *
          anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x) := by
  simp only [hβ]
  have hE : ∀ k, 0 < E k := fun k => hσ₁.trans_le (hEσ k).1
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have hσ₂ : 0 < σ₂ := hσ₁.trans_le hσ
  have hs : (0 : ℝ) < 2 * τ₂ := by positivity
  have hhI : GaussianIntegrable (fun y => dot w (g y)) := gaussianIntegrable_dot w hgI
  have hXiI : ∀ j, GaussianIntegrable (fun y => (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j) := by
    intro j
    have hAe : GaussianIntegrable (fun y => (A *ᵥ (e + g y)) j) := by
      have h1 := (GaussianIntegrable.const (d := d) ((A *ᵥ e) j)).add
        (gaussianIntegrable_mulVec A hgI j)
      refine h1.mono ?_ fun y => ?_
      · refine h1.1.congr (Eventually.of_forall fun y => ?_)
        simp [Matrix.mulVec_add]
      · simp [Matrix.mulVec_add]
    exact (hfI j).sub hAe
  have hQXiI : ∀ m, GaussianIntegrable
      (fun y => (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m) := gaussianIntegrable_mulVec Q hXiI
  have hQgI : ∀ m, GaussianIntegrable (fun y => (Q *ᵥ g y) m) := gaussianIntegrable_mulVec Q hgI
  have hRint : ∀ (n : Fin d → ℕ) {f : Vec d → ℝ}, GaussianIntegrable f →
      Integrable (fun y => f y * rotKernel Q b n z y) := by
    intro n f hf
    obtain ⟨Bn, hBn⟩ := exists_abs_rotKernel_le hQ hτ₁ hτ hb n z
    exact hf.integrable_mul (measurable_rotKernel Q b n z).aestronglyMeasurable hs hBn
  -- the sum over m
  have hA1 : ∫ y, (∑ m, 2 * lam m * rotKernel Q b (Pi.single m 2) z y) * dot w (g y) =
      ∑ m, 2 * lam m * ∫ y, rotKernel Q b (Pi.single m 2) z y * dot w (g y) := by
    have hpt : ∀ y, (∑ m, 2 * lam m * rotKernel Q b (Pi.single m 2) z y) * dot w (g y) =
        ∑ m, 2 * lam m * (dot w (g y) * rotKernel Q b (Pi.single m 2) z y) := by
      intro y
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum _ fun m _ => (hRint _ hhI).const_mul _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  -- the symmetry of the weak second derivatives
  have hBC : ∀ m, ∫ y, rotKernel Q b (Pi.single m 2) z y * dot w (g y) =
      ∑ k, (Q *ᵥ w) k * ∫ y, (Q *ᵥ g y) m *
        rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y := by
    intro m
    rw [integral_rotKernel_two_mul_dot_eq hQ hgrad hgI hτ₁ hτ hb z w m]
    have hpt : ∀ y, (∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single m 1 + Pi.single k 1) z y) *
        (Q *ᵥ g y) m = ∑ k, (Q *ᵥ w) k * ((Q *ᵥ g y) m *
          rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y) := by
      intro y
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [single_add_single_comm]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum _ fun k _ => (hRint _ (hQgI m)).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  -- the corrector equation
  have hDE : ∑ m, 2 * lam m * ∫ y, rotKernel Q b (Pi.single m 2) z y * dot w (g y) =
      2 * ∑ k, (Q *ᵥ w) k * -∫ y, ∑ m, (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m *
        rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y := by
    simp only [hBC]
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sum_lam_integral_eq hQ hA hdiv hgI hfI hτ₁ hτ hb z k, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  -- the splitting with the heat kernel and Fubini's theorem
  have hbfun : (fun j => E j + u) = b := funext fun k => (hbE k).symm
  have hsplit0 := integral_anisoKernel_sub_mul_heatKernel hE hu
  have hsplit1 : ∀ k w, ∫ y, anisoKernel E (Pi.single k 1) (w - y) * euclideanHeatKernel u y =
      anisoKernel (fun j => E j + u) (Pi.single k 1) w := by
    intro k w
    have h1 := integral_anisoKernel_sub_mul_heatKernel_succ hE hu (n := 0) (fun _ => by simp)
      hsplit0 k w
    simp only [zero_add] at h1
    exact h1
  have hsplit2 : ∀ k m w, ∫ y, anisoKernel E (Pi.single k 1 + Pi.single m 1) (w - y) *
      euclideanHeatKernel u y = anisoKernel b (Pi.single k 1 + Pi.single m 1) w := by
    intro k m w
    rw [← hbfun]
    exact integral_anisoKernel_sub_mul_heatKernel_succ hE hu (single_le_one k) (hsplit1 k) m w
  have hEb : ∀ k m, ∃ B, ∀ w, |anisoKernel E (Pi.single k 1 + Pi.single m 1) w| ≤
      B * euclideanHeatKernel (2 * σ₂) w := by
    intro k m
    obtain ⟨B, -, hB⟩ := exists_abs_anisoKernel_le (Pi.single k 1 + Pi.single m 1) hσ₁ hσ
    exact ⟨B, hB E hEσ⟩
  have hFG : ∀ k, ∫ y, ∑ m, (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m *
      rotKernel Q b (Pi.single k 1 + Pi.single m 1) z y =
      ∑ m, ∫ x, anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x) *
        ∫ y, euclideanHeatKernel u (z - x - y) * (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m := by
    intro k
    rw [integral_finsetSum _ fun m _ => hRint _ (hQXiI m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    obtain ⟨B, hB⟩ := hEb k m
    exact (integral_mul_rotKernel_split hQ hu (hsplit2 k m) (by positivity) hB (hQXiI m) z).1
  have hFGi : ∀ k m, Integrable (fun x => anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x) *
      ∫ y, euclideanHeatKernel u (z - x - y) * (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m) := by
    intro k m
    obtain ⟨B, hB⟩ := hEb k m
    exact (integral_mul_rotKernel_split hQ hu (hsplit2 k m) (by positivity) hB (hQXiI m) z).2
  have hSC : ∀ x m, (∫ y, euclideanHeatKernel u (z - x - y) *
      (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m) =
      (Q *ᵥ fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
        (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j) m := by
    intro x m
    exact (mulVec_integral_apply Q (fun j => (hXiI j).integrable_heatKernel_mul hu (z - x)) m).symm
  rw [hA1, hDE]
  simp only [hFG]
  have hlast : ∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
      (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j) m *
        anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x) =
      ∑ k, (Q *ᵥ w) k * ∑ m, ∫ x, anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x) *
        ∫ y, euclideanHeatKernel u (z - x - y) *
          (Q *ᵥ (a y *ᵥ (e + g y) - A *ᵥ (e + g y))) m := by
    have hint : ∀ k m, Integrable (fun x => (Q *ᵥ w) k * (Q *ᵥ fun j =>
        ∫ y, euclideanHeatKernel u (z - x - y) * (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j) m *
          anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)) := by
      intro k m
      refine ((hFGi k m).const_mul ((Q *ᵥ w) k)).congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [hSC x m]
      ring
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ => hint k m]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun m _ => hint k m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hSC x m]
    ring
  rw [hlast]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-! ## The bound at a fixed time -/

theorem ofReal_integral_le_lintegral_ofReal' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

/-- The kernel of the heat identity: `(8Λ + 1) u⁻¹ (4πu)^{-d/2} e^{-|x|²/(16Λu)}`. -/
def heatIdentityKernel (d : ℕ) (Λ u : ℝ) (x : Vec d) : ℝ :=
  (8 * Λ + 1) * u⁻¹ * ((4 * Real.pi * u) ^ (-(d : ℝ) / 2) *
    Real.exp (-euclideanSq x / (16 * Λ * u)))

/-- **The derivative of `F` is bounded by the commutators**: for `u ≤ E_k ≤ 2Λu` and `|w| = 1`,
`|2 ∫ ∑_{k,m} (Qw)_k (Q C(x))_m ∂_k ∂_m G_E(Q x) dx| ≤ ∫⁻ k(u, x) |C(x)| dx`. -/
theorem ofReal_abs_hessian_integral_le {Q : Mat d} (hQ : Q.transpose * Q = 1) {Λ u : ℝ}
    (hΛ : 1 ≤ Λ) (hu : 0 < u) {E : Fin d → ℝ} (hE : ∀ k, u ≤ E k ∧ E k ≤ 2 * Λ * u)
    {w : Vec d} (hw : euclideanNorm w = 1) (C : Vec d → Vec d) :
    ENNReal.ofReal |-2 * ∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
        anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)| ≤
      ∫⁻ x, ENNReal.ofReal (heatIdentityKernel d Λ u x * euclideanNorm (C x)) := by
  have hK : 1 ≤ 2 * Λ := by linarith
  have hpt : ∀ x, 2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
      anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)| ≤
      heatIdentityKernel d Λ u x * euclideanNorm (C x) := by
    intro x
    have h := abs_hessian_anisoKernel_le hu hK hE (Q *ᵥ w) (Q *ᵥ C x) (Q *ᵥ x)
    rw [euclideanNorm_mulVec_of_orthogonal hQ, euclideanNorm_mulVec_of_orthogonal hQ, hw,
      euclideanSq_mulVec_of_orthogonal hQ, one_mul] at h
    unfold heatIdentityKernel
    calc 2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
          anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|
        ≤ 2 * ((2 * (2 * Λ) + 1 / 2) * u⁻¹ * ((4 * Real.pi * u) ^ (-(d : ℝ) / 2) *
            Real.exp (-euclideanSq x / (8 * (2 * Λ) * u))) * euclideanNorm (C x)) := by
          gcongr
      _ = _ := by
          rw [show 8 * (2 * Λ) * u = 16 * Λ * u by ring]
          ring
  rw [abs_mul, abs_neg, abs_two]
  calc ENNReal.ofReal (2 * |∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
        anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|)
      ≤ ENNReal.ofReal (∫ x, 2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
          anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
          anisoKernel E (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|) :=
        ofReal_integral_le_lintegral_ofReal' fun x => by positivity
    _ ≤ _ := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)

/-! ## The terminal value -/

/-- **The terminal value vanishes**: for `β₁ = 2T ≤ b_k ≤ 2ΛT = β₂` and `|w| = 1`,
`|∫ G_b(Q(z - y)) w · g(y) dy| ≤ (2Λ)^{d/2} √Λ T^{-1/2} ∫ Φ_{4ΛT}(z - y) |φ(y)| dy`, which is small
for large `T` by the sublinearity of `φ`. -/
theorem abs_integral_rotKernel_terminal_le {Q : Mat d} (hQ : Q.transpose * Q = 1) {Λ T : ℝ}
    (hΛ : 1 ≤ Λ) (hT : 0 < T) {b : Fin d → ℝ} (hb : ∀ k, 2 * T ≤ b k ∧ b k ≤ 2 * Λ * T)
    {φ : Vec d → ℝ} {g : Vec d → Vec d} (hgrad : HasWeakGradient Set.univ φ g)
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k)) (hφI : GaussianIntegrable φ)
    {w : Vec d} (hw : euclideanNorm w = 1) (z : Vec d) :
    |∫ y, rotKernel Q b 0 z y * dot w (g y)| ≤
      (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
        (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) *
          ∫ y, euclideanHeatKernel (4 * Λ * T) (z - y) * |φ y| := by
  have hβ₁ : 0 < 2 * T := by positivity
  have hβ : 2 * T ≤ 2 * Λ * T := by nlinarith
  have hb0 : ∀ k, 0 < b k := fun k => hβ₁.trans_le (hb k).1
  obtain ⟨B, B', hψb, hψg⟩ := exists_rotKernel_bounds hQ hβ₁ hβ hb (n := 0) (fun _ => by simp) z
  have hs : (0 : ℝ) < 2 * (2 * Λ * T) := by positivity
  -- the weak integration by parts in each coordinate
  have hparts : ∀ j, ∫ y, rotKernel Q b 0 z y * g y j =
      -∫ y, φ y * coordinateDerivative j (rotKernel Q b 0 z) y := by
    intro j
    have h := (hgrad j).integral_mul_coordinateDerivative_eq (contDiff_rotKernel Q b 0 z) hs hψb
      hψg (hφI.2 _ hs z) ((hgI j).2 _ hs z)
    rw [h, neg_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  have hint1 : ∀ j, Integrable (fun y => rotKernel Q b 0 z y * g y j) := fun j =>
    ((hgI j).integrable_mul (measurable_rotKernel Q b 0 z).aestronglyMeasurable hs hψb).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  have hdm : ∀ j, AEStronglyMeasurable (fun y => coordinateDerivative j (rotKernel Q b 0 z) y) volume :=
    fun j => (contDiff_coordinateDerivative_top (contDiff_rotKernel Q b 0 z) j).continuous.aestronglyMeasurable
  have hint2 : ∀ j, Integrable (fun y => φ y * coordinateDerivative j (rotKernel Q b 0 z) y) :=
    fun j => hφI.integrable_mul (hdm j) hs fun y =>
      (abs_component_le_euclideanNorm _ j).trans (hψg y)
  have hsum : ∫ y, rotKernel Q b 0 z y * dot w (g y) =
      ∫ y, φ y * ∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single k 1) z y := by
    have h1 : ∫ y, rotKernel Q b 0 z y * dot w (g y) =
        ∑ j, w j * ∫ y, rotKernel Q b 0 z y * g y j := by
      have hpt : ∀ y, rotKernel Q b 0 z y * dot w (g y) =
          ∑ j, w j * (rotKernel Q b 0 z y * g y j) := by
        intro y
        simp only [dot, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [integral_congr_ae (Eventually.of_forall hpt),
        integral_finsetSum _ fun j _ => (hint1 j).const_mul (w j)]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    have h2 : ∫ y, φ y * ∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single k 1) z y =
        -∑ j, w j * ∫ y, φ y * coordinateDerivative j (rotKernel Q b 0 z) y := by
      have hpt2 : ∀ y, φ y * ∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single k 1) z y =
          ∑ j, -(w j * (φ y * coordinateDerivative j (rotKernel Q b 0 z) y)) := by
        intro y
        have hf := fderiv_rotKernel_apply Q hb0 (n := 0) (fun _ => by simp) z y w
        rw [fderiv_apply_eq_sum_coordinateDerivative (χ := rotKernel Q b 0 z) y w] at hf
        simp only [zero_add] at hf
        rw [show (∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single k 1) z y) =
            -∑ j, w j * coordinateDerivative j (rotKernel Q b 0 z) y by rw [hf, neg_neg],
          mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [integral_congr_ae (Eventually.of_forall hpt2),
        integral_finsetSum _ fun j _ => (show Integrable (fun y => -(w j * (φ y *
          coordinateDerivative j (rotKernel Q b 0 z) y))) from ((hint2 j).const_mul (w j)).neg),
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [integral_neg, integral_const_mul]
    rw [h1, h2]
    simp only [hparts, mul_neg, Finset.sum_neg_distrib]
  rw [hsum]
  -- the pointwise bound
  have hgb : ∀ y, |∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single k 1) z y| ≤
      (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
        (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) * euclideanHeatKernel (4 * Λ * T) (z - y) := by
    intro y
    have h := abs_gradient_anisoKernel_le hβ₁ hβ hb (Q *ᵥ w) (Q *ᵥ (z - y))
    rw [euclideanNorm_mulVec_of_orthogonal hQ, hw, mul_one, euclideanSq_mulVec_of_orthogonal hQ,
      show 4 * Real.pi * (2 * T) = 8 * Real.pi * T by ring,
      show 8 * (2 * Λ * T) = 16 * Λ * T by ring, show 2 * (2 * T) = 4 * T by ring,
      show 16 * Λ * T = 4 * (4 * Λ * T) by ring, exp_neg_euclideanSq_eq (by positivity),
      show 4 * Real.pi * (4 * Λ * T) = 16 * Real.pi * Λ * T by ring] at h
    refine h.trans (le_of_eq ?_)
    rw [show (4 : ℝ) * (4 * Λ * T) = 16 * Λ * T by ring]
    ring
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
    ((hφI.2 _ (by positivity) z).const_mul _) (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [abs_mul]
  calc |φ y| * |∑ k, (Q *ᵥ w) k * rotKernel Q b (Pi.single k 1) z y|
      ≤ |φ y| * ((8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
        (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) * euclideanHeatKernel (4 * Λ * T) (z - y)) :=
        mul_le_mul_of_nonneg_left (hgb y) (abs_nonneg _)
    _ = _ := by ring

theorem terminal_constant_eq {Λ T : ℝ} (hΛ : 0 < Λ) (hT : 0 < T) :
    (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
      (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) * Real.sqrt (4 * Λ * T) =
      (2 * Λ) ^ ((d : ℝ) / 2) * (2 * Λ) := by
  have h1 : (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) =
      (2 * Λ) ^ ((d : ℝ) / 2) * (8 * Real.pi * T) ^ ((d : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have h2 : Real.sqrt (16 * Λ * T) * Real.sqrt (4 * Λ * T) = 8 * Λ * T := by
    rw [← Real.sqrt_mul (by positivity), show 16 * Λ * T * (4 * Λ * T) = (8 * Λ * T) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have h3 : (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (8 * Real.pi * T) ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity), show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  rw [h1]
  calc (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
        ((2 * Λ) ^ ((d : ℝ) / 2) * (8 * Real.pi * T) ^ ((d : ℝ) / 2)) * Real.sqrt (4 * Λ * T)
      = ((8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (8 * Real.pi * T) ^ ((d : ℝ) / 2)) *
          (2 * Λ) ^ ((d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) * Real.sqrt (4 * Λ * T)) / (4 * T) := by
        ring
    _ = _ := by
        rw [h3, h2]
        field_simp
        ring

/-! ## The heat identity bound -/

theorem euclideanNorm_inv_smul_self {V : Vec d} (hV : euclideanNorm V ≠ 0) :
    euclideanNorm ((euclideanNorm V)⁻¹ • V) = 1 := by
  have h0 : euclideanSq V = euclideanNorm V ^ 2 := (euclideanNorm_sq_eq V).symm
  have hsq : euclideanSq ((euclideanNorm V)⁻¹ • V) = 1 := by
    have h1 : euclideanSq ((euclideanNorm V)⁻¹ • V) = (euclideanNorm V)⁻¹ ^ 2 * euclideanSq V := by
      simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h0]
    field_simp
  show Real.sqrt (euclideanSq ((euclideanNorm V)⁻¹ • V)) = 1
  rw [hsq, Real.sqrt_one]

theorem dot_inv_smul_self (V : Vec d) : dot ((euclideanNorm V)⁻¹ • V) V = euclideanNorm V := by
  by_cases hV : euclideanNorm V = 0
  · have h1 : dot ((euclideanNorm V)⁻¹ • V) V = (euclideanNorm V)⁻¹ * euclideanSq V := by
      simp only [dot, euclideanSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hV, inv_zero, zero_mul]
  · have h1 : dot ((euclideanNorm V)⁻¹ • V) V = (euclideanNorm V)⁻¹ * euclideanSq V := by
      simp only [dot, euclideanSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, ← euclideanNorm_sq_eq]
    field_simp

/-- **The bound from the heat identity (H)** for a fixed coefficient field and any kernel `K`
that bounds the Hessian term: `|∫ Φ_{z,r} g| ≤ ∫⁻_{u > r²/2} ∫⁻ K(u, x)
|∫ Φ(u, z - x - y) (a - ā)(e + g)(y) dy| dx du`. -/
theorem heatIdentity_bound_of_kernel {Q : Mat d} (hQ : Q.transpose * Q = 1) {A : Mat d}
    {lam : Fin d → ℝ} (hA : ∀ v, Q *ᵥ (A *ᵥ v) = fun m => lam m * (Q *ᵥ v) m)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hlam : ∀ k, 1 ≤ lam k ∧ lam k ≤ Λ)
    {a : Vec d → Mat d} {e : Vec d} {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hgrad : HasWeakGradient Set.univ φ g)
    (hdiv : HasWeakDivergence Set.univ (fun x => a x *ᵥ (e + g x)) (fun _ => 0))
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k))
    (hfI : ∀ k, GaussianIntegrable (fun y => (a y *ᵥ (e + g y)) k))
    (hφI : GaussianIntegrable φ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, S ≤ s → ∀ x : Vec d,
      euclideanNorm x ≤ Real.sqrt s → ∫ y, euclideanHeatKernel s (x - y) * |φ y| ≤ ε * Real.sqrt s)
    (z : Vec d) {r : ℝ} (hr : 0 < r) {K : ℝ → Vec d → ℝ}
    (hK : ∀ u : ℝ, r ^ 2 / 2 < u → ∀ w : Vec d, euclideanNorm w = 1 → ∀ C : Vec d → Vec d,
      ENNReal.ofReal |-2 * ∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
        anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
          (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)| ≤
        ∫⁻ x, ENNReal.ofReal (K u x * euclideanNorm (C x))) :
    ENNReal.ofReal (euclideanNorm (fun j => ∫ y, euclideanHeatKernel (r ^ 2) (z - y) * g y j)) ≤
      ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (K u x *
        euclideanNorm (fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
          (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j)) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hr2 : 0 < r ^ 2 := by positivity
  set V : Vec d := fun j => ∫ y, euclideanHeatKernel (r ^ 2) (z - y) * g y j with hV
  by_cases hV0 : euclideanNorm V = 0
  · rw [hV0, ENNReal.ofReal_zero]
    exact bot_le
  set w : Vec d := (euclideanNorm V)⁻¹ • V with hw
  have hw1 : euclideanNorm w = 1 := euclideanNorm_inv_smul_self hV0
  have hgΦ : ∀ j, Integrable (fun y => euclideanHeatKernel (r ^ 2) (z - y) * g y j) := fun j =>
    (hgI j).integrable_heatKernel_mul hr2 z
  have hVw : euclideanNorm V = ∫ y, euclideanHeatKernel (r ^ 2) (z - y) * dot w (g y) := by
    rw [← dot_inv_smul_self V, ← hw]
    have hpt : ∀ y, euclideanHeatKernel (r ^ 2) (z - y) * dot w (g y) =
        ∑ j, w j * (euclideanHeatKernel (r ^ 2) (z - y) * g y j) := by
      intro y
      simp only [dot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum _ fun j _ => (hgΦ j).const_mul (w j)]
    simp only [dot, hV]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  obtain ⟨α, hα⟩ : ∃ α : Fin d → ℝ, α = fun k => r ^ 2 - r ^ 2 * lam k := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin d → ℝ, β = fun k => 2 * lam k := ⟨_, rfl⟩
  have hβ' : ∀ m, β m = 2 * lam m := fun m => by rw [hβ]
  have ht : ∀ u k, α k + β k * u = r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k := by
    intro u k
    rw [hα, hβ]
    ring
  have hlam0 : ∀ k, 0 ≤ lam k := fun k => zero_le_one.trans (hlam k).1
  -- the initial value
  have hf0 : ∫ y, rotKernel Q (fun k => α k + β k * (r ^ 2 / 2)) 0 z y * dot w (g y) =
      euclideanNorm V := by
    have hconst : (fun k => α k + β k * (r ^ 2 / 2)) = fun _ => r ^ 2 := by
      funext k
      rw [ht]
      ring
    rw [hVw]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [rotKernel, hconst]
    rw [anisoKernel_const_eq hr2, euclideanHeatKernel_mulVec_of_orthogonal hQ]
  set X := ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (K u x *
    euclideanNorm (fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
      (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j)) with hX
  have key : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (euclideanNorm V) ≤ X + ENNReal.ofReal δ := by
    intro δ hδ
    -- the terminal time
    set M := (2 * Λ) ^ ((d : ℝ) / 2) * (2 * Λ) with hM
    have hM0 : 0 < M := by positivity
    obtain ⟨S, hS0, hS⟩ := hsub (δ / M) (div_pos hδ hM0)
    set T := max (r ^ 2 / 2 + 1) (max (S / (4 * Λ)) (euclideanNorm z ^ 2 / (4 * Λ))) with hT
    have hT1 : r ^ 2 / 2 + 1 ≤ T := le_max_left _ _
    have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT1
    have hTu : r ^ 2 / 2 ≤ T := by linarith
    have hsT : S ≤ 4 * Λ * T := by
      have : S / (4 * Λ) ≤ T := (le_max_left _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hzT : euclideanNorm z ≤ Real.sqrt (4 * Λ * T) := by
      refine Real.le_sqrt_of_sq_le ?_
      have : euclideanNorm z ^ 2 / (4 * Λ) ≤ T := (le_max_right _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hbT : ∀ k, 2 * T ≤ α k + β k * T ∧ α k + β k * T ≤ 2 * Λ * T := by
      intro k
      rw [ht]
      have h1 := hlam k
      constructor <;> nlinarith
    have hterm := abs_integral_rotKernel_terminal_le hQ hΛ hT0 hbT hgrad hgI hφI hw1 z
    have hφT := hS (4 * Λ * T) hsT z hzT
    have hfT : |∫ y, rotKernel Q (fun k => α k + β k * T) 0 z y * dot w (g y)| ≤ δ := by
      refine hterm.trans ?_
      have hc0 : 0 ≤ (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
          (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) := by positivity
      calc (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
            (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) *
              ∫ y, euclideanHeatKernel (4 * Λ * T) (z - y) * |φ y|
          ≤ (8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
            (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) * (δ / M * Real.sqrt (4 * Λ * T)) :=
            mul_le_mul_of_nonneg_left hφT hc0
        _ = δ / M * ((8 * Real.pi * T) ^ (-(d : ℝ) / 2) * (Real.sqrt (16 * Λ * T) / (4 * T)) *
            (16 * Real.pi * Λ * T) ^ ((d : ℝ) / 2) * Real.sqrt (4 * Λ * T)) := by ring
        _ = δ := by
            rw [terminal_constant_eq hΛ0 hT0, ← hM]
            field_simp
    -- the fundamental theorem of calculus in time
    have hbI : ∀ u ∈ Icc (r ^ 2 / 2) T, ∀ k, r ^ 2 ≤ α k + β k * u ∧
        α k + β k * u ≤ r ^ 2 + 2 * Λ * T := by
      intro u hu k
      rw [ht]
      have h1 := hlam k
      have h2 := hu.1
      have h3 := hu.2
      constructor <;> nlinarith
    have hftc := integral_rotKernel_sub_eq_integral hQ hTu hr2
      (by nlinarith : r ^ 2 ≤ r ^ 2 + 2 * Λ * T) hbI (gaussianIntegrable_dot w hgI) z
    rw [hf0] at hftc
    -- the derivative at each time
    have hD : ∀ u ∈ Ioc (r ^ 2 / 2) T, ENNReal.ofReal |∫ y,
        (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) * dot w (g y)| ≤
        ∫⁻ x, ENNReal.ofReal (K u x *
          euclideanNorm (fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
            (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j)) := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1.le
      have hEσ : ∀ k, u ≤ α k + β k * u - u ∧ α k + β k * u - u ≤ 2 * Λ * u := by
        intro k
        rw [ht]
        have h1 := hlam k
        have h2 := hu.1
        constructor <;> nlinarith
      have hbu : ∀ k, r ^ 2 ≤ α k + β k * u ∧ α k + β k * u ≤ r ^ 2 + 2 * Λ * u := by
        intro k
        rw [ht]
        have h1 := hlam k
        have h2 := hu.1
        constructor <;> nlinarith
      rw [integral_time_derivative_eq hQ hA hgrad hdiv hgI hfI hu0 hr2
        (by nlinarith : r ^ 2 ≤ r ^ 2 + 2 * Λ * u) hu0 (by nlinarith : u ≤ 2 * Λ * u) hEσ
        (fun k => by ring) hbu hβ' z w]
      have hEeq : (fun k => α k + β k * u - u) =
          fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u := funext fun k => by rw [ht]
      rw [hEeq]
      exact hK u hu.1 w hw1 _
    -- assembly
    have hV1 : euclideanNorm V ≤ δ + ∫ u in Ioc (r ^ 2 / 2) T, |∫ y,
        (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) * dot w (g y)| := by
      have h1 : euclideanNorm V = (∫ y, rotKernel Q (fun k => α k + β k * T) 0 z y * dot w (g y)) -
          ∫ u in Ioc (r ^ 2 / 2) T, ∫ y,
            (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) * dot w (g y) := by
        rw [← hftc]
        ring
      rw [h1]
      have h2 := abs_integral_le_integral_abs (μ := volume.restrict (Ioc (r ^ 2 / 2) T))
        (f := fun u => ∫ y,
          (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) * dot w (g y))
      have h3 := neg_abs_le (∫ u in Ioc (r ^ 2 / 2) T, ∫ y,
        (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) * dot w (g y))
      have h4 := le_abs_self (∫ y, rotKernel Q (fun k => α k + β k * T) 0 z y * dot w (g y))
      linarith
    calc ENNReal.ofReal (euclideanNorm V)
        ≤ ENNReal.ofReal δ + ENNReal.ofReal (∫ u in Ioc (r ^ 2 / 2) T, |∫ y,
            (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) *
              dot w (g y)|) := by
          rw [← ENNReal.ofReal_add hδ.le (integral_nonneg fun u => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hV1
      _ ≤ ENNReal.ofReal δ + ∫⁻ u in Ioc (r ^ 2 / 2) T, ENNReal.ofReal |∫ y,
            (∑ m, β m * rotKernel Q (fun k => α k + β k * u) (Pi.single m 2) z y) *
              dot w (g y)| := by
          gcongr
          exact ofReal_integral_le_lintegral_ofReal' fun u => abs_nonneg _
      _ ≤ ENNReal.ofReal δ + ∫⁻ u in Ioc (r ^ 2 / 2) T, ∫⁻ x,
            ENNReal.ofReal (K u x *
              euclideanNorm (fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
                (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j)) := by
          exact add_le_add le_rfl (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
            (Eventually.of_forall hD)))
      _ ≤ ENNReal.ofReal δ + X := by
          gcongr
          exact lintegral_mono_set Ioc_subset_Ioi_self
      _ = X + ENNReal.ofReal δ := add_comm _ _
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have h := key ε hε
  rwa [ENNReal.ofReal_coe_nnreal] at h

/-- **The bound from the heat identity (H)** for a fixed coefficient field with the isotropic
kernel `k(u, x) = (8Λ + 1) u⁻¹ (4πu)^{-d/2} e^{-|x|²/(16Λu)}`. -/
theorem heatIdentity_bound {Q : Mat d} (hQ : Q.transpose * Q = 1) {A : Mat d}
    {lam : Fin d → ℝ} (hA : ∀ v, Q *ᵥ (A *ᵥ v) = fun m => lam m * (Q *ᵥ v) m)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hlam : ∀ k, 1 ≤ lam k ∧ lam k ≤ Λ)
    {a : Vec d → Mat d} {e : Vec d} {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hgrad : HasWeakGradient Set.univ φ g)
    (hdiv : HasWeakDivergence Set.univ (fun x => a x *ᵥ (e + g x)) (fun _ => 0))
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k))
    (hfI : ∀ k, GaussianIntegrable (fun y => (a y *ᵥ (e + g y)) k))
    (hφI : GaussianIntegrable φ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, S ≤ s → ∀ x : Vec d,
      euclideanNorm x ≤ Real.sqrt s → ∫ y, euclideanHeatKernel s (x - y) * |φ y| ≤ ε * Real.sqrt s)
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (euclideanNorm (fun j => ∫ y, euclideanHeatKernel (r ^ 2) (z - y) * g y j)) ≤
      ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (heatIdentityKernel d Λ u x *
        euclideanNorm (fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
          (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j)) := by
  refine heatIdentity_bound_of_kernel hQ hA hΛ hlam hgrad hdiv hgI hfI hφI hsub z hr ?_
  intro u hu w hw C
  have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu
  refine ofReal_abs_hessian_integral_le hQ hΛ hu0 (fun k => ?_) hw C
  have h1 := hlam k
  have h2 : 0 ≤ 2 * u - r ^ 2 := by linarith
  constructor <;> nlinarith

/-- The times of the sharp kernel: `v + (λ_k - 1)(2v - r²)₊`. -/
def sharpTimes (lam : Fin d → ℝ) (r v : ℝ) : Fin d → ℝ :=
  fun k => v + (lam k - 1) * max (2 * v - r ^ 2) 0

/-- **The sharp kernel**: `v⁻¹ (1 + ½ ∑_k (Qx)_k²/Ê_k) G_Ê(Qx)` with `Ê = sharpTimes lam r v`,
`v = max(u, 1)`; its mass is `(d + 1)/v`. -/
def sharpHeatKernel (Q : Mat d) (lam : Fin d → ℝ) (r u : ℝ) (x : Vec d) : ℝ :=
  (max u 1)⁻¹ * ((1 + 1 / 2 * ∑ k, (Q *ᵥ x) k ^ 2 / sharpTimes lam r (max u 1) k) *
    anisoKernel (sharpTimes lam r (max u 1)) 0 (Q *ᵥ x))

theorem sharpTimes_ge {lam : Fin d → ℝ} (hlam : ∀ k, 1 ≤ lam k) (r v : ℝ) (k : Fin d) :
    v ≤ sharpTimes lam r v k := by
  unfold sharpTimes
  have h1 := hlam k
  have h2 : 0 ≤ max (2 * v - r ^ 2) 0 := le_max_right _ _
  nlinarith

theorem sharpTimes_eq {lam : Fin d → ℝ} {r u : ℝ} (hu : r ^ 2 / 2 < u) (hu1 : 1 ≤ u) :
    sharpTimes lam r (max u 1) = fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u := by
  funext k
  rw [sharpTimes, max_eq_left hu1, max_eq_left (by linarith)]
  ring

/-- **The derivative of `F` is bounded by the commutators against the sharp kernel.** -/
theorem ofReal_abs_hessian_integral_le_sharp {Q : Mat d} (hQ : Q.transpose * Q = 1)
    {lam : Fin d → ℝ} (hlam : ∀ k, 1 ≤ lam k) {r u : ℝ} (hu : r ^ 2 / 2 < u) (hu1 : 1 ≤ u)
    {w : Vec d} (hw : euclideanNorm w = 1) (C : Vec d → Vec d) :
    ENNReal.ofReal |-2 * ∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
        anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
          (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)| ≤
      ∫⁻ x, ENNReal.ofReal (sharpHeatKernel Q lam r u x * euclideanNorm (C x)) := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
  have hE : ∀ k, u ≤ (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u) k := by
    intro k
    rw [← sharpTimes_eq hu hu1]
    exact (le_max_left u 1).trans (sharpTimes_ge hlam r (max u 1) k)
  have hpt : ∀ x, 2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
      anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
        (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)| ≤
      sharpHeatKernel Q lam r u x * euclideanNorm (C x) := by
    intro x
    have h := abs_hessian_anisoKernel_le_sharp hu0 hE (Q *ᵥ w) (Q *ᵥ C x) (Q *ᵥ x)
    rw [euclideanNorm_mulVec_of_orthogonal hQ, euclideanNorm_mulVec_of_orthogonal hQ, hw,
      one_mul] at h
    unfold sharpHeatKernel
    rw [sharpTimes_eq hu hu1, max_eq_left hu1]
    exact h
  rw [abs_mul, abs_neg, abs_two]
  calc ENNReal.ofReal (2 * |∫ x, ∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
        anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
          (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|)
      ≤ ENNReal.ofReal (∫ x, 2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
          anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
            (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * |∑ k, ∑ m, (Q *ᵥ w) k * (Q *ᵥ C x) m *
          anisoKernel (fun k => r ^ 2 + 2 * (u - r ^ 2 / 2) * lam k - u)
            (Pi.single k 1 + Pi.single m 1) (Q *ᵥ x)|) :=
        ofReal_integral_le_lintegral_ofReal' fun x => by positivity
    _ ≤ _ := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)

/-- **The bound from the heat identity (H)** with the sharp kernel, for `r² ≥ 2`. -/
theorem heatIdentity_bound_sharp {Q : Mat d} (hQ : Q.transpose * Q = 1) {A : Mat d}
    {lam : Fin d → ℝ} (hA : ∀ v, Q *ᵥ (A *ᵥ v) = fun m => lam m * (Q *ᵥ v) m)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hlam : ∀ k, 1 ≤ lam k ∧ lam k ≤ Λ)
    {a : Vec d → Mat d} {e : Vec d} {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hgrad : HasWeakGradient Set.univ φ g)
    (hdiv : HasWeakDivergence Set.univ (fun x => a x *ᵥ (e + g x)) (fun _ => 0))
    (hgI : ∀ k, GaussianIntegrable (fun y => g y k))
    (hfI : ∀ k, GaussianIntegrable (fun y => (a y *ᵥ (e + g y)) k))
    (hφI : GaussianIntegrable φ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, S ≤ s → ∀ x : Vec d,
      euclideanNorm x ≤ Real.sqrt s → ∫ y, euclideanHeatKernel s (x - y) * |φ y| ≤ ε * Real.sqrt s)
    (z : Vec d) {r : ℝ} (hr : 0 < r) (hr2 : 2 ≤ r ^ 2) :
    ENNReal.ofReal (euclideanNorm (fun j => ∫ y, euclideanHeatKernel (r ^ 2) (z - y) * g y j)) ≤
      ∫⁻ u in Ioi (r ^ 2 / 2), ∫⁻ x, ENNReal.ofReal (sharpHeatKernel Q lam r u x *
        euclideanNorm (fun j => ∫ y, euclideanHeatKernel u (z - x - y) *
          (a y *ᵥ (e + g y) - A *ᵥ (e + g y)) j)) := by
  refine heatIdentity_bound_of_kernel hQ hA hΛ hlam hgrad hdiv hgI hfI hφI hsub z hr ?_
  intro u hu w hw C
  exact ofReal_abs_hessian_integral_le_sharp hQ (fun k => (hlam k).1) hu (by linarith) hw C

end QSH
