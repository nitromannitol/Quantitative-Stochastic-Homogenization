import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoli

/-!
# The global Caccioppoli estimate near the boundary

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.8, the estimate (C.18): for `u ∈ H¹₀(U)` solving `-∇·(a∇u) = h` in `U`,
`z ∈ ∂U` and `r > 0`,
`‖∇u‖_{L̲²(B_{r/2}(z) ∩ U)} ≤ C (r^{-1} ‖u‖_{L̲²(B_r(z) ∩ U)} + ‖h‖_{H̲^{-1}(B_r(z) ∩ U)})`.

The book's proof is that of Lemma C.2 with the test function `φ² u`, which lies in
`H¹₀(B_r(z) ∩ U)` because `u ∈ H¹₀(U)`. This file proves:
* `h10MulCutoff`: for `u ∈ H¹₀(U)`, a smooth compactly supported `θ` and an open `V ⊆ U` with
  `supp θ ∩ U ⊆ V`, the product `θ u` as an element of `H¹₀(V)`, with the approximants `θ uₙ`;
* `caccioppoli_of_cutoff`: the Caccioppoli computation of Lemma C.2 on an arbitrary set `V` of
  finite measure, for a solution `u ∈ H¹(V)`, a constant `c`, a cutoff `φ` equal to `1` on
  `W ⊆ V` with `|∇φ| ≤ 64/r`, and a test `φ² (u - c) ∈ H¹₀(V)`, with the constant explicit in
  `|V| / |W|` and `r |V|^{-1/d}`;
* `boundaryCaccioppoli`: (C.18) for every ball `B_r(z)` with `|B_{r/2}(z) ∩ U| > 0`, with this
  explicit constant.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The product `θ u ∈ H¹₀(V)` of `u ∈ H¹₀(U)` with a smooth compactly supported `θ`, for an open
`V ⊆ U` containing `supp θ ∩ U`; its approximants are `θ uₙ`. -/
def h10MulCutoff {U V : Set (Vec d)} (u : PDE.H10Function U) (hVo : IsOpen V) (hVU : V ⊆ U)
    {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθV : tsupport θ ∩ U ⊆ V) : PDE.H10Function V where
  toH1Function := (u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc
  approx n := fun x => θ x * u.approx n x
  approx_smooth n := hθ.mul (u.approx_smooth n)
  approx_hasCompactSupport n := (u.approx_hasCompactSupport n).mul_left
  approx_support_subset n :=
    (subset_inter tsupport_mul_subset_left
      (tsupport_mul_subset_right.trans (u.approx_support_subset n))).trans hθV
  tendsto_approx := by
    obtain ⟨M, hM⟩ := hθ.continuous.bounded_above_of_compact_support hθc
    have hres : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
    have hbound : ∀ n, eLpNorm (fun x => θ x * u.approx n x -
        ((u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc).toFun x) 2
          (volume.restrict V) ≤ ENNReal.ofReal M *
            eLpNorm (fun x => u.approx n x - u.toH1Function.toFun x) 2 (volume.restrict U) := by
      intro n
      simp only [PDE.H1Function.mulContDiffHasCompactSupport_toFun,
        PDE.H1Function.restrict_toFun]
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x => ?_) 2).trans
        (mul_le_mul_right (eLpNorm_mono_measure _ hres) _)
      · exact ((hθ.continuous.mul (u.approx_smooth n).continuous).aestronglyMeasurable.sub
          (hθ.continuous.aestronglyMeasurable.mul
            (u.toH1Function.memL2.aestronglyMeasurable.mono_measure hres)))
      · change ‖θ x * u.approx n x - θ x * u.toH1Function.toFun x‖ ≤
          M * ‖u.approx n x - u.toH1Function.toFun x‖
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    have h := ENNReal.Tendsto.const_mul u.tendsto_approx
      (Or.inr (ENNReal.ofReal_ne_top (r := M)))
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => zero_le) hbound
  tendsto_approx_grad := by
    intro i
    obtain ⟨M, hM⟩ := hθ.continuous.bounded_above_of_compact_support hθc
    have hDθc : Continuous fun x => fderiv ℝ θ x (PDE.basisVec i) :=
      (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨M', hM'⟩ := hDθc.bounded_above_of_compact_support
      (hθc.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i))
    have hres : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
    set a : ℕ → Vec d → ℝ := fun n x =>
      fderiv ℝ (u.approx n) x (PDE.basisVec i) - u.toH1Function.grad x i with ha
    set b : ℕ → Vec d → ℝ := fun n x => u.approx n x - u.toH1Function.toFun x with hb
    have hgm : AEStronglyMeasurable (fun x => u.toH1Function.grad x i) (volume.restrict U) :=
      (u.toH1Function.gradMemL2 i).aestronglyMeasurable
    have ham : ∀ n, AEStronglyMeasurable (a n) (volume.restrict U) := fun n =>
      (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.sub hgm
    have hbm : ∀ n, AEStronglyMeasurable (b n) (volume.restrict U) := fun n =>
      (u.approx_smooth n).continuous.aestronglyMeasurable.sub
        u.toH1Function.memL2.aestronglyMeasurable
    have hpt : ∀ n x, fderiv ℝ (fun y => θ y * u.approx n y) x (PDE.basisVec i) -
        ((u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc).grad x i =
          θ x * a n x + fderiv ℝ θ x (PDE.basisVec i) * b n x := by
      intro n x
      have hθd : DifferentiableAt ℝ θ x := hθ.differentiable (by simp) x
      have hud : DifferentiableAt ℝ (u.approx n) x :=
        (u.approx_smooth n).differentiable (by simp) x
      have e : (fun y => θ y * u.approx n y) = θ * u.approx n := rfl
      rw [e, fderiv_mul hθd hud, PDE.H1Function.mulContDiffHasCompactSupport_grad]
      change θ x * fderiv ℝ (u.approx n) x (PDE.basisVec i) +
          u.approx n x * fderiv ℝ θ x (PDE.basisVec i) -
          (θ x * u.toH1Function.grad x i +
            u.toH1Function.toFun x * fderiv ℝ θ x (PDE.basisVec i)) = _
      simp only [ha, hb]
      ring
    have hbound : ∀ n, eLpNorm (fun x => fderiv ℝ (fun y => θ y * u.approx n y) x
        (PDE.basisVec i) -
        ((u.toH1Function.restrict hVo hVU).mulContDiffHasCompactSupport hθ hθc).grad x i) 2
          (volume.restrict V) ≤ ENNReal.ofReal M * eLpNorm (a n) 2 (volume.restrict U) +
            ENNReal.ofReal M' * eLpNorm (b n) 2 (volume.restrict U) := by
      intro n
      simp_rw [hpt n]
      have hsplit : (fun x => θ x * a n x + fderiv ℝ θ x (PDE.basisVec i) * b n x) =
          (fun x => θ x * a n x) + fun x => fderiv ℝ θ x (PDE.basisVec i) * b n x := rfl
      rw [hsplit]
      refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
      · refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hθ.continuous.aestronglyMeasurable.mul ((ham n).mono_measure hres))
          (Eventually.of_forall fun x => ?_) 2).trans
          (mul_le_mul_right (eLpNorm_mono_measure _ hres) _)
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
      · refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hDθc.aestronglyMeasurable.mul ((hbm n).mono_measure hres))
          (Eventually.of_forall fun x => ?_) 2).trans
          (mul_le_mul_right (eLpNorm_mono_measure _ hres) _)
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _)
    have h1 := ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i)
      (Or.inr (ENNReal.ofReal_ne_top (r := M)))
    have h2 := ENNReal.Tendsto.const_mul u.tendsto_approx
      (Or.inr (ENNReal.ofReal_ne_top (r := M')))
    have h3 := h1.add h2
    rw [mul_zero, mul_zero, add_zero] at h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
      (fun n => zero_le) hbound

/-- The product of `u ∈ H¹₀(U)` with a cutoff `θ` is the function `θ u`. -/
theorem h10MulCutoff_apply {U V : Set (Vec d)} (u : PDE.H10Function U) (hVo : IsOpen V)
    (hVU : V ⊆ U) {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθV : tsupport θ ∩ U ⊆ V) (x : Vec d) :
    (h10MulCutoff u hVo hVU hθ hθc hθV).toH1Function x = θ x * u.toH1Function x := by
  exact (congrFun (PDE.H1Function.mulContDiffHasCompactSupport_toFun _ hθ hθc) x).trans rfl

/-- The gradient of the product of `u ∈ H¹₀(U)` with a cutoff `θ`. -/
theorem h10MulCutoff_grad {U V : Set (Vec d)} (u : PDE.H10Function U) (hVo : IsOpen V)
    (hVU : V ⊆ U) {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθV : tsupport θ ∩ U ⊆ V) (x : Vec d) :
    (h10MulCutoff u hVo hVU hθ hθc hθV).toH1Function.grad x =
      θ x • u.toH1Function.grad x + u.toH1Function x • PDE.classicalGradient θ x := by
  exact (congrFun (PDE.H1Function.mulContDiffHasCompactSupport_grad _ hθ hθc) x).trans rfl

/-- **The Caccioppoli computation of Lemma C.2 on a general set.** Let `V` have finite measure and
`W ⊆ V` positive measure, let `u ∈ H¹(V)` solve `-∇·(a∇u) = f + ∇·F` in `V`, let `φ` be smooth with
`0 ≤ φ ≤ 1`, `φ = 1` on `W` and `|∇φ| ≤ 64/r`, and let `v = φ² (u - c) ∈ H¹₀(V)`. Then
`‖∇u‖_{L̲²(W)} ≤ C (r^{-1} ‖u - c‖_{L̲²(V)} + ‖f + ∇·F‖_{H̲^{-1}(V)})` with
`C² = (|V|/|W|) · 2 (2 r |V|^{-1/d} + 256 d + 2 d² + 16384 Λ)`. -/
theorem caccioppoli_of_cutoff {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    {V W : Set (Vec d)} (hVm : MeasurableSet V) (hVt : volume V ≠ ⊤) (hWm : MeasurableSet W)
    (hWV : W ⊆ V) (hW0 : volume W ≠ 0) {u : Vec d → ℝ} {g : Vec d → Vec d} {f : Vec d → ℝ}
    {F : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict V))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict V)) (hw : HasWeakGradient V u g)
    (hf : MemLp f 2 (volume.restrict V))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict V))
    (hdiv : HasWeakDivergence V (fun x => (a x).mulVec (g x) + F x) (fun x => -f x))
    {r : ℝ} (hr : 0 < r) {φ : Vec d → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∀ x, φ x ≤ 1) (hφW : ∀ x ∈ W, φ x = 1)
    (hφK : ∀ x, PDE.vecEuclideanNorm (PDE.classicalGradient φ x) ≤ 64 / r) (c : ℝ)
    (v : PDE.H10Function V) (hvfun : ∀ x, v.toH1Function x = φ x * (φ x * (u x - c)))
    (hvgrad : ∀ x, v.toH1Function.grad x = φ x • (φ x • g x + (u x - c) •
      PDE.classicalGradient φ x) + (φ x * (u x - c)) • PDE.classicalGradient φ x) :
    ENNReal.ofReal (vectorRms volume W g) ≤
      ENNReal.ofReal (Real.sqrt (volume.real V / volume.real W *
        (2 * (2 * (r * (volume V).toReal ^ (-(1 : ℝ) / d)) + 256 * d + 2 * d ^ 2 +
          16384 * Λ)))) *
        (ENNReal.ofReal (r⁻¹ * scalarRms volume V (fun x => u x - c)) +
          negativeSobolevOneNorm 2 V f F) := by
  have hV0 : volume V ≠ 0 := fun h => hW0 (measure_mono_null hWV h)
  have hWt : volume W ≠ ⊤ := ne_top_of_le_ne_top hVt (measure_mono hWV)
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVt
  have hUpos : 0 < volume.real V := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hV0 hVt
  have hWpos : 0 < volume.real W := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hW0 hWt
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁, c₁ = r * (volume V).toReal ^ (-(1 : ℝ) / d) := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := hc₁def ▸ mul_nonneg hr.le (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hρ : (volume V).toReal ^ (-(1 : ℝ) / d) = c₁ / r := by
    rw [hc₁def]
    field_simp
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 * c₁ + 256 * d + 2 * d ^ 2 + 16384 * Λ := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  have hratio : 0 < volume.real V / volume.real W := div_pos hUpos hWpos
  have hCpos : 0 < Real.sqrt (volume.real V / volume.real W * (2 * M)) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [← hc₁def, show 2 * c₁ + 256 * (d : ℝ) + 2 * d ^ 2 + 16384 * Λ = M from hMdef.symm]
  by_cases hHtop : negativeSobolevOneNorm 2 V f F = ⊤
  · rw [hHtop, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCpos).ne']
    exact le_top
  obtain ⟨H, hHdef⟩ : ∃ H, H = (negativeSobolevOneNorm 2 V f F).toReal := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := hHdef ▸ ENNReal.toReal_nonneg
  have hHeq : negativeSobolevOneNorm 2 V f F = ENNReal.ofReal H := by
    rw [hHdef, ENNReal.ofReal_toReal hHtop]
  -- the elliptic library's objects
  obtain ⟨A, hAdef⟩ : ∃ A, A = ellipticFieldOf a := ⟨_, rfl⟩
  have hEll : PDE.IsEllipticFieldOn 1 Λ V A :=
    hAdef ▸ isEllipticFieldOn_ellipticFieldOf hΛ a hVm
  have hAx : ∀ x, PDE.IsEllipticMatrix 1 Λ (A x) :=
    hAdef ▸ isEllipticMatrix_ellipticFieldOf hΛ a
  obtain ⟨u₁, hu₁g, hsol⟩ : ∃ u₁ : PDE.H1Function V,
      (∀ x, u₁.grad x = g x) ∧ PDE.IsWeakDivergenceFormSolutionOn A V u₁ f F :=
    ⟨toH1FunctionOn hu hg hw, fun _ => rfl,
      hAdef ▸ isWeakDivergenceFormSolutionOn_toH1FunctionOn hΛ a hVm hu hg hw hf hF hdiv⟩
  have hsol10 := hsol.toH10SolutionOn_of_isEllipticFieldOn hEll hf hF
  obtain ⟨K, hK⟩ : ∃ K, K = 64 / r := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨gφ, hgφ⟩ : ∃ gφ : Vec d → Vec d, gφ = fun x => PDE.classicalGradient φ x :=
    ⟨_, rfl⟩
  have hgφ_cont : Continuous gφ := by
    rw [hgφ]
    refine continuous_pi fun i => ?_
    exact (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgφ_bound : ∀ x, PDE.vecNormSq (gφ x) ≤ K ^ 2 := by
    intro x
    have h1 := hφK x
    have h2 : PDE.vecEuclideanNorm (gφ x) ^ 2 = PDE.vecNormSq (gφ x) :=
      Real.sq_sqrt (PDE.vecNormSq_nonneg _)
    rw [← h2, hK, hgφ]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hφcont : Continuous φ := hφs.continuous
  simp only [← hgφ] at hvgrad
  -- the tested equation and the pairing bound
  have hid := (hsol10 v).2
  have hpair := abs_integral_pairing_le_of_h10 hVt hf hF hH0 hHeq.le v
  obtain ⟨E, hEdef⟩ : ∃ E : Vec d → ℝ,
      E = fun x => PDE.vecDot (g x) (PDE.matVecMul (A x) (g x)) := ⟨_, rfl⟩
  have hEge : ∀ x, PDE.vecNormSq (g x) ≤ E x := by
    intro x
    have h1 := (hAx x).2.2.1 (g x)
    rw [one_mul] at h1
    rw [hEdef]
    exact h1
  have hE0 : ∀ x, 0 ≤ E x := fun x => (PDE.vecNormSq_nonneg _).trans (hEge x)
  have hpt : ∀ x, PDE.vecDot (PDE.matVecMul (A x) (u₁.grad x)) (v.toH1Function.grad x) =
      φ x ^ 2 * E x + 2 * φ x * (u x - c) * PDE.vecDot (PDE.matVecMul (A x) (g x)) (gφ x) := by
    intro x
    rw [hvgrad x, hu₁g x, hEdef]
    simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hyoung : ∀ x, -(φ x ^ 2 * E x / 2 + 2 * Λ * ((u x - c) ^ 2 * PDE.vecNormSq (gφ x))) ≤
      2 * φ x * (u x - c) * PDE.vecDot (PDE.matVecMul (A x) (g x)) (gφ x) := by
    intro x
    have h := PDE.DGNM.abs_two_mul_mul_vecDot_le_caccioppoli (η := φ x) (w := u x - c)
      (hAx x) (g x) (gφ x)
    have h' := neg_abs_le (2 * φ x * (u x - c) * PDE.vecDot (PDE.matVecMul (A x) (g x)) (gφ x))
    have e : φ x ^ 2 * PDE.vecDot (g x) (PDE.matVecMul (A x) (g x)) / 2 +
        2 * Λ * (u x - c) ^ 2 * PDE.vecNormSq (gφ x) =
        φ x ^ 2 * E x / 2 + 2 * Λ * ((u x - c) ^ 2 * PDE.vecNormSq (gφ x)) := by
      rw [hEdef]
      ring
    rw [e] at h
    linarith
  -- integrability
  have hg' : PDE.MemVectorL2On V g := hg
  have hE_int : IntegrableOn E V := by
    rw [hEdef]
    exact PDE.integrableOn_vecDot_of_memVectorL2On hg'
      (PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hg')
  have hφ2E_int : IntegrableOn (fun x => φ x ^ 2 * E x) V := by
    refine hE_int.bdd_mul (c := 1) (hφcont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hφ0 x) (hφ1 x)
  have hwm : MemLp (fun x => u x - c) 2 (volume.restrict V) := hu.sub (memLp_const c)
  have hw_int : IntegrableOn (fun x => (u x - c) ^ 2) V := hwm.integrable_sq
  have hN_cont : Continuous fun x => PDE.vecNormSq (gφ x) := by
    unfold PDE.vecNormSq PDE.vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hgφ_cont).mul ((continuous_apply i).comp hgφ_cont)
  have hJ_int : IntegrableOn (fun x => (u x - c) ^ 2 * PDE.vecNormSq (gφ x)) V := by
    have h := hw_int.bdd_mul (c := K ^ 2) hN_cont.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (PDE.vecNormSq_nonneg _)]
        exact hgφ_bound x)
    exact h.congr (Eventually.of_forall fun x => mul_comm _ _)
  have htot_int := (hsol10 v).1.flux_integrable
  -- the energy inequality
  have hlow : ∫ x in V, (φ x ^ 2 * E x / 2 -
      2 * Λ * ((u x - c) ^ 2 * PDE.vecNormSq (gφ x))) ≤
      ∫ x in V, PDE.vecDot (PDE.matVecMul (A x) (u₁.grad x)) (v.toH1Function.grad x) := by
    refine integral_mono ((hφ2E_int.div_const 2).sub (hJ_int.const_mul _)) htot_int
      fun x => ?_
    rw [hpt x]
    have := hyoung x
    linarith
  rw [integral_sub (hφ2E_int.div_const 2) (hJ_int.const_mul _), integral_div,
    integral_const_mul, hid] at hlow
  obtain ⟨I, hIdef⟩ : ∃ I, I = ∫ x in V, φ x ^ 2 * E x := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J, J = ∫ x in V, (u x - c) ^ 2 * PDE.vecNormSq (gφ x) := ⟨_, rfl⟩
  obtain ⟨Wi, hWidef⟩ : ∃ Wi, Wi = ∫ x in V, (u x - c) ^ 2 := ⟨_, rfl⟩
  rw [← hIdef, ← hJdef] at hlow
  have hIJ : I / 2 - 2 * Λ * J ≤ volume.real V * (H * h10TestNorm V v) :=
    hlow.trans ((le_abs_self _).trans hpair)
  have hJW : J ≤ K ^ 2 * Wi := by
    rw [hJdef, hWidef, ← integral_const_mul]
    refine integral_mono hJ_int (hw_int.const_mul _) fun x => ?_
    have h1 := hgφ_bound x
    have h2 := sq_nonneg (u x - c)
    change (u x - c) ^ 2 * PDE.vecNormSq (gφ x) ≤ K ^ 2 * (u x - c) ^ 2
    calc (u x - c) ^ 2 * PDE.vecNormSq (gφ x) ≤ (u x - c) ^ 2 * K ^ 2 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = K ^ 2 * (u x - c) ^ 2 := mul_comm _ _
  have hI0 : 0 ≤ I := hIdef ▸ integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hE0 x)
  have hW0' : 0 ≤ Wi := hWidef ▸ integral_nonneg fun x => sq_nonneg _
  -- normalized quantities
  obtain ⟨y, hydef⟩ : ∃ y, y = scalarRms volume V (fun x => u x - c) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := hydef ▸ Real.sqrt_nonneg _
  have hy2 : y ^ 2 = (volume.real V)⁻¹ * Wi := by
    rw [hydef, scalarRms, Real.sq_sqrt, setAverage_eq, smul_eq_mul, hWidef]
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (hWidef ▸ hW0')
  obtain ⟨xx, hxxdef⟩ : ∃ xx, xx = Real.sqrt ((volume.real V)⁻¹ * I) := ⟨_, rfl⟩
  have hxx0 : 0 ≤ xx := hxxdef ▸ Real.sqrt_nonneg _
  have hxx2 : xx ^ 2 = (volume.real V)⁻¹ * I := by
    rw [hxxdef]
    exact Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr measureReal_nonneg) hI0)
  have hvmeas : AEStronglyMeasurable (fun x => v.toH1Function x) (volume.restrict V) :=
    v.toH1Function.memL2.aestronglyMeasurable
  -- the H¹ norm of the test
  have hT0 : (PDE.eLpMeanNormOn V 2 v.toH1Function.toFun).toReal ≤ y := by
    have hpt0 : ∀ x, (v.toH1Function x) ^ 2 ≤ (u x - c) ^ 2 := by
      intro x
      rw [hvfun x, show φ x * (φ x * (u x - c)) = (φ x * φ x) * (u x - c) by ring, mul_pow]
      have h2 : (φ x * φ x) ^ 2 ≤ 1 :=
        pow_le_one₀ (mul_nonneg (hφ0 x) (hφ0 x))
          ((mul_le_of_le_one_left (hφ0 x) (hφ1 x)).trans (hφ1 x))
      exact mul_le_of_le_one_left (sq_nonneg _) h2
    have h := eLpMeanNormOn_two_le_ofReal_sqrt hV0 hvmeas hw_int (Eventually.of_forall hpt0)
    rw [show Real.sqrt (⨍ x in V, (u x - c) ^ 2 ∂volume) = y from hydef.symm] at h
    exact ENNReal.toReal_le_of_le_ofReal hy0 h
  have hTi : ∀ i : Fin d,
      (PDE.eLpMeanNormOn V 2 (fun x => v.toH1Function.grad x i)).toReal ≤
        xx + 2 * K * y := by
    intro i
    have hsplit : (fun x => v.toH1Function.grad x i) =
        (fun x => φ x ^ 2 * g x i) + fun x => 2 * φ x * (u x - c) * gφ x i := by
      funext x
      rw [hvgrad x]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hm1 : AEStronglyMeasurable (fun x => φ x ^ 2 * g x i) (volume.restrict V) :=
      (hφcont.pow 2).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x => 2 * φ x * (u x - c) * gφ x i)
        (volume.restrict V) :=
      ((continuous_const.mul hφcont).aestronglyMeasurable.mul hwm.aestronglyMeasurable).mul
        ((continuous_apply i).comp hgφ_cont).aestronglyMeasurable
    have hpt1 : ∀ x, (φ x ^ 2 * g x i) ^ 2 ≤ φ x ^ 2 * E x := by
      intro x
      have hgi := (sq_apply_le_vecNormSq (g x) i).trans (hEge x)
      have hp : φ x ^ 2 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
      have hp0 : 0 ≤ φ x ^ 2 := sq_nonneg _
      calc (φ x ^ 2 * g x i) ^ 2 = φ x ^ 2 * (φ x ^ 2 * g x i ^ 2) := by ring
        _ ≤ φ x ^ 2 * (1 * E x) := by
          refine mul_le_mul_of_nonneg_left ?_ hp0
          exact mul_le_mul hp hgi (sq_nonneg _) zero_le_one
        _ = φ x ^ 2 * E x := by ring
    have hpt2 : ∀ x, (2 * φ x * (u x - c) * gφ x i) ^ 2 ≤ 4 * K ^ 2 * (u x - c) ^ 2 := by
      intro x
      have hgi := (sq_apply_le_vecNormSq (gφ x) i).trans (hgφ_bound x)
      have hp : φ x ^ 2 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
      calc (2 * φ x * (u x - c) * gφ x i) ^ 2 =
          4 * (u x - c) ^ 2 * (φ x ^ 2 * gφ x i ^ 2) := by ring
        _ ≤ 4 * (u x - c) ^ 2 * (1 * K ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hp hgi (sq_nonneg _) zero_le_one
        _ = 4 * K ^ 2 * (u x - c) ^ 2 := by ring
    have h1 := eLpMeanNormOn_two_le_ofReal_sqrt hV0 hm1 hφ2E_int (Eventually.of_forall hpt1)
    have h4int : IntegrableOn (fun x => 4 * K ^ 2 * (u x - c) ^ 2) V :=
      hw_int.const_mul _
    have h2 := eLpMeanNormOn_two_le_ofReal_sqrt hV0 hm2 h4int (Eventually.of_forall hpt2)
    have hxxeq : Real.sqrt (⨍ x in V, φ x ^ 2 * E x ∂volume) = xx := by
      rw [hxxdef, setAverage_eq, smul_eq_mul, hIdef]
    have hKyeq : Real.sqrt (⨍ x in V, 4 * K ^ 2 * (u x - c) ^ 2 ∂volume) = 2 * K * y := by
      rw [setAverage_eq, smul_eq_mul, integral_const_mul, hydef, scalarRms, setAverage_eq,
        smul_eq_mul, mul_left_comm, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hK0, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hxxeq] at h1
    rw [hKyeq] at h2
    have hsum : PDE.eLpMeanNormOn V 2 (fun x => v.toH1Function.grad x i) ≤
        ENNReal.ofReal xx + ENNReal.ofReal (2 * K * y) := by
      rw [hsplit]
      exact (eLpNorm_add_le (by norm_num)).trans (add_le_add h1 h2)
    rw [← ENNReal.ofReal_add hxx0 (by positivity)] at hsum
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsum
  have hT : h10TestNorm V v ≤ c₁ / r * y + d * (xx + 2 * K * y) := by
    unfold h10TestNorm
    rw [hρ]
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hTi i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hc₁r : 0 ≤ c₁ / r := by positivity
    have := mul_le_mul_of_nonneg_left hT0 hc₁r
    linarith
  -- the normalized energy bound
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = r⁻¹ * y := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hyY : y = r * Y := by rw [hYdef]; field_simp
  have hmain : xx ^ 2 / 2 - 2 * Λ * ((volume.real V)⁻¹ * J) ≤ H * h10TestNorm V v := by
    have h := mul_le_mul_of_nonneg_left hIJ (inv_nonneg.mpr hUpos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hUpos.ne', one_mul] at h
    rw [hxx2]
    have e : (volume.real V)⁻¹ * (I / 2 - 2 * Λ * J) =
        (volume.real V)⁻¹ * I / 2 - 2 * Λ * ((volume.real V)⁻¹ * J) := by ring
    linarith
  have hj : (volume.real V)⁻¹ * J ≤ K ^ 2 * y ^ 2 := by
    rw [hy2]
    have := mul_le_mul_of_nonneg_left hJW (inv_nonneg.mpr hUpos.le)
    linarith
  have hi := caccioppoli_absorb hr hH0 hY0 hc₁ (by linarith) (Nat.cast_nonneg d) hK hyY
    hmain hj hT
  rw [← hMdef] at hi
  -- from the weighted energy on `V` to `W`
  have hgsq_int : IntegrableOn (fun x => euclideanSq (g x)) W :=
    (PDE.integrableOn_vecDot_of_memVectorL2On hg' hg').mono_set hWV
  have hball : ∫ x in W, euclideanSq (g x) ≤ I := by
    rw [hIdef]
    calc ∫ x in W, euclideanSq (g x) ≤ ∫ x in W, φ x ^ 2 * E x := by
          refine setIntegral_mono_on hgsq_int (hφ2E_int.mono_set hWV) hWm fun x hx => ?_
          rw [hφW x hx, one_pow, one_mul]
          exact hEge x
      _ ≤ ∫ x in V, φ x ^ 2 * E x := setIntegral_mono_set hφ2E_int
          (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hE0 x))
          (Eventually.of_forall hWV)
  have hrms : vectorRms volume W g ≤
      Real.sqrt (volume.real V / volume.real W * (2 * M)) * (Y + H) := by
    have h1 : ⨍ x in W, euclideanSq (g x) ∂volume ≤ volume.real V / volume.real W * xx ^ 2 := by
      rw [setAverage_eq, smul_eq_mul, hxx2, div_eq_mul_inv, mul_comm (volume.real V),
        mul_assoc, ← mul_assoc (volume.real V), mul_inv_cancel₀ hUpos.ne', one_mul]
      exact mul_le_mul_of_nonneg_left hball (inv_nonneg.mpr hWpos.le)
    have h2 : volume.real V / volume.real W * xx ^ 2 ≤
        (Real.sqrt (volume.real V / volume.real W * (2 * M)) * (Y + H)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), add_comm Y H, mul_assoc]
      exact mul_le_mul_of_nonneg_left hi hratio.le
    rw [vectorRms]
    calc Real.sqrt (⨍ x in W, euclideanSq (g x) ∂volume)
        ≤ Real.sqrt ((Real.sqrt (volume.real V / volume.real W * (2 * M)) * (Y + H)) ^ 2) :=
          Real.sqrt_le_sqrt (h1.trans h2)
      _ = Real.sqrt (volume.real V / volume.real W * (2 * M)) * (Y + H) :=
          Real.sqrt_sq (by positivity)
  rw [hHeq, ← hydef, ← hYdef, ← ENNReal.ofReal_add hY0 hH0, ← ENNReal.ofReal_mul hCpos.le]
  exact ENNReal.ofReal_le_ofReal hrms

theorem ball_half_subset (z : Vec d) {r : ℝ} : ball z (r / 2) ⊆ ball z r := by
  intro x hx
  have hx' : euclideanNorm (x - z) < r / 2 := hx
  change euclideanNorm (x - z) < r
  have : 0 ≤ euclideanNorm (x - z) := Real.sqrt_nonneg _
  linarith

/-- **Lemma C.8, the estimate (C.18), with an explicit constant.** For an open set `U`,
`u ∈ H¹₀(U)` solving `-∇·(a∇u) = f + ∇·F` in `U` with `f, F ∈ L²(U)`, and a ball `B_r(z)` with
`|B_{r/2}(z) ∩ U| > 0`, writing `V = B_r(z) ∩ U` and `W = B_{r/2}(z) ∩ U`,
`‖∇u‖_{L̲²(W)} ≤ C (r^{-1} ‖u‖_{L̲²(V)} + ‖f + ∇·F‖_{H̲^{-1}(V)})` with
`C² = (|V|/|W|) · 2 (2 r |V|^{-1/d} + 256 d + 2 d² + 16384 Λ)`. -/
theorem boundaryCaccioppoli {Λ : ℝ} (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (a : CoefficientField d Λ) {u : Vec d → ℝ} {g : Vec d → Vec d} {f : Vec d → ℝ}
    {F : Vec d → Vec d} (hu : H01 U u g) (hf : MemLp f 2 (volume.restrict U))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hdiv : HasWeakDivergence U (fun x => (a x).mulVec (g x) + F x) (fun x => -f x))
    (z : Vec d) {r : ℝ} (hr : 0 < r) (hW0 : volume (ball z (r / 2) ∩ U) ≠ 0) :
    ENNReal.ofReal (vectorRms volume (ball z (r / 2) ∩ U) g) ≤
      ENNReal.ofReal (Real.sqrt (volume.real (ball z r ∩ U) / volume.real (ball z (r / 2) ∩ U) *
        (2 * (2 * (r * (volume (ball z r ∩ U)).toReal ^ (-(1 : ℝ) / d)) + 256 * d +
          2 * d ^ 2 + 16384 * Λ)))) *
        (ENNReal.ofReal (r⁻¹ * scalarRms volume (ball z r ∩ U) u) +
          negativeSobolevOneNorm 2 (ball z r ∩ U) f F) := by
  set V := ball z r ∩ U with hVdef
  set W := ball z (r / 2) ∩ U with hWdef
  have hr2 : 0 < r / 2 := by linarith
  have hVo : IsOpen V := (isOpen_ball z _).inter hUo
  have hVU : V ⊆ U := inter_subset_right
  have hWV : W ⊆ V := inter_subset_inter_left U (ball_half_subset z)
  have hWm : MeasurableSet W := ((isOpen_ball z _).inter hUo).measurableSet
  have hVt : volume V ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    rw [ball_eq_euclideanBall z hr]
    exact PDE.volume_euclideanBall_ne_top z hr.le
  have hres : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
  have hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => MemLp.eval hu.2.1 i
  -- the cutoff
  have φ : PDE.QuantitativeSmoothCutoff (ball z (r / 2)) (ball z r) (64 / r) := by
    have h := PDE.quantitativeBallCutoff z hr2.le (show r / 2 < r by linarith)
    rw [← ball_eq_euclideanBall z hr2, ← ball_eq_euclideanBall z hr,
      show 32 / (r - r / 2) = 64 / r by field_simp; norm_num] at h
    exact h
  have hφd : ∀ x, DifferentiableAt ℝ φ.toFun x := fun x => φ.smooth.differentiable (by simp) x
  set θ : Vec d → ℝ := fun x => φ.toFun x * φ.toFun x with hθdef
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ := φ.smooth.mul φ.smooth
  have hθc : HasCompactSupport θ := φ.hasCompactSupport.mul_left
  have hθV : tsupport θ ∩ U ⊆ V := fun x hx =>
    ⟨φ.tsupport_subset (tsupport_mul_subset_left hx.1), hx.2⟩
  have hθgrad : ∀ x, PDE.classicalGradient θ x =
      (2 * φ.toFun x) • PDE.classicalGradient φ.toFun x := by
    intro x
    funext i
    have e : θ = φ.toFun * φ.toFun := rfl
    simp only [PDE.classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, fderiv_mul (hφd x) (hφd x)]
    change φ.toFun x * fderiv ℝ φ.toFun x (PDE.basisVec i) +
      φ.toFun x * fderiv ℝ φ.toFun x (PDE.basisVec i) = _
    ring
  set v := h10MulCutoff hu.toH10Function hVo hVU hθs hθc hθV with hvdef
  have hvfun : ∀ x, v.toH1Function x = φ.toFun x * (φ.toFun x * (u x - 0)) := by
    intro x
    rw [h10MulCutoff_apply, H01.toH10Function_apply, sub_zero, hθdef]
    ring
  have hvgrad : ∀ x, v.toH1Function.grad x = φ.toFun x • (φ.toFun x • g x + (u x - 0) •
      PDE.classicalGradient φ.toFun x) + (φ.toFun x * (u x - 0)) •
        PDE.classicalGradient φ.toFun x := by
    intro x
    rw [h10MulCutoff_grad, H01.toH10Function_grad, H01.toH10Function_apply, hθgrad x, sub_zero]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hθdef]
    ring
  have h := caccioppoli_of_cutoff hΛ a hVo.measurableSet hVt hWm hWV hW0
    (hu.1.mono_measure hres) (fun i => (hg i).mono_measure hres)
    (hasWeakGradient_mono hVU hu.2.2.1) (hf.mono_measure hres)
    (fun i => (hF i).mono_measure hres) (hdiv.mono' hVU) hr φ.smooth φ.nonneg φ.le_one
    (fun x hx => φ.eq_one_on_inner x hx.1) φ.gradient_bound 0 v hvfun hvgrad
  simp only [sub_zero] at h
  exact h

end QSH
