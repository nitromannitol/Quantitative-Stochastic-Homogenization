import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification
import Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-!
# Smoothing of test functions and the Laplacian pairing on balls

For a smooth compactly supported `χ` let `χ̄ = χ * ρ_ℓ` with the normalized round kernel `ρ_ℓ`
of radius `ℓ`. Its second derivatives are the smoothings of those of `χ`, so by Jensen's inequality
`|∂_b∂_a χ̄|² ≤ (sup ρ_ℓ) ∫ (∂_b∂_a χ)² ≤ C ℓ^{-d} ‖Δχ‖²_{L²}`, using `‖∇²χ‖_{L²} = ‖Δχ‖_{L²}`; and
by the mollification estimate `‖∂ᵢχ - ∂ᵢχ̄‖_{L²} ≤ ℓ ‖∇∂ᵢχ‖_{L²}`.

`abs_integral_mul_laplacian_le_of_hessian_pairing`: if `u ∈ H¹(B_{r'})` and the pairing of `u` with
`Δψ` for tests `ψ` in `B_{r'}` is bounded by `E` times the supremum of the second derivatives of
`ψ`, then for tests `χ` in `B_r`, `r + ℓ ≤ r'`,
`|∫ u Δχ| ≤ (d ℓ ‖∇u‖_{L²(B_{r'})} + E (C ℓ^{-d})^{1/2}) ‖Δχ‖_{L²}`: split `Δχ = Δχ̄ + Δ(χ - χ̄)` and
integrate the second part by parts once.
-/

open MeasureTheory Filter Set
open scoped Convolution Topology InnerProductSpace Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem integral_mul_eq_inner_toLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, f x * g x ∂μ = ⟪hf.toLp f, hg.toLp g⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem norm_toLp_eq_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ}
    (hg : MemLp g 2 μ) : ‖hg.toLp g‖ = Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h1 : ‖hg.toLp g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x h1
    rw [h1]
    simp [pow_two]
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

theorem integrable_mul_of_memLp_two {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x * g x) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- **Cauchy–Schwarz**: `|∫ f g| ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}`. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  rw [integral_mul_eq_inner_toLp hf hg, ← norm_toLp_eq_sqrt hf, ← norm_toLp_eq_sqrt hg]
  exact abs_real_inner_le_norm _ _

/-- The smoothing `χ * ρ_ℓ` of a function by the normalized round kernel of radius `ℓ`. -/
def kernelSmooth (ℓ : ℝ) (χ : Vec d → ℝ) : Vec d → ℝ :=
  χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] PDE.harmonicKernelScaled ℓ

theorem kernelSmooth_apply (ℓ : ℝ) (χ : Vec d → ℝ) (x : Vec d) :
    kernelSmooth ℓ χ x = ∫ y, PDE.harmonicKernelScaled ℓ y * χ (x - y) := by
  unfold kernelSmooth
  rw [PDE.harmonicScalarConvolution_comm, MeasureTheory.convolution_def]
  simp [ContinuousLinearMap.lsmul_apply]

theorem locallyIntegrable_harmonicKernelScaled (ℓ : ℝ) :
    LocallyIntegrable (PDE.harmonicKernelScaled (d := d) ℓ) volume :=
  (PDE.harmonicKernelScaled_smooth ℓ).continuous.locallyIntegrable

theorem contDiff_kernelSmooth {ℓ : ℝ} {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) : ContDiff ℝ (⊤ : ℕ∞) (kernelSmooth ℓ χ) :=
  HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hχc hχ
    (locallyIntegrable_harmonicKernelScaled ℓ)

theorem hasCompactSupport_kernelSmooth {ℓ : ℝ} (hℓ : 0 < ℓ) {χ : Vec d → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (kernelSmooth ℓ χ) :=
  hχc.convolution _ (PDE.harmonicKernelScaled_hasCompactSupport hℓ)

theorem tsupport_kernelSmooth_subset {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 < r) {χ : Vec d → ℝ}
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ PDE.euclideanBall 0 r) :
    tsupport (kernelSmooth ℓ χ) ⊆ PDE.euclideanBall 0 (r + ℓ) := by
  have hK := PDE.harmonicKernelScaled_hasCompactSupport (d := d) hℓ
  have hsub : tsupport (kernelSmooth ℓ χ) ⊆ tsupport χ + tsupport (PDE.harmonicKernelScaled ℓ) :=
    closure_minimal ((support_convolution_subset _).trans
      (add_subset_add subset_closure subset_closure)) (hχc.isCompact.add hK.isCompact).isClosed
  refine hsub.trans ?_
  rintro _ ⟨z, hz, w, hw, rfl⟩
  have hz' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp (hχs hz)
  have hw' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hℓ).mp
    (PDE.harmonicKernelScaled_tsupport_subset hℓ hw)
  refine (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)).mpr ?_
  rw [sub_zero] at hz' hw' ⊢
  calc PDE.vecEuclideanNorm (z + w) ≤ PDE.vecEuclideanNorm z + PDE.vecEuclideanNorm w :=
        PDE.vecEuclideanNorm_add_le _ _
    _ < r + ℓ := by linarith

theorem euclideanCoordDeriv_kernelSmooth {ℓ : ℝ} {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (i : Fin d) :
    PDE.euclideanCoordDeriv i (kernelSmooth ℓ χ) = kernelSmooth ℓ (PDE.euclideanCoordDeriv i χ) :=
  PDE.euclideanCoordDeriv_convolution_left hχc hχ (locallyIntegrable_harmonicKernelScaled ℓ) i

theorem euclideanCoordSecondDeriv_kernelSmooth {ℓ : ℝ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (i j : Fin d) :
    PDE.euclideanCoordSecondDeriv i j (kernelSmooth ℓ χ) =
      kernelSmooth ℓ (PDE.euclideanCoordSecondDeriv i j χ) :=
  PDE.euclideanCoordSecondDeriv_convolution_left hχc hχ
    (locallyIntegrable_harmonicKernelScaled ℓ) i j

theorem euclideanCoordLaplacian_kernelSmooth {ℓ : ℝ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    PDE.euclideanCoordLaplacian (kernelSmooth ℓ χ) =
      kernelSmooth ℓ (PDE.euclideanCoordLaplacian χ) :=
  PDE.euclideanCoordLaplacian_convolution_left hχc hχ (locallyIntegrable_harmonicKernelScaled ℓ)

/-- A bound `ρ_ℓ ≤ C ℓ^{-d}` for the scaled kernels. -/
theorem exists_harmonicKernelScaled_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ y : Vec d,
      PDE.harmonicKernelScaled ℓ y ≤ ℓ⁻¹ ^ d * C := by
  obtain ⟨C, hC⟩ := (PDE.harmonicKernel_hasCompactSupport (d := d)).exists_bound_of_continuous
    PDE.harmonicKernel_smooth.continuous
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun ℓ hℓ y => ?_⟩
  unfold PDE.harmonicKernelScaled
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_nonneg.2 hℓ.le) _)
  exact (le_abs_self _).trans (hC _)

theorem harmonicKernelScaled_ne_zero_imp {ℓ : ℝ} (hℓ : 0 < ℓ) {y : Vec d}
    (hy : PDE.harmonicKernelScaled ℓ y ≠ 0) : euclideanSq y ≤ ℓ ^ 2 := by
  have h := PDE.harmonicKernelScaled_tsupport_subset hℓ (subset_tsupport _ hy)
  have h' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hℓ).mp h
  rw [sub_zero] at h'
  have h2 : euclideanSq y = PDE.vecEuclideanNorm y ^ 2 := by
    rw [PDE.vecEuclideanNorm, Real.sq_sqrt]
    · rfl
    · unfold PDE.vecNormSq PDE.vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
  rw [h2]
  have h0 : 0 ≤ PDE.vecEuclideanNorm y := Real.sqrt_nonneg _
  nlinarith

/-- The pointwise bound `(F * ρ_ℓ)(x)² ≤ C ℓ^{-d} ∫ F²`. -/
theorem sq_kernelSmooth_le {ℓ C : ℝ} (hℓ : 0 < ℓ)
    (hC : ∀ y : Vec d, PDE.harmonicKernelScaled ℓ y ≤ ℓ⁻¹ ^ d * C) {F : Vec d → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Vec d) :
    kernelSmooth ℓ F x ^ 2 ≤ ℓ⁻¹ ^ d * C * ∫ y, F y ^ 2 := by
  set ρ := PDE.harmonicKernelScaled (d := d) ℓ with hρdef
  have hρc : Continuous ρ := (PDE.harmonicKernelScaled_smooth ℓ).continuous
  have hρs : HasCompactSupport ρ := PDE.harmonicKernelScaled_hasCompactSupport hℓ
  have hρ0 : ∀ y, 0 ≤ ρ y := PDE.harmonicKernelScaled_nonneg hℓ
  have hρ1 : ∫ y, ρ y = 1 := PDE.harmonicKernelScaled_integral_eq_one hℓ
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hcF : Continuous fun y => F (x - y) := hF.comp (continuous_const.sub continuous_id)
  have hgw : Integrable fun y => F (x - y) * ρ y :=
    (hcF.mul hρc).integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hρs)
  have hg2w : Integrable fun y => F (x - y) ^ 2 * ρ y :=
    ((hcF.pow 2).mul hρc).integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hρs)
  have hF2 : Integrable fun y => F y ^ 2 := by
    refine (hF.pow 2).integrable_of_hasCompactSupport ?_
    have h := hFc.mul_left (f := F)
    convert h using 1
    funext y
    simp [pow_two]
  have hF2' : Integrable fun y => F (x - y) ^ 2 :=
    hF2.comp_sub_left x
  have e : kernelSmooth ℓ F x = ∫ y, F (x - y) * ρ y := by
    rw [kernelSmooth_apply]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp [hρdef, mul_comm])
  rw [e]
  refine (sq_integral_mul_le hρ0 hρ1 hρi hgw hg2w).trans ?_
  calc ∫ y, F (x - y) ^ 2 * ρ y ≤ ∫ y, ℓ⁻¹ ^ d * C * F (x - y) ^ 2 :=
        integral_mono hg2w (hF2'.const_mul _) fun y => by
          rw [mul_comm (ℓ⁻¹ ^ d * C)]
          exact mul_le_mul_of_nonneg_left (hC y) (sq_nonneg _)
    _ = ℓ⁻¹ ^ d * C * ∫ y, F y ^ 2 := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun y => F y ^ 2) volume x

theorem euclideanCoordLaplacian_eq_zero_of_notMem_tsupport {χ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport χ) : PDE.euclideanCoordLaplacian χ x = 0 := by
  unfold PDE.euclideanCoordLaplacian
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : x ∉ tsupport (PDE.euclideanCoordDeriv i χ) := fun h =>
    hx (PDE.tsupport_euclideanCoordDeriv_subset_tsupport i χ h)
  by_contra hne
  exact h1 (PDE.support_euclideanCoordDeriv_subset_tsupport i (PDE.euclideanCoordDeriv i χ) hne)

theorem euclideanCoordSecondDeriv_eq_zero_of_notMem_tsupport {χ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport χ) (i j : Fin d) : PDE.euclideanCoordSecondDeriv i j χ x = 0 := by
  have h1 : x ∉ tsupport (PDE.euclideanCoordDeriv i χ) := fun h =>
    hx (PDE.tsupport_euclideanCoordDeriv_subset_tsupport i χ h)
  by_contra hne
  exact h1 (PDE.support_euclideanCoordDeriv_subset_tsupport j (PDE.euclideanCoordDeriv i χ) hne)

theorem contDiff_euclideanCoordSecondDeriv {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (i j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (PDE.euclideanCoordSecondDeriv i j χ) :=
  PDE.contDiff_euclideanCoordDeriv (PDE.contDiff_euclideanCoordDeriv hχ i) j

theorem hasCompactSupport_euclideanCoordSecondDeriv {χ : Vec d → ℝ} (hχc : HasCompactSupport χ)
    (i j : Fin d) : HasCompactSupport (PDE.euclideanCoordSecondDeriv i j χ) :=
  PDE.hasCompactSupport_euclideanCoordDeriv (PDE.hasCompactSupport_euclideanCoordDeriv hχc i) j

/-- `∑ᵢⱼ ∫ (∂ⱼ∂ᵢ χ)² = ∫ (Δχ)²` for smooth compactly supported `χ`. -/
theorem sum_integral_sq_secondDeriv_eq {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    ∑ i, ∑ j, ∫ x, PDE.euclideanCoordSecondDeriv i j χ x ^ 2 =
      ∫ x, PDE.euclideanCoordLaplacian χ x ^ 2 :=
  Homogenization.integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_euclideanCoordLaplacian_sq
    hχ hχc

theorem integral_sq_secondDeriv_le {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (a b : Fin d) :
    ∫ x, PDE.euclideanCoordSecondDeriv a b χ x ^ 2 ≤
      ∫ x, PDE.euclideanCoordLaplacian χ x ^ 2 := by
  rw [← sum_integral_sq_secondDeriv_eq hχ hχc]
  have hnn : ∀ i j, 0 ≤ ∫ x, PDE.euclideanCoordSecondDeriv i j χ x ^ 2 := fun i j =>
    integral_nonneg fun x => sq_nonneg _
  calc ∫ x, PDE.euclideanCoordSecondDeriv a b χ x ^ 2
      ≤ ∑ j, ∫ x, PDE.euclideanCoordSecondDeriv a j χ x ^ 2 :=
        Finset.single_le_sum (f := fun j => ∫ x, PDE.euclideanCoordSecondDeriv a j χ x ^ 2)
          (fun j _ => hnn a j) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, ∫ x, PDE.euclideanCoordSecondDeriv i j χ x ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ∫ x, PDE.euclideanCoordSecondDeriv i j χ x ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ a)

end QSH
