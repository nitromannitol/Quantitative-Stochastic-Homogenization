import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestDerivatives

/-!
# Pairings of a function with compact kernels

Calculus for the averages `ρ_b * v` of the finite-ball estimate (consultant note T22, (2)) of the
proof of Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.

For an integrable `F` and a smooth compactly supported kernel `K` the pairing
`kernelPairing K F x = ∫ F(w) K(x - w) dw` is smooth in `x` with
`∂^α (kernelPairing K F) = kernelPairing (∂^α K) F`. For the scaled kernels
`K_b(z) = b^{-c} f(z/b)` it is differentiable in the scale, with
`∂_b (kernelPairing K_b F) x = -b^{-c-1} kernelPairing ((c f + y·∇f)(·/b)) F x`
(`hasDerivAt_kernelPairing_scaledKernel`).
-/

open MeasureTheory Filter
open scoped ContDiff Convolution Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The pairing and its spatial derivatives -/

/-- The pairing `x ↦ ∫ F(w) K(x - w) dw`. -/
def kernelPairing (K F : Vec d → ℝ) (x : Vec d) : ℝ := ∫ w, F w * K (x - w)

theorem kernelPairing_eq_convolution (K F : Vec d → ℝ) :
    kernelPairing K F = F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K := by
  funext x
  simp [kernelPairing, convolution_def, smul_eq_mul]

theorem coordinateDerivative_kernelPairing {K : Vec d → ℝ} (hK : ContDiff ℝ ∞ K)
    (hKc : HasCompactSupport K) {F : Vec d → ℝ} (hF : LocallyIntegrable F volume) (i : Fin d) :
    coordinateDerivative i (kernelPairing K F) = kernelPairing (coordinateDerivative i K) F := by
  funext x
  have h1 : ContDiff ℝ 1 K := hK.of_le (by simp)
  rw [kernelPairing_eq_convolution, kernelPairing_eq_convolution]
  unfold coordinateDerivative
  rw [(hKc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hF h1 x).fderiv,
    convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hF (hKc.fderiv (𝕜 := ℝ))
      (h1.continuous_fderiv one_ne_zero) x (unitVector i)]

theorem contDiff_kernelPairing {K : Vec d → ℝ} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    {F : Vec d → ℝ} (hF : LocallyIntegrable F volume) : ContDiff ℝ ∞ (kernelPairing K F) := by
  rw [kernelPairing_eq_convolution]
  exact hKc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hF hK

theorem iterDeriv_kernelPairing {j : ℕ} (α : Fin j → Fin d) {K : Vec d → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) {F : Vec d → ℝ}
    (hF : LocallyIntegrable F volume) :
    iterDeriv α (kernelPairing K F) = kernelPairing (iterDeriv α K) F := by
  induction j generalizing K with
  | zero => rfl
  | succ j ih =>
    rw [iterDeriv_succ, coordinateDerivative_kernelPairing hK hKc hF,
      ih (Fin.tail α) (contDiff_coordinateDerivative hK _)
        (hasCompactSupport_coordinateDerivative hKc _)]
    rfl

/-- The pairing is supported by the kernel: it only sees `F` on `x - tsupport K`. -/
theorem kernelPairing_congr {K F G : Vec d → ℝ} {x : Vec d}
    (h : ∀ w, x - w ∈ tsupport K → F w = G w) : kernelPairing K F x = kernelPairing K G x := by
  unfold kernelPairing
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  by_cases hw : x - w ∈ tsupport K
  · simp only [h w hw]
  · simp only [image_eq_zero_of_notMem_tsupport hw, mul_zero]

theorem abs_kernelPairing_le {K F : Vec d → ℝ} (hF : Integrable F) {S : ℝ}
    (hS : ∀ z, |K z| ≤ S) (x : Vec d) : |kernelPairing K F x| ≤ S * ∫ w, |F w| := by
  unfold kernelPairing
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) (hF.abs.const_mul S)
    (Eventually.of_forall fun w => ?_))
  dsimp only
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hS _) (abs_nonneg _)

/-! ## Scaled kernels and their scale derivative -/

/-- The scaled kernel `z ↦ b^{-c} f(z/b)`. -/
def scaledKernel (c : ℕ) (b : ℝ) (f : Vec d → ℝ) (z : Vec d) : ℝ := (b⁻¹) ^ c * f (b⁻¹ • z)

/-- The Euler operator `c f(y) + y · ∇f(y)`. -/
def eulerOp (c : ℕ) (f : Vec d → ℝ) (y : Vec d) : ℝ :=
  c * f y + ∑ l, y l * coordinateDerivative l f y

theorem iterDeriv_scaledKernel {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℕ) (b : ℝ) :
    iterDeriv α (scaledKernel c b f) = scaledKernel (c + j) b (iterDeriv α f) := by
  have e : scaledKernel c b f = fun z => (b⁻¹) ^ c * dilate b f z := rfl
  rw [e, iterDeriv_const_mul α (contDiff_dilate hf b), iterDeriv_dilate α hf b]
  funext z
  simp only [scaledKernel, dilate, pow_add]
  ring

theorem contDiff_scaledKernel {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (scaledKernel c b f) :=
  contDiff_const.mul (contDiff_dilate hf b)

theorem hasCompactSupport_scaledKernel {f : Vec d → ℝ} (hf : HasCompactSupport f) (c : ℕ)
    {b : ℝ} (hb : b ≠ 0) : HasCompactSupport (scaledKernel c b f) := by
  have h : HasCompactSupport (fun z : Vec d => f (b⁻¹ • z)) := hf.comp_smul (inv_ne_zero hb)
  exact h.mul_left

/-- **The scale derivative of a scaled kernel**:
`∂_b (b^{-c-1} f(z/b)) = -b^{-c-2} ((c + 1) f + y · ∇f)(z/b)`. -/
theorem hasDerivAt_scaledKernel {f : Vec d → ℝ} (hf : Differentiable ℝ f) (c : ℕ) {b : ℝ}
    (hb : b ≠ 0) (z : Vec d) :
    HasDerivAt (fun b => scaledKernel (c + 1) b f z)
      (-(b⁻¹) ^ (c + 2) * eulerOp (c + 1) f (b⁻¹ • z)) b := by
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ (c + 1) * f (s • z))
      (s ^ c * eulerOp (c + 1) f (s • z)) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => s ^ (c + 1)) (((c + 1 : ℕ) : ℝ) * s ^ c) s := by
      simpa using hasDerivAt_pow (c + 1) s
    have h2 : HasDerivAt (fun s : ℝ => s • z) z s := by
      simpa using (hasDerivAt_id s).smul_const z
    have h3 : HasDerivAt (fun s : ℝ => f (s • z)) (fderiv ℝ f (s • z) z) s :=
      (hf _).hasFDerivAt.comp_hasDerivAt s h2
    convert h1.mul h3 using 1
    rw [fderiv_apply_eq_sum_coordinateDerivative, eulerOp, Finset.mul_sum, mul_add,
      Finset.mul_sum, Finset.sum_congr rfl fun l _ => show s ^ c * ((s • z) l *
        coordinateDerivative l f (s • z)) = s ^ (c + 1) * (z l * coordinateDerivative l f (s • z))
        by simp only [Pi.smul_apply, smul_eq_mul]; ring]
    push_cast
    ring
  have hinv : HasDerivAt (fun b : ℝ => b⁻¹) (-(b ^ 2)⁻¹) b := hasDerivAt_inv hb
  have h := (hg b⁻¹).comp b hinv
  convert h using 1
  · funext b
    simp [scaledKernel, Function.comp]
  · have hb2 : (b ^ 2)⁻¹ = (b⁻¹) ^ 2 := by rw [inv_pow]
    rw [hb2]
    ring

/-- **The scale derivative of the pairing with a scaled kernel.** -/
theorem hasDerivAt_kernelPairing_scaledKernel {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (c : ℕ) {F : Vec d → ℝ} (hF : Integrable F) (x : Vec d)
    {b₀ : ℝ} (hb₀ : 0 < b₀) :
    HasDerivAt (fun b => kernelPairing (scaledKernel (c + 1) b f) F x)
      (-(b₀⁻¹) ^ (c + 2) * kernelPairing (fun z => eulerOp (c + 1) f (b₀⁻¹ • z)) F x) b₀ := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hE : Continuous (eulerOp (c + 1) f) := by
    unfold eulerOp
    exact (continuous_const.mul hf.continuous).add (continuous_finsetSum _ fun l _ =>
      (continuous_apply l).mul (contDiff_coordinateDerivative hf l).continuous)
  have hEc : HasCompactSupport (eulerOp (c + 1) f) := by
    unfold eulerOp
    refine HasCompactSupport.add (hfc.mul_left) ?_
    have : HasCompactSupport (fun y => ∑ l, y l * coordinateDerivative l f y) := by
      refine HasCompactSupport.intro hfc fun y hy => ?_
      refine Finset.sum_eq_zero fun l _ => ?_
      have : y ∉ tsupport (coordinateDerivative l f) :=
        fun h => hy (tsupport_coordinateDerivative_subset' l f h)
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    exact this
  obtain ⟨KE, hKE⟩ := hE.bounded_above_of_compact_support hEc
  have hfm : Continuous f := hf.continuous
  obtain ⟨Kf, hKf⟩ := hfm.bounded_above_of_compact_support hfc
  set s : Set ℝ := Set.Ioo (b₀ / 2) (2 * b₀) with hs
  have hs0 : s ∈ 𝓝 b₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ b ∈ s, 0 < b := fun b hb => lt_trans (by linarith) hb.1
  set F' : ℝ → Vec d → ℝ := fun b w =>
    F w * (-(b⁻¹) ^ (c + 2) * eulerOp (c + 1) f (b⁻¹ • (x - w))) with hF'
  have hmeas : ∀ b : ℝ, AEStronglyMeasurable (fun w => F w * scaledKernel (c + 1) b f (x - w))
      volume := fun b =>
    hF.aestronglyMeasurable.mul ((contDiff_scaledKernel hf (c + 1) b).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint0 : Integrable (fun w => F w * scaledKernel (c + 1) b₀ f (x - w)) := by
    refine Integrable.mono' (hF.norm.mul_const ((b₀⁻¹) ^ (c + 1) * Kf)) (hmeas b₀)
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul, scaledKernel, norm_mul, norm_pow, Real.norm_of_nonneg (inv_nonneg.2 hb₀.le)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKf _)
      (pow_nonneg (inv_nonneg.2 hb₀.le) _)) (norm_nonneg _)
  have hF'c : Continuous (fun w : Vec d => -(b₀⁻¹) ^ (c + 2) * eulerOp (c + 1) f (b₀⁻¹ • (x - w))) :=
    continuous_const.mul (hE.comp (by fun_prop))
  have hF'm : AEStronglyMeasurable (F' b₀) volume :=
    hF.aestronglyMeasurable.mul hF'c.aestronglyMeasurable
  set M : ℝ := ((b₀ / 2)⁻¹) ^ (c + 2) * KE with hM
  have hbound : ∀ᵐ w ∂(volume : Measure (Vec d)), ∀ b ∈ s, ‖F' b w‖ ≤ ‖F w‖ * M := by
    refine Eventually.of_forall fun w b hb => ?_
    have hb0 := hpos b hb
    rw [hF', norm_mul, norm_mul, norm_neg, norm_pow, Real.norm_of_nonneg (inv_nonneg.2 hb0.le)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (inv_nonneg.2 hb0.le)
      ((inv_le_inv₀ hb0 (by linarith)).2 hb.1.le) _) (hKE _) (norm_nonneg _)
      (pow_nonneg (inv_nonneg.2 (by linarith)) _)) (norm_nonneg _)
  have hdiff : ∀ᵐ w ∂(volume : Measure (Vec d)), ∀ b ∈ s,
      HasDerivAt (fun b => F w * scaledKernel (c + 1) b f (x - w)) (F' b w) b :=
    Eventually.of_forall fun w b hb =>
      (hasDerivAt_scaledKernel hfd c (hpos b hb).ne' (x - w)).const_mul (F w)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs0
    (Eventually.of_forall fun b => hmeas b) hint0 hF'm hbound (hF.norm.mul_const M) hdiff
  have e : ∫ w, F' b₀ w = -(b₀⁻¹) ^ (c + 2) *
      kernelPairing (fun z => eulerOp (c + 1) f (b₀⁻¹ • z)) F x := by
    rw [kernelPairing, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hF']
    ring
  rw [← e]
  exact h.2

end QSH
