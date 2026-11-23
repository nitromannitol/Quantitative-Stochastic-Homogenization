import QuantitativeStochasticHomogenization.Ch04.Sec04.SlopeFromObservation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorHighContrast

/-!
# Weak gradients and weak solutions under the affine map `x ↦ c x + y`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, prepared for the transfer of Theorem C of Armstrong, Kuusi and Loher,
*Homogenization at a polynomial scale in high contrast*, to balls with an arbitrary center.
For `c > 0` let `A x = c x + y`. If `g` is the weak gradient of `v` on `U` and `A` maps `V` into
`U`, then `x ↦ g(A x)` is the weak gradient of `x ↦ c⁻¹ v(A x)` on `V` in the sense of the
high-contrast theory; if moreover `-∇·(a g) = 0` weakly on `U` and `b = a ∘ A` almost
everywhere, then `x ↦ g(A x)` solves the equation of `b` on `V`. Square integrability is
transported in the same way. The proofs change variables in whole-space integrals, using that the
test functions vanish outside their supports.
-/

open MeasureTheory Filter

open scoped Pointwise

noncomputable section

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat

open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- `∫ F (c x + y) dx = |c^d|⁻¹ ∫ F`. -/
theorem integral_comp_smul_add (F : Vec d → ℝ) (c : ℝ) (y : Vec d) :
    ∫ x, F (c • x + y) = |c ^ d|⁻¹ * ∫ x, F x := by
  have h1 := Measure.integral_comp_smul (volume : Measure (Vec d)) (fun x => F (x + y)) c
  rw [Module.finrank_fin_fun, smul_eq_mul] at h1
  rw [h1, integral_add_right_eq_self (μ := volume) F y, abs_inv]

theorem integrable_comp_smul_add {F : Vec d → ℝ} (hF : Integrable F) {c : ℝ} (hc : c ≠ 0)
    (y : Vec d) : Integrable (fun x => F (c • x + y)) :=
  (hF.comp_add_right y).comp_smul hc

/-- The homeomorphism `x' ↦ c⁻¹ (x' - y)`, inverse of `x ↦ c x + y`. -/
def affineInvHomeomorph {c : ℝ} (hc : c ≠ 0) (y : Vec d) : Vec d ≃ₜ Vec d :=
  (Homeomorph.addRight (-y)).trans (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc))

theorem affineInvHomeomorph_apply {c : ℝ} (hc : c ≠ 0) (y x : Vec d) :
    affineInvHomeomorph hc y x = c⁻¹ • (x - y) := by
  simp [affineInvHomeomorph, sub_eq_add_neg]

theorem inv_smul_smul_add_sub {c : ℝ} (hc : c ≠ 0) (x y : Vec d) :
    c⁻¹ • (c • x + y - y) = x := by
  rw [add_sub_cancel_right, inv_smul_smul₀ hc]

theorem smul_inv_smul_sub_add {c : ℝ} (hc : c ≠ 0) (x y : Vec d) :
    c • (c⁻¹ • (x - y)) + y = x := by
  rw [smul_inv_smul₀ hc, sub_add_cancel]

/-- The transported test `ψ(x') = φ(c⁻¹ (x' - y))` of a test `φ` supported in `V` is a test
supported in `U` when `x ↦ c x + y` maps `V` into `U`. -/
theorem isSpatialTest_comp_affineInv {U V : Set (Vec d)} {φ : Vec d → ℝ} {c : ℝ} (hc : c ≠ 0)
    (y : Vec d) (hV : ∀ x ∈ V, c • x + y ∈ U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ V) :
    IsSpatialTest U (fun x' => φ (c⁻¹ • (x' - y))) := by
  have heq : (fun x' => φ (c⁻¹ • (x' - y))) = φ ∘ affineInvHomeomorph hc y := by
    funext x'
    simp [affineInvHomeomorph_apply]
  refine ⟨hφ.comp ((contDiff_const_smul _).comp (contDiff_id.sub contDiff_const)), ?_, ?_⟩
  · rw [heq]
    exact hcs.comp_homeomorph _
  · rw [heq, tsupport_comp_eq_preimage]
    intro x' hx'
    have h1 := hV _ (hsupp hx')
    rw [affineInvHomeomorph_apply, smul_inv_smul_sub_add hc] at h1
    exact h1

theorem fderiv_comp_affineInv_apply {φ : Vec d → ℝ} (hφ : Differentiable ℝ φ) (c : ℝ)
    (y x' v : Vec d) :
    fderiv ℝ (fun z => φ (c⁻¹ • (z - y))) x' v = c⁻¹ * fderiv ℝ φ (c⁻¹ • (x' - y)) v := by
  have hlin : HasFDerivAt (fun z : Vec d => c⁻¹ • (z - y))
      (c⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x' := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) x').sub_const y).const_smul c⁻¹
  have h : HasFDerivAt (fun z => φ (c⁻¹ • (z - y)))
      ((fderiv ℝ φ (c⁻¹ • (x' - y))).comp (c⁻¹ • ContinuousLinearMap.id ℝ (Vec d))) x' :=
    ((hφ _).hasFDerivAt).comp x' hlin
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem mul_eq_mul_mul_inv_mul {c : ℝ} (hc : c ≠ 0) (s M : ℝ) : s * M = c * (M * (c⁻¹ * s)) := by
  rw [show c * (M * (c⁻¹ * s)) = (c * c⁻¹) * (s * M) by ring, mul_inv_cancel₀ hc, one_mul]

theorem setIntegral_eq_integral_of_tsupport {V : Set (Vec d)} {φ : Vec d → ℝ}
    (hsupp : tsupport φ ⊆ V) {F : Vec d → ℝ} (hF : ∀ x, x ∉ tsupport φ → F x = 0) :
    ∫ x in V, F x = ∫ x, F x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hF x fun h => hx (hsupp h)

/-- **Weak gradients under `x ↦ c x + y`.** -/
theorem hasWeakGradientOn_comp_smul_add {U V : Set (Vec d)} {v : Vec d → ℝ}
    {g : Vec d → Vec d} {c : ℝ} (hc : 0 < c) (y : Vec d) (hV : ∀ x ∈ V, c • x + y ∈ U)
    (h : HasWeakGradient U v g) :
    _root_.Homogenization.HasWeakGradientOn V (fun x => c⁻¹ * v (c • x + y))
      (fun x => g (c • x + y)) := by
  intro i φ hφ hcs hsupp
  beta_reduce
  have hc0 : c ≠ 0 := hc.ne'
  set ψ : Vec d → ℝ := fun x' => φ (c⁻¹ • (x' - y)) with hψdef
  have hψ : IsSpatialTest U ψ := isSpatialTest_comp_affineInv hc0 y hV hφ hcs hsupp
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hderiv : ∀ x', coordinateDerivative i ψ x' =
      c⁻¹ * fderiv ℝ φ (c⁻¹ • (x' - y)) (basisVec i) := fun x' =>
    fderiv_comp_affineInv_apply hdiff c y x' _
  have hmain := (h i).2.2 ψ hψ
  beta_reduce at hmain
  rw [setIntegral_mul_spatialTest_eq_integral v (isSpatialTest_coordinateDerivative hψ i),
    setIntegral_mul_spatialTest_eq_integral (fun x => g x i) hψ] at hmain
  have hL : ∫ x in V, c⁻¹ * v (c • x + y) * fderiv ℝ φ x (basisVec i) =
      |c ^ d|⁻¹ * ∫ x', v x' * coordinateDerivative i ψ x' := by
    rw [setIntegral_eq_integral_of_tsupport
      (F := fun x => c⁻¹ * v (c • x + y) * fderiv ℝ φ x (basisVec i)) hsupp (fun x hx => by
        simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]), ← integral_comp_smul_add _ c y]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hderiv, inv_smul_smul_add_sub hc0]
    ring
  have hR : ∫ x in V, g (c • x + y) i * φ x =
      |c ^ d|⁻¹ * ∫ x', g x' i * ψ x' := by
    rw [setIntegral_eq_integral_of_tsupport (F := fun x => g (c • x + y) i * φ x) hsupp
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]), ← integral_comp_smul_add _ c y]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hψdef, inv_smul_smul_add_sub hc0]
  rw [hL, hR, hmain, mul_neg]

/-- **Weak solutions under `x ↦ c x + y`**, for a coefficient field `b` equal to `a ∘ A`
almost everywhere. -/
theorem isWeakSolutionOn_comp_smul_add {Λ : ℝ} (a : CoefficientField d Λ) {U V : Set (Vec d)}
    {g : Vec d → Vec d} {c : ℝ} (hc : 0 < c) (y : Vec d) (hV : ∀ x ∈ V, c • x + y ∈ U)
    (h : HasWeakDivergence U (fun x => (a x).mulVec (g x)) (fun _ => 0))
    {b : CoeffField d} (hb : ∀ᵐ x ∂volume, b x = a.field (c • x + y)) :
    IsWeakSolutionOn b V (fun x => g (c • x + y)) := by
  intro φ hφl
  beta_reduce
  have hc0 : c ≠ 0 := hc.ne'
  have hφ := hφl.contDiff
  have hcs := hφl.hasCompactSupport
  have hsupp := hφl.tsupport_subset
  set ψ : Vec d → ℝ := fun x' => φ (c⁻¹ • (x' - y)) with hψdef
  have hψ : IsSpatialTest U ψ := isSpatialTest_comp_affineInv hc0 y hV hφ hcs hsupp
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  set H : Vec d → ℝ := fun x' => dot ((a x').mulVec (g x')) (gradient ψ x') with hHdef
  have hHU : IntegrableOn H U volume :=
    integrableOn_dot_gradient_of_locallyIntegrableOn h.1 hψ
  have hH0 : ∀ x', x' ∉ tsupport ψ → H x' = 0 := fun x' hx' => by
    simp only [hHdef, gradient_eq_zero_of_notMem_tsupport hx']
    simp [dot]
  have hHint : Integrable H := by
    have hsub : Function.support H ⊆ U := fun x' hx' => by
      by_contra hxU
      exact hx' (hH0 x' fun hmem => hxU (hψ.2.2 hmem))
    exact (integrableOn_iff_integrable_of_support_subset hsub).mp hHU
  have hpt : ∀ x, b x = a.field (c • x + y) →
      vecDot (smoothGrad φ x) (matVecMul (b x) (g (c • x + y))) = c * H (c • x + y) := by
    intro x hx
    have hg : ∀ k, gradient ψ (c • x + y) k = c⁻¹ * smoothGrad φ x k := fun k => by
      simp only [hψdef, gradient, coordinateDerivative]
      rw [fderiv_comp_affineInv_apply hdiff c y, inv_smul_smul_add_sub hc0]
      rfl
    rw [hx]
    have e1 : vecDot (smoothGrad φ x) (matVecMul (a.field (c • x + y)) (g (c • x + y))) =
        ∑ k, smoothGrad φ x k * ((a.field (c • x + y)).mulVec (g (c • x + y))) k := rfl
    have e2 : H (c • x + y) = ∑ k, ((a.field (c • x + y)).mulVec (g (c • x + y))) k *
        (c⁻¹ * smoothGrad φ x k) := by
      simp only [hHdef, dot]
      exact Finset.sum_congr rfl fun k _ => by rw [hg k]
    rw [e1, e2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_eq_mul_mul_inv_mul hc0 _ _
  have hae : (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (g (c • x + y)))) =ᵐ[volume]
      fun x => c * H (c • x + y) := by
    filter_upwards [hb] with x hx
    exact hpt x hx
  have hint : Integrable (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (g (c • x + y)))) :=
    ((integrable_comp_smul_add hHint hc0 y).const_mul c).congr hae.symm
  refine ⟨hint.integrableOn, ?_⟩
  have hzero : ∫ x', H x' = 0 := by
    have h0 := h.2.2 ψ hψ
    simp only [zero_mul, integral_zero, neg_zero] at h0
    rw [setIntegral_dot_gradient_eq_integral _ hψ] at h0
    exact h0
  have hφ0 : ∀ x, x ∉ tsupport φ →
      vecDot (smoothGrad φ x) (matVecMul (b x) (g (c • x + y))) = 0 := fun x hx => by
    have : smoothGrad φ x = 0 := by
      funext k
      simp [smoothGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
    rw [this]
    simp [vecDot]
  rw [setIntegral_eq_integral_of_tsupport hsupp hφ0, integral_congr_ae hae, integral_const_mul,
    integral_comp_smul_add, hzero]
  ring

/-- **Square integrability under `x ↦ c x + y`.** -/
theorem MemLp.comp_smul_add_restrict {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    {U S : Set (Vec d)} (hU : MeasurableSet U) (hS : MeasurableSet S) {c : ℝ} (hc : c ≠ 0)
    (y : Vec d) (hSU : ∀ x ∈ S, c • x + y ∈ U) {p : ENNReal}
    (hf : MemLp f p (volume.restrict U)) :
    MemLp (fun x => f (c • x + y)) p (volume.restrict S) := by
  have hT : MeasurePreserving (fun x : Vec d => x + y)
      (volume.restrict ((fun x => x + y) ⁻¹' U)) (volume.restrict U) :=
    (measurePreserving_add_right volume y).restrict_preimage hU
  have h1 : MemLp (fun x => f (x + y)) p (volume.restrict ((fun x => x + y) ⁻¹' U)) :=
    hf.comp_measurePreserving hT
  have hsub : c • S ⊆ (fun x => x + y) ⁻¹' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hSU x hx
  have h2 : MemLp (fun x => f (x + y)) p (volume.restrict (c • S)) :=
    h1.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact MemLp.comp_smul_restrict hc hS h2

end QSH
