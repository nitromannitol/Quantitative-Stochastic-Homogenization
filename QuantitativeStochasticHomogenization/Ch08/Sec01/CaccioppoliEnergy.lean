import QuantitativeStochasticHomogenization.Ch08.Sec01.FluxEnergy
import QuantitativeStochasticHomogenization.Ch08.Sec01.CaccioppoliSlice

/-!
# The energy inequality behind the parabolic Caccioppoli inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 8.1, proof of Lemma 8.1. For a weak solution of `∂ₜu - ∇·(a∇u) = ∇·F` in `Q_{2r}` and every
`t ∈ (-r², 0]`,
`∫_{B_r} u(t)² + ∫_{-r²}^t ∫_{B_r} |∇u|² ≤ C r⁻² ∫_{Q_{2r}} u² + C |B_{2r}| ∫_{I_{2r}} ‖∇·F‖²_{H̲⁻¹(B_{2r})}`
with `C(d, Λ)`. The proof is the book's: the energy identity for the test function `η_r² u`, the
ellipticity of `a`, Young's inequality for the cross term `2 η_r u ∇η_r · a∇u`, the bound of the
pairing with `∇·F` on each time slice, and absorption.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace QSH

open PDE.Parabolic.WeakSlice PDE.Parabolic.Energy

variable {d : ℕ}

/-- The flux `a∇u + F` of a weak solution is square integrable. -/
theorem memLp_parabolicFlux {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) {U : Set (Vec d)}
    {I : Set ℝ} (u : PDE.ParH1Function U I) {F : Vec d × ℝ → Vec d}
    (hF : ∀ i, MemLp (fun z => F z i) 2 (volume.restrict (U ×ˢ I))) (i : Fin d) :
    MemLp (fun z => ((a z.1).mulVec (u.grad z) + F z) i) 2 (volume.restrict (U ×ˢ I)) := by
  have hae : ∀ᵐ z ∂(volume : Measure (Vec d × ℝ)), ellipticFieldOf a z.1 = a z.1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (ellipticFieldOf_ae_eq hΛ a)
  show MemLp (fun z => (a z.1).mulVec (u.grad z) i + F z i) 2 _
  refine MemLp.add ?_ (hF i)
  simp only [Matrix.mulVec, dotProduct]
  refine memLp_finsetSum _ fun j _ => ?_
  refine (u.gradMemL2 j).of_le_mul (c := Λ) ?_ ?_
  · have hm : AEStronglyMeasurable (fun z : Vec d × ℝ => a z.1 i j) (volume.restrict (U ×ˢ I)) :=
      (((measurable_pi_iff.1 (measurable_pi_iff.1 (measurable_ellipticFieldOf a) i) j).comp
        measurable_fst).aestronglyMeasurable).congr
        (ae_restrict_of_ae (hae.mono fun z hz => congrFun (congrFun hz i) j))
    exact hm.mul (u.gradMemL2 j).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (matrix_abs_entry_le (coefficientField_isEllipticMatrix a hΛ le_rfl z.1) i j) (norm_nonneg _)

/-- Almost every time slice of a square-integrable function on `U × J` is square integrable. -/
theorem ae_slice_memLp_restrict {U : Set (Vec d)} (hU : MeasurableSet U) {J : Set ℝ}
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (U ×ˢ J))) :
    ∀ᵐ τ ∂(volume.restrict J), MemLp (fun y => g (y, τ)) 2 (volume.restrict U) :=
  (ae_slice_memLp hU hg).mono fun _ h => (memLp_indicator_iff_restrict hU).1 h

/-- The pointwise lower bound of the elliptic part of the energy identity:
`∇u · a∇(η²u) ≥ ½ η² |∇u|² - 2Λ u² |∇η|²`. -/
theorem parabolic_flux_lower {Λ : ℝ} {A : Mat d} (hA : PDE.IsEllipticMatrix 1 Λ A) (g e : Vec d)
    (η w : ℝ) :
    η ^ 2 * PDE.vecNormSq g / 2 - 2 * Λ * w ^ 2 * PDE.vecNormSq e ≤
      ∑ i, PDE.matVecMul A g i * (η ^ 2 * g i + 2 * η * w * e i) := by
  have h := PDE.DGNM.abs_two_mul_mul_vecDot_le_caccioppoli (η := η) (w := w) hA g e
  have hell : 1 * PDE.vecNormSq g ≤ PDE.vecDot g (PDE.matVecMul A g) := hA.2.2.1 g
  have hsum : ∑ i, PDE.matVecMul A g i * (η ^ 2 * g i + 2 * η * w * e i) =
      η ^ 2 * PDE.vecDot g (PDE.matVecMul A g) +
        2 * η * w * PDE.vecDot (PDE.matVecMul A g) e := by
    simp only [PDE.vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have h2 := neg_abs_le (2 * η * w * PDE.vecDot (PDE.matVecMul A g) e)
  have h3 : η ^ 2 * PDE.vecNormSq g ≤ η ^ 2 * PDE.vecDot g (PDE.matVecMul A g) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  linarith

/-- The pairing term of the energy identity on a time slab `U × J`, `U = B_{2r}`:
`|∫_J ∫_U F · ∇(η_r² u)| ≤ 4d² |U| ∫_I ‖∇·F‖²_{H̲⁻¹(U)} + β ∫_J ∫_U u² + 1/8 ∫_J ∫_U η_r² |∇u|²`
with `β = (|U|^{-1/d} + 128d/r)²/(8d²)`, from the bound on each time slice. -/
theorem parabolicCaccioppoli_rhs (hd : 0 < d) {r : ℝ} (hr : 0 < r) {U : Set (Vec d)}
    (hU : U = ball (0 : Vec d) (2 * r)) {I : Set ℝ} (u : PDE.ParH1Function U I)
    {F : Vec d × ℝ → Vec d} (hF' : ∀ i, MemLp (fun z => F z i) 2 (volume.restrict (U ×ˢ I)))
    {J : Set ℝ} (hJI : J ⊆ I) :
    ENNReal.ofReal |∫ z in U ×ˢ J, ∑ i, F z i *
        ((parabolicCutoff hr).toFun z ^ 2 * u.grad z i + 2 * (parabolicCutoff hr).toFun z *
          u.toFun z * PDE.parSpaceGrad (parabolicCutoff hr).toFun z i)| ≤
      ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
          (∫⁻ τ in I, negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2) +
        ENNReal.ofReal (((volume U).toReal ^ (-(1 : ℝ) / d) + 2 * d * (64 / r)) ^ 2 /
            (8 * d ^ 2) * (∫ z in U ×ˢ J, u.toFun z ^ 2) +
          1 / 8 * ∫ z in U ×ˢ J, (parabolicCutoff hr).toFun z ^ 2 * PDE.vecNormSq (u.grad z)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h2r : 0 < 2 * r := by linarith
  have hUe : U = PDE.euclideanBall 0 (2 * r) := by rw [hU]; exact ball_eq_euclideanBall 0 h2r
  have hUo : IsOpen U := by rw [hUe]; exact PDE.isOpen_euclideanBall 0 (2 * r)
  have hUm : MeasurableSet U := hUo.measurableSet
  have hUconv : PDE.IsOpenBoundedConvexDomain U := by
    rw [hUe]; exact PDE.isOpenBoundedConvexDomain_euclideanBall 0 h2r
  have hUfin : volume U ≠ ⊤ := by rw [hUe]; exact PDE.volume_euclideanBall_ne_top 0 h2r.le
  have hU0 : volume U ≠ 0 := by rw [hUe]; exact (PDE.volume_euclideanBall_pos 0 h2r).ne'
  obtain ⟨η, hη⟩ : ∃ η : Vec d × ℝ → ℝ, η = (parabolicCutoff (d := d) hr).toFun := ⟨_, rfl⟩
  have hη0 : ∀ z, 0 ≤ η z := hη ▸ parabolicCutoff_nonneg hr
  have hη1 : ∀ z, η z ≤ 1 := hη ▸ parabolicCutoff_le_one hr
  have hηx : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ (64 / r) ^ 2 :=
    hη ▸ vecNormSq_parSpaceGrad_parabolicCutoff_le hr
  have hηC : ContDiff ℝ 1 η := hη ▸ (parabolicCutoff (d := d) hr).contDiff
  have hηc : Continuous η := hηC.continuous
  have hηxc : ∀ i, Continuous fun z => PDE.parSpaceGrad η z i := fun i =>
    (hηC.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hηxi : ∀ z i, |PDE.parSpaceGrad η z i| ≤ 64 / r := by
    intro z i
    have h1 := (sq_apply_le_vecNormSq (PDE.parSpaceGrad η z) i).trans (hηx z)
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 (by rwa [sq_abs])
  rw [← hη]
  have hsub : U ×ˢ J ⊆ U ×ˢ I := prod_mono subset_rfl hJI
  have hle : volume.restrict (U ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
    Measure.restrict_mono hsub le_rfl
  have hu2 : MemLp u.toFun 2 (volume.restrict (U ×ˢ J)) := u.memL2.mono_measure hle
  have hg2 : ∀ i, MemLp (fun z => u.grad z i) 2 (volume.restrict (U ×ˢ J)) := fun i =>
    (u.gradMemL2 i).mono_measure hle
  have hF2 : ∀ i, MemLp (fun z => F z i) 2 (volume.restrict (U ×ˢ J)) := fun i =>
    (hF' i).mono_measure hle
  have hSint : IntegrableOn (fun z => u.toFun z ^ 2) (U ×ˢ J) := hu2.integrable_sq
  have hgsq : IntegrableOn (fun z => PDE.vecNormSq (u.grad z)) (U ×ˢ J) := by
    unfold PDE.vecNormSq PDE.vecDot
    exact integrable_finsetSum _ fun i _ => (hg2 i).integrable_mul (hg2 i)
  have hDint : IntegrableOn (fun z => η z ^ 2 * PDE.vecNormSq (u.grad z)) (U ×ˢ J) := by
    refine hgsq.bdd_mul (c := 1) (hηc.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hη0 z) (hη1 z)
  have hW2 : ∀ i, MemLp (fun z => η z ^ 2 * u.grad z i +
      2 * η z * u.toFun z * PDE.parSpaceGrad η z i) 2 (volume.restrict (U ×ˢ J)) := by
    intro i
    refine MemLp.add ?_ ?_
    · refine (hg2 i).of_le_mul (c := 1) ((hηc.pow 2).aestronglyMeasurable.mul
        (hg2 i).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (pow_le_one₀ (hη0 z) (hη1 z)) (norm_nonneg _)
    · refine hu2.of_le_mul (c := 2 * (64 / r))
        (((continuous_const.mul hηc).aestronglyMeasurable.mul hu2.aestronglyMeasurable).mul
          (hηxc i).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (hη0 z), Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
      have h1 := hη1 z
      have h2 := hηxi z i
      have h3 := abs_nonneg (u.toFun z)
      have h4 := hη0 z
      calc 2 * η z * |u.toFun z| * |PDE.parSpaceGrad η z i| ≤ 2 * 1 * |u.toFun z| * (64 / r) := by
            gcongr
        _ = 2 * (64 / r) * |u.toFun z| := by ring
  set b₂ : Vec d × ℝ → ℝ := fun z => ∑ i, F z i *
    (η z ^ 2 * u.grad z i + 2 * η z * u.toFun z * PDE.parSpaceGrad η z i) with hb₂
  have hB2int : IntegrableOn b₂ (U ×ˢ J) :=
    integrable_finsetSum _ fun i _ => (hF2 i).integrable_mul (hW2 i)
  -- the right-hand side on each time slice
  obtain ⟨hPint, hPeq⟩ := integral_prod_slices hB2int
  obtain ⟨hY1int, hY1eq⟩ := integral_prod_slices hSint
  obtain ⟨hY2int, hY2eq⟩ := integral_prod_slices hDint
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ,
      β = ((volume U).toReal ^ (-(1 : ℝ) / d) + 2 * d * (64 / r)) ^ 2 / (8 * d ^ 2) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hsl : ∀ᵐ τ ∂(volume.restrict J), ENNReal.ofReal |∫ x in U, b₂ (x, τ)| ≤
      ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
          negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2 +
        ENNReal.ofReal (β * (∫ x in U, u.toFun (x, τ) ^ 2) +
          1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ))) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hJI (ae_slice_memLp_restrict hUm u.memL2)
    have h2 := ae_restrict_of_ae_restrict_of_subset hJI
      (ae_all_iff.2 fun i => ae_slice_memLp_restrict hUm (u.gradMemL2 i))
    have h3 := ae_restrict_of_ae_restrict_of_subset hJI
      (ae_all_iff.2 fun i => ae_slice_memLp_restrict hUm (hF' i))
    have h4 := ae_restrict_of_ae_restrict_of_subset hJI u.sliceWeakGradient
    filter_upwards [h1, h2, h3, h4] with τ hτ1 hτ2 hτ3 hτ4
    obtain ⟨hsm, hcs, hts, hgr⟩ := slice_parabolicCutoff (d := d) hr τ
    rw [← hη] at hsm hcs hts hgr
    rw [← hU] at hts
    let w : PDE.H1Function U :=
      { toFun := fun x => u.toFun (x, τ)
        grad := fun x => u.grad (x, τ)
        memL2 := hτ1
        gradMemL2 := hτ2
        hasWeakGradient := hτ4 }
    have key := slicePairing_le hd hUconv hU0 hUfin w hsm hcs hts (fun x => hη0 _)
      (fun x => hη1 _) (K := 64 / r) (by positivity) (fun x => by rw [hgr x]; exact hηx _) hτ3
    simp only [hgr] at key
    rw [hβdef]
    exact key
  have hYint : IntegrableOn (fun τ => β * (∫ x in U, u.toFun (x, τ) ^ 2) +
      1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ))) J :=
    (hY1int.const_mul β).add (hY2int.const_mul (1 / 8))
  have hY0 : 0 ≤ᵐ[volume.restrict J] fun τ => β * (∫ x in U, u.toFun (x, τ) ^ 2) +
      1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ)) := by
    refine Eventually.of_forall fun τ => ?_
    have e1 : 0 ≤ ∫ x in U, u.toFun (x, τ) ^ 2 := integral_nonneg fun x => sq_nonneg _
    have e2 : 0 ≤ ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ)) :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)
    have e3 := mul_nonneg hβ0 e1
    have e4 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) e2
    show 0 ≤ β * (∫ x in U, u.toFun (x, τ) ^ 2) +
      1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ))
    linarith
  have hYeq : ∫ τ in J, (β * (∫ x in U, u.toFun (x, τ) ^ 2) +
      1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ))) =
      β * (∫ z in U ×ˢ J, u.toFun z ^ 2) +
        1 / 8 * ∫ z in U ×ˢ J, η z ^ 2 * PDE.vecNormSq (u.grad z) := by
    rw [integral_add (hY1int.const_mul _) (hY2int.const_mul _), integral_const_mul,
      integral_const_mul, hY1eq, hY2eq]
  have hB2le : ENNReal.ofReal |∫ z in U ×ˢ J, b₂ z| ≤
      ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
          (∫⁻ τ in I, negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2) +
        ENNReal.ofReal (β * (∫ z in U ×ˢ J, u.toFun z ^ 2) +
          1 / 8 * ∫ z in U ×ˢ J, η z ^ 2 * PDE.vecNormSq (u.grad z)) := by
    rw [hPeq, ← hYeq]
    calc ENNReal.ofReal |∫ τ in J, ∫ x in U, b₂ (x, τ)|
        ≤ ENNReal.ofReal (∫ τ in J, |∫ x in U, b₂ (x, τ)|) :=
          ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
      _ = ∫⁻ τ in J, ENNReal.ofReal |∫ x in U, b₂ (x, τ)| :=
          ofReal_integral_eq_lintegral_ofReal hPint.abs
            (Eventually.of_forall fun τ => abs_nonneg _)
      _ ≤ ∫⁻ τ in J, (ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
            negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2 +
          ENNReal.ofReal (β * (∫ x in U, u.toFun (x, τ) ^ 2) +
            1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ)))) :=
          lintegral_mono_ae hsl
      _ = ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
            (∫⁻ τ in J, negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2) +
          ENNReal.ofReal (∫ τ in J, (β * (∫ x in U, u.toFun (x, τ) ^ 2) +
            1 / 8 * ∫ x in U, η (x, τ) ^ 2 * PDE.vecNormSq (u.grad (x, τ)))) := by
          rw [lintegral_add_right' _ hYint.aemeasurable.ennreal_ofReal,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ofReal_integral_eq_lintegral_ofReal hYint hY0]
      _ ≤ _ := by
          gcongr
  rw [hβdef] at hB2le
  exact hB2le

/-- The energy identity of the parabolic Caccioppoli inequality with the elliptic and the
time-derivative terms estimated: for `t ∈ (-r², 0]` and `J = (-3r², t]`,
`½ ∫_U η_r(t)² u(t)² + ½ ∫_J ∫_U η_r² |∇u|² - (M/(2r²) + 2Λ(64/r)²) ∫_J ∫_U u² ≤ |∫_J ∫_U F · ∇(η_r² u)|`. -/
theorem parabolicCaccioppoli_identity {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) {r : ℝ}
    (hr : 0 < r) {M : ℝ} (hM : ∀ y, |rampDeriv y| ≤ M) {U : Set (Vec d)}
    (hU : U = ball (0 : Vec d) (2 * r)) {I : Set ℝ} (hI : I = Ioc (-(2 * r) ^ 2) 0)
    (u : PDE.ParH1Function U I) {F : Vec d × ℝ → Vec d}
    (hF' : ∀ i, MemLp (fun z => F z i) 2 (volume.restrict (U ×ˢ I)))
    (hu : IsParabolicSolution a U I u F) {t : ℝ}
    (ht : t ∈ Ioc (-r ^ 2) (0 : ℝ)) :
    1 / 2 * (∫ x in U, (parabolicCutoff hr).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) +
      1 / 2 * (∫ z in U ×ˢ Ioc (-3 * r ^ 2) t,
        (parabolicCutoff hr).toFun z ^ 2 * PDE.vecNormSq (u.grad z)) -
      M / (2 * r ^ 2) * (∫ z in U ×ˢ Ioc (-3 * r ^ 2) t, u.toFun z ^ 2) -
      2 * Λ * (64 / r) ^ 2 *
        (∫ z in U ×ˢ Ioc (-3 * r ^ 2) t, u.toFun z ^ 2) ≤
    |∫ z in U ×ˢ Ioc (-3 * r ^ 2) t, ∑ i, F z i *
        ((parabolicCutoff hr).toFun z ^ 2 * u.grad z i + 2 * (parabolicCutoff hr).toFun z *
          u.toFun z * PDE.parSpaceGrad (parabolicCutoff hr).toFun z i)| := by
  have hΛ0 : 0 < Λ := by linarith
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have h2r : 0 < 2 * r := by linarith
  have hUo : IsOpen U := by
    rw [hU, ball_eq_euclideanBall 0 h2r]; exact PDE.isOpen_euclideanBall 0 (2 * r)
  have hIo : I.OrdConnected := by rw [hI]; exact ordConnected_Ioc
  have hu' : IsParabolicFluxSolution U I u (fun z => (a z.1).mulVec (u.grad z) + F z) := hu
  have hG := memLp_parabolicFlux hΛ a u hF'
  obtain ⟨η, hη⟩ : ∃ η : Vec d × ℝ → ℝ, η = (parabolicCutoff (d := d) hr).toFun := ⟨_, rfl⟩
  have hη0 : ∀ z, 0 ≤ η z := hη ▸ parabolicCutoff_nonneg hr
  have hη1 : ∀ z, η z ≤ 1 := hη ▸ parabolicCutoff_le_one hr
  have hηt : ∀ z, |PDE.parTimeDeriv η z| ≤ M / (2 * r ^ 2) :=
    hη ▸ abs_parTimeDeriv_parabolicCutoff_le hM hr
  have hηx : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ (64 / r) ^ 2 :=
    hη ▸ vecNormSq_parSpaceGrad_parabolicCutoff_le hr
  have hηC : ContDiff ℝ 1 η := hη ▸ (parabolicCutoff (d := d) hr).contDiff
  have hηc : Continuous η := hηC.continuous
  have hηxc : ∀ i, Continuous fun z => PDE.parSpaceGrad η z i := fun i =>
    (hηC.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hηxi : ∀ z i, |PDE.parSpaceGrad η z i| ≤ 64 / r := by
    intro z i
    have h1 := (sq_apply_le_vecNormSq (PDE.parSpaceGrad η z) i).trans (hηx z)
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 (by rwa [sq_abs])
  rw [← hη]
  have hs₀ : -3 * r ^ 2 ∈ I := by rw [hI]; exact ⟨by nlinarith, by nlinarith⟩
  have htI : t ∈ I := by rw [hI]; exact ⟨by nlinarith [ht.1], ht.2⟩
  have hs₀t : -3 * r ^ 2 < t := by nlinarith [ht.1]
  obtain ⟨φ, hφ⟩ : ∃ φ : PDE.ParCutoff U I, φ.toFun = (parabolicCutoff (d := d) hr).toFun := by
    subst hU hI
    exact ⟨parabolicCutoff hr, rfl⟩
  obtain ⟨hAi, hBi, hid⟩ := fluxEnergyIdentity hUo hIo u hG hu' φ hs₀ htI hs₀t
  rw [hφ, ← hη] at hAi hBi hid
  obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Ioc (-3 * r ^ 2) t := ⟨_, rfl⟩
  rw [← hJdef] at hAi hBi hid ⊢
  have hJI : J ⊆ I := by
    rw [hJdef, hI]; exact Ioc_subset_Ioc (by nlinarith) ht.2
  have hsub : U ×ˢ J ⊆ U ×ˢ I := prod_mono subset_rfl hJI
  have hle : volume.restrict (U ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
    Measure.restrict_mono hsub le_rfl
  have hu2 : MemLp u.toFun 2 (volume.restrict (U ×ˢ J)) := u.memL2.mono_measure hle
  have hg2 : ∀ i, MemLp (fun z => u.grad z i) 2 (volume.restrict (U ×ˢ J)) := fun i =>
    (u.gradMemL2 i).mono_measure hle
  have hF2 : ∀ i, MemLp (fun z => F z i) 2 (volume.restrict (U ×ˢ J)) := fun i =>
    (hF' i).mono_measure hle
  have hSint : IntegrableOn (fun z => u.toFun z ^ 2) (U ×ˢ J) := hu2.integrable_sq
  have hgsq : IntegrableOn (fun z => PDE.vecNormSq (u.grad z)) (U ×ˢ J) := by
    unfold PDE.vecNormSq PDE.vecDot
    exact integrable_finsetSum _ fun i _ => (hg2 i).integrable_mul (hg2 i)
  have hDint : IntegrableOn (fun z => η z ^ 2 * PDE.vecNormSq (u.grad z)) (U ×ˢ J) := by
    refine hgsq.bdd_mul (c := 1) (hηc.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hη0 z) (hη1 z)
  have hW2 : ∀ i, MemLp (fun z => η z ^ 2 * u.grad z i +
      2 * η z * u.toFun z * PDE.parSpaceGrad η z i) 2 (volume.restrict (U ×ˢ J)) := by
    intro i
    refine MemLp.add ?_ ?_
    · refine (hg2 i).of_le_mul (c := 1) ((hηc.pow 2).aestronglyMeasurable.mul
        (hg2 i).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (pow_le_one₀ (hη0 z) (hη1 z)) (norm_nonneg _)
    · refine hu2.of_le_mul (c := 2 * (64 / r))
        (((continuous_const.mul hηc).aestronglyMeasurable.mul hu2.aestronglyMeasurable).mul
          (hηxc i).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (hη0 z), Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
      have h1 := hη1 z
      have h2 := hηxi z i
      have h3 := abs_nonneg (u.toFun z)
      have h4 := hη0 z
      calc 2 * η z * |u.toFun z| * |PDE.parSpaceGrad η z i| ≤ 2 * 1 * |u.toFun z| * (64 / r) := by
            gcongr
        _ = 2 * (64 / r) * |u.toFun z| := by ring
  set b₁ : Vec d × ℝ → ℝ := fun z => ∑ i, (a z.1).mulVec (u.grad z) i *
    (η z ^ 2 * u.grad z i + 2 * η z * u.toFun z * PDE.parSpaceGrad η z i) with hb₁
  set b₂ : Vec d × ℝ → ℝ := fun z => ∑ i, F z i *
    (η z ^ 2 * u.grad z i + 2 * η z * u.toFun z * PDE.parSpaceGrad η z i) with hb₂
  have hB2int : IntegrableOn b₂ (U ×ˢ J) :=
    integrable_finsetSum _ fun i _ => (hF2 i).integrable_mul (hW2 i)
  have hsplit : ∀ z, (∑ i, ((a z.1).mulVec (u.grad z) + F z) i *
      (η z ^ 2 * u.grad z i + 2 * η z * u.toFun z * PDE.parSpaceGrad η z i)) = b₁ z + b₂ z := by
    intro z
    simp only [hb₁, hb₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hB1int : IntegrableOn b₁ (U ×ˢ J) := by
    refine (hBi.sub hB2int).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit z]
    ring
  have hBeq : ∫ z in U ×ˢ J, (∑ i, ((a z.1).mulVec (u.grad z) + F z) i *
      (η z ^ 2 * u.grad z i + 2 * η z * u.toFun z * PDE.parSpaceGrad η z i)) =
      (∫ z in U ×ˢ J, b₁ z) + ∫ z in U ×ˢ J, b₂ z := by
    rw [← integral_add hB1int hB2int]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  -- the lower bound of the elliptic part
  have hlowpt : ∀ z, η z ^ 2 * PDE.vecNormSq (u.grad z) / 2 -
      2 * Λ * (64 / r) ^ 2 * u.toFun z ^ 2 ≤ b₁ z := by
    intro z
    have h := parabolic_flux_lower (coefficientField_isEllipticMatrix a hΛ le_rfl z.1)
      (u.grad z) (PDE.parSpaceGrad η z) (η z) (u.toFun z)
    have h2 : 2 * Λ * u.toFun z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η z) ≤
        2 * Λ * (64 / r) ^ 2 * u.toFun z ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hηx z)
        (mul_nonneg (mul_nonneg zero_le_two hΛ0.le) (sq_nonneg (u.toFun z)))
      linarith
    exact (by linarith : η z ^ 2 * PDE.vecNormSq (u.grad z) / 2 -
      2 * Λ * (64 / r) ^ 2 * u.toFun z ^ 2 ≤ η z ^ 2 * PDE.vecNormSq (u.grad z) / 2 -
        2 * Λ * u.toFun z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η z)).trans h
  have hlow : (∫ z in U ×ˢ J, η z ^ 2 * PDE.vecNormSq (u.grad z)) / 2 -
      2 * Λ * (64 / r) ^ 2 * (∫ z in U ×ˢ J, u.toFun z ^ 2) ≤ ∫ z in U ×ˢ J, b₁ z := by
    have h := integral_mono ((hDint.div_const 2).sub (hSint.const_mul (2 * Λ * (64 / r) ^ 2)))
      hB1int hlowpt
    simp only [Pi.sub_apply] at h
    rwa [integral_sub (hDint.div_const 2) (hSint.const_mul _), integral_div,
      integral_const_mul] at h
  -- the bound of the time-derivative term
  have hApt : ∀ z, u.toFun z ^ 2 * η z * PDE.parTimeDeriv η z ≤
      M / (2 * r ^ 2) * u.toFun z ^ 2 := by
    intro z
    have h1 : η z * PDE.parTimeDeriv η z ≤ M / (2 * r ^ 2) :=
      (le_abs_self _).trans (by
        rw [abs_mul, abs_of_nonneg (hη0 z)]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hη1 z)).trans (hηt z))
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (u.toFun z))
    linarith
  have hA : (∫ z in U ×ˢ J, u.toFun z ^ 2 * η z * PDE.parTimeDeriv η z) ≤
      M / (2 * r ^ 2) * ∫ z in U ×ˢ J, u.toFun z ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono hAi (hSint.const_mul _) hApt
  -- the energy identity, with the vanishing of the cutoff at `-3r²`
  have hE0 : ∫ x in U, η (x, -3 * r ^ 2) ^ 2 * u.toFun (x, -3 * r ^ 2) ^ 2 = 0 := by
    have h0 : ∀ x, η (x, -3 * r ^ 2) = 0 := fun x => by
      rw [hη]
      exact parabolicCutoff_eq_zero hr x le_rfl
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
    show η (x, -3 * r ^ 2) ^ 2 * u.toFun (x, -3 * r ^ 2) ^ 2 = 0
    rw [h0 x]
    ring
  rw [hE0, hBeq] at hid
  obtain ⟨S', hS'⟩ : ∃ S', S' = ∫ z in U ×ˢ J, u.toFun z ^ 2 := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D', D' = ∫ z in U ×ˢ J, η z ^ 2 * PDE.vecNormSq (u.grad z) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E', E' = ∫ x in U, η (x, t) ^ 2 * u.toFun (x, t) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B₂, B₂ = ∫ z in U ×ˢ J, b₂ z := ⟨_, rfl⟩
  rw [← hS', ← hD'] at hlow ⊢
  rw [← hS'] at hA
  rw [← hE', ← hB₂] at hid
  rw [← hE', ← hB₂]
  linarith only [hid, hlow, hA, neg_le_abs B₂]

/-- **The energy inequality of Lemma 8.1.** For a weak solution of `∂ₜu - ∇·(a∇u) = ∇·F` in
`Q_{2r}` and `t ∈ (-r², 0]`,
`∫_{B_r} u(t)² + ∫_{-r²}^t ∫_{B_r} |∇u|² ≤ C r⁻² ∫_{Q_{2r}} u² + C |B_{2r}| ∫_{I_{2r}} ‖∇·F‖²_{H̲⁻¹(B_{2r})}`
with `C` depending only on `d` and `Λ`. -/
theorem parabolicCaccioppoli_energy {Λ : ℝ} (hΛ : 1 ≤ Λ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoefficientField d Λ) (r : ℝ), 0 < r →
      ∀ (u : PDE.ParH1Function (ball (0 : Vec d) (2 * r)) (Ioc (-(2 * r) ^ 2) 0))
      (F : Vec d × ℝ → Vec d),
      (∀ i, MemLp (fun z => F z i) 2 (volume.restrict (parabolicCylinder d (2 * r)))) →
      IsParabolicSolution a (ball 0 (2 * r)) (Ioc (-(2 * r) ^ 2) 0) u F →
      ∀ t ∈ Ioc (-r ^ 2) (0 : ℝ),
        ENNReal.ofReal ((∫ x in ball (0 : Vec d) r, u.toFun (x, t) ^ 2) +
            ∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, euclideanSq (u.grad z)) ≤
          ENNReal.ofReal (C * (r ^ 2)⁻¹ * ∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2) +
          ENNReal.ofReal (C * volume.real (ball (0 : Vec d) (2 * r))) *
            ∫⁻ τ in Ioc (-(2 * r) ^ 2) 0,
              negativeSobolevOneNorm 2 (ball (0 : Vec d) (2 * r)) (fun _ => 0)
                (fun x => F (x, τ)) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_rampDeriv_bound
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ PDE.volume_euclideanBall_toReal_pos 0 one_pos
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁, c₁ = ω ^ (-(1 : ℝ) / d) := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := hc₁def ▸ Real.rpow_nonneg hω.le _
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ,
      C₀ = M / 2 + 2 * Λ * 64 ^ 2 + (c₁ / 2 + 128 * d) ^ 2 / (8 * d ^ 2) := ⟨_, rfl⟩
  have hC₀ : 0 ≤ C₀ := by
    have h1 : 0 ≤ 2 * Λ * 64 ^ 2 := mul_nonneg (mul_nonneg zero_le_two hΛ0.le) (by norm_num)
    have h2 : 0 ≤ (c₁ / 2 + 128 * d) ^ 2 / (8 * d ^ 2) := by positivity
    have h3 : 0 ≤ M / 2 := div_nonneg hM0 zero_le_two
    rw [hC₀def]
    linarith
  have hd2 : 0 < (d : ℝ) ^ 2 := pow_pos hdR 2
  refine ⟨3 * C₀ + 11 * d ^ 2, by linarith, ?_⟩
  intro a r hr
  have h2r : 0 < 2 * r := by linarith
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  -- the ball `U = B_{2r}`
  set U := ball (0 : Vec d) (2 * r) with hUdef
  set I := Ioc (-(2 * r) ^ 2) (0 : ℝ) with hIdef
  intro u F hF hu t ht
  have hUe : U = PDE.euclideanBall 0 (2 * r) := ball_eq_euclideanBall 0 h2r
  have hUo : IsOpen U := by rw [hUe]; exact PDE.isOpen_euclideanBall 0 (2 * r)
  have hUm : MeasurableSet U := hUo.measurableSet
  have hUconv : PDE.IsOpenBoundedConvexDomain U := by
    rw [hUe]; exact PDE.isOpenBoundedConvexDomain_euclideanBall 0 h2r
  have hUfin : volume U ≠ ⊤ := by rw [hUe]; exact PDE.volume_euclideanBall_ne_top 0 h2r.le
  have hU0 : volume U ≠ 0 := by rw [hUe]; exact (PDE.volume_euclideanBall_pos 0 h2r).ne'
  have hUvol : (volume U).toReal = (2 * r) ^ d * ω := by
    rw [hUe, hωdef]; exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos 0 h2r
  have hρ : (volume U).toReal ^ (-(1 : ℝ) / d) = c₁ / (2 * r) := by
    rw [hUvol, Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast,
      ← Real.rpow_mul h2r.le]
    have e : (d : ℝ) * (-(1 : ℝ) / d) = -1 := by field_simp
    rw [e, Real.rpow_neg_one, hc₁def]
    ring
  have hF' : ∀ i, MemLp (fun z => F z i) 2 (volume.restrict (U ×ˢ I)) := hF
  have htI : t ∈ I := ⟨by nlinarith [ht.1], ht.2⟩
  have hid := parabolicCaccioppoli_identity hΛ a hr hM rfl rfl u hF' hu ht
  obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Ioc (-3 * r ^ 2) t := ⟨_, rfl⟩
  have hJI : J ⊆ I := by
    rw [hJdef]; exact Ioc_subset_Ioc (by nlinarith) ht.2
  have hrhs := parabolicCaccioppoli_rhs hd hr rfl u hF' hJI
  obtain ⟨η, hη⟩ : ∃ η : Vec d × ℝ → ℝ, η = (parabolicCutoff (d := d) hr).toFun := ⟨_, rfl⟩
  have hη0 : ∀ z, 0 ≤ η z := hη ▸ parabolicCutoff_nonneg hr
  have hη1 : ∀ z, η z ≤ 1 := hη ▸ parabolicCutoff_le_one hr
  have hηc : Continuous η := (hη ▸ (parabolicCutoff (d := d) hr).contDiff).continuous
  rw [← hη] at hid hrhs
  rw [← hJdef] at hid
  have hsub : U ×ˢ J ⊆ U ×ˢ I := prod_mono subset_rfl hJI
  have hle : volume.restrict (U ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
    Measure.restrict_mono hsub le_rfl
  have hg2 : ∀ i, MemLp (fun z => u.grad z i) 2 (volume.restrict (U ×ˢ J)) := fun i =>
    (u.gradMemL2 i).mono_measure hle
  have hgsq : IntegrableOn (fun z => PDE.vecNormSq (u.grad z)) (U ×ˢ J) := by
    unfold PDE.vecNormSq PDE.vecDot
    exact integrable_finsetSum _ fun i _ => (hg2 i).integrable_mul (hg2 i)
  have hDint : IntegrableOn (fun z => η z ^ 2 * PDE.vecNormSq (u.grad z)) (U ×ˢ J) := by
    refine hgsq.bdd_mul (c := 1) (hηc.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hη0 z) (hη1 z)
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ,
      β = ((volume U).toReal ^ (-(1 : ℝ) / d) + 2 * d * (64 / r)) ^ 2 / (8 * d ^ 2) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  rw [← hβdef] at hrhs
  obtain ⟨S', hS'⟩ : ∃ S', S' = ∫ z in U ×ˢ J, u.toFun z ^ 2 := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D', D' = ∫ z in U ×ˢ J, η z ^ 2 * PDE.vecNormSq (u.grad z) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E', E' = ∫ x in U, η (x, t) ^ 2 * u.toFun (x, t) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B₂, B₂ = ∫ z in U ×ˢ J, ∑ i, F z i *
      (η z ^ 2 * u.grad z i + 2 * η z * u.toFun z * PDE.parSpaceGrad η z i) := ⟨_, rfl⟩
  rw [← hS', ← hD', ← hE', ← hB₂] at hid
  rw [← hS', ← hD', ← hB₂] at hrhs
  have hZ0 : 0 ≤ β * S' + 1 / 8 * D' := by
    have e1 : 0 ≤ S' := hS' ▸ integral_nonneg fun z => sq_nonneg _
    have e2 : 0 ≤ D' := hD' ▸ integral_nonneg fun z =>
      mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)
    linarith only [mul_nonneg hβ0 e1, e2]
  have hX : ENNReal.ofReal (1 / 2 * E' + 1 / 2 * D' - M / (2 * r ^ 2) * S' -
      2 * Λ * (64 / r) ^ 2 * S' - (β * S' + 1 / 8 * D')) ≤
      ENNReal.ofReal (4 * d ^ 2 * volume.real U) *
        (∫⁻ τ in I, negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2) := by
    rw [ENNReal.ofReal_sub _ hZ0]
    exact tsub_le_iff_right.2 ((ENNReal.ofReal_le_ofReal hid).trans hrhs)
  -- the left-hand side
  have hBr : ball (0 : Vec d) r ⊆ U := fun x hx => by
    change euclideanNorm (x - 0) < 2 * r
    have : euclideanNorm (x - 0) < r := hx
    linarith
  have hEint : IntegrableOn (fun x => η (x, t) ^ 2 * u.toFun (x, t) ^ 2) U := by
    have := slice_integrable hUo u (parabolicCutoff hr) htI
    rwa [← hη] at this
  have hLHS1 : ∫ x in ball (0 : Vec d) r, u.toFun (x, t) ^ 2 ≤ E' := by
    rw [hE']
    calc ∫ x in ball (0 : Vec d) r, u.toFun (x, t) ^ 2 =
        ∫ x in ball (0 : Vec d) r, η (x, t) ^ 2 * u.toFun (x, t) ^ 2 := by
          refine setIntegral_congr_fun (measurableSet_ball 0 r) fun x hx => ?_
          rw [hη, parabolicCutoff_eq_one hr hx ht.1.le]
          ring
      _ ≤ ∫ x in U, η (x, t) ^ 2 * u.toFun (x, t) ^ 2 :=
          setIntegral_mono_set hEint
            (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (Eventually.of_forall hBr)
  have hsub2 : ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t ⊆ U ×ˢ J := by
    rw [hJdef]
    exact prod_mono hBr (Ioc_subset_Ioc (by nlinarith) le_rfl)
  have hLHS2 : ∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, euclideanSq (u.grad z) ≤ D' := by
    rw [hD']
    calc ∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, euclideanSq (u.grad z) =
        ∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, η z ^ 2 * PDE.vecNormSq (u.grad z) := by
          refine setIntegral_congr_fun ((measurableSet_ball 0 r).prod measurableSet_Ioc)
            fun z hz => ?_
          have h1 : η z = 1 := by
            rw [hη]
            exact parabolicCutoff_eq_one hr hz.1 hz.2.1.le
          rw [h1, one_pow, one_mul]
          rfl
      _ ≤ ∫ z in U ×ˢ J, η z ^ 2 * PDE.vecNormSq (u.grad z) :=
          setIntegral_mono_set hDint
            (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
            (Eventually.of_forall hsub2)
  have hS₂ : S' ≤ ∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2 := by
    rw [hS']
    exact setIntegral_mono_set
      ((u.memL2 : MemLp u.toFun 2 (volume.restrict (parabolicCylinder d (2 * r)))).integrable_sq)
      (Eventually.of_forall fun z => sq_nonneg _) (Eventually.of_forall hsub)
  have hE'0 : 0 ≤ E' := hE' ▸ integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS'0 : 0 ≤ S' := hS' ▸ integral_nonneg fun z => sq_nonneg _
  have hγ : M / (2 * r ^ 2) + 2 * Λ * (64 / r) ^ 2 + β = C₀ * (r ^ 2)⁻¹ := by
    rw [hβdef, hρ, hC₀def]
    field_simp
    ring
  have hE'0 : 0 ≤ E' := hE' ▸ integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS'0 : 0 ≤ S' := hS' ▸ integral_nonneg fun z => sq_nonneg _
  have hγ : M / (2 * r ^ 2) + 2 * Λ * (64 / r) ^ 2 + β = C₀ * (r ^ 2)⁻¹ := by
    rw [hβdef, hρ, hC₀def]
    field_simp
    ring
  -- assembly
  obtain ⟨L, hL⟩ : ∃ L, L =
      ∫⁻ τ in I, negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, τ)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = 1 / 2 * E' + 1 / 2 * D' - M / (2 * r ^ 2) * S' -
      2 * Λ * (64 / r) ^ 2 * S' - (β * S' + 1 / 8 * D') := ⟨_, rfl⟩
  rw [← hL, ← hXdef] at hX
  have hsum : (∫ x in ball (0 : Vec d) r, u.toFun (x, t) ^ 2) +
      (∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, euclideanSq (u.grad z)) ≤
      (3 * C₀ + 11 * d ^ 2) * (r ^ 2)⁻¹ * (∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2) +
        8 / 3 * X := by
    have h1 : (8 / 3 * C₀) * (r ^ 2)⁻¹ * S' ≤
        (3 * C₀ + 11 * d ^ 2) * (r ^ 2)⁻¹ * (∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2) := by
      have hr2' : 0 ≤ (r ^ 2)⁻¹ := inv_nonneg.mpr hr2.le
      have hK0 : (0 : ℝ) ≤ 3 * C₀ + 11 * d ^ 2 := by linarith only [hC₀, hd2]
      have h4 := mul_le_mul_of_nonneg_left hS₂ (mul_nonneg hK0 hr2')
      have h2 : (8 / 3 * C₀) * (r ^ 2)⁻¹ * S' ≤ (3 * C₀ + 11 * d ^ 2) * (r ^ 2)⁻¹ * S' := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hr2') hS'0
        linarith only [hC₀, hd2]
      linarith only [h2, h4]
    have h3 : (8 / 3 * C₀) * (r ^ 2)⁻¹ * S' =
        8 / 3 * (M / (2 * r ^ 2) * S') + 8 / 3 * (2 * Λ * (64 / r) ^ 2 * S') +
          8 / 3 * (β * S') := by
      rw [show 8 / 3 * C₀ * (r ^ 2)⁻¹ * S' = 8 / 3 * ((C₀ * (r ^ 2)⁻¹) * S') by ring, ← hγ]
      ring
    linarith only [hLHS1, hLHS2, h1, h3, hXdef, hE'0]
  have hX0 : 0 ≤ (8 : ℝ) / 3 := by norm_num
  rw [← hL]
  calc ENNReal.ofReal ((∫ x in ball (0 : Vec d) r, u.toFun (x, t) ^ 2) +
        ∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, euclideanSq (u.grad z))
      ≤ ENNReal.ofReal ((3 * C₀ + 11 * d ^ 2) * (r ^ 2)⁻¹ *
            (∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2)) +
          ENNReal.ofReal (8 / 3 * X) :=
        (ENNReal.ofReal_le_ofReal hsum).trans ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal ((3 * C₀ + 11 * d ^ 2) * (r ^ 2)⁻¹ *
            (∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2)) +
          ENNReal.ofReal ((3 * C₀ + 11 * d ^ 2) * volume.real U) * L := by
        refine add_le_add le_rfl ?_
        rw [ENNReal.ofReal_mul hX0]
        have hcoef : 8 / 3 * (4 * d ^ 2 * volume.real U) ≤
            (3 * C₀ + 11 * d ^ 2) * volume.real U := by
          have hV : 0 ≤ volume.real U := measureReal_nonneg
          have h' : 8 / 3 * (4 * (d : ℝ) ^ 2) ≤ 3 * C₀ + 11 * d ^ 2 := by
            linarith only [hC₀, hd2]
          calc 8 / 3 * (4 * d ^ 2 * volume.real U) = (8 / 3 * (4 * d ^ 2)) * volume.real U := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_right h' hV
        calc ENNReal.ofReal (8 / 3) * ENNReal.ofReal X
            ≤ ENNReal.ofReal (8 / 3) * (ENNReal.ofReal (4 * d ^ 2 * volume.real U) * L) := by
              gcongr
          _ = ENNReal.ofReal (8 / 3 * (4 * d ^ 2 * volume.real U)) * L := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hX0]
          _ ≤ ENNReal.ofReal ((3 * C₀ + 11 * d ^ 2) * volume.real U) * L := by
              gcongr

end QSH
