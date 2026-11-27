import QuantitativeStochasticHomogenization.Ch03.Sec03.BallDirichletField
import QuantitativeStochasticHomogenization.Ch03.Sec03.Equation350

/-!
# The estimate (3.52)

Armstrong–Kuusi–Mourrat, Section 3.3, Step 1 of the proof of (3.46): for `q ∈ Ā_k` the solution of the
Dirichlet problem in `B_r` for the coefficient field `a` with the values of `q` is within
`C r^{-δ} ‖q‖_{L̲²(B_r)}` of `q` in `L̲²(B_r)`, (3.52), by Theorem 2.18 after the dilation `x ↦ r x`,
since `q` itself solves the homogenized Dirichlet problem. `dirichletApprox_of_bound` is the
deterministic step, for one coefficient field and one radius, with the data gradient of `q` in
`L^{2+δ}` by the Meyers estimate for the constant coefficient field `ā`.
-/

open MeasureTheory Filter Set
open scoped Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

set_option maxHeartbeats 400000 in
/-- **The heterogeneous Dirichlet approximation at one scale**, from the estimate of Theorem 2.18 on
`B_{1/2}` for one coefficient field: for `R ≥ 1` and an `A`-harmonic `q ∈ H¹(B_R)` there is a weak
solution `u ∈ H¹(B_{R/2})` of `-∇·(a∇u) = 0` (the solution of the Dirichlet problem with the values
of `q`) with
`‖q - u‖²_{L̲²(B_{R/2})} ≤ C₁ (C_M ‖q - (q)_{B_R}‖_{L̲²(B_R)})² (R^{-β(d-s')} + X R^{-s'})`. -/
theorem dirichletApprox_of_bound (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {δ CM C₁ β s' X : ℝ}
    (hδd : δ ≤ 1 / d) (hCM : 0 ≤ CM) (hC₁ : 0 ≤ C₁) (hX0 : 0 ≤ X)
    (a : CoefficientField d Λ)
    (A : Mat d) (hMey : ∀ R : ℝ, 0 < R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient (ball 0 R) u g →
      HasWeakDivergence (ball 0 R) (fun x => A.mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal (CM * (R⁻¹ * scalarRms volume (ball 0 R)
          (fun x => u x - ⨍ y in ball 0 R, u y))))
    (h218 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (f : Vec d → ℝ) (F : Vec d → Vec d),
        IsW1p (ball 0 (1 / 2)) (ENNReal.ofReal (2 + δ)) f F →
      ∀ (uε u : Vec d → ℝ) (gε g : Vec d → Vec d),
        H01 (ball 0 (1 / 2)) (fun x => uε x - f x) (fun x => gε x - F x) →
        HasWeakDivergence (ball 0 (1 / 2)) (fun x => (a (ε⁻¹ • x)).mulVec (gε x)) (fun _ => 0) →
        H01 (ball 0 (1 / 2)) (fun x => u x - f x) (fun x => g x - F x) →
        HasWeakDivergence (ball 0 (1 / 2)) (fun x => A.mulVec (g x)) (fun _ => 0) →
        ENNReal.ofReal (scalarRms volume (ball 0 (1 / 2)) (fun x => uε x - u x)) ^ 2 ≤
          ENNReal.ofReal C₁ * PDE.eLpMeanNormOn (ball 0 (1 / 2)) (ENNReal.ofReal (2 + δ))
            (fun x => euclideanNorm (F x)) ^ 2 *
            ENNReal.ofReal (ε ^ (β * ((d : ℝ) - s')) + X * ε ^ s'))
    {R : ℝ} (hR1 : 1 ≤ R) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R)))
    (hug : HasWeakGradient (ball 0 R) u g)
    (hdiv : HasWeakDivergence (ball 0 R) (fun x => A.mulVec (g x)) (fun _ => 0)) :
    ∃ (uh : Vec d → ℝ) (gh : Vec d → Vec d), MemLp uh 2 (volume.restrict (ball 0 (R / 2))) ∧
      (∀ i, MemLp (fun x => gh x i) 2 (volume.restrict (ball 0 (R / 2)))) ∧
      HasWeakGradient (ball 0 (R / 2)) uh gh ∧
      HasWeakDivergence (ball 0 (R / 2)) (fun x => (a x).mulVec (gh x)) (fun _ => 0) ∧
      scalarRms volume (ball 0 (R / 2)) (fun x => u x - uh x) ^ 2 ≤
        C₁ * (CM * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y)) ^ 2 *
          (R⁻¹ ^ (β * ((d : ℝ) - s')) + X * R⁻¹ ^ s') := by
  have hd0 : 0 < d := by omega
  have hR : 0 < R := by linarith
  set S : Set (Vec d) := ball 0 (R / 2) with hS
  set U₀ : Set (Vec d) := ball 0 (1 / 2) with hU₀
  have hRU : R • U₀ = S := by rw [hU₀, smul_ball_zero hR, hS]; ring_nf
  have hSR : S ⊆ ball (0 : Vec d) R := fun x hx => by
    have h : euclideanNorm x < R / 2 := mem_ball_zero_iff'.1 hx
    exact mem_ball_zero_iff'.2 (by linarith)
  have hmapS : ∀ x ∈ U₀, R • x ∈ S := fun x hx => by rw [← hRU]; exact Set.smul_mem_smul_set hx
  have hSm : MeasurableSet S := measurableSet_ball' 0 _
  have hUm : MeasurableSet U₀ := measurableSet_ball' 0 _
  have hRm : MeasurableSet (ball (0 : Vec d) R) := measurableSet_ball' 0 _
  have hS0 : volume S ≠ 0 := volume_ball_ne_zero' 0 (by positivity)
  have hSt : volume S ≠ ⊤ := volume_ball_ne_top' 0 _
  have hUt : volume U₀ ≠ ⊤ := volume_ball_ne_top' 0 _
  have hμS : volume.restrict S ≤ volume.restrict (ball 0 R) := Measure.restrict_mono hSR le_rfl
  -- integrability of `u` and `∇u` on `B_{R/2}`
  have hM := hMey R hR u g hu hg hug hdiv
  have hgn : MemLp (fun x => euclideanNorm (g x)) (ENNReal.ofReal (2 + δ)) (volume.restrict S) :=
    memLp_of_eLpMeanNormOn_ne_top hS0 hSt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM)
  have hgp : ∀ i, MemLp (fun x => g x i) (ENNReal.ofReal (2 + δ)) (volume.restrict S) := fun i =>
    hgn.of_le (((hg i).mono_measure hμS).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ euclideanNorm (g x) from Real.sqrt_nonneg _)]
        exact abs_coord_le_euclideanNorm _ i)
  have hup : MemLp u (ENNReal.ofReal (2 + δ)) (volume.restrict S) :=
    (memLp_two_add_inv_of_h1_ball hd (by positivity : (0 : ℝ) < R / 2) (hu.mono_measure hμS)
      (fun i => (hg i).mono_measure hμS) (HasWeakGradient.mono hSR hug)).mono_exponent
      (ENNReal.ofReal_le_ofReal (by linarith))
  -- the rescaled data on `B_{1/2}`
  have hmap0 : ∀ x ∈ U₀, R • x + 0 ∈ S := fun x hx => by rw [add_zero]; exact hmapS x hx
  have hgR : ∀ i, MemLp (fun x => g (R • x) i) 2 (volume.restrict U₀) := fun i => by
    have h := MemLp.comp_smul_add_restrict (f := fun x => g x i) hSm hUm hR.ne' 0 hmap0
      ((hg i).mono_measure hμS)
    simpa only [add_zero] using h
  have hloc : ∀ i, LocallyIntegrableOn (fun x => ((fun _ => A) (R • x)).mulVec (g (R • x)) i)
      U₀ volume := fun i => by
    have : IsFiniteMeasure (volume.restrict U₀) := isFiniteMeasure_restrict.mpr hUt
    exact IntegrableOn.locallyIntegrableOn
      ((TwoScale.memLp_const_mulVec A hgR i).integrable one_le_two)
  obtain ⟨hf2, hF2, hfF, hdivF⟩ := rescale_h1_div hRm hUm hUt hR
    (fun x hx => hSR (hmapS x hx)) (fun _ => A) hu hg hug hdiv hloc
  have hfp : MemLp (fun x => u (R • x)) (ENNReal.ofReal (2 + δ)) (volume.restrict U₀) := by
    have h := MemLp.comp_smul_add_restrict hSm hUm hR.ne' 0 hmap0 hup
    simpa only [add_zero] using h
  have hFp : ∀ i, MemLp (fun x => (R • g (R • x)) i) (ENNReal.ofReal (2 + δ))
      (volume.restrict U₀) := fun i => by
    have h := MemLp.comp_smul_add_restrict (f := fun x => g x i) hSm hUm hR.ne' 0 hmap0 (hgp i)
    simp only [add_zero] at h
    exact h.const_mul R
  have hW : IsW1p U₀ (ENNReal.ofReal (2 + δ)) (fun x => u (R • x)) (fun x => R • g (R • x)) :=
    ⟨hfp, memLp_pi_iff.2 hFp, hfF⟩
  -- the heterogeneous Dirichlet problem on `B_{1/2}`, for `x ↦ a (R x)`
  obtain ⟨w, gw, hw, hdivw⟩ := exists_ballDirichlet_field hΛ hd0 (by norm_num : (0 : ℝ) < 1 / 2)
    (rescaledCoefficientField a (inv_ne_zero hR.ne')) hF2
  have hdivw' : HasWeakDivergence U₀ (fun x => (a (R⁻¹⁻¹ • x)).mulVec
      ((fun x => gw x + R • g (R • x)) x)) (fun _ => 0) := by
    simpa only [rescaledCoefficientField_apply] using hdivw
  have hH0 : H01 U₀ (fun x => (w x + u (R • x)) - u (R • x))
      (fun x => (gw x + R • g (R • x)) - R • g (R • x)) :=
    hw.congr (fun x => (add_sub_cancel_right _ _).symm) (fun x => (add_sub_cancel_right _ _).symm)
  have hHf : H01 U₀ (fun x => u (R • x) - u (R • x)) (fun x => R • g (R • x) - R • g (R • x)) :=
    (H01_zero U₀).congr (fun x => (sub_self _).symm) (fun x => (sub_self _).symm)
  have hdivF' : HasWeakDivergence U₀ (fun x => A.mulVec (R • g (R • x))) (fun _ => 0) := hdivF
  have hb := h218 R⁻¹ (inv_pos.2 hR) (inv_le_one_of_one_le₀ hR1) _ _ hW _ _ _ _ hH0 hdivw' hHf
    hdivF'
  -- the norm of the rescaled gradient
  have hFn : PDE.eLpMeanNormOn U₀ (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (R • g (R • x))) ≤
        ENNReal.ofReal (CM * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y)) := by
    have e1 : (fun x => euclideanNorm (R • g (R • x))) =
        R • fun x => euclideanNorm (g (R • x)) := by
      funext x; rw [euclideanNorm_smul, abs_of_pos hR]; rfl
    have hmeas : AEStronglyMeasurable (fun x => euclideanNorm (g x))
        (PDE.normalizedVolumeOn (R • U₀)) := by
      rw [hRU]
      exact aestronglyMeasurable_euclideanNorm_normalizedVolumeOn le_rfl
        (fun i => (hg i).mono_measure hμS)
    rw [e1, PDE.eLpMeanNormOn, eLpNorm_const_smul, Real.enorm_of_nonneg hR.le]
    change ENNReal.ofReal R * PDE.eLpMeanNormOn U₀ (ENNReal.ofReal (2 + δ))
      (fun x => euclideanNorm (g (R • x))) ≤ _
    rw [eLpMeanNormOn_comp_smul hR U₀ _ hmeas, hRU]
    refine (mul_le_mul_right hM _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hR.le]
    congr 1
    field_simp
  -- the back-rescaled approximation on `B_{R/2}`
  have hmapB : ∀ y ∈ S, R⁻¹ • y ∈ U₀ := fun y hy => by
    rw [← hRU] at hy
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.1 hy
    rwa [inv_smul_smul₀ hR.ne']
  have hu₀ : MemLp (fun x => w x + u (R • x)) 2 (volume.restrict U₀) := hw.1.add hf2
  have hg₀ : ∀ i, MemLp (fun x => (gw x + R • g (R • x)) i) 2 (volume.restrict U₀) := fun i =>
    (MemLp.eval hw.2.1 i).add (hF2 i)
  have hug₀ : HasWeakGradient U₀ (fun x => w x + u (R • x)) (fun x => gw x + R • g (R • x)) :=
    hasWeakGradient_add hw.2.2.1 hfF
  have hlocB : ∀ i, LocallyIntegrableOn (fun y => ((fun x =>
      rescaledCoefficientField a (inv_ne_zero hR.ne') x) (R⁻¹ • y)).mulVec
      ((fun x => gw x + R • g (R • x)) (R⁻¹ • y)) i) S volume := fun i => by
    have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSt
    have hmap0' : ∀ y ∈ S, R⁻¹ • y + 0 ∈ U₀ := fun y hy => by rw [add_zero]; exact hmapB y hy
    have hc : ∀ j, MemLp (fun y => (gw (R⁻¹ • y) + R • g (R • R⁻¹ • y)) j) 2
        (volume.restrict S) := fun j => by
      have h := MemLp.comp_smul_add_restrict (f := fun x => (gw x + R • g (R • x)) j) hUm hSm
        (inv_ne_zero hR.ne') 0 hmap0' (hg₀ j)
      simpa only [add_zero] using h
    have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
    have h := memLp_coefficient_mulVec_apply_of_coord hΛ0 a hc i
    have e : (fun y => ((fun x => rescaledCoefficientField a (inv_ne_zero hR.ne') x)
        (R⁻¹ • y)).mulVec ((fun x => gw x + R • g (R • x)) (R⁻¹ • y)) i) =
        fun y => (a y).mulVec (gw (R⁻¹ • y) + R • g (R • R⁻¹ • y)) i := by
      funext y
      simp only [rescaledCoefficientField_apply, inv_inv, smul_smul, mul_inv_cancel₀ hR.ne',
        one_smul]
    rw [e]
    exact IntegrableOn.locallyIntegrableOn (h.integrable one_le_two)
  obtain ⟨huh, hgh, hughh, hdivuh⟩ := rescale_h1_div hUm hSm hSt (inv_pos.2 hR) hmapB
    (fun x => rescaledCoefficientField a (inv_ne_zero hR.ne') x) hu₀ hg₀ hug₀ hdivw hlocB
  have hdivuh' : HasWeakDivergence S (fun y => (a y).mulVec
      (R⁻¹ • (fun x => gw x + R • g (R • x)) (R⁻¹ • y))) (fun _ => 0) := by
    convert hdivuh using 3 with y
    simp only [rescaledCoefficientField_apply, inv_inv, smul_smul, mul_inv_cancel₀ hR.ne',
      one_smul]
  refine ⟨_, _, huh, hgh, hughh, hdivuh', ?_⟩
  -- the estimate
  have hrms : scalarRms volume S (fun y => u y - (w (R⁻¹ • y) + u (R • R⁻¹ • y))) =
      scalarRms volume U₀ (fun x => u (R • x) - (w x + u (R • x))) := by
    rw [← hRU, ← TwoScale.scalarRms_comp_smul hR]
    simp only [inv_smul_smul₀ hR.ne']
  rw [hrms]
  have hneg : scalarRms volume U₀ (fun x => u (R • x) - (w x + u (R • x))) =
      scalarRms volume U₀ (fun x => (w x + u (R • x)) - u (R • x)) := by
    have e : (fun x => u (R • x) - (w x + u (R • x))) =
        fun x => -1 * ((w x + u (R • x)) - u (R • x)) := by funext x; ring
    rw [e, scalarRms_const_mul, abs_neg, abs_one, one_mul]
  rw [hneg]
  have hX := hb.trans (mul_le_mul_left (mul_le_mul_right
    (pow_le_pow_left₀ zero_le hFn 2) _) _)
  have hb0 : 0 ≤ R⁻¹ ^ (β * ((d : ℝ) - s')) + X * R⁻¹ ^ s' :=
    add_nonneg (Real.rpow_nonneg (inv_nonneg.2 hR.le) _)
      (mul_nonneg hX0 (Real.rpow_nonneg (inv_nonneg.2 hR.le) _))
  have hs0 : 0 ≤ scalarRms volume U₀ (fun x => (w x + u (R • x)) - u (R • x)) :=
    Real.sqrt_nonneg _
  have hm0 : 0 ≤ CM * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) :=
    mul_nonneg hCM (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_pow hs0, ← ENNReal.ofReal_pow hm0, ← ENNReal.ofReal_mul hC₁,
    ← ENNReal.ofReal_mul (mul_nonneg hC₁ (sq_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hC₁ (sq_nonneg _)) hb0)] at hX
  exact hX

end QSH
