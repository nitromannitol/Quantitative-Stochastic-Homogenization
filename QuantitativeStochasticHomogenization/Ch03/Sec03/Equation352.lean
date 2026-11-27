import QuantitativeStochasticHomogenization.Ch03.Sec03.BallDirichletField
import QuantitativeStochasticHomogenization.Ch03.Sec03.Equation350

/-!
# The estimate (3.52)

Armstrong–Kuusi–Mourrat, Section 3.3, Step 1 of the proof of (3.46): for `q ∈ Ā_k` the solution of the
Dirichlet problem in `B_r` for the coefficient field `a` with the values of `q` is within
`C r^{-γ} ‖q‖_{L̲²(B_r)}`, `γ = α(d - s)`, of `q` in `L̲²(B_r)`, (3.52), by Theorem 2.18 after the dilation `x ↦ r x`,
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

set_option maxHeartbeats 400000 in
/-- **The heterogeneous Dirichlet approximation**, for `d ≥ 2` and `Λ > 1`, (3.52) before the
specialization to `Ā_k`: there is `α(d, Λ) > 0` such that for every `s ∈ (0, d)` there is
`C(s, d, Λ)` with, for every law satisfying (0.10)–(0.11), a random variable `X ≥ 1` with
`X ≤ O_s(C)` such that, for almost every coefficient field, every `R ≥ X` and every weak solution
`q ∈ H¹(B_R)` of `-∇·(ā∇q) = 0` in `B_R`, there is a weak solution `u ∈ H¹(B_{R/2})` of
`-∇·(a∇u) = 0` in `B_{R/2}` (the solution of the Dirichlet problem with the values of `q`) with
`‖q - u‖_{L̲²(B_{R/2})} ≤ C R^{-α(d-s)} ‖q - (q)_{B_R}‖_{L̲²(B_R)}`. -/
theorem dirichletApproximation (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) :
    ∃ α : ℝ, 0 < α ∧ ∀ s : ℝ, 0 < s → s < d → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s C ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ R : ℝ, X a ≤ R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        MemLp u 2 (volume.restrict (ball 0 R)) →
        (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
        HasWeakGradient (ball 0 R) u g →
        HasWeakDivergence (ball 0 R) (fun x => (homogenizedMatrix P).mulVec (g x)) (fun _ => 0) →
        ∃ (uh : Vec d → ℝ) (gh : Vec d → Vec d), MemLp uh 2 (volume.restrict (ball 0 (R / 2))) ∧
          (∀ i, MemLp (fun x => gh x i) 2 (volume.restrict (ball 0 (R / 2)))) ∧
          HasWeakGradient (ball 0 (R / 2)) uh gh ∧
          HasWeakDivergence (ball 0 (R / 2)) (fun x => (a x).mulVec (gh x)) (fun _ => 0) ∧
          scalarRms volume (ball 0 (R / 2)) (fun x => u x - uh x) ≤
            C * R ^ (-(α * ((d : ℝ) - s))) *
              scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨δM, CM, hδM, hCM, hMey⟩ := meyers_halfBall hd hΛ.le
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δM (1 / d) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min hδM (by positivity)
  have hδd : δ ≤ 1 / d := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δM := by rw [hδdef]; exact min_le_left _ _
  have hMey' : ∀ (a : CoefficientField d Λ) (R : ℝ), 0 < R → ∀ (u : Vec d → ℝ)
      (g : Vec d → Vec d), MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient (ball 0 R) u g →
      HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal (CM * (R⁻¹ * scalarRms volume (ball 0 R)
          (fun x => u x - ⨍ y in ball 0 R, u y))) := fun a R hR u g hu hg hug hdiv => by
    refine le_trans ?_ (hMey R hR a u g hu hg hug hdiv)
    have : IsProbabilityMeasure (PDE.normalizedVolumeOn (ball (0 : Vec d) (R / 2))) :=
      PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
        (pos_iff_ne_zero.2 (volume_ball_ne_zero' 0 (by positivity)))
        (lt_top_iff_ne_top.2 (volume_ball_ne_top' 0 _))
    exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))
  -- the domain `B_{1/2} ⊆ □_0`
  have hU := isOpenBoundedConvexDomain_ball_of_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 1 / 2)
  have hUne : (ball (0 : Vec d) (1 / 2)).Nonempty :=
    ⟨0, mem_ball_zero_iff'.2 (by simp [euclideanNorm, euclideanSq, dot])⟩
  have hUc0 : ball (0 : Vec d) (1 / 2) ⊆ triadicCube d 0 := fun x hx => by
    have h := mem_ball_zero_iff'.1 hx
    refine Set.mem_pi.2 fun i _ => ?_
    have hi := (abs_coord_le_euclideanNorm x i).trans_lt h
    rw [abs_lt] at hi
    simp only [pow_zero, Set.mem_Ioo]
    constructor <;> linarith [hi.1, hi.2]
  obtain ⟨β, hβ, h218⟩ := theorem_2_18 hd hΛ hU.1 hU.2.2 hUne hUc0 hδ
  refine ⟨min β 1 / 4, by positivity, fun s hs hsd => ?_⟩
  have hds : 0 < (d : ℝ) - s := by linarith
  obtain ⟨C₁, hC₁, h1⟩ := h218 ((s + d) / 2) (by linarith) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨CX, hCX⟩ : ∃ CX : ℝ,
      CX = (2 : ℝ) ^ s⁻¹ * max (C₁ ^ (1 / s)) (1 / Real.log 2 ^ s⁻¹) := ⟨_, rfl⟩
  have hCX0 : 0 ≤ CX := by rw [hCX]; positivity
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, CA = Real.sqrt (2 * C₁) * CM := ⟨_, rfl⟩
  have hCA0 : 0 ≤ CA := by rw [hCA]; exact mul_nonneg (Real.sqrt_nonneg _) hCM
  refine ⟨CX + CA + 1, by linarith, fun P hP => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X₁, hX₁, hX₁0, hae⟩ := h1 P hP
  refine ⟨fun a => max (X₁ a ^ (1 / s)) 1, ?_, fun a => le_max_right _ _, ?_⟩
  · have h1' := hX₁.rpow hX₁0 (one_div_pos.2 hs)
    rw [one_div_one_div] at h1'
    have h2 := osBound_of_le_const (P := P) (X := fun _ => (1 : ℝ)) measurable_const hs one_pos
      (Eventually.of_forall fun _ => le_rfl)
    refine (osBound_max h1' h2).mono_scale ?_
    rw [← hCX]
    linarith
  filter_upwards [hae] with a ha
  intro R hR u g hu hg hug hdiv
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hXR : X₁ a ≤ R ^ s := by
    have h := (le_max_left _ _).trans hR
    have e : X₁ a = (X₁ a ^ (1 / s)) ^ s := by
      rw [← Real.rpow_mul (hX₁0 a), one_div_mul_cancel hs.ne', Real.rpow_one]
    rw [e]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (hX₁0 a) _) h hs.le
  have hb := fun ε hε hε1 f F hW uε u' gε g' h₁ h₂ h₃ h₄ =>
    (le_self_add.trans (le_self_add.trans le_self_add)).trans
      (ha ε hε hε1 f F hW uε u' gε g' h₁ h₂ h₃ h₄)
  obtain ⟨uh, gh, h1u, h2u, h3u, h4u, h5u⟩ := dirichletApprox_of_bound hd hΛ.le hδd hCM hC₁.le
    (hX₁0 a) a (homogenizedMatrix P) (hMey' (constantCoefficientField (homogenizedMatrix P)
      (homogenizedMatrix_transpose hP hΛ0) (euclideanSq_le_dot_homogenizedMatrix hP hΛ0)
      (fun ξ => (homogenizedMatrix_dot_bounds hP hΛ0 ξ).2))) hb hR1 hu hg hug hdiv
  refine ⟨uh, gh, h1u, h2u, h3u, h4u, ?_⟩
  -- the rate
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ,
      ρ = scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) := ⟨_, rfl⟩
  rw [← hρ] at h5u ⊢
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact Real.sqrt_nonneg _
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = R ^ (-(min β 1 / 4 * ((d : ℝ) - s))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact Real.rpow_nonneg hR0.le _
  have hEsq : E ^ 2 = R ^ (-(min β 1 * ((d : ℝ) - s) / 2)) := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    congr 1; push_cast; ring
  have hb1 : R⁻¹ ^ (β * ((d : ℝ) - (s + d) / 2)) ≤ E ^ 2 := by
    rw [hEsq]
    refine inv_rpow_le_rpow_neg hR1 ?_
    have : min β 1 * ((d : ℝ) - s) ≤ β * ((d : ℝ) - s) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hds.le
    linarith
  have hb2 : X₁ a * R⁻¹ ^ ((s + d) / 2) ≤ E ^ 2 := by
    rw [hEsq]
    calc X₁ a * R⁻¹ ^ ((s + d) / 2) ≤ R ^ s * R ^ (-((s + d) / 2)) :=
          mul_le_mul hXR (inv_rpow_le_rpow_neg hR1 le_rfl)
            (Real.rpow_nonneg (inv_nonneg.2 hR0.le) _) (Real.rpow_nonneg hR0.le _)
      _ = R ^ (-(((d : ℝ) - s) / 2)) := by
          rw [← Real.rpow_add hR0]; congr 1; ring
      _ ≤ _ := by
          refine Real.rpow_le_rpow_of_exponent_le hR1 ?_
          have : min β 1 * ((d : ℝ) - s) ≤ 1 * ((d : ℝ) - s) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hds.le
          linarith
  have hsq : scalarRms volume (ball 0 (R / 2)) (fun x => u x - uh x) ^ 2 ≤
      (CA * E * ρ) ^ 2 := by
    refine h5u.trans ?_
    have hCA2 : CA ^ 2 = 2 * C₁ * CM ^ 2 := by
      rw [hCA, mul_pow, Real.sq_sqrt (by positivity)]
    have e : (CA * E * ρ) ^ 2 = C₁ * (CM * ρ) ^ 2 * (2 * E ^ 2) := by
      rw [mul_pow, mul_pow, hCA2]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC₁.le (sq_nonneg _))
  have h0 : 0 ≤ CA * E * ρ := mul_nonneg (mul_nonneg hCA0 hE0) hρ0
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (show 0 ≤ scalarRms volume (ball 0 (R / 2)) (fun x => u x - uh x) from
    Real.sqrt_nonneg _), Real.sqrt_sq h0] at hle
  rw [← hE]
  calc _ ≤ CA * E * ρ := hle
    _ ≤ (CX + CA + 1) * E * ρ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hE0) hρ0

/-- **(3.52)**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: above a random scale `X ≤ O_s(C)`, for almost
every coefficient field, every `k`, every `r ≥ X` and every `q ∈ Ā_k`, there is a weak solution `u` of
`-∇·(a∇u) = 0` in `B_r` (the solution of the Dirichlet problem in `B_r` with the values of `q`) with
`‖u - q‖_{L̲²(B_r)} ≤ C_k r^{-γ} ‖q‖_{L̲²(B_r)}`, `γ = α(d - s)`. The exponent, the scale and the
exceptional set do not depend on `k`. -/
theorem equation_3_52 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ (C : ℕ → ℝ) (CX : ℝ), 0 < CX ∧ (∀ k, 0 ≤ C k) ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ (k : ℕ) (r : ℝ), X a ≤ r → ∀ q ∈ harmonicPolys (homogenizedMatrix P) k,
          ∃ u, IsSolutionBall a r u ∧
            scalarRms volume (ball 0 r) (fun x => u x - q x) ≤
              C k * r ^ (-γ) * scalarRms volume (ball 0 r) q := by
  obtain ⟨α, hα, hdir⟩ := dirichletApproximation hd hΛ
  obtain ⟨CD, hCD, hD⟩ := hdir s hs hsd
  have hds : 0 < (d : ℝ) - s := by linarith
  choose C₂₇ hC₂₇ hgrow using fun k : ℕ => scalarRms_poly_growth (d := d) k
  refine ⟨α * ((d : ℝ) - s), mul_pos hα hds, fun k => CD * (C₂₇ k * 2 ^ k), CD, hCD,
    fun k => mul_nonneg hCD.le (mul_nonneg (hC₂₇ k) (by positivity)), fun P hP => ?_⟩
  obtain ⟨X, hXos, hX1, hXae⟩ := hD P hP
  refine ⟨X, hXos, hX1, ?_⟩
  filter_upwards [hXae] with a ha
  intro k r hXr q hq
  have hr1 : 1 ≤ r := (hX1 a).trans hXr
  have hr0 : 0 < r := by linarith
  have h2r : 0 < 2 * r := by linarith
  obtain ⟨⟨Q, hQ, hQe⟩, hqh⟩ := hq
  obtain ⟨hqL2, gq, hgq, hqgrad, hqdiv⟩ := hqh (2 * r) h2r
  obtain ⟨u, g, hu, hg, hug, hdiv, hb⟩ := ha (2 * r) (hXr.trans (by linarith)) q gq hqL2 hgq
    hqgrad hqdiv
  rw [show 2 * r / 2 = r by ring] at hu hg hug hdiv hb
  refine ⟨u, ⟨hu, g, hg, hug, hdiv⟩, ?_⟩
  have hneg : scalarRms volume (ball 0 r) (fun x => u x - q x) =
      scalarRms volume (ball 0 r) (fun x => q x - u x) := by
    have e : (fun x => u x - q x) = fun x => -1 * (q x - u x) := by funext x; ring
    rw [e, scalarRms_const_mul, abs_neg, abs_one, one_mul]
  rw [hneg]
  have hosc : scalarRms volume (ball 0 (2 * r)) (fun x => q x - ⨍ y in ball 0 (2 * r), q y) ≤
      scalarRms volume (ball 0 (2 * r)) q := by
    refine (scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' 0 _) hqL2 0).trans ?_
    simp only [sub_zero, le_refl]
  have hqP : q = fun x => MvPolynomial.eval x Q := funext hQe
  have hg2 := hgrow k Q hQ r (2 * r) hr0 (by linarith)
  rw [← hqP, show 2 * r / r = 2 by field_simp] at hg2
  have hpow : (2 * r) ^ (-(α * ((d : ℝ) - s))) ≤ r ^ (-(α * ((d : ℝ) - s))) :=
    Real.rpow_le_rpow_of_nonpos hr0 (by linarith) (by nlinarith)
  have hq0 := scalarRms_nonneg (d := d) (ball 0 r) q
  calc scalarRms volume (ball 0 r) (fun x => q x - u x)
      ≤ CD * (2 * r) ^ (-(α * ((d : ℝ) - s))) *
          scalarRms volume (ball 0 (2 * r)) (fun x => q x - ⨍ y in ball 0 (2 * r), q y) := hb
    _ ≤ CD * r ^ (-(α * ((d : ℝ) - s))) * (C₂₇ k * 2 ^ k * scalarRms volume (ball 0 r) q) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hCD.le) (hosc.trans hg2)
          (scalarRms_nonneg _ _) (mul_nonneg hCD.le (Real.rpow_nonneg hr0.le _))
    _ = CD * (C₂₇ k * 2 ^ k) * r ^ (-(α * ((d : ℝ) - s))) * scalarRms volume (ball 0 r) q := by
        ring

end QSH
