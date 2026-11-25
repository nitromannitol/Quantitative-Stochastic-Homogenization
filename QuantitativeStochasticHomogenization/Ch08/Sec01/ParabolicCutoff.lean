import QuantitativeStochasticHomogenization.Ch08.Sec01.ParabolicSolutions
import QuantitativeStochasticHomogenization.AppC.InteriorCaccioppoli
import EllipticRegularity.Parabolic.WeakSlice.Product
import EllipticRegularity.Parabolic.WeakSlice.Ramp

/-!
# The cutoff of the parabolic Caccioppoli inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 8.1, the cutoff `η_r` of the proof of Lemma 8.1: `η_r(x, t) = θ_r(t) ζ_r(x)` with
`0 ≤ η_r ≤ 1`, `η_r = 1` on `B_r × [-r², 0]`, `η_r = 0` for `t ≤ -3r²` and outside `B_{3r/2}`,
`|∂ₜη_r| ≤ M r⁻²` for a universal constant `M`, and `|∇η_r| ≤ 64/r`. It is a cutoff of the cylinder
`Q_{2r}` in the sense of `PDE.ParCutoff`: it vanishes on `Q_{2r}` outside a compact subset.
-/

open MeasureTheory Set

noncomputable section

namespace QSH

open PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- The time cutoff `θ_r(t) = ψ((t + 3r²)/(2r²))`, with `ψ` the smooth transition function. -/
def timeCutoff (r t : ℝ) : ℝ :=
  Real.smoothTransition ((t + 3 * r ^ 2) / (2 * r ^ 2))

theorem timeCutoff_contDiff (r : ℝ) : ContDiff ℝ 1 (timeCutoff r) :=
  (Real.smoothTransition.contDiff (n := 1)).comp
    ((contDiff_id.add contDiff_const).div_const _)

theorem timeCutoff_nonneg (r t : ℝ) : 0 ≤ timeCutoff r t :=
  Real.smoothTransition.nonneg _

theorem timeCutoff_le_one (r t : ℝ) : timeCutoff r t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem timeCutoff_eq_zero {r t : ℝ} (hr : 0 < r) (ht : t ≤ -3 * r ^ 2) : timeCutoff r t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))

theorem timeCutoff_eq_one {r t : ℝ} (hr : 0 < r) (ht : -r ^ 2 ≤ t) : timeCutoff r t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith)

theorem hasDerivAt_timeCutoff (r t : ℝ) :
    HasDerivAt (timeCutoff r) (rampDeriv ((t + 3 * r ^ 2) / (2 * r ^ 2)) / (2 * r ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t + 3 * r ^ 2) / (2 * r ^ 2)) (1 / (2 * r ^ 2)) t :=
    ((hasDerivAt_id t).add_const _).div_const _
  have h2 := (rampDeriv_hasDerivAt ((t + 3 * r ^ 2) / (2 * r ^ 2))).comp t h1
  exact h2.congr_deriv (by ring)

/-- A bound for the derivative of the smooth transition function. -/
theorem exists_rampDeriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |rampDeriv y| ≤ M := by
  have hc : HasCompactSupport rampDeriv :=
    HasCompactSupport.of_support_subset_isCompact (K := Icc (0 : ℝ) 1) isCompact_Icc
      fun y hy => by
        by_contra h
        exact hy (rampDeriv_eq_zero_of_notMem h)
  obtain ⟨M, hM⟩ := rampDeriv_continuous.bounded_above_of_compact_support hc
  exact ⟨max M 0, le_max_right _ _, fun y => (hM y).trans (le_max_left _ _)⟩

theorem abs_deriv_timeCutoff_le {M : ℝ} (hM : ∀ y, |rampDeriv y| ≤ M) {r : ℝ} (hr : 0 < r)
    (t : ℝ) : |deriv (timeCutoff r) t| ≤ M / (2 * r ^ 2) := by
  rw [(hasDerivAt_timeCutoff r t).deriv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * r ^ 2)]
  exact div_le_div_of_nonneg_right (hM _) (by positivity)

/-- The spatial cutoff `ζ_r` of `B_r` in `B_{3r/2}`, with `|∇ζ_r| ≤ 64/r`. -/
def spaceCutoff {r : ℝ} (hr : 0 < r) :
    PDE.QuantitativeSmoothCutoff (PDE.euclideanBall (0 : Vec d) r)
      (PDE.euclideanBall (0 : Vec d) (3 * r / 2)) (64 / r) :=
  let c := PDE.quantitativeBallCutoff (0 : Vec d) hr.le (show r < 3 * r / 2 by linarith)
  { toFun := c.toFun
    smooth := c.smooth
    hasCompactSupport := c.hasCompactSupport
    tsupport_subset := c.tsupport_subset
    nonneg := c.nonneg
    le_one := c.le_one
    eq_one_on_inner := c.eq_one_on_inner
    gradient_bound := fun x => (c.gradient_bound x).trans_eq
      ((div_eq_div_iff (by linarith) hr.ne').2 (by ring)) }

theorem spaceCutoff_tsupport_subset {r : ℝ} (hr : 0 < r) :
    tsupport (spaceCutoff (d := d) hr).toFun ⊆ ball (0 : Vec d) (2 * r) := by
  refine (spaceCutoff hr).tsupport_subset.trans ?_
  rw [ball_eq_euclideanBall 0 (by linarith : (0 : ℝ) < 2 * r)]
  exact PDE.euclideanBall_mono (by linarith) (by linarith)

theorem vecNormSq_classicalGradient_spaceCutoff_le {r : ℝ} (hr : 0 < r) (x : Vec d) :
    PDE.vecNormSq (PDE.classicalGradient (spaceCutoff (d := d) hr).toFun x) ≤ (64 / r) ^ 2 := by
  have h1 := (spaceCutoff (d := d) hr).gradient_bound x
  have h2 : PDE.vecEuclideanNorm (PDE.classicalGradient (spaceCutoff (d := d) hr).toFun x) ^ 2 =
      PDE.vecNormSq (PDE.classicalGradient (spaceCutoff (d := d) hr).toFun x) :=
    Real.sq_sqrt (PDE.vecNormSq_nonneg _)
  rw [← h2]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- **The cutoff of Lemma 8.1**: `η_r(x, t) = θ_r(t) ζ_r(x)`, a cutoff of `Q_{2r}`. -/
def parabolicCutoff {r : ℝ} (hr : 0 < r) :
    PDE.ParCutoff (ball (0 : Vec d) (2 * r)) (Ioc (-(2 * r) ^ 2) 0) where
  toFun := fun w => timeCutoff r w.2 * (spaceCutoff hr).toFun w.1
  contDiff := contDiff_prod (timeCutoff_contDiff r)
    ((spaceCutoff hr).smooth.of_le (by exact_mod_cast le_top))
  compact_support := by
    refine ⟨tsupport (spaceCutoff hr).toFun ×ˢ Icc (-3 * r ^ 2) 0,
      (spaceCutoff hr).hasCompactSupport.isCompact.prod isCompact_Icc,
      prod_mono (spaceCutoff_tsupport_subset hr) fun t ht => ⟨by nlinarith [ht.1], ht.2⟩, ?_⟩
    rintro ⟨x, t⟩ ⟨_, htI⟩ hn
    by_cases hx : x ∈ tsupport (spaceCutoff (d := d) hr).toFun
    · have ht : t < -3 * r ^ 2 := by
        by_contra h
        exact hn ⟨hx, not_lt.mp h, htI.2⟩
      simp only
      rw [timeCutoff_eq_zero hr ht.le, zero_mul]
    · simp only
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem parabolicCutoff_apply {r : ℝ} (hr : 0 < r) (z : Vec d × ℝ) :
    (parabolicCutoff hr).toFun z = timeCutoff r z.2 * (spaceCutoff hr).toFun z.1 := rfl

theorem parabolicCutoff_nonneg {r : ℝ} (hr : 0 < r) (z : Vec d × ℝ) :
    0 ≤ (parabolicCutoff hr).toFun z :=
  mul_nonneg (timeCutoff_nonneg r z.2) ((spaceCutoff hr).nonneg z.1)

theorem parabolicCutoff_le_one {r : ℝ} (hr : 0 < r) (z : Vec d × ℝ) :
    (parabolicCutoff hr).toFun z ≤ 1 :=
  mul_le_one₀ (timeCutoff_le_one r z.2) ((spaceCutoff hr).nonneg z.1) ((spaceCutoff hr).le_one z.1)

theorem parabolicCutoff_eq_one {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : x ∈ ball (0 : Vec d) r)
    {t : ℝ} (ht : -r ^ 2 ≤ t) : (parabolicCutoff hr).toFun (x, t) = 1 := by
  rw [parabolicCutoff_apply, timeCutoff_eq_one hr ht, one_mul]
  exact (spaceCutoff hr).eq_one_on_inner x (by rwa [← ball_eq_euclideanBall 0 hr])

theorem parabolicCutoff_eq_zero {r : ℝ} (hr : 0 < r) (x : Vec d) {t : ℝ}
    (ht : t ≤ -3 * r ^ 2) : (parabolicCutoff hr).toFun (x, t) = 0 := by
  rw [parabolicCutoff_apply, timeCutoff_eq_zero hr ht, zero_mul]

theorem parTimeDeriv_parabolicCutoff {r : ℝ} (hr : 0 < r) (z : Vec d × ℝ) :
    PDE.parTimeDeriv (parabolicCutoff hr).toFun z =
      deriv (timeCutoff r) z.2 * (spaceCutoff hr).toFun z.1 :=
  parTimeDeriv_prod (timeCutoff_contDiff r)
    ((spaceCutoff hr).smooth.of_le (by exact_mod_cast le_top)) z

theorem abs_parTimeDeriv_parabolicCutoff_le {M : ℝ} (hM : ∀ y, |rampDeriv y| ≤ M) {r : ℝ}
    (hr : 0 < r) (z : Vec d × ℝ) :
    |PDE.parTimeDeriv (parabolicCutoff hr).toFun z| ≤ M / (2 * r ^ 2) := by
  rw [parTimeDeriv_parabolicCutoff, abs_mul, abs_of_nonneg ((spaceCutoff hr).nonneg z.1)]
  exact (mul_le_of_le_one_right (abs_nonneg _) ((spaceCutoff hr).le_one z.1)).trans
    (abs_deriv_timeCutoff_le hM hr z.2)

theorem parSpaceGrad_parabolicCutoff {r : ℝ} (hr : 0 < r) (z : Vec d × ℝ) :
    PDE.parSpaceGrad (parabolicCutoff hr).toFun z =
      timeCutoff r z.2 • PDE.classicalGradient (spaceCutoff hr).toFun z.1 :=
  parSpaceGrad_prod (timeCutoff_contDiff r)
    ((spaceCutoff hr).smooth.of_le (by exact_mod_cast le_top)) z

theorem vecNormSq_parSpaceGrad_parabolicCutoff_le {r : ℝ} (hr : 0 < r) (z : Vec d × ℝ) :
    PDE.vecNormSq (PDE.parSpaceGrad (parabolicCutoff hr).toFun z) ≤ (64 / r) ^ 2 := by
  rw [parSpaceGrad_parabolicCutoff]
  have h0 := timeCutoff_nonneg r z.2
  have h1 := timeCutoff_le_one r z.2
  have e : PDE.vecNormSq (timeCutoff r z.2 • PDE.classicalGradient (spaceCutoff (d := d) hr).toFun z.1)
      = timeCutoff r z.2 ^ 2 *
        PDE.vecNormSq (PDE.classicalGradient (spaceCutoff (d := d) hr).toFun z.1) := by
    simp only [PDE.vecNormSq, PDE.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact (mul_le_of_le_one_left (PDE.vecNormSq_nonneg _) (pow_le_one₀ h0 h1)).trans
    (vecNormSq_classicalGradient_spaceCutoff_le hr z.1)

/-- The time slice of the cutoff is smooth, and its gradient is the spatial gradient of `η_r`. -/
theorem slice_parabolicCutoff {r : ℝ} (hr : 0 < r) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (parabolicCutoff (d := d) hr).toFun (x, τ)) ∧
      HasCompactSupport (fun x => (parabolicCutoff (d := d) hr).toFun (x, τ)) ∧
      tsupport (fun x => (parabolicCutoff (d := d) hr).toFun (x, τ)) ⊆ ball (0 : Vec d) (2 * r) ∧
      ∀ x, PDE.classicalGradient (fun x => (parabolicCutoff (d := d) hr).toFun (x, τ)) x =
        PDE.parSpaceGrad (parabolicCutoff hr).toFun (x, τ) := by
  have hs := (spaceCutoff (d := d) hr).smooth
  have hsub : tsupport (fun x => (parabolicCutoff (d := d) hr).toFun (x, τ)) ⊆
      tsupport (spaceCutoff (d := d) hr).toFun :=
    tsupport_mul_subset_right (f := fun _ => timeCutoff r τ)
  refine ⟨(contDiff_const (c := timeCutoff r τ)).mul hs, ?_,
    hsub.trans (spaceCutoff_tsupport_subset hr), fun x => ?_⟩
  · exact (spaceCutoff (d := d) hr).hasCompactSupport.mono' ((subset_tsupport _).trans hsub)
  · rw [parSpaceGrad_parabolicCutoff]
    ext i
    simp only [PDE.classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
    show fderiv ℝ (fun x => timeCutoff r τ * (spaceCutoff (d := d) hr).toFun x) x (PDE.basisVec i) = _
    rw [fderiv_const_mul ((hs.differentiable (by simp)) x)]
    rfl

end QSH
