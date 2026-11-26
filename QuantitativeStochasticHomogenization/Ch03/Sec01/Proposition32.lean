import QuantitativeStochasticHomogenization.Ch03.Sec01.HalfBallMeyers
import QuantitativeStochasticHomogenization.Ch03.Sec01.BallDirichlet
import QuantitativeStochasticHomogenization.AppB.TheoremB9

/-!
# Proposition 3.2: harmonic approximation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.1, Proposition 3.2, for `d ≥ 2` and `Λ > 1`: there is `α(d, Λ) > 0` such that for every
`s ∈ (0, d)` there is `C(s, d, Λ)` with, for every law satisfying the assumptions, a random
variable `X_s ≥ 1` with `X_s ≤ O_s(C)`, (3.11), such that for almost every coefficient field, every
`R ≥ X_s` and every weak solution `u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R`, there is `ū ∈ H¹(B_{R/2})`
with `-∇·(ā∇ū) = 0` in `B_{R/2}` and
`‖u - ū‖_{L̲²(B_{R/2})} ≤ C R^{-α(d-s)} ‖u - (u)_{B_R}‖_{L̲²(B_R)}`, (3.13) (`proposition_3_2`).

The proof is the book's: the Meyers estimate (3.14) on `B_{R/2}` (`meyers_halfBall`), Theorem 2.18
on `B_{1/2} ⊆ □_0` for `x ↦ u(Rx)` with `ε = 1/R` and `(s + d)/2` in place of `s`, where `ū(R ·)` is
the solution of the homogenized Dirichlet problem with the boundary values of `u(R ·)`
(`exists_ballDirichlet`), and `X_s = max(X_{(s+d)/2}^{1/s}, 1)`. The exponent `2 + δ` of
Theorem 2.18 is the Meyers exponent, reduced to at most `2 + 1/d` so that `u ∈ L^{2+δ}(B_{R/2})`
by the Sobolev inequality (Theorem B.9). Departures from the book: `d ≥ 2` and `Λ > 1`, the
hypotheses of Theorem 2.18; the estimate holds for almost every coefficient field, as Theorem 2.18;
the norms are the normalized norms.
-/

open MeasureTheory Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace QSH

variable {d : ℕ}

theorem HasWeakGradient.const_mul' {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient U u g) (c : ℝ) :
    HasWeakGradient U (fun x => c * u x) (fun x => c • g x) := fun i => by
  obtain ⟨hu, hg, hint⟩ := h i
  refine ⟨(hu.smul c : _), (hg.smul c : _), fun φ hφ => ?_⟩
  have e1 : ∫ x in U, c * u x * coordinateDerivative i φ x =
      c * ∫ x in U, u x * coordinateDerivative i φ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x in U, (c • g x) i * φ x = c * ∫ x in U, g x i * φ x := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, hint φ hφ]
  ring

theorem HasWeakDivergence.const_smul' {U : Set (Vec d)} {F : Vec d → Vec d}
    (h : HasWeakDivergence U F (fun _ => 0)) (c : ℝ) :
    HasWeakDivergence U (fun x => c • F x) (fun _ => 0) := by
  obtain ⟨hF, h0, hint⟩ := h
  refine ⟨fun i => ((hF i).smul c : _), h0, fun φ hφ => ?_⟩
  have e : ∫ x in U, dot (c • F x) (gradient φ x) = c * ∫ x in U, dot (F x) (gradient φ x) := by
    rw [← integral_const_mul]; congr 1; funext x
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; ring_nf
  rw [e, hint φ hφ]
  simp

/-- `u ∈ H¹(B_r)` is in `L^{2+1/d}(B_r)`, by the Sobolev inequality (Theorem B.9) with exponent
`p = 2d/(d+1)`. -/
theorem memLp_two_add_inv_of_h1_ball (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r)))
    (hug : HasWeakGradient (ball 0 r) u g) :
    MemLp u (ENNReal.ofReal (2 + 1 / d)) (volume.restrict (ball 0 r)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 2 * d / (d + 1) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ (by linarith)]; linarith
  have hpd : p < d := by rw [hp, div_lt_iff₀ (by linarith)]; nlinarith
  have hp2 : ENNReal.ofReal p ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by rw [hp, div_le_iff₀ (by linarith)]; linarith)
  have hq : 2 + 1 / (d : ℝ) ≤ d * p / (d - p) := by
    have e : d * p / (d - p) = 2 * d / (d - 1) := by
      rw [hp]; field_simp; ring
    have h1 : (2 : ℝ) + 1 / d = (2 * d + 1) / d := by field_simp
    rw [e, h1, div_le_div_iff₀ hd0 (by linarith)]
    nlinarith
  have hU0 : volume (ball (0 : Vec d) r) ≠ 0 := volume_ball_ne_zero' 0 hr
  have hUt : volume (ball (0 : Vec d) r) ≠ ⊤ := volume_ball_ne_top' 0 r
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) r)) := isFiniteMeasure_restrict.mpr hUt
  obtain ⟨C, hC, hB⟩ := theorem_B_9_one (d := d) p hp1 hpd
  have hW : IsW1p (ball 0 r) (ENNReal.ofReal p) u g :=
    ⟨hu.mono_exponent hp2, (memLp_pi_iff.2 hg).mono_exponent hp2, hug⟩
  have h := (hB 0 r hr u g).1 hW
  have hfin : ENNReal.ofReal (C * r) * PDE.eLpMeanNormOn (ball 0 r) (ENNReal.ofReal p)
      (fun x => euclideanNorm (g x)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (eLpMeanNormOn_ne_top_of_memLp hU0 hUt
      ((memLp_euclideanNorm_of_coord hg).mono_exponent hp2))
  obtain ⟨w, hw⟩ := iInf_lt_iff.1 (lt_of_le_of_lt h (lt_top_iff_ne_top.2 hfin))
  have hmw : MemLp (fun x => u x - w) (ENNReal.ofReal (d * p / (d - p)))
      (volume.restrict (ball 0 r)) := memLp_of_eLpMeanNormOn_ne_top hU0 hUt hw.ne
  have hmu : MemLp u (ENNReal.ofReal (d * p / (d - p))) (volume.restrict (ball 0 r)) := by
    have e : (fun x => u x - w) + (fun _ => w) = u := by funext x; simp
    rw [← e]; exact hmw.add (memLp_const w)
  exact hmu.mono_exponent (ENNReal.ofReal_le_ofReal hq)

/-- **Rescaling** `x ↦ c x` of an `H¹` function and of a divergence-free flux: if `cV ⊆ U`, then
`v(c ·) ∈ H¹(V)` with gradient `c ∇v(c ·)` and `B(c ·) c ∇v(c ·)` is divergence free in `V`. -/
theorem rescale_h1_div {U V : Set (Vec d)} (hUm : MeasurableSet U) (hVm : MeasurableSet V)
    (hVt : volume V ≠ ⊤) {c : ℝ} (hc : 0 < c) (hV : ∀ x ∈ V, c • x ∈ U) {v : Vec d → ℝ}
    {G : Vec d → Vec d} (B : Vec d → Mat d) (hv : MemLp v 2 (volume.restrict U))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U)) (hvG : HasWeakGradient U v G)
    (hdiv : HasWeakDivergence U (fun x => (B x).mulVec (G x)) (fun _ => 0))
    (hloc : ∀ i, LocallyIntegrableOn (fun x => (B (c • x)).mulVec (G (c • x)) i) V volume) :
    MemLp (fun x => v (c • x)) 2 (volume.restrict V) ∧
      (∀ i, MemLp (fun x => (c • G (c • x)) i) 2 (volume.restrict V)) ∧
      HasWeakGradient V (fun x => v (c • x)) (fun x => c • G (c • x)) ∧
      HasWeakDivergence V (fun x => (B (c • x)).mulVec (c • G (c • x))) (fun _ => 0) := by
  have hV' : ∀ x ∈ V, c • x + 0 ∈ U := fun x hx => by rw [add_zero]; exact hV x hx
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVt
  have h1 : MemLp (fun x => v (c • x)) 2 (volume.restrict V) := by
    have h := MemLp.comp_smul_add_restrict hUm hVm hc.ne' 0 hV' hv
    simpa only [add_zero] using h
  have h2 : ∀ i, MemLp (fun x => G (c • x) i) 2 (volume.restrict V) := fun i => by
    have h := MemLp.comp_smul_add_restrict (f := fun x => G x i) hUm hVm hc.ne' 0 hV' (hG i)
    simpa only [add_zero] using h
  have hw := hasWeakGradientOn_comp_smul_add hc 0 hV' hvG
  simp only [add_zero] at hw
  have hw' : HasWeakGradient V (fun x => c⁻¹ * v (c • x)) (fun x => G (c • x)) :=
    hasWeakGradient_of_hasWeakGradientOn' hw
      (IntegrableOn.locallyIntegrableOn ((h1.const_mul c⁻¹).integrable one_le_two))
      (fun i => IntegrableOn.locallyIntegrableOn ((h2 i).integrable one_le_two))
  have hw'' := hw'.const_mul' c
  have e : (fun x => c * (c⁻¹ * v (c • x))) = fun x => v (c • x) := by
    funext x; field_simp
  rw [e] at hw''
  refine ⟨h1, fun i => (h2 i).const_mul c, hw'', ?_⟩
  have hd := TwoScale.hasWeakDivergence_comp_smul_add hc 0 hV' hdiv
    (fun i => by simpa only [add_zero] using hloc i)
  simp only [add_zero] at hd
  have hd' := hd.const_smul' c
  convert hd' using 2 with x
  rw [Matrix.mulVec_smul]

set_option maxHeartbeats 400000 in
/-- **The harmonic approximation at one scale**, from the estimate of Theorem 2.18 on `B_{1/2}`
for one coefficient field: for `R ≥ 1` and a weak solution `u ∈ H¹(B_R)` there is an `A`-harmonic
`ū ∈ H¹(B_{R/2})` with
`‖u - ū‖²_{L̲²(B_{R/2})} ≤ C₁ (C_M ‖u - (u)_{B_R}‖_{L̲²(B_R)})² (R^{-β(d-s')} + X R^{-s'})`. -/
theorem harmonicApprox_of_bound (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {δ CM C₁ β s' X : ℝ}
    (hδd : δ ≤ 1 / d) (hCM : 0 ≤ CM) (hC₁ : 0 ≤ C₁) (hX0 : 0 ≤ X)
    (a : CoefficientField d Λ)
    (hMey : ∀ R : ℝ, 0 < R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient (ball 0 R) u g →
      HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
      PDE.eLpMeanNormOn (ball 0 (R / 2)) (ENNReal.ofReal (2 + δ))
          (fun x => euclideanNorm (g x)) ≤
        ENNReal.ofReal (CM * (R⁻¹ * scalarRms volume (ball 0 R)
          (fun x => u x - ⨍ y in ball 0 R, u y))))
    (A : Mat d) (hAt : A.transpose = A) (hA1 : ∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (hA2 : ∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ)
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
    (hdiv : HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0)) :
    ∃ (uh : Vec d → ℝ) (gh : Vec d → Vec d), MemLp uh 2 (volume.restrict (ball 0 (R / 2))) ∧
      (∀ i, MemLp (fun x => gh x i) 2 (volume.restrict (ball 0 (R / 2)))) ∧
      HasWeakGradient (ball 0 (R / 2)) uh gh ∧
      HasWeakDivergence (ball 0 (R / 2)) (fun x => A.mulVec (gh x)) (fun _ => 0) ∧
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
  have hloc : ∀ i, LocallyIntegrableOn (fun x => (a (R • x)).mulVec (g (R • x)) i) U₀ volume :=
    fun i => by
      have : IsFiniteMeasure (volume.restrict U₀) := isFiniteMeasure_restrict.mpr hUt
      have h := memLp_coefficient_mulVec_apply (rescaledCoefficientField a (inv_ne_zero hR.ne'))
        (memLp_pi_iff.2 hgR) i
      simp only [rescaledCoefficientField_apply, inv_inv] at h
      exact IntegrableOn.locallyIntegrableOn (h.integrable one_le_two)
  obtain ⟨hf2, hF2, hfF, hdivF⟩ := rescale_h1_div hRm hUm hUt hR
    (fun x hx => hSR (hmapS x hx)) (fun x => a x) hu hg hug hdiv hloc
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
  -- the homogenized Dirichlet problem on `B_{1/2}`
  obtain ⟨w, gw, hw, hdivw⟩ := exists_ballDirichlet hΛ hd0 (by norm_num : (0 : ℝ) < 1 / 2) A hAt
    hA1 hA2 hF2
  have hH0 : H01 U₀ (fun x => (w x + u (R • x)) - u (R • x))
      (fun x => (gw x + R • g (R • x)) - R • g (R • x)) :=
    hw.congr (fun x => (add_sub_cancel_right _ _).symm) (fun x => (add_sub_cancel_right _ _).symm)
  have hHf : H01 U₀ (fun x => u (R • x) - u (R • x)) (fun x => R • g (R • x) - R • g (R • x)) :=
    (H01_zero U₀).congr (fun x => (sub_self _).symm) (fun x => (sub_self _).symm)
  have hdivF' : HasWeakDivergence U₀ (fun x => (a (R⁻¹⁻¹ • x)).mulVec (R • g (R • x)))
      (fun _ => 0) := by simpa only [inv_inv] using hdivF
  have hb := h218 R⁻¹ (inv_pos.2 hR) (inv_le_one_of_one_le₀ hR1) _ _ hW _ _ _ _ hHf hdivF' hH0
    hdivw
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
  have hlocB : ∀ i, LocallyIntegrableOn (fun y => ((fun _ => A) (R⁻¹ • y)).mulVec
      ((fun x => gw x + R • g (R • x)) (R⁻¹ • y)) i) S volume := fun i => by
    have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSt
    have hmap0' : ∀ y ∈ S, R⁻¹ • y + 0 ∈ U₀ := fun y hy => by rw [add_zero]; exact hmapB y hy
    have hc : ∀ j, MemLp (fun y => (gw (R⁻¹ • y) + R • g (R • R⁻¹ • y)) j) 2
        (volume.restrict S) := fun j => by
      have h := MemLp.comp_smul_add_restrict (f := fun x => (gw x + R • g (R • x)) j) hUm hSm
        (inv_ne_zero hR.ne') 0 hmap0' (hg₀ j)
      simpa only [add_zero] using h
    exact IntegrableOn.locallyIntegrableOn
      ((TwoScale.memLp_const_mulVec A hc i).integrable one_le_two)
  obtain ⟨huh, hgh, hughh, hdivuh⟩ := rescale_h1_div hUm hSm hSt (inv_pos.2 hR) hmapB (fun _ => A)
    hu₀ hg₀ hug₀ hdivw hlocB
  refine ⟨_, _, huh, hgh, hughh, hdivuh, ?_⟩
  -- the estimate
  have hrms : scalarRms volume S (fun y => u y - (w (R⁻¹ • y) + u (R • R⁻¹ • y))) =
      scalarRms volume U₀ (fun x => u (R • x) - (w x + u (R • x))) := by
    rw [← hRU, ← TwoScale.scalarRms_comp_smul hR]
    simp only [inv_smul_smul₀ hR.ne']
  rw [hrms]
  have hX := hb.trans (mul_le_mul_left (mul_le_mul_right
    (pow_le_pow_left₀ zero_le hFn 2) _) _)
  have hb0 : 0 ≤ R⁻¹ ^ (β * ((d : ℝ) - s')) + X * R⁻¹ ^ s' :=
    add_nonneg (Real.rpow_nonneg (inv_nonneg.2 hR.le) _)
      (mul_nonneg hX0 (Real.rpow_nonneg (inv_nonneg.2 hR.le) _))
  have hs0 : 0 ≤ scalarRms volume U₀ (fun x => u (R • x) - (w x + u (R • x))) :=
    Real.sqrt_nonneg _
  have hm0 : 0 ≤ CM * scalarRms volume (ball 0 R) (fun x => u x - ⨍ y in ball 0 R, u y) :=
    mul_nonneg hCM (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_pow hs0, ← ENNReal.ofReal_pow hm0, ← ENNReal.ofReal_mul hC₁,
    ← ENNReal.ofReal_mul (mul_nonneg hC₁ (sq_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hC₁ (sq_nonneg _)) hb0)] at hX
  exact hX

/-- `R⁻¹^x ≤ R^{-y}` for `R ≥ 1` and `y ≤ x`. -/
theorem inv_rpow_le_rpow_neg {R x y : ℝ} (hR : 1 ≤ R) (hyx : y ≤ x) :
    R⁻¹ ^ x ≤ R ^ (-y) := by
  rw [Real.inv_rpow (by linarith), ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)

set_option maxHeartbeats 400000 in
/-- **Proposition 3.2 (harmonic approximation)**, for `d ≥ 2` and `Λ > 1`: there is `α(d, Λ) > 0`
such that for every `s ∈ (0, d)` there is `C(s, d, Λ)` with, for every law satisfying
(0.10)–(0.11), a random variable `X ≥ 1` with `X ≤ O_s(C)`, (3.11), such that, for almost every
coefficient field, every `R ≥ X` and every weak solution `u ∈ H¹(B_R)` of `-∇·(a∇u) = 0` in `B_R`,
there is a weak solution `ū ∈ H¹(B_{R/2})` of `-∇·(ā∇ū) = 0` in `B_{R/2}` with
`‖u - ū‖_{L̲²(B_{R/2})} ≤ C R^{-α(d-s)} ‖u - (u)_{B_R}‖_{L̲²(B_R)}`, (3.13). -/
theorem proposition_3_2 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) :
    ∃ α : ℝ, 0 < α ∧ ∀ s : ℝ, 0 < s → s < d → ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s C ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ R : ℝ, X a ≤ R → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        MemLp u 2 (volume.restrict (ball 0 R)) →
        (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R))) →
        HasWeakGradient (ball 0 R) u g →
        HasWeakDivergence (ball 0 R) (fun x => (a x).mulVec (g x)) (fun _ => 0) →
        ∃ (uh : Vec d → ℝ) (gh : Vec d → Vec d), MemLp uh 2 (volume.restrict (ball 0 (R / 2))) ∧
          (∀ i, MemLp (fun x => gh x i) 2 (volume.restrict (ball 0 (R / 2)))) ∧
          HasWeakGradient (ball 0 (R / 2)) uh gh ∧
          HasWeakDivergence (ball 0 (R / 2)) (fun x => (homogenizedMatrix P).mulVec (gh x))
            (fun _ => 0) ∧
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
  obtain ⟨uh, gh, h1u, h2u, h3u, h4u, h5u⟩ := harmonicApprox_of_bound hd hΛ.le hδd hCM hC₁.le
    (hX₁0 a) a (hMey' a) (homogenizedMatrix P) (homogenizedMatrix_transpose hP hΛ0)
    (euclideanSq_le_dot_homogenizedMatrix hP hΛ0)
    (fun ξ => (homogenizedMatrix_dot_bounds hP hΛ0 ξ).2) hb hR1 hu hg hug hdiv
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

end QSH
