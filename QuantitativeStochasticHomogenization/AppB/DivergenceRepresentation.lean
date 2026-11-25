import QuantitativeStochasticHomogenization.AppC.NegativeSobolevPairing
import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity
import PDEFoundation.Analysis.NativeLpInjectedDuality
import PDEFoundation.Sobolev.Inequalities.SmoothZeroBoundaryPoincare
import PDEFoundation.Sobolev.W1p.ZeroBoundary
import PDEFoundation.Sobolev.W1p.EuclideanGradient
import PDEFoundation.Measure.BallVolume
import PDEFoundation.Geometry.ConvexDomain

/-!
# `W^{-1,p}` as the divergence of `L^p` vector fields on balls

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Remark B.6: for `p ∈ (1, ∞]`, every `h ∈ W^{-1,p}(U)` is `∇·H` for a vector field
`H ∈ L^p(U; ℝ^d)` with `C⁻¹ ‖h‖_{W^{-1,p}(U)} ≤ ‖H‖_{L^p(U)} ≤ C ‖h‖_{W^{-1,p}(U)}`. The book's
argument is the Riesz representation theorem together with the Poincaré inequality, which makes
`‖∇w‖_{L^{p'}(U)}` a norm on `W_0^{1,p'}(U)` equivalent to the `W^{1,p'}(U)` norm.

Here `U = B_r(z)` is a ball, `p ∈ (1, ∞)`, the distribution is `h = f + ∇·F` with
`f, F ∈ L¹(B_r(z))`, and the norms are the normalized ones of (B.1), (B.4) and (0.29)
(`negativeSobolevOneNorm`). The constant depends only on `d`.

The proof is the book's. On the smooth compactly supported tests `ψ` of `B_r(z)`, the gradient
map `ψ ↦ ∇ψ ∈ L^{p'}(B_r(z); ℝ^d)` (for the normalized volume) is injective, and by the Poincaré
inequality `‖ψ‖_{L̲^{p'}(B_r)} ≤ 2 (2^d + 1) r ‖∇ψ‖_{L̲^{p'}(B_r)}` of the elliptic regularity
library and `|B_r|^{-1/d} r = |B_1|^{-1/d}`, the test norm `‖ψ‖_{W̲^{1,p'}(B_r)}` is at most
`C(d) ‖∇ψ‖_{L̲^{p'}(B_r)}`. The functional `ψ ↦ ⨍_{B_r} h ψ` is therefore bounded for the norm
`‖∇ψ‖_{L̲^{p'}}`, and the Hahn–Banach theorem and the duality `(L^{p'})^* = L^p`
(`PDE.exists_nativeLp_density_through_injective`) represent it as `-⨍_{B_r} H · ∇ψ`.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem coordinateDerivative_weakTestFunction_add {U : Set (Vec d)}
    (φ ψ : PDE.WeakTestFunction U) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (φ + ψ).toFun x =
      coordinateDerivative i φ.toFun x + coordinateDerivative i ψ.toFun x := by
  have hφ : DifferentiableAt ℝ φ.toFun x := φ.contDiff.differentiable (by simp) x
  have hψ : DifferentiableAt ℝ ψ.toFun x := ψ.contDiff.differentiable (by simp) x
  change fderiv ℝ (φ.toFun + ψ.toFun) x (unitVector i) =
    fderiv ℝ φ.toFun x (unitVector i) + fderiv ℝ ψ.toFun x (unitVector i)
  rw [fderiv_add hφ hψ, add_apply]

theorem coordinateDerivative_weakTestFunction_smul {U : Set (Vec d)} (c : ℝ)
    (φ : PDE.WeakTestFunction U) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (c • φ).toFun x = c * coordinateDerivative i φ.toFun x := by
  have hφ : DifferentiableAt ℝ φ.toFun x := φ.contDiff.differentiable (by simp) x
  change fderiv ℝ (fun y => c * φ.toFun y) x (unitVector i) = c * fderiv ℝ φ.toFun x (unitVector i)
  rw [fderiv_const_mul hφ]
  simp

theorem gradient_weakTestFunction_add {U : Set (Vec d)} (φ ψ : PDE.WeakTestFunction U)
    (x : Vec d) : gradient (φ + ψ).toFun x = gradient φ.toFun x + gradient ψ.toFun x := by
  funext i
  exact coordinateDerivative_weakTestFunction_add φ ψ i x

theorem continuous_coordinateDerivative_weakTestFunction {U : Set (Vec d)}
    (φ : PDE.WeakTestFunction U) (i : Fin d) :
    Continuous (coordinateDerivative i φ.toFun) :=
  (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_coordinateDerivative_weakTestFunction {U : Set (Vec d)}
    (φ : PDE.WeakTestFunction U) (i : Fin d) :
    HasCompactSupport (coordinateDerivative i φ.toFun) :=
  φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (unitVector i)

/-- The integrand `f ψ - F · ∇ψ` of the pairing of `h = f + ∇·F` with a test is integrable on `U`
when `f, F ∈ L¹(U)`. -/
theorem integrableOn_distributionPairing_integrand {U : Set (Vec d)} {f : Vec d → ℝ}
    {F : Vec d → Vec d} (hf : IntegrableOn f U) (hF : ∀ i, IntegrableOn (fun x => F x i) U)
    (φ : PDE.WeakTestFunction U) :
    IntegrableOn (fun x => f x * φ.toFun x - dot (F x) (gradient φ.toFun x)) U := by
  have hφc : Continuous φ.toFun := φ.contDiff.continuous
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support φ.hasCompactSupport
  have h1 : Integrable (fun x => f x * φ.toFun x) (volume.restrict U) :=
    Integrable.mul_bdd hf hφc.aestronglyMeasurable (Eventually.of_forall hM)
  have h2 : Integrable (fun x => dot (F x) (gradient φ.toFun x)) (volume.restrict U) := by
    unfold dot
    refine integrable_finsetSum _ fun i _ => ?_
    have hc := continuous_coordinateDerivative_weakTestFunction φ i
    obtain ⟨Mi, hMi⟩ := hc.bounded_above_of_compact_support
      (hasCompactSupport_coordinateDerivative_weakTestFunction φ i)
    exact Integrable.mul_bdd (hF i) hc.aestronglyMeasurable (Eventually.of_forall hMi)
  exact h1.sub h2

theorem memLp_restrict_of_memLp_normalizedVolumeOn {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {p : ℝ≥0∞} {g : Vec d → ℝ} (hg : MemLp g p (PDE.normalizedVolumeOn U)) :
    MemLp g p (volume.restrict U) := by
  have e : volume.restrict U = volume U • PDE.normalizedVolumeOn U := by
    rw [PDE.normalizedVolumeOn, smul_smul, ENNReal.mul_inv_cancel hU0 hUt, one_smul]
  rw [e]
  exact hg.smul_measure hUt

theorem integral_normalizedVolumeOn_eq_mul {U : Set (Vec d)} (g : Vec d → ℝ) :
    ∫ x, g x ∂(PDE.normalizedVolumeOn U) = (volume.real U)⁻¹ * ∫ x in U, g x := by
  rw [PDE.normalizedVolumeOn, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    measureReal_def]

/-- The constant `2 (2^d + 1) |B_1|^{-1/d} + d` of Remark B.6 on balls. -/
def divergenceRepresentationConstant (d : ℕ) : ℝ :=
  2 * (2 ^ d + 1) * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ^ (-(1 : ℝ) / d) + d

theorem divergenceRepresentationConstant_nonneg (d : ℕ) :
    0 ≤ divergenceRepresentationConstant d :=
  add_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (Nat.cast_nonneg d)

/-- `|B_r(z)|^{-1/d} r = |B_1|^{-1/d}`. -/
theorem volume_ball_toReal_rpow_mul (hd : 0 < d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (ball z r)).toReal ^ (-(1 : ℝ) / d) * r =
      (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ^ (-(1 : ℝ) / d) := by
  have hvol : (volume (ball z r)).toReal =
      r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := by
    rw [ball_eq_euclideanBall z hr, PDE.volume_euclideanBall_eq_unit_mul_of_pos z hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
  have hpow : (r ^ d) ^ (-(1 : ℝ) / d) = r⁻¹ := by
    rw [neg_div, Real.rpow_neg (pow_nonneg hr.le d), one_div,
      Real.pow_rpow_inv_natCast hr.le (by omega)]
  rw [hvol, Real.mul_rpow (pow_nonneg hr.le d) ENNReal.toReal_nonneg, hpow, mul_right_comm,
    inv_mul_cancel₀ hr.ne', one_mul]

/-- **Remark B.6 on balls, the representation.** For `d ≥ 1`, `s ∈ (1, ∞)`, a ball `B_r(z)` and
`h = f + ∇·F` with `f, F ∈ L¹(B_r(z))` and `‖h‖_{W̲^{-1,s}(B_r(z))} ≤ N`, there is
`H ∈ L^s(B_r(z); ℝ^d)` with `∫ h ψ = -∫ H · ∇ψ` for every smooth compactly supported test `ψ` and
`‖H‖_{L̲^s(B_r(z))} ≤ C(d) N`, `C(d) = divergenceRepresentationConstant d`. -/
theorem exists_divergence_representation_ball (hd : 0 < d) {s : ℝ} (hs : 1 < s) (z : Vec d)
    {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} {F : Vec d → Vec d} (hf : IntegrableOn f (ball z r))
    (hF : ∀ i, IntegrableOn (fun x => F x i) (ball z r)) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : negativeSobolevOneNorm s (ball z r) f F ≤ ENNReal.ofReal N) :
    ∃ H : Vec d → Vec d,
      (∀ i, MemLp (fun x => H x i) (ENNReal.ofReal s) (volume.restrict (ball z r))) ∧
      (∀ ψ, IsSpatialTest (ball z r) ψ →
        ∫ x in ball z r, (f x * ψ x - dot (F x) (gradient ψ x)) =
          -∫ x in ball z r, dot (H x) (gradient ψ x)) ∧
      PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) ≤
        ENNReal.ofReal (divergenceRepresentationConstant d * N) := by
  set U := ball z r with hUdef
  have hUe : U = PDE.euclideanBall z r := ball_eq_euclideanBall z hr
  have hconv : PDE.IsOpenBoundedConvexDomain U := by
    rw [hUe]
    exact PDE.isOpenBoundedConvexDomain_euclideanBall z hr
  have hdiam : PDE.HasEuclideanDiameterLE U (2 * r) := by
    rw [hUe]
    exact PDE.hasEuclideanDiameterLE_euclideanBall z hr
  have hU0 : volume U ≠ 0 := by
    rw [hUe]
    exact (PDE.volume_euclideanBall_pos z hr).ne'
  have hUt : volume U ≠ ⊤ := by
    rw [hUe]
    exact PDE.volume_euclideanBall_ne_top z hr.le
  have hUpos : 0 < volume U := pos_iff_ne_zero.mpr hU0
  have hs1 : 0 < s - 1 := sub_pos.mpr hs
  have hq1 : 1 < s / (s - 1) := (one_lt_div hs1).mpr (by linarith)
  have : Fact (1 ≤ ENNReal.ofReal s) := ⟨ENNReal.one_le_ofReal.mpr hs.le⟩
  have : Fact (1 ≤ ENNReal.ofReal (s / (s - 1))) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  have hq0 : ENNReal.ofReal (s / (s - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  set ν := PDE.normalizedVolumeOn U with hν
  have : IsProbabilityMeasure ν :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUpos hUt.lt_top
  have hrestrict : volume.restrict U = volume U • ν := by
    rw [hν, PDE.normalizedVolumeOn, smul_smul, ENNReal.mul_inv_cancel hU0 hUt, one_smul]
  set c := divergenceRepresentationConstant d with hc
  have hc0 : 0 ≤ c := divergenceRepresentationConstant_nonneg d
  have hgradc : ∀ φ : PDE.WeakTestFunction U, Continuous (gradient φ.toFun) := fun φ =>
    continuous_pi fun i => continuous_coordinateDerivative_weakTestFunction φ i
  have hGmem : ∀ φ : PDE.WeakTestFunction U,
      MemLp (PDE.toHilbertVecField (gradient φ.toFun)) (ENNReal.ofReal (s / (s - 1))) ν := by
    intro φ
    have hgi : PDE.GradMemLpOn U (ENNReal.ofReal (s / (s - 1))) (gradient φ.toFun) := fun i =>
      (continuous_coordinateDerivative_weakTestFunction φ i).memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative_weakTestFunction φ i)
    exact PDE.memLp_normalizedVolumeOn_of_memLpOn
      (PDE.gradMemLpOn_iff_memLp_toHilbertVecField.mp hgi) hUpos
  let A : PDE.WeakTestFunction U →ₗ[ℝ] Lp (PDE.HilbertVec d) (ENNReal.ofReal (s / (s - 1))) ν :=
    { toFun := fun φ => (hGmem φ).toLp (PDE.toHilbertVecField (gradient φ.toFun))
      map_add' := fun φ ψ => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        ext i
        change coordinateDerivative i (φ + ψ).toFun x =
          coordinateDerivative i φ.toFun x + coordinateDerivative i ψ.toFun x
        exact coordinateDerivative_weakTestFunction_add φ ψ i x
      map_smul' := fun a φ => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        ext i
        change coordinateDerivative i (a • φ).toFun x = a * coordinateDerivative i φ.toFun x
        exact coordinateDerivative_weakTestFunction_smul a φ i x }
  -- the norm of `A φ` is `‖∇φ‖_{L̲^{s'}(U)}`
  have hnormA : ∀ φ : PDE.WeakTestFunction U, ‖A φ‖ =
      (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
        (fun x => PDE.vecEuclideanNorm (gradient φ.toFun x))).toReal := by
    intro φ
    change ‖(hGmem φ).toLp (PDE.toHilbertVecField (gradient φ.toFun))‖ = _
    rw [Lp.norm_toLp, PDE.eLpNorm_toHilbertVecField_eq ν _ _ (hgradc φ).aestronglyMeasurable]
    rfl
  have hfinA : ∀ φ : PDE.WeakTestFunction U,
      PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
        (fun x => PDE.vecEuclideanNorm (gradient φ.toFun x)) ≠ ⊤ := by
    intro φ
    have h := (hGmem φ).eLpNorm_ne_top
    rw [PDE.eLpNorm_toHilbertVecField_eq ν _ _ (hgradc φ).aestronglyMeasurable] at h
    exact h
  -- the Poincaré inequality for tests, normalized
  have hP : ∀ φ : PDE.WeakTestFunction U,
      PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) φ.toFun ≤
        ENNReal.ofReal (((2 : ℝ) ^ d + 1) * (2 * r)) *
          PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
            (fun x => PDE.vecEuclideanNorm (gradient φ.toFun x)) := by
    intro φ
    have h := PDE.eLpNormOn_testFunction_le_two_pow_add_one_mul_diameter_grad hd hconv hdiam
      (by linarith) hq1 φ
    unfold PDE.euclideanFieldELpNormOn at h
    rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUt.lt_top,
      PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUt.lt_top, mul_left_comm]
    exact mul_le_mul_right h _
  -- the test norm is controlled by the gradient
  have hT : ∀ φ : PDE.WeakTestFunction U,
      sobolevOneTestNorm (ENNReal.ofReal (s / (s - 1))) U φ.toFun ≤ c * ‖A φ‖ := by
    intro φ
    set M := (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
      (fun x => PDE.vecEuclideanNorm (gradient φ.toFun x))).toReal with hM
    have h1 : (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) φ.toFun).toReal ≤
        ((2 : ℝ) ^ d + 1) * (2 * r) * M := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinA φ)) (hP φ)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by positivity) (by linarith))] at h
      exact h
    have h2 : ∀ i : Fin d, (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
        (coordinateDerivative i φ.toFun)).toReal ≤ M := by
      intro i
      refine ENNReal.toReal_mono (hfinA φ) (eLpNorm_mono_real
        (continuous_coordinateDerivative_weakTestFunction φ i).aestronglyMeasurable fun x => ?_)
      rw [Real.norm_eq_abs]
      exact PDE.abs_apply_le_vecEuclideanNorm (gradient φ.toFun x) i
    have hV : 0 ≤ (volume U).toReal ^ (-(1 : ℝ) / d) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hscale := volume_ball_toReal_rpow_mul hd z hr
    rw [← hUdef] at hscale
    rw [hnormA φ, ← hM]
    unfold sobolevOneTestNorm
    calc (volume U).toReal ^ (-(1 : ℝ) / d) *
          (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) φ.toFun).toReal +
          ∑ i : Fin d, (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
            (coordinateDerivative i φ.toFun)).toReal
        ≤ (volume U).toReal ^ (-(1 : ℝ) / d) * (((2 : ℝ) ^ d + 1) * (2 * r) * M) +
          ∑ _i : Fin d, M :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hV) (Finset.sum_le_sum fun i _ => h2 i)
      _ = (2 * (2 ^ d + 1) * ((volume U).toReal ^ (-(1 : ℝ) / d) * r) + d) * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ = c * M := by rw [hscale, hc, divergenceRepresentationConstant]
  -- the gradient map is injective
  have hA : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).mpr fun φ hφ => ?_
    have hM0 : PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
        (fun x => PDE.vecEuclideanNorm (gradient φ.toFun x)) = 0 := by
      have h := congrArg norm hφ
      rw [norm_zero, hnormA φ] at h
      exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (hfinA φ)
    have hφ0 : PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) φ.toFun = 0 := by
      have h := hP φ
      rw [hM0, mul_zero] at h
      exact le_antisymm h zero_le
    have hae : φ.toFun =ᵐ[ν] 0 := (eLpNorm_eq_zero_iff hq0).mp hφ0
    have hae' : φ.toFun =ᵐ[volume.restrict U] 0 := by
      rw [hrestrict]
      exact Measure.ae_smul_measure hae _
    have heq := Measure.eqOn_open_of_ae_eq hae' hconv.isOpen
      φ.contDiff.continuous.continuousOn
      (continuousOn_const : ContinuousOn (fun _ : Vec d => (0 : ℝ)) U)
    ext x
    by_cases hx : x ∈ U
    · exact heq hx
    · by_contra hne
      exact hx (φ.tsupport_subset (subset_tsupport _ (Function.mem_support.mpr hne)))
  -- the functional `ψ ↦ ⨍_U h ψ`
  let L₀ : PDE.WeakTestFunction U →ₗ[ℝ] ℝ :=
    { toFun := fun φ => distributionPairing U f F φ.toFun
      map_add' := fun φ ψ => by
        have key : ∀ x, f x * (φ + ψ).toFun x - dot (F x) (gradient (φ + ψ).toFun x) =
            (f x * φ.toFun x - dot (F x) (gradient φ.toFun x)) +
              (f x * ψ.toFun x - dot (F x) (gradient ψ.toFun x)) := by
          intro x
          rw [gradient_weakTestFunction_add]
          have e : (φ + ψ).toFun x = φ.toFun x + ψ.toFun x := rfl
          rw [e]
          simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
          ring
        simp only [distributionPairing, setAverage_eq, smul_eq_mul, key]
        rw [integral_add (integrableOn_distributionPairing_integrand hf hF φ)
          (integrableOn_distributionPairing_integrand hf hF ψ), mul_add]
      map_smul' := fun a φ => by
        rw [RingHom.id_apply, smul_eq_mul]
        exact distributionPairing_const_mul f F φ.contDiff a }
  let : NormedAddCommGroup (PDE.WeakTestFunction U) :=
    NormedAddCommGroup.induced (PDE.WeakTestFunction U)
      (Lp (PDE.HilbertVec d) (ENNReal.ofReal (s / (s - 1))) ν) A hA
  let : NormedSpace ℝ (PDE.WeakTestFunction U) :=
    NormedSpace.induced ℝ (PDE.WeakTestFunction U)
      (Lp (PDE.HilbertVec d) (ENNReal.ofReal (s / (s - 1))) ν) A
  have hbound : ∀ φ : PDE.WeakTestFunction U, ‖L₀ φ‖ ≤ N * c * ‖φ‖ := by
    intro φ
    change |distributionPairing U f F φ.toFun| ≤ N * c * ‖A φ‖
    have htest : IsSpatialTest U φ.toFun := ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
    calc |distributionPairing U f F φ.toFun|
        ≤ N * sobolevOneTestNorm (ENNReal.ofReal (s / (s - 1))) U φ.toFun :=
          abs_distributionPairing_le hN0 hN htest
      _ ≤ N * (c * ‖A φ‖) := mul_le_mul_of_nonneg_left (hT φ) hN0
      _ = N * c * ‖A φ‖ := (mul_assoc _ _ _).symm
  let L : PDE.WeakTestFunction U →L[ℝ] ℝ := L₀.mkContinuous (N * c) hbound
  have hLnorm : ‖L‖ ≤ N * c := LinearMap.mkContinuous_norm_le L₀ (mul_nonneg hN0 hc0) hbound
  obtain ⟨H, hHm, hHLp, hrep, hHnorm⟩ :=
    PDE.exists_nativeLp_density_through_injective (μ := ν) (d := d) (p := s) hs A hA L
  refine ⟨H, fun i => ?_, fun ψ hψ => ?_, ?_⟩
  · refine memLp_restrict_of_memLp_normalizedVolumeOn hU0 hUt ?_
    refine hHLp.of_le (hHm i) (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ PDE.vecEuclideanNorm (H x) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
    exact PDE.abs_apply_le_vecEuclideanNorm (H x) i
  · let φ : PDE.WeakTestFunction U := ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
    have h1 : L φ = distributionPairing U f F ψ := rfl
    have h2 : ∫ x, PDE.vecDot (H x) ((A φ x).toVec) ∂ν = ∫ x, dot (H x) (gradient ψ x) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (hGmem φ)] with x hx
      change PDE.vecDot (H x)
        ((((hGmem φ).toLp (PDE.toHilbertVecField (gradient φ.toFun))) x).toVec) = _
      rw [hx]
      rfl
    have h3 := hrep φ
    rw [h1, h2, hν, integral_normalizedVolumeOn_eq_mul, distributionPairing, setAverage_eq,
      smul_eq_mul] at h3
    have hvr : (volume.real U)⁻¹ ≠ 0 := by
      rw [measureReal_def]
      exact inv_ne_zero (ENNReal.toReal_pos hU0 hUt).ne'
    rw [← mul_neg] at h3
    exact mul_left_cancel₀ hvr h3
  · have hfin := hHLp.eLpNorm_ne_top
    change eLpNorm (fun x => PDE.vecEuclideanNorm (H x)) (ENNReal.ofReal s) ν ≤ _
    rw [← ENNReal.ofReal_toReal hfin, hHnorm]
    exact ENNReal.ofReal_le_ofReal (by linarith [hLnorm, mul_comm N c])

theorem aestronglyMeasurable_euclideanNorm_of_coord {μ : Measure (Vec d)} {H : Vec d → Vec d}
    (hH : ∀ i, AEStronglyMeasurable (fun x => H x i) μ) :
    AEStronglyMeasurable (fun x => euclideanNorm (H x)) μ := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hH i).mul (hH i))

/-- **Remark B.6, the lower bound**: `‖∇·H‖_{W̲^{-1,s}(U)} ≤ ‖H‖_{L̲^s(U)}` for `s ∈ (1, ∞)`. -/
theorem negativeSobolevOneNorm_zero_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) {s : ℝ}
    (hs : 1 < s) {H : Vec d → Vec d}
    (hH : ∀ i, MemLp (fun x => H x i) (ENNReal.ofReal s) (volume.restrict U)) :
    negativeSobolevOneNorm s U (fun _ => 0) H ≤
      PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) := by
  set μ := PDE.normalizedVolumeOn U with hμ
  have hpos : 0 < volume U := pos_iff_ne_zero.mpr hU0
  have hs0 : 0 < s := by linarith
  have hq1 : 1 < s / (s - 1) := (one_lt_div (sub_pos.mpr hs)).mpr (by linarith)
  have hpq : s.HolderConjugate (s / (s - 1)) := Real.HolderConjugate.conjExponent hs
  have hHμ : AEStronglyMeasurable (fun x => euclideanNorm (H x)) μ :=
    (aestronglyMeasurable_euclideanNorm_of_coord fun i =>
      (hH i).aestronglyMeasurable).smul_measure _
  have hmF : AEMeasurable (fun x => ‖euclideanNorm (H x)‖ₑ) μ := hHμ.enorm
  refine iSup_le fun ψ => ?_
  obtain ⟨ψ, htest, hT⟩ := ψ
  have hgrad : ∀ i, Continuous fun x => coordinateDerivative i ψ x := fun i =>
    (htest.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hav : distributionPairing U (fun _ => 0) H ψ =
      ∫ x, (0 * ψ x - dot (H x) (gradient ψ x)) ∂μ := by
    rw [hμ, integral_normalizedVolumeOn_eq_mul, distributionPairing, setAverage_eq, smul_eq_mul]
  rw [hav, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ x, ‖0 * ψ x - dot (H x) (gradient ψ x)‖ₑ ≤
      ∑ i, ‖euclideanNorm (H x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ := by
    intro x
    have hn : 0 ≤ euclideanNorm (H x) := Real.sqrt_nonneg _
    rw [zero_mul, zero_sub, enorm_neg, Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |dot (H x) (gradient ψ x)| ≤
        ENNReal.ofReal (∑ i, euclideanNorm (H x) * |coordinateDerivative i ψ x|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (PDE.abs_apply_le_vecEuclideanNorm (H x) i)
            (abs_nonneg _)
      _ = ∑ i, ‖euclideanNorm (H x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hn (abs_nonneg _))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul hn, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg hn]
  have hholder : ∀ i, ∫⁻ x, ‖euclideanNorm (H x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ ∂μ ≤
      PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) *
        PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) (coordinateDerivative i ψ) := by
    intro i
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hmF (hgrad i).aestronglyMeasurable.enorm
    have e1 : PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) =
        (∫⁻ x, ‖euclideanNorm (H x)‖ₑ ^ s ∂μ) ^ (1 / s) := by
      rw [PDE.eLpMeanNormOn, ← hμ, eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_pos.mpr hs0).ne' ENNReal.ofReal_ne_top hHμ, ENNReal.toReal_ofReal hs0.le]
    have e2 : PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) (coordinateDerivative i ψ) =
        (∫⁻ x, ‖coordinateDerivative i ψ x‖ₑ ^ (s / (s - 1)) ∂μ) ^ (1 / (s / (s - 1))) := by
      rw [PDE.eLpMeanNormOn, ← hμ, eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_pos.mpr (by linarith)).ne' ENNReal.ofReal_ne_top
        (hgrad i).aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith)]
    rw [e1, e2]
    exact h
  have hsumT : ∑ i, PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
      (coordinateDerivative i ψ) ≤ 1 := by
    have hfin : ∀ i, PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
        (coordinateDerivative i ψ) ≠ ⊤ := fun i =>
      PDE.memLp_normalizedVolumeOn_of_memLpOn ((hgrad i).memLp_of_hasCompactSupport
        (htest.2.1.fderiv_apply (𝕜 := ℝ) (unitVector i))) hpos |>.eLpNorm_ne_top
    have e : ∑ i, PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) (coordinateDerivative i ψ) =
        ENNReal.ofReal (∑ i, (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1)))
          (coordinateDerivative i ψ)).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hfin i)).symm
    rw [e, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hT)
    unfold sobolevOneTestNorm
    have h0 : 0 ≤ (volume U).toReal ^ (-(1 : ℝ) / d) *
        (PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) ψ).toReal :=
      mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) ENNReal.toReal_nonneg
    linarith
  have hmeas : ∀ i ∈ Finset.univ, AEMeasurable
      (fun x => ‖euclideanNorm (H x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ) μ :=
    fun i _ => hmF.mul (hgrad i).aestronglyMeasurable.enorm
  calc ∫⁻ x, ‖0 * ψ x - dot (H x) (gradient ψ x)‖ₑ ∂μ
      ≤ ∫⁻ x, ∑ i, ‖euclideanNorm (H x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ ∂μ :=
        lintegral_mono hpt
    _ = ∑ i, ∫⁻ x, ‖euclideanNorm (H x)‖ₑ * ‖coordinateDerivative i ψ x‖ₑ ∂μ :=
        lintegral_finsetSum' _ hmeas
    _ ≤ ∑ i, PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) *
          PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) (coordinateDerivative i ψ) :=
        Finset.sum_le_sum fun i _ => hholder i
    _ = PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) *
          ∑ i, PDE.eLpMeanNormOn U (ENNReal.ofReal (s / (s - 1))) (coordinateDerivative i ψ) := by
        rw [Finset.mul_sum]
    _ ≤ PDE.eLpMeanNormOn U (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) * 1 := by
        gcongr
    _ = _ := mul_one _

/-- Two right-hand sides with the same pairings against every test have the same normalized
`W^{-1,s}` norm. -/
theorem negativeSobolevOneNorm_eq_of_representation {U : Set (Vec d)} {s : ℝ} {f : Vec d → ℝ}
    {F H : Vec d → Vec d}
    (hrep : ∀ ψ, IsSpatialTest U ψ → ∫ x in U, (f x * ψ x - dot (F x) (gradient ψ x)) =
      -∫ x in U, dot (H x) (gradient ψ x)) :
    negativeSobolevOneNorm s U f F = negativeSobolevOneNorm s U (fun _ => 0) H := by
  unfold negativeSobolevOneNorm
  refine iSup_congr fun ψ => ?_
  have h : ∫ x in U, (0 * ψ.1 x - dot (H x) (gradient ψ.1 x)) =
      -∫ x in U, dot (H x) (gradient ψ.1 x) := by
    simp only [zero_mul, zero_sub]
    exact integral_neg _
  rw [distributionPairing, distributionPairing, setAverage_eq, setAverage_eq, hrep ψ.1 ψ.2.1, h]

/-- **Remark B.6 on balls.** For `d ≥ 1` there is `C(d) < ∞` such that, for `s ∈ (1, ∞)`, a ball
`B_r(z)` and `h = f + ∇·F ∈ W^{-1,s}(B_r(z))` with `f, F ∈ L¹(B_r(z))`, there is a vector field
`H ∈ L^s(B_r(z); ℝ^d)` with `∫_{B_r(z)} h ψ = -∫_{B_r(z)} H · ∇ψ` for every `ψ ∈ C_c^∞(B_r(z))` and
`‖h‖_{W̲^{-1,s}(B_r(z))} ≤ ‖H‖_{L̲^s(B_r(z))} ≤ C ‖h‖_{W̲^{-1,s}(B_r(z))}`. -/
theorem remark_B_6 (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ), 1 < s → ∀ (z : Vec d) (r : ℝ), 0 < r →
      ∀ (f : Vec d → ℝ) (F : Vec d → Vec d), IntegrableOn f (ball z r) →
      (∀ i, IntegrableOn (fun x => F x i) (ball z r)) →
      negativeSobolevOneNorm s (ball z r) f F ≠ ⊤ →
      ∃ H : Vec d → Vec d,
        (∀ i, MemLp (fun x => H x i) (ENNReal.ofReal s) (volume.restrict (ball z r))) ∧
        (∀ ψ, IsSpatialTest (ball z r) ψ →
          ∫ x in ball z r, (f x * ψ x - dot (F x) (gradient ψ x)) =
            -∫ x in ball z r, dot (H x) (gradient ψ x)) ∧
        negativeSobolevOneNorm s (ball z r) f F ≤
          PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) ∧
        PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal s) (fun x => euclideanNorm (H x)) ≤
          ENNReal.ofReal C * negativeSobolevOneNorm s (ball z r) f F := by
  refine ⟨divergenceRepresentationConstant d, divergenceRepresentationConstant_nonneg d,
    fun s hs z r hr f F hf hF hfin => ?_⟩
  obtain ⟨H, hHmem, hrep, hnorm⟩ := exists_divergence_representation_ball hd hs z hr hf hF
    ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hfin).ge
  have hU0 : volume (ball z r) ≠ 0 := by
    rw [ball_eq_euclideanBall z hr]
    exact (PDE.volume_euclideanBall_pos z hr).ne'
  refine ⟨H, hHmem, hrep, ?_, ?_⟩
  · rw [negativeSobolevOneNorm_eq_of_representation hrep]
    exact negativeSobolevOneNorm_zero_le hU0 hs hHmem
  · rw [ENNReal.ofReal_mul (divergenceRepresentationConstant_nonneg d),
      ENNReal.ofReal_toReal hfin] at hnorm
    exact hnorm

end QSH
