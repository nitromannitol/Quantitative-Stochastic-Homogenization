import QuantitativeStochasticHomogenization.Ch01.Sec04.DivCurlIdentity
import QuantitativeStochasticHomogenization.AppB.TheoremB10
import QuantitativeStochasticHomogenization.Ch03.Sec04.WeakGradientCentering

/-!
# Estimates for the div-curl lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the estimates in the proof of Lemma 1.16 on a bounded open convex domain `U`:

* the Sobolev–Poincaré inequality `‖u - (u)_U‖_{L̲^{s*}(U)} ≤ C D ‖∇u‖_{L̲²(U)}` for `u ∈ H¹(U)`,
  `s ∈ [1, 2]`, `s < d`, and `D` a bound of the diameter of `U`
  (`PDE.exists_convexSobolevPoincare_constant`, as in Proposition B.11);
* Morrey's inequality for the test functions of `U ⊆ B_r(z)`,
  `|ψ| ≤ C r ‖∇ψ‖_{L̲^p(U)}` for `p > d` (`abs_le_of_isSpatialTest_ball`, Theorem B.10);
* `‖∇ ∂_i φ‖_{L̲^p(U)} ≤ d ‖φ‖_{W̲^{2,p}(U)}`;
* Hölder's inequality for the normalized norms and the finiteness of the `H^{-1}(U)` norm of an
  `L²(U)` function.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Mixed coordinate derivatives of a smooth function commute. -/
theorem coordinateDerivative_comm_of_contDiff {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin d) :
    coordinateDerivative i (coordinateDerivative j ψ) =
      coordinateDerivative j (coordinateDerivative i ψ) := by
  ext x
  have hinner : (2 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
  have hn : minSmoothness ℝ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact_mod_cast hinner
  have hs := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt hn
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y) x := by
    have hbound : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact_mod_cast hinner
    exact ((hψ.contDiffAt (x := x)).fderiv_right hbound).differentiableAt (by norm_num)
  have happly (v w : Vec d) :
      fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
        (fderiv ℝ (fderiv ℝ ψ) x w) v := by
    have h := fderiv_clm_apply hd (differentiableAt_const (x := x) v)
    have h' := congrArg (fun L : Vec d →L[ℝ] ℝ => L w) h
    simpa using h'
  have hswap := hs.iteratedFDeriv_cons (v := unitVector i) (w := unitVector j)
  change fderiv ℝ (coordinateDerivative j ψ) x (unitVector i) =
    fderiv ℝ (coordinateDerivative i ψ) x (unitVector j)
  rw [show coordinateDerivative j ψ = fun y => fderiv ℝ ψ y (unitVector j) by rfl,
      show coordinateDerivative i ψ = fun y => fderiv ℝ ψ y (unitVector i) by rfl]
  rw [happly (unitVector j) (unitVector i), happly (unitVector i) (unitVector j)]
  simpa [iteratedFDeriv_two_apply] using hswap

/-- `u - c ∈ H¹(U)` with the same gradient, on a set of finite measure. -/
theorem H1.sub_const {U : Set (Vec d)} (hUt : volume U ≠ ⊤) {u : Vec d → ℝ}
    {G : Vec d → Vec d} (hu : H1 U u G) (c : ℝ) : H1 U (fun x => u x - c) G := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  exact ⟨hu.1.sub (memLp_const c), hu.2.1, hasWeakGradient_sub_const U hu.2.2 c⟩

/-- Hölder's inequality for the normalized norms: `|⨍_U f g| ≤ ‖f‖_{L̲^p(U)} ‖g‖_{L̲^q(U)}` for
`1/p + 1/q = 1`. -/
theorem abs_setAverage_mul_le {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1] {f g : Vec d → ℝ}
    (hf : MemLp f p (volume.restrict U)) (hg : MemLp g q (volume.restrict U)) :
    |⨍ x in U, f x * g x| ≤
      (PDE.eLpMeanNormOn U p f).toReal * (PDE.eLpMeanNormOn U q g).toReal := by
  set ν := PDE.normalizedVolumeOn U with hν
  have hfν : AEStronglyMeasurable f ν := hf.aestronglyMeasurable.smul_measure (volume U)⁻¹
  have hgν : AEStronglyMeasurable g ν := hg.aestronglyMeasurable.smul_measure (volume U)⁻¹
  have havg : ⨍ x in U, f x * g x = ∫ x, f x * g x ∂ν := by
    rw [hν, PDE.integral_normalizedVolumeOn_eq_integralAverage, PDE.integralAverage, setAverage_eq,
      smul_eq_mul, measureReal_def]
  rw [havg, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  simp only [ofReal_norm]
  rw [← eLpNorm_one_eq_lintegral_enorm (f := fun x => f x * g x) (hfν.mul hgν),
    ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (eLpMeanNormOn_ne_top_of_memLp hU0 hUt hf)
    (eLpMeanNormOn_ne_top_of_memLp hU0 hUt hg)) ?_
  have h := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := 1) hfν hgν
  exact h

theorem memLp_two_euclideanNorm {U : Set (Vec d)} {G : Vec d → Vec d}
    (hG : MemLp G 2 (volume.restrict U)) :
    MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U) :=
  PDE.GradMemLpOn.memLp_vecEuclideanNorm fun i => hG.eval i

/-- The normalized `L²(U)` norm of a coordinate is at most that of the Euclidean norm. -/
theorem eLpMeanNormOn_apply_le_euclideanNorm (U : Set (Vec d)) (p : ℝ≥0∞) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict U)) (i : Fin d) :
    PDE.eLpMeanNormOn U p (fun x => G x i) ≤
      PDE.eLpMeanNormOn U p (fun x => euclideanNorm (G x)) := by
  refine eLpNorm_mono_real ((continuous_apply i).comp_aestronglyMeasurable
    (hG.smul_measure (volume U)⁻¹)) fun x => ?_
  rw [Real.norm_eq_abs]
  exact PDE.abs_apply_le_vecEuclideanNorm (G x) i

/-- The normalized `H^{-1}(U)` norm of an `L²(U)` function is finite. -/
theorem negativeSobolevOneNorm_two_le {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    negativeSobolevOneNorm 2 U f 0 ≤
      ENNReal.ofReal ((volume U).toReal ^ ((1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 f).toReal) := by
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUt
  refine iSup_le fun ⟨ψ0, hψ, hψ1⟩ => ENNReal.ofReal_le_ofReal ?_
  rw [hq] at hψ1
  have hψm : MemLp ψ0 2 (volume.restrict U) :=
    (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1).restrict U
  have hp : distributionPairing U f 0 ψ0 = ⨍ x in U, f x * ψ0 x := by
    unfold distributionPairing
    simp [dot]
  rw [hp]
  refine (abs_setAverage_mul_le hU0 hUt hf hψm).trans ?_
  have hpsi : (PDE.eLpMeanNormOn U 2 ψ0).toReal ≤ (volume U).toReal ^ ((1 : ℝ) / d) := by
    have h1 : (volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 ψ0).toReal ≤ 1 := by
      refine le_trans ?_ hψ1
      unfold sobolevOneTestNorm
      have := Finset.sum_nonneg (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
        ENNReal.toReal_nonneg (a := PDE.eLpMeanNormOn U 2 (coordinateDerivative i ψ0))
      linarith
    have h2 : (volume U).toReal ^ ((1 : ℝ) / d) * (volume U).toReal ^ (-(1 : ℝ) / d) = 1 := by
      rw [← Real.rpow_add hV]
      ring_nf
      exact Real.rpow_zero _
    calc (PDE.eLpMeanNormOn U 2 ψ0).toReal
        = (volume U).toReal ^ ((1 : ℝ) / d) *
            ((volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 ψ0).toReal) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ (volume U).toReal ^ ((1 : ℝ) / d) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _
  calc (PDE.eLpMeanNormOn U 2 f).toReal * (PDE.eLpMeanNormOn U 2 ψ0).toReal
      ≤ (PDE.eLpMeanNormOn U 2 f).toReal * (volume U).toReal ^ ((1 : ℝ) / d) :=
        mul_le_mul_of_nonneg_left hpsi ENNReal.toReal_nonneg
    _ = _ := mul_comm _ _

/-- **Sobolev–Poincaré inequality for `H¹` on bounded convex domains**:
`‖u - (u)_U‖_{L̲^{s*}(U)} ≤ C D ‖∇u‖_{L̲²(U)}` for `s ∈ [1, 2]`, `s < d`. -/
theorem exists_sobolevPoincare_H1 (hd : 2 ≤ d) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Vec d)) (D : ℝ), IsOpen U → Bornology.IsBounded U →
      Convex ℝ U → U.Nonempty → (∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D) →
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), H1 U u G →
        PDE.eLpMeanNormOn U (ENNReal.ofReal (PDE.sobolevConjugate d s))
            (fun x => u x - PDE.integralAverage U u) ≤
          ENNReal.ofReal (C * D) * PDE.eLpMeanNormOn U 2 (fun x => euclideanNorm (G x)) := by
  obtain ⟨C1, hC1, hP⟩ := PDE.exists_convexSobolevPoincare_constant d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hγ : 0 < s * ((d : ℝ) - 1) / ((d : ℝ) - s) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  refine ⟨C1 * (s * ((d : ℝ) - 1) / ((d : ℝ) - s)), mul_pos hC1 hγ,
    fun U D hUo hUb hUc hne hD u G hu => ?_⟩
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hs2' : ENNReal.ofReal s ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hs2
  let w : PDE.W1pFunction U (ENNReal.ofReal s) :=
    { toFun := u
      grad := G
      memLp := hu.1.mono_exponent hs2'
      gradMemLp := fun i => (hu.2.1.eval i).mono_exponent hs2'
      hasWeakGradient := fun i φ h1 h2 h3 => (hu.2.2 i).2.2 φ ⟨h1, h2, h3⟩ }
  have h := hP s hs1 hsd U D (isOpenBoundedConvexDomain_of_isBounded hUo hUb hUc) hne hD w
  have : IsProbabilityMeasure (PDE.normalizedVolumeOn U) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (pos_iff_ne_zero.2 hU0)
      (lt_top_iff_ne_top.2 hUt)
  refine h.trans (mul_le_mul' le_rfl ?_)
  exact eLpNorm_le_eLpNorm_of_exponent_le hs2'

theorem support_euclideanNorm_gradient_subset {ψ : Vec d → ℝ} :
    Function.support (fun y => euclideanNorm (gradient ψ y)) ⊆ tsupport ψ := by
  intro y hy
  by_contra h
  apply hy
  change euclideanNorm (gradient ψ y) = 0
  have hg : gradient ψ y = 0 := by
    funext i
    simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ h]
  rw [hg]
  simp [euclideanNorm, euclideanSq, dot]

/-- **Morrey's inequality for the test functions of `U ⊆ B_r(z)`**, `p > d`:
`|ψ| ≤ 8 √d (1 - d/p)⁻¹ r ‖∇ψ‖_{L̲^p(U)}`. -/
theorem abs_le_of_isSpatialTest_of_subset_ball (hd : 0 < d) {p : ℝ} (hdp : (d : ℝ) < p)
    {U : Set (Vec d)} (hU0 : volume U ≠ 0) {z : Vec d} {r : ℝ} (hr : 0 < r)
    (hUB : U ⊆ ball z r) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (x : Vec d) :
    |ψ x| ≤ 8 * Real.sqrt d / (1 - d / p) * r *
      (PDE.eLpMeanNormOn U (ENNReal.ofReal p) (fun y => euclideanNorm (gradient ψ y))).toReal := by
  have hp0 : 0 < p := (Nat.cast_pos.2 hd).trans hdp
  have hc : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hdp
    linarith
  have hψB : IsSpatialTest (ball z r) ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hUB⟩
  refine (abs_le_of_isSpatialTest_ball hd hdp z hr hψB x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hBt := volume_ball_ne_top_of_pos z hr
  have hUt : volume U ≠ ⊤ := ne_top_of_le_ne_top hBt (measure_mono hUB)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have hFc : Continuous fun y => euclideanNorm (gradient ψ y) :=
    PDE.continuous_vecEuclideanNorm.comp (continuous_gradient_of_contDiff hψ1)
  have hFs : HasCompactSupport fun y => euclideanNorm (gradient ψ y) :=
    hψ.2.1.mono' support_euclideanNorm_gradient_subset
  have hFm : MemLp (fun y => euclideanNorm (gradient ψ y)) (ENNReal.ofReal p) volume :=
    hFc.memLp_of_hasCompactSupport hFs
  have hsU : Function.support (fun y => euclideanNorm (gradient ψ y)) ⊆ U :=
    support_euclideanNorm_gradient_subset.trans hψ.2.2
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hBt),
    PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hUt)]
  change ((volume (ball z r))⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
      eLpNorm (fun y => euclideanNorm (gradient ψ y)) (ENNReal.ofReal p)
        (volume.restrict (ball z r))).toReal ≤
    ((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
      eLpNorm (fun y => euclideanNorm (gradient ψ y)) (ENNReal.ofReal p)
        (volume.restrict U)).toReal
  rw [eLpNorm_restrict_eq_of_support_subset hFc.aestronglyMeasurable (hsU.trans hUB),
    eLpNorm_restrict_eq_of_support_subset hFc.aestronglyMeasurable hsU]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
    ENNReal.toReal_nonneg (ENNReal.inv_ne_top.2 hU0)) hFm.eLpNorm_lt_top.ne)
    (mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 (measure_mono hUB))
      ENNReal.toReal_nonneg) le_rfl)

/-- `‖∇ ∂_i φ‖_{L̲^p(U)} ≤ d ‖φ‖_{W̲^{2,p}(U)}` for a test function `φ`, `p ≥ 1`. -/
theorem toReal_eLpMeanNormOn_gradient_coordinateDerivative_le {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤) {p : ℝ≥0∞} (hp : 1 ≤ p) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) :
    (PDE.eLpMeanNormOn U p
        (fun y => euclideanNorm (gradient (coordinateDerivative i φ) y))).toReal ≤
      d * sobolevTwoTestNorm p U φ := by
  have hφi := isSpatialTest_coordinateDerivative hφ i
  have hfin : ∀ j, PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i φ)) ≠ ⊤ :=
    fun j => eLpMeanNormOn_ne_top_of_memLp hU0 hUt
      (((isSpatialTest_coordinateDerivative hφi j).1.continuous.memLp_of_hasCompactSupport
        (isSpatialTest_coordinateDerivative hφi j).2.1).restrict U)
  have h1 : PDE.eLpMeanNormOn U p
      (fun y => euclideanNorm (gradient (coordinateDerivative i φ) y)) ≤
      ∑ j, PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i φ)) :=
    eLpNorm_euclideanNorm_le_sum hp
      (continuous_gradient_of_contDiff (hφi.1.of_le (by exact_mod_cast le_top))).aestronglyMeasurable
  have h2 := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => hfin j) h1
  rw [ENNReal.toReal_sum fun j _ => hfin j] at h2
  refine h2.trans ?_
  calc ∑ j, (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i φ))).toReal
      ≤ ∑ _j : Fin d, sobolevTwoTestNorm p U φ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rcases le_or_gt i j with hij | hij
        · exact toReal_eLpMeanNormOn_second_le p U φ hij
        · rw [coordinateDerivative_comm_of_contDiff hφ.1 j i]
          exact toReal_eLpMeanNormOn_second_le p U φ hij.le
    _ = d * sobolevTwoTestNorm p U φ := by simp

end QSH
