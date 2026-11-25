import QuantitativeStochasticHomogenization.AppB.TheoremB8
import SobolevStatements.ConvexSobolevPoincare

/-!
# Theorem B.9: the local Sobolev–Poincaré inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix B, Theorem B.9 for `k = 1`: for `p ∈ [1, d)` there is `C(p, d)` such that, for every
`r > 0` and `v ∈ W^{1,p}(B_r)`,
`inf_{w ∈ ℝ} ‖v - w‖_{L̲^{dp/(d-p)}(B_r)} ≤ C r ‖∇v‖_{L̲^p(B_r)}` (B.7), and the infimum may be
replaced by `w = 0` when `v ∈ W^{1,p}_0(B_r)`. The norms are the volume-normalized norms
`‖f‖_{L̲^q(U)} = (⨍_U |f|^q)^{1/q}` of the book, so that both sides scale in the same way; the
balls `B_r(z)` may have any center.

The first part is the Sobolev–Poincaré inequality on bounded convex domains of the elliptic
regularity library, `PDE.exists_convexSobolevPoincare_constant`, with `w = (v)_{B_r}`; the second
is the zero-boundary Gagliardo–Nirenberg–Sobolev inequality of `PDE.exists_sobolev_constant`,
rescaled with `|B_r(z)| ≤ (2r)^d` (Evans, Section 5.6.1; Gilbarg–Trudinger, Theorem 7.10).
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem ball_eq_PDE_euclideanBall (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ball z r = PDE.euclideanBall z r := by
  ext x
  simp only [ball, PDE.euclideanBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot,
    euclideanNorm, euclideanSq, dot, Set.mem_ofPred_eq]
  exact Real.sqrt_lt' hr

theorem isOpenBoundedConvexDomain_ball_of_pos (z : Vec d) {r : ℝ} (hr : 0 < r) :
    PDE.IsOpenBoundedConvexDomain (ball z r) := by
  rw [ball_eq_PDE_euclideanBall z hr]
  exact PDE.isOpenBoundedConvexDomain_euclideanBall z hr

theorem volume_ball_pos_of_pos (z : Vec d) {r : ℝ} (hr : 0 < r) : 0 < volume (ball z r) := by
  rw [ball_eq_PDE_euclideanBall z hr]
  exact PDE.volume_euclideanBall_pos z hr

theorem volume_ball_le (z : Vec d) {r : ℝ} (hr : 0 < r) :
    volume (ball z r) ≤ ENNReal.ofReal ((2 * r) ^ d) := by
  rw [ball_eq_PDE_euclideanBall z hr]
  calc volume (PDE.euclideanBall z r) ≤ volume (Metric.ball z r) :=
        measure_mono (PDE.euclideanBall_subset_supBall hr)
    _ = ENNReal.ofReal ((2 * r) ^ d) := by rw [Real.volume_pi_ball z hr, Fintype.card_fin]

theorem volume_ball_ne_top_of_pos (z : Vec d) {r : ℝ} (hr : 0 < r) : volume (ball z r) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_ball_le z hr)

/-- `|B_r(z)|^{1/d} ≤ 2 r`. -/
theorem volume_ball_rpow_le (hd : 0 < d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    volume (ball z r) ^ (1 / (d : ℝ)) ≤ ENNReal.ofReal (2 * r) := by
  calc volume (ball z r) ^ (1 / (d : ℝ)) ≤ ENNReal.ofReal ((2 * r) ^ d) ^ (1 / (d : ℝ)) :=
        ENNReal.rpow_le_rpow (volume_ball_le z hr) (by positivity)
    _ = ENNReal.ofReal (2 * r) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          Real.pow_rpow_inv_natCast (by positivity) hd.ne']

theorem one_div_toReal_ofReal {q : ℝ} (hq : 0 < q) : (1 / ENNReal.ofReal q).toReal = 1 / q := by
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hq.le]

/-- Passing from the unnormalized to the normalized norms: if `‖f‖_{L^q(U)} ≤ K ‖h‖_{L^p(U)}`
and `1/q = 1/p - s`, then `‖f‖_{L̲^q(U)} ≤ K |U|^s ‖h‖_{L̲^p(U)}`. -/
theorem eLpMeanNormOn_le_of_eLpNorm_le {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 / q = 1 / p - s)
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : Vec d → E} {h : Vec d → F}
    {K : ℝ≥0∞}
    (hfh : eLpNorm f (ENNReal.ofReal q) (volume.restrict U) ≤
      K * eLpNorm h (ENNReal.ofReal p) (volume.restrict U)) :
    PDE.eLpMeanNormOn U (ENNReal.ofReal q) f ≤
      K * volume U ^ s * PDE.eLpMeanNormOn U (ENNReal.ofReal p) h := by
  have hUlt : volume U < ⊤ := lt_top_iff_ne_top.2 hUt
  rw [PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUlt,
    PDE.eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUlt, one_div_toReal_ofReal hq,
    one_div_toReal_ofReal hp, hpq]
  have hV : (volume U)⁻¹ ^ (1 / p - s) = (volume U)⁻¹ ^ (1 / p) * volume U ^ s := by
    rw [ENNReal.rpow_sub _ _ (ENNReal.inv_ne_zero.2 hUt) (ENNReal.inv_ne_top.2 hU0),
      ENNReal.inv_rpow (volume U) s, div_eq_mul_inv, inv_inv]
  rw [hV]
  calc (volume U)⁻¹ ^ (1 / p) * volume U ^ s * PDE.eLpNormOn U (ENNReal.ofReal q) f
      ≤ (volume U)⁻¹ ^ (1 / p) * volume U ^ s *
          (K * PDE.eLpNormOn U (ENNReal.ofReal p) h) := by
        gcongr
        exact hfh
    _ = K * volume U ^ s * ((volume U)⁻¹ ^ (1 / p) * PDE.eLpNormOn U (ENNReal.ofReal p) h) := by
        ring

/-- Passing from the normalized to the unnormalized norms: if `‖f‖_{L̲^q(U)} ≤ K ‖h‖_{L̲^p(U)}`
and `1/q = 1/p - s`, then `‖f‖_{L^q(U)} ≤ K |U|^{-s} ‖h‖_{L^p(U)}`. -/
theorem eLpNorm_le_of_eLpMeanNormOn_le {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hUt : volume U ≠ ⊤) {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 / q = 1 / p - s)
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : Vec d → E} {h : Vec d → F}
    {K : ℝ≥0∞}
    (hfh : PDE.eLpMeanNormOn U (ENNReal.ofReal q) f ≤
      K * PDE.eLpMeanNormOn U (ENNReal.ofReal p) h) :
    eLpNorm f (ENNReal.ofReal q) (volume.restrict U) ≤
      K * volume U ^ (-s) * eLpNorm h (ENNReal.ofReal p) (volume.restrict U) := by
  have hUlt : volume U < ⊤ := lt_top_iff_ne_top.2 hUt
  have hUpos : 0 < volume U := pos_iff_ne_zero.2 hU0
  change PDE.eLpNormOn U (ENNReal.ofReal q) f ≤
    K * volume U ^ (-s) * PDE.eLpNormOn U (ENNReal.ofReal p) h
  rw [PDE.eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hUpos hUlt,
    PDE.eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hUpos hUlt, one_div_toReal_ofReal hq,
    one_div_toReal_ofReal hp, hpq]
  have hV : volume U ^ (1 / p - s) = volume U ^ (1 / p) * volume U ^ (-s) := by
    rw [sub_eq_add_neg, ENNReal.rpow_add _ _ hU0 hUt]
  rw [hV]
  calc volume U ^ (1 / p) * volume U ^ (-s) * PDE.eLpMeanNormOn U (ENNReal.ofReal q) f
      ≤ volume U ^ (1 / p) * volume U ^ (-s) *
          (K * PDE.eLpMeanNormOn U (ENNReal.ofReal p) h) := by
        gcongr
    _ = K * volume U ^ (-s) * (volume U ^ (1 / p) * PDE.eLpMeanNormOn U (ENNReal.ofReal p) h) := by
        ring

theorem one_div_sobolevConjugate {p : ℝ} (hp : 0 < p) (hpd : p < d) :
    1 / PDE.sobolevConjugate d p = 1 / p - 1 / d := by
  have hd0 : (0 : ℝ) < d := hp.trans hpd
  rw [PDE.sobolevConjugate]
  field_simp

/-- **Theorem B.9** (local Sobolev–Poincaré inequality), `k = 1`: for `p ∈ [1, d)` there is
`C(p, d)` such that for every ball `B_r(z)` and `v ∈ W^{1,p}(B_r(z))`,
`inf_{w ∈ ℝ} ‖v - w‖_{L̲^{dp/(d-p)}(B_r(z))} ≤ C r ‖∇v‖_{L̲^p(B_r(z))}` (B.7), and
`‖v‖_{L̲^{dp/(d-p)}(B_r(z))} ≤ C r ‖∇v‖_{L̲^p(B_r(z))}` if `v ∈ W^{1,p}_0(B_r(z))`. -/
theorem theorem_B_9_one (p : ℝ) (hp : 1 ≤ p) (hpd : p < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (v : Vec d → ℝ) (g : Vec d → Vec d),
      (IsW1p (ball z r) (ENNReal.ofReal p) v g →
        ⨅ w : ℝ, PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal (d * p / (d - p)))
            (fun x => v x - w) ≤
          ENNReal.ofReal (C * r) *
            PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x))) ∧
      (IsW01p (ball z r) (ENNReal.ofReal p) v g →
        PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal (d * p / (d - p))) v ≤
          ENNReal.ofReal (C * r) *
            PDE.eLpMeanNormOn (ball z r) (ENNReal.ofReal p) (fun x => euclideanNorm (g x))) := by
  have hd : 2 ≤ d := by
    have : 1 < d := by exact_mod_cast (show (1 : ℝ) < d by linarith)
    omega
  have hp0 : 0 < p := by linarith
  obtain ⟨C1, hC1, hP⟩ := PDE.exists_convexSobolevPoincare_constant d hd
  obtain ⟨C2, hC2, hS⟩ := PDE.exists_sobolev_constant d hd
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = p * ((d : ℝ) - 1) / ((d : ℝ) - p) := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    rw [hγdef]
    exact div_pos (mul_pos hp0 (by linarith)) (by linarith)
  refine ⟨2 * C1 * γ + 2 * C2 * γ, by positivity, fun z r hr v g => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · have hs := hP p hp hpd (ball z r) (2 * r) (isOpenBoundedConvexDomain_ball_of_pos z hr)
      (by rw [ball_eq_PDE_euclideanBall z hr]; exact PDE.euclideanBall_nonempty z hr)
      (by rw [ball_eq_PDE_euclideanBall z hr]; exact PDE.hasEuclideanDiameterLE_euclideanBall z hr)
      hv.toW1pFunction
    rw [← hγdef] at hs
    refine (iInf_le _ (PDE.integralAverage (ball z r) v)).trans (hs.trans ?_)
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    nlinarith [mul_pos hC2 hγ]
  · have hz := (hS p hp hpd).2 (ball z r) (isOpenBoundedConvexDomain_ball_of_pos z hr).1
      hv.1.toW1pFunction hv.hasSupportedSmoothApproximation
    rw [← hγdef] at hz
    have h1 := eLpMeanNormOn_le_of_eLpNorm_le (U := ball z r) (volume_ball_pos_of_pos z hr).ne'
      (volume_ball_ne_top_of_pos z hr) hp0 (PDE.sobolevConjugate_pos hp0 hpd)
      (one_div_sobolevConjugate hp0 hpd) hz
    refine h1.trans (mul_le_mul' ?_ le_rfl)
    calc ENNReal.ofReal (C2 * γ) * volume (ball z r) ^ (1 / (d : ℝ))
        ≤ ENNReal.ofReal (C2 * γ) * ENNReal.ofReal (2 * r) :=
          mul_le_mul' le_rfl (volume_ball_rpow_le (by omega) z hr)
      _ = ENNReal.ofReal (C2 * γ * (2 * r)) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ((2 * C1 * γ + 2 * C2 * γ) * r) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hC1 hγ])

end QSH
