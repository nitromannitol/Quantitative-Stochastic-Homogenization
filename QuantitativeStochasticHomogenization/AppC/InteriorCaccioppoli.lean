import QuantitativeStochasticHomogenization.AppC.NegativeSobolevPairing
import QuantitativeStochasticHomogenization.Ch04.Sec04.BallCaccioppoli
import PDEFoundation.PDE.DGNM.Caccioppoli
import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
import PDEFoundation.Sobolev.H1.Product
import PDEFoundation.Sobolev.Cutoff.Ball
import PDEFoundation.Measure.BallVolume

/-!
# The interior Caccioppoli inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.2: if `h ∈ H^{-1}(B_r)` and `u ∈ H¹(B_r)` solve `-∇·(a∇u) = h` in `B_r`, then
`‖∇u‖_{L̲²(B_{r/2})} ≤ C (r^{-1} ‖u - (u)_{B_r}‖_{L̲²(B_r)} + ‖h‖_{H̲^{-1}(B_r)})` with `C(d, Λ)`.

The right-hand side is `h = f + ∇·F` with `f ∈ L²(B_r)`, `F ∈ L²(B_r; ℝ^d)` (every element of
`H^{-1}(B_r)` has this form), the equation is `∇·(a∇u + F) = -f` weakly, and `‖h‖_{H̲^{-1}(B_r)}` is
`negativeSobolevOneNorm 2`. The proof is the book's: test the equation with `φ² (u - (u)_{B_r})`
for a cutoff `φ` of `B_{r/2}` in `B_r` with `|∇φ| ≤ 64/r`, bound the cross term by Young's
inequality, the pairing with `h` by `‖h‖_{H̲^{-1}} ‖φ² (u - (u)_{B_r})‖_{H̲¹}`
(`abs_integral_pairing_le_of_h10`), and absorb. The theorem is stated for balls with an arbitrary
center; `lemma_C_2` is the book's case of the centered ball `B_r`.
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The weak equation `∇·(a∇u + F) = -f` of a coefficient field is the elliptic library's weak
formulation of `-∇·(a∇u) = f + ∇·F` for the measurable elliptic representative of `a`. -/
theorem isWeakDivergenceFormSolutionOn_toH1FunctionOn {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : MeasurableSet U) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) (hw : HasWeakGradient U u g)
    {f : Vec d → ℝ} {F : Vec d → Vec d} (hf : MemLp f 2 (volume.restrict U))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hdiv : HasWeakDivergence U (fun x => (a x).mulVec (g x) + F x) (fun x => -f x)) :
    PDE.IsWeakDivergenceFormSolutionOn (ellipticFieldOf a) U (toH1FunctionOn hu hg hw) f F := by
  intro φ
  have hdata : PDE.DivergenceFormL2DataOn (ellipticFieldOf a) U (toH1FunctionOn hu hg hw) f F :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn (isEllipticFieldOn_ellipticFieldOf hΛ a hU)
      hf hF
  have ht := hdata.testable φ
  refine ⟨ht, ?_⟩
  have htest : IsSpatialTest U φ.toFun := ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  have h := hdiv.2.2 φ.toFun htest
  have hae : (fun x => PDE.vecDot (PDE.matVecMul (ellipticFieldOf a x)
      ((toH1FunctionOn hu hg hw).grad x)) (φ.grad x)) =ᵐ[volume.restrict U]
      fun x => dot ((a x).mulVec (g x)) (gradient φ.toFun x) := by
    filter_upwards [ae_restrict_of_ae (ellipticFieldOf_ae_eq hΛ a)] with x hx
    change dot ((ellipticFieldOf a x).mulVec (g x)) (gradient φ.toFun x) = _
    rw [hx]
  have i1 : Integrable (fun x => dot ((a x).mulVec (g x)) (gradient φ.toFun x))
      (volume.restrict U) := (integrable_congr hae).mp ht.flux_integrable
  have i2 : Integrable (fun x => dot (F x) (gradient φ.toFun x)) (volume.restrict U) :=
    ht.forcing_integrable
  have hsplit : ∫ x in U, dot ((a x).mulVec (g x) + F x) (gradient φ.toFun x) =
      (∫ x in U, dot ((a x).mulVec (g x)) (gradient φ.toFun x)) +
        ∫ x in U, dot (F x) (gradient φ.toFun x) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hneg : ∫ x in U, (-f x) * φ.toFun x = -∫ x in U, f x * φ.toFun x := by
    rw [← integral_neg]
    simp only [neg_mul]
  rw [integral_congr_ae hae]
  change _ = (∫ x in U, f x * φ.toFun x) - ∫ x in U, dot (F x) (gradient φ.toFun x)
  rw [hsplit, hneg, neg_neg] at h
  linarith

/-- A normalized `L²` norm dominated in square by an integrable function:
`‖ψ‖_{L̲²(U)} ≤ (⨍_U G)^{1/2}` when `ψ² ≤ G` on `U`. -/
theorem eLpMeanNormOn_two_le_ofReal_sqrt {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    {ψ G : Vec d → ℝ} (hψ : AEStronglyMeasurable ψ (volume.restrict U)) (hG : IntegrableOn G U)
    (hle : ∀ᵐ x ∂(volume.restrict U), ψ x ^ 2 ≤ G x) :
    PDE.eLpMeanNormOn U 2 ψ ≤ ENNReal.ofReal (Real.sqrt (⨍ x in U, G x ∂volume)) := by
  set μ := PDE.normalizedVolumeOn U with hμ
  have hac : μ ≪ volume.restrict U := Measure.smul_absolutelyContinuous
  have hGμ : Integrable G μ :=
    PDE.integrable_normalizedVolumeOn_of_integrableOn hG (pos_iff_ne_zero.mpr hU0)
  have hψμ : AEStronglyMeasurable ψ μ := hψ.mono_ac hac
  have hleμ : ∀ᵐ x ∂μ, ψ x ^ 2 ≤ G x := hac.ae_le hle
  have hsqμ : Integrable (fun x => ψ x ^ 2) μ :=
    hGμ.mono' (hψμ.pow 2) (hleμ.mono fun x hx => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hx)
  have hmem : MemLp ψ 2 μ := (memLp_two_iff_integrable_sq hψμ).2 hsqμ
  have havg : ⨍ x in U, G x ∂volume = ∫ x, G x ∂μ := by
    rw [hμ, PDE.integral_normalizedVolumeOn_eq_integralAverage, PDE.integralAverage,
      setAverage_eq, smul_eq_mul, measureReal_def]
  rw [PDE.eLpMeanNormOn, ← hμ, hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero
    ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnorm : (fun x => ‖ψ x‖ ^ (ENNReal.toReal 2)) = fun x => ψ x ^ 2 := by
    funext x
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [havg, Real.sqrt_eq_rpow, hnorm, ENNReal.toReal_ofNat, ← one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x => sq_nonneg _)
    (integral_mono_ae hsqμ hGμ hleμ) (by norm_num)

theorem sq_apply_le_vecNormSq (v : Vec d) (i : Fin d) : v i ^ 2 ≤ PDE.vecNormSq v := by
  unfold PDE.vecNormSq PDE.vecDot
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

/-- The test function `φ (φ (u - c)) ∈ H¹₀(U)` of the Caccioppoli inequality and its gradient. -/
theorem exists_h10_cutoff_sq_test {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (u : PDE.H1Function U) (c : ℝ) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ v : PDE.H10Function U, (∀ x, v.toH1Function x = φ x * (φ x * (u x - c))) ∧
      ∀ x, v.toH1Function.grad x = φ x • (φ x • u.grad x + (u x - c) •
        PDE.classicalGradient φ x) + (φ x * (u x - c)) • PDE.classicalGradient φ x := by
  refine ⟨((u.subConst hU c).mulContDiffHasCompactSupport hφ hφc).mulContDiffHasCompactSupportToH10
    hU hφ hφc hφU, fun x => ?_, fun x => ?_⟩
  · simp only [PDE.H1Function.mulContDiffHasCompactSupportToH10_toH1Function,
      PDE.H1Function.mulContDiffHasCompactSupport_toFun]
    rw [PDE.H1Function.subConst_apply]
  · simp only [PDE.H1Function.mulContDiffHasCompactSupportToH10_toH1Function,
      PDE.H1Function.mulContDiffHasCompactSupport_grad,
      PDE.H1Function.mulContDiffHasCompactSupport_toFun, PDE.H1Function.grad_subConst]
    rw [PDE.H1Function.subConst_apply]

/-- The arithmetic of the absorption in the proof of Lemma C.2. -/
theorem caccioppoli_absorb {xx y H Y K c₁ r Λ D j T : ℝ} (hr : 0 < r)
    (hH : 0 ≤ H) (hY : 0 ≤ Y) (hc₁ : 0 ≤ c₁) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hK : K = 64 / r)
    (hy : y = r * Y) (hmain : xx ^ 2 / 2 - 2 * Λ * j ≤ H * T) (hj : j ≤ K ^ 2 * y ^ 2)
    (hT : T ≤ c₁ / r * y + D * (xx + 2 * K * y)) :
    xx ^ 2 ≤ 2 * (2 * c₁ + 256 * D + 2 * D ^ 2 + 16384 * Λ) * (H + Y) ^ 2 := by
  have hKy : K * y = 64 * Y := by rw [hK, hy]; field_simp
  have hcy : c₁ / r * y = c₁ * Y := by rw [hy]; field_simp
  have hK2 : K ^ 2 * y ^ 2 = 4096 * Y ^ 2 := by
    rw [show K ^ 2 * y ^ 2 = (K * y) ^ 2 by ring, hKy]
    ring
  have hHT := mul_le_mul_of_nonneg_left hT hH
  have e1 : H * (c₁ / r * y + D * (xx + 2 * K * y)) =
      c₁ * (H * Y) + D * H * xx + 128 * D * (H * Y) := by
    rw [hcy, show D * (xx + 2 * K * y) = D * xx + 2 * D * (K * y) by ring, hKy]
    ring
  rw [e1] at hHT
  have h4 := mul_le_mul_of_nonneg_left hj (by linarith : (0 : ℝ) ≤ 2 * Λ)
  rw [hK2] at h4
  have hyoung : D * H * xx ≤ xx ^ 2 / 4 + D ^ 2 * H ^ 2 := by
    nlinarith [sq_nonneg (xx / 2 - D * H)]
  have hHY : 0 ≤ H * Y := mul_nonneg hH hY
  have hb1 : H * Y ≤ (H + Y) ^ 2 := by nlinarith
  have hb2 : H ^ 2 ≤ (H + Y) ^ 2 := by nlinarith
  have hb3 : Y ^ 2 ≤ (H + Y) ^ 2 := by nlinarith
  have i1 := mul_le_mul_of_nonneg_left hb1 (by positivity : (0 : ℝ) ≤ c₁ + 128 * D)
  have i2 := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ D ^ 2)
  have i3 := mul_le_mul_of_nonneg_left hb3 (by positivity : (0 : ℝ) ≤ 8192 * Λ)
  nlinarith

/-- **Lemma C.2 (interior Caccioppoli inequality)** on a ball `B_r(z)`: for `u ∈ H¹(B_r(z))`
solving `-∇·(a∇u) = h` with `h = f + ∇·F ∈ H^{-1}(B_r(z))`,
`‖∇u‖_{L̲²(B_{r/2}(z))} ≤ C (r^{-1} ‖u - (u)_{B_r(z)}‖_{L̲²(B_r(z))} + ‖h‖_{H̲^{-1}(B_r(z))})`,
with `C` depending only on `d` and `Λ`. -/
theorem interiorCaccioppoli {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball z r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball z r))) →
      HasWeakGradient (ball z r) u g →
      MemLp f 2 (volume.restrict (ball z r)) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball z r))) →
      HasWeakDivergence (ball z r) (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      ENNReal.ofReal (vectorRms volume (ball z (r / 2)) g) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r⁻¹ * scalarRms volume (ball z r)
            (fun x => u x - ⨍ y in ball z r, u y ∂volume)) +
          negativeSobolevOneNorm 2 (ball z r) f F) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine ⟨1, one_pos, fun z r _ a u g f F _ _ _ _ _ _ => ?_⟩
    have h0 : vectorRms volume (ball z (r / 2)) g = 0 := by
      simp [vectorRms, euclideanSq, dot]
    rw [h0, ENNReal.ofReal_zero]
    exact bot_le
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ PDE.volume_euclideanBall_toReal_pos 0 one_pos
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁, c₁ = ω ^ (-(1 : ℝ) / d) := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := hc₁def ▸ Real.rpow_nonneg hω.le _
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 * c₁ + 256 * d + 2 * d ^ 2 + 16384 * Λ := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  have hCpos : 0 < Real.sqrt (2 ^ d * (2 * M)) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt (2 ^ d * (2 * M)), hCpos, ?_⟩
  intro z r hr a u g f F hu hg hw hf hF hdiv
  have hr2 : 0 < r / 2 := by linarith
  have hUe : ball z r = PDE.euclideanBall z r := ball_eq_euclideanBall z hr
  have hU2e : ball z (r / 2) = PDE.euclideanBall z (r / 2) := ball_eq_euclideanBall z hr2
  have hUconv : PDE.IsOpenBoundedConvexDomain (ball z r) := by
    rw [hUe]
    exact PDE.isOpenBoundedConvexDomain_euclideanBall z hr
  have hUm : MeasurableSet (ball z r) := measurableSet_ball z r
  have hUvol : (volume (ball z r)).toReal = r ^ d * ω := by
    rw [hUe, hωdef]
    exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos z hr
  have hU2vol : (volume (ball z (r / 2))).toReal = (r / 2) ^ d * ω := by
    rw [hU2e, hωdef]
    exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos z hr2
  have hUfin : volume (ball z r) ≠ ⊤ := by
    rw [hUe]
    exact PDE.volume_euclideanBall_ne_top z hr.le
  have hU0 : volume (ball z r) ≠ 0 := by
    rw [hUe]
    exact (PDE.volume_euclideanBall_pos z hr).ne'
  have : IsFiniteMeasure (volume.restrict (ball z r)) := isFiniteMeasure_restrict.mpr hUfin
  have hUreal : volume.real (ball z r) = r ^ d * ω := by rw [measureReal_def, hUvol]
  have hUpos : 0 < volume.real (ball z r) := by rw [hUreal]; positivity
  have hρ : (volume (ball z r)).toReal ^ (-(1 : ℝ) / d) = c₁ / r := by
    rw [hUvol, Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have e : (d : ℝ) * (-(1 : ℝ) / d) = -1 := by field_simp
    rw [e, Real.rpow_neg_one, hc₁def]
    ring
  by_cases hHtop : negativeSobolevOneNorm 2 (ball z r) f F = ⊤
  · rw [hHtop, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCpos).ne']
    exact le_top
  obtain ⟨H, hHdef⟩ : ∃ H, H = (negativeSobolevOneNorm 2 (ball z r) f F).toReal := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := hHdef ▸ ENNReal.toReal_nonneg
  have hHeq : negativeSobolevOneNorm 2 (ball z r) f F = ENNReal.ofReal H := by
    rw [hHdef, ENNReal.ofReal_toReal hHtop]
  -- the elliptic library's objects
  obtain ⟨A, hAdef⟩ : ∃ A, A = ellipticFieldOf a := ⟨_, rfl⟩
  have hEll : PDE.IsEllipticFieldOn 1 Λ (ball z r) A :=
    hAdef ▸ isEllipticFieldOn_ellipticFieldOf hΛ a hUm
  have hAx : ∀ x, PDE.IsEllipticMatrix 1 Λ (A x) :=
    hAdef ▸ isEllipticMatrix_ellipticFieldOf hΛ a
  obtain ⟨u₁, hu₁f, hu₁g, hsol⟩ : ∃ u₁ : PDE.H1Function (ball z r), (∀ x, u₁ x = u x) ∧
      (∀ x, u₁.grad x = g x) ∧ PDE.IsWeakDivergenceFormSolutionOn A (ball z r) u₁ f F :=
    ⟨toH1FunctionOn hu hg hw, fun _ => rfl, fun _ => rfl,
      hAdef ▸ isWeakDivergenceFormSolutionOn_toH1FunctionOn hΛ a hUm hu hg hw hf hF hdiv⟩
  have hsol10 := hsol.toH10SolutionOn_of_isEllipticFieldOn hEll hf hF
  obtain ⟨c, hcdef⟩ : ∃ c, c = ⨍ y in ball z r, u y ∂volume := ⟨_, rfl⟩
  have φ : PDE.QuantitativeSmoothCutoff (ball z (r / 2)) (ball z r) (64 / r) := by
    have h := PDE.quantitativeBallCutoff z hr2.le (show r / 2 < r by linarith)
    rw [← hU2e, ← hUe, show 32 / (r - r / 2) = 64 / r by field_simp; norm_num] at h
    exact h
  obtain ⟨K, hK⟩ : ∃ K, K = 64 / r := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨gφ, hgφ⟩ : ∃ gφ : Vec d → Vec d, gφ = fun x => PDE.classicalGradient φ.toFun x :=
    ⟨_, rfl⟩
  have hgφ_cont : Continuous gφ := by
    rw [hgφ]
    refine continuous_pi fun i => ?_
    exact (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgφ_bound : ∀ x, PDE.vecNormSq (gφ x) ≤ K ^ 2 := by
    intro x
    have h1 := φ.gradient_bound x
    have h2 : PDE.vecEuclideanNorm (gφ x) ^ 2 = PDE.vecNormSq (gφ x) :=
      Real.sq_sqrt (PDE.vecNormSq_nonneg _)
    rw [← h2, hK]
    rw [hgφ]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hφ0 : ∀ x, 0 ≤ φ x := φ.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := φ.le_one
  have hφcont : Continuous φ.toFun := φ.smooth.continuous
  obtain ⟨v, hvfun, hvgrad⟩ := exists_h10_cutoff_sq_test hUconv u₁ c φ.smooth
    φ.hasCompactSupport φ.tsupport_subset
  simp only [hu₁f, hu₁g, ← hgφ] at hvfun hvgrad
  -- the tested equation and the pairing bound
  have hid := (hsol10 v).2
  have hpair := abs_integral_pairing_le_of_h10 hUfin hf hF hH0 hHeq.le v
  obtain ⟨E, hEdef⟩ : ∃ E : Vec d → ℝ, E = fun x => PDE.vecDot (g x) (PDE.matVecMul (A x) (g x)) :=
    ⟨_, rfl⟩
  have hEge : ∀ x, PDE.vecNormSq (g x) ≤ E x := by
    intro x
    have h1 := (hAx x).2.2.1 (g x)
    rw [one_mul] at h1
    rw [hEdef]
    exact h1
  have hE0 : ∀ x, 0 ≤ E x := fun x => (PDE.vecNormSq_nonneg _).trans (hEge x)
  have hpt : ∀ x, PDE.vecDot (PDE.matVecMul (A x) (u₁.grad x)) (v.toH1Function.grad x) =
      φ x ^ 2 * E x + 2 * φ x * (u x - c) * PDE.vecDot (PDE.matVecMul (A x) (g x)) (gφ x) := by
    intro x
    rw [hvgrad x, hu₁g x, hEdef]
    simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hyoung : ∀ x, -(φ x ^ 2 * E x / 2 + 2 * Λ * ((u x - c) ^ 2 * PDE.vecNormSq (gφ x))) ≤
      2 * φ x * (u x - c) * PDE.vecDot (PDE.matVecMul (A x) (g x)) (gφ x) := by
    intro x
    have h := PDE.DGNM.abs_two_mul_mul_vecDot_le_caccioppoli (η := φ x) (w := u x - c) (hAx x)
      (g x) (gφ x)
    have h' := neg_abs_le (2 * φ x * (u x - c) * PDE.vecDot (PDE.matVecMul (A x) (g x)) (gφ x))
    have e : φ x ^ 2 * PDE.vecDot (g x) (PDE.matVecMul (A x) (g x)) / 2 +
        2 * Λ * (u x - c) ^ 2 * PDE.vecNormSq (gφ x) =
        φ x ^ 2 * E x / 2 + 2 * Λ * ((u x - c) ^ 2 * PDE.vecNormSq (gφ x)) := by
      rw [hEdef]
      ring
    rw [e] at h
    linarith
  -- integrability
  have hg' : PDE.MemVectorL2On (ball z r) g := hg
  have hE_int : IntegrableOn E (ball z r) := by
    rw [hEdef]
    exact PDE.integrableOn_vecDot_of_memVectorL2On hg'
      (PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hg')
  have hφ2E_int : IntegrableOn (fun x => φ x ^ 2 * E x) (ball z r) := by
    refine hE_int.bdd_mul (c := 1) (hφcont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hφ0 x) (hφ1 x)
  have hwm : MemLp (fun x => u x - c) 2 (volume.restrict (ball z r)) := hu.sub (memLp_const c)
  have hw_int : IntegrableOn (fun x => (u x - c) ^ 2) (ball z r) := hwm.integrable_sq
  have hN_cont : Continuous fun x => PDE.vecNormSq (gφ x) := by
    unfold PDE.vecNormSq PDE.vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hgφ_cont).mul ((continuous_apply i).comp hgφ_cont)
  have hJ_int : IntegrableOn (fun x => (u x - c) ^ 2 * PDE.vecNormSq (gφ x)) (ball z r) := by
    have h := hw_int.bdd_mul (c := K ^ 2) hN_cont.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (PDE.vecNormSq_nonneg _)]
        exact hgφ_bound x)
    exact h.congr (Eventually.of_forall fun x => mul_comm _ _)
  have htot_int := (hsol10 v).1.flux_integrable
  -- the energy inequality
  have hlow : ∫ x in ball z r, (φ x ^ 2 * E x / 2 -
      2 * Λ * ((u x - c) ^ 2 * PDE.vecNormSq (gφ x))) ≤
      ∫ x in ball z r, PDE.vecDot (PDE.matVecMul (A x) (u₁.grad x)) (v.toH1Function.grad x) := by
    refine integral_mono ((hφ2E_int.div_const 2).sub (hJ_int.const_mul _)) htot_int
      fun x => ?_
    rw [hpt x]
    have := hyoung x
    linarith
  rw [integral_sub (hφ2E_int.div_const 2) (hJ_int.const_mul _), integral_div,
    integral_const_mul, hid] at hlow
  obtain ⟨I, hIdef⟩ : ∃ I, I = ∫ x in ball z r, φ x ^ 2 * E x := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J, J = ∫ x in ball z r, (u x - c) ^ 2 * PDE.vecNormSq (gφ x) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = ∫ x in ball z r, (u x - c) ^ 2 := ⟨_, rfl⟩
  rw [← hIdef, ← hJdef] at hlow
  have hIJ : I / 2 - 2 * Λ * J ≤ volume.real (ball z r) * (H * h10TestNorm (ball z r) v) :=
    hlow.trans ((le_abs_self _).trans hpair)
  have hJW : J ≤ K ^ 2 * W := by
    rw [hJdef, hWdef, ← integral_const_mul]
    refine integral_mono hJ_int (hw_int.const_mul _) fun x => ?_
    have h1 := hgφ_bound x
    have h2 := sq_nonneg (u x - c)
    change (u x - c) ^ 2 * PDE.vecNormSq (gφ x) ≤ K ^ 2 * (u x - c) ^ 2
    calc (u x - c) ^ 2 * PDE.vecNormSq (gφ x) ≤ (u x - c) ^ 2 * K ^ 2 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = K ^ 2 * (u x - c) ^ 2 := mul_comm _ _
  have hI0 : 0 ≤ I := hIdef ▸ integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hE0 x)
  have hW0 : 0 ≤ W := hWdef ▸ integral_nonneg fun x => sq_nonneg _
  -- normalized quantities
  obtain ⟨y, hydef⟩ : ∃ y, y = scalarRms volume (ball z r) (fun x => u x - c) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := hydef ▸ Real.sqrt_nonneg _
  have hy2 : y ^ 2 = (volume.real (ball z r))⁻¹ * W := by
    rw [hydef, scalarRms, Real.sq_sqrt, setAverage_eq, smul_eq_mul, hWdef]
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (hWdef ▸ hW0)
  obtain ⟨xx, hxxdef⟩ : ∃ xx, xx = Real.sqrt ((volume.real (ball z r))⁻¹ * I) := ⟨_, rfl⟩
  have hxx0 : 0 ≤ xx := hxxdef ▸ Real.sqrt_nonneg _
  have hxx2 : xx ^ 2 = (volume.real (ball z r))⁻¹ * I := by
    rw [hxxdef]
    exact Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr measureReal_nonneg) hI0)
  have hvmeas : AEStronglyMeasurable (fun x => v.toH1Function x) (volume.restrict (ball z r)) :=
    v.toH1Function.memL2.aestronglyMeasurable
  -- the H¹ norm of the test
  have hT0 : (PDE.eLpMeanNormOn (ball z r) 2 v.toH1Function.toFun).toReal ≤ y := by
    have hpt0 : ∀ x, (v.toH1Function x) ^ 2 ≤ (u x - c) ^ 2 := by
      intro x
      rw [hvfun x, show φ x * (φ x * (u x - c)) = (φ x * φ x) * (u x - c) by ring, mul_pow]
      have h2 : (φ x * φ x) ^ 2 ≤ 1 :=
        pow_le_one₀ (mul_nonneg (hφ0 x) (hφ0 x)) ((mul_le_of_le_one_left (hφ0 x) (hφ1 x)).trans (hφ1 x))
      exact mul_le_of_le_one_left (sq_nonneg _) h2
    have h := eLpMeanNormOn_two_le_ofReal_sqrt hU0 hvmeas hw_int (Eventually.of_forall hpt0)
    rw [show Real.sqrt (⨍ x in ball z r, (u x - c) ^ 2 ∂volume) = y from hydef.symm] at h
    exact ENNReal.toReal_le_of_le_ofReal hy0 h
  have hTi : ∀ i : Fin d,
      (PDE.eLpMeanNormOn (ball z r) 2 (fun x => v.toH1Function.grad x i)).toReal ≤
        xx + 2 * K * y := by
    intro i
    have hsplit : (fun x => v.toH1Function.grad x i) =
        (fun x => φ x ^ 2 * g x i) + fun x => 2 * φ x * (u x - c) * gφ x i := by
      funext x
      rw [hvgrad x]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hm1 : AEStronglyMeasurable (fun x => φ x ^ 2 * g x i) (volume.restrict (ball z r)) :=
      (hφcont.pow 2).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x => 2 * φ x * (u x - c) * gφ x i)
        (volume.restrict (ball z r)) :=
      ((continuous_const.mul hφcont).aestronglyMeasurable.mul hwm.aestronglyMeasurable).mul
        ((continuous_apply i).comp hgφ_cont).aestronglyMeasurable
    have hpt1 : ∀ x, (φ x ^ 2 * g x i) ^ 2 ≤ φ x ^ 2 * E x := by
      intro x
      have hgi := (sq_apply_le_vecNormSq (g x) i).trans (hEge x)
      have hp : φ x ^ 2 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
      have hp0 : 0 ≤ φ x ^ 2 := sq_nonneg _
      calc (φ x ^ 2 * g x i) ^ 2 = φ x ^ 2 * (φ x ^ 2 * g x i ^ 2) := by ring
        _ ≤ φ x ^ 2 * (1 * E x) := by
          refine mul_le_mul_of_nonneg_left ?_ hp0
          exact mul_le_mul hp hgi (sq_nonneg _) zero_le_one
        _ = φ x ^ 2 * E x := by ring
    have hpt2 : ∀ x, (2 * φ x * (u x - c) * gφ x i) ^ 2 ≤ 4 * K ^ 2 * (u x - c) ^ 2 := by
      intro x
      have hgi := (sq_apply_le_vecNormSq (gφ x) i).trans (hgφ_bound x)
      have hp : φ x ^ 2 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
      calc (2 * φ x * (u x - c) * gφ x i) ^ 2 =
          4 * (u x - c) ^ 2 * (φ x ^ 2 * gφ x i ^ 2) := by ring
        _ ≤ 4 * (u x - c) ^ 2 * (1 * K ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hp hgi (sq_nonneg _) zero_le_one
        _ = 4 * K ^ 2 * (u x - c) ^ 2 := by ring
    have h1 := eLpMeanNormOn_two_le_ofReal_sqrt hU0 hm1 hφ2E_int (Eventually.of_forall hpt1)
    have h4int : IntegrableOn (fun x => 4 * K ^ 2 * (u x - c) ^ 2) (ball z r) :=
      hw_int.const_mul _
    have h2 := eLpMeanNormOn_two_le_ofReal_sqrt hU0 hm2 h4int (Eventually.of_forall hpt2)
    have hxxeq : Real.sqrt (⨍ x in ball z r, φ x ^ 2 * E x ∂volume) = xx := by
      rw [hxxdef, setAverage_eq, smul_eq_mul, hIdef]
    have hKyeq : Real.sqrt (⨍ x in ball z r, 4 * K ^ 2 * (u x - c) ^ 2 ∂volume) = 2 * K * y := by
      rw [setAverage_eq, smul_eq_mul, integral_const_mul, hydef, scalarRms, setAverage_eq,
        smul_eq_mul, mul_left_comm, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hK0, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hxxeq] at h1
    rw [hKyeq] at h2
    have hsum : PDE.eLpMeanNormOn (ball z r) 2 (fun x => v.toH1Function.grad x i) ≤
        ENNReal.ofReal xx + ENNReal.ofReal (2 * K * y) := by
      rw [hsplit]
      exact (eLpNorm_add_le (by norm_num)).trans (add_le_add h1 h2)
    rw [← ENNReal.ofReal_add hxx0 (by positivity)] at hsum
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsum
  have hT : h10TestNorm (ball z r) v ≤ c₁ / r * y + d * (xx + 2 * K * y) := by
    unfold h10TestNorm
    rw [hρ]
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hTi i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hc₁r : 0 ≤ c₁ / r := by positivity
    have := mul_le_mul_of_nonneg_left hT0 hc₁r
    linarith
  -- the normalized energy bound
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = r⁻¹ * y := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hyY : y = r * Y := by rw [hYdef]; field_simp
  have hmain : xx ^ 2 / 2 - 2 * Λ * ((volume.real (ball z r))⁻¹ * J) ≤
      H * h10TestNorm (ball z r) v := by
    have h := mul_le_mul_of_nonneg_left hIJ (inv_nonneg.mpr hUpos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hUpos.ne', one_mul] at h
    rw [hxx2]
    have e : (volume.real (ball z r))⁻¹ * (I / 2 - 2 * Λ * J) =
        (volume.real (ball z r))⁻¹ * I / 2 - 2 * Λ * ((volume.real (ball z r))⁻¹ * J) := by ring
    linarith
  have hj : (volume.real (ball z r))⁻¹ * J ≤ K ^ 2 * y ^ 2 := by
    rw [hy2]
    have := mul_le_mul_of_nonneg_left hJW (inv_nonneg.mpr hUpos.le)
    linarith
  have hi := caccioppoli_absorb hr hH0 hY0 hc₁ (by linarith) (Nat.cast_nonneg d) hK hyY
    hmain hj hT
  rw [← hMdef] at hi
  -- from `B_{r/2}(z)` to the weighted energy on `B_r(z)`
  have hsub : ball z (r / 2) ⊆ ball z r := by
    intro x hx
    change euclideanNorm (x - z) < r
    have : euclideanNorm (x - z) < r / 2 := hx
    linarith
  have hgsq_int : IntegrableOn (fun x => euclideanSq (g x)) (ball z (r / 2)) :=
    (PDE.integrableOn_vecDot_of_memVectorL2On hg' hg').mono_set hsub
  have hball : ∫ x in ball z (r / 2), euclideanSq (g x) ≤ I := by
    rw [hIdef]
    calc ∫ x in ball z (r / 2), euclideanSq (g x) ≤ ∫ x in ball z (r / 2), φ x ^ 2 * E x := by
          refine setIntegral_mono_on hgsq_int (hφ2E_int.mono_set hsub)
            (measurableSet_ball z (r / 2)) fun x hx => ?_
          rw [φ.eq_one_on_inner x hx, one_pow, one_mul]
          exact hEge x
      _ ≤ ∫ x in ball z r, φ x ^ 2 * E x := setIntegral_mono_set hφ2E_int
          (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hE0 x))
          (Eventually.of_forall hsub)
  have hrms : vectorRms volume (ball z (r / 2)) g ≤ Real.sqrt (2 ^ d * (2 * M)) * (Y + H) := by
    have hB : volume.real (ball z (r / 2)) = (r / 2) ^ d * ω := by
      rw [measureReal_def, hU2vol]
    have hBinv : (volume.real (ball z (r / 2)))⁻¹ = 2 ^ d * (volume.real (ball z r))⁻¹ := by
      rw [hB, hUreal, div_pow]
      field_simp
    have h1 : ⨍ x in ball z (r / 2), euclideanSq (g x) ∂volume ≤ 2 ^ d * xx ^ 2 := by
      rw [setAverage_eq, smul_eq_mul, hBinv, hxx2, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hball (inv_nonneg.mpr hUpos.le)
    have h2 : 2 ^ d * xx ^ 2 ≤ (Real.sqrt (2 ^ d * (2 * M)) * (Y + H)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), add_comm Y H]
      have := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ 2 ^ d)
      linarith
    rw [vectorRms]
    calc Real.sqrt (⨍ x in ball z (r / 2), euclideanSq (g x) ∂volume)
        ≤ Real.sqrt ((Real.sqrt (2 ^ d * (2 * M)) * (Y + H)) ^ 2) :=
          Real.sqrt_le_sqrt (h1.trans h2)
      _ = Real.sqrt (2 ^ d * (2 * M)) * (Y + H) := Real.sqrt_sq (by positivity)
  rw [hHeq, ← hcdef, ← hydef, ← hYdef, ← ENNReal.ofReal_add hY0 hH0,
    ← ENNReal.ofReal_mul hCpos.le]
  exact ENNReal.ofReal_le_ofReal hrms

/-- **Lemma C.2 (interior Caccioppoli inequality).** Fix `r > 0`. If `h = f + ∇·F ∈ H^{-1}(B_r)`
and `u ∈ H¹(B_r)` satisfy `-∇·(a∇u) = h` in `B_r`, then
`‖∇u‖_{L̲²(B_{r/2})} ≤ C (r^{-1} ‖u - (u)_{B_r}‖_{L̲²(B_r)} + ‖h‖_{H̲^{-1}(B_r)})` with `C(d, Λ)`. -/
theorem lemma_C_2 {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → ∀ (a : CoefficientField d Λ)
      (u : Vec d → ℝ) (g : Vec d → Vec d) (f : Vec d → ℝ) (F : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakGradient (ball 0 r) u g →
      MemLp f 2 (volume.restrict (ball 0 r)) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball 0 r))) →
      HasWeakDivergence (ball 0 r) (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      ENNReal.ofReal (vectorRms volume (ball 0 (r / 2)) g) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r⁻¹ * scalarRms volume (ball 0 r)
            (fun x => u x - ⨍ y in ball 0 r, u y ∂volume)) +
          negativeSobolevOneNorm 2 (ball 0 r) f F) := by
  obtain ⟨C, hC, h⟩ := interiorCaccioppoli (d := d) hΛ
  exact ⟨C, hC, fun r hr => h 0 r hr⟩

end QSH
