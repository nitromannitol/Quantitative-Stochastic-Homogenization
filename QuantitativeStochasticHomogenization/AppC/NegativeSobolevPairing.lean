import QuantitativeStochasticHomogenization.Front.Notation
import PDEFoundation.Measure.NormalizedLp
import PDEFoundation.Sobolev.H1.ZeroBoundary
import PDEFoundation.Sobolev.H1.Pairing
import PDEFoundation.PDE.WeakDivergenceForm

/-!
# Normalized `W^{-1,p}` norms of distributions `f + ∇·F`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Definition B.4 and (0.29), for the right-hand sides of Appendix C. A distribution `h ∈ H^{-1}(U)` is
written `h = f + ∇·F` with `f ∈ L²(U)` and `F ∈ L²(U; ℝ^d)`; its pairing with a test `ψ` is
`∫_U h ψ = ∫_U f ψ - ∫_U F · ∇ψ`, and its normalized `W^{-1,p}(U)` norm is
`sup {⨍_U h ψ : ψ ∈ C_c^∞(U), ‖ψ‖_{W̲^{1,p'}(U)} ≤ 1}` with `p' = p/(p-1)` and the normalized norm
`‖ψ‖_{W̲^{1,q}(U)} = |U|^{-1/d} ‖ψ‖_{L̲^q(U)} + ∑_i ‖∂_i ψ‖_{L̲^q(U)}` of (B.1). The case `p = 2`
is the normalized `H^{-1}(U)` norm.

The main result `abs_integral_pairing_le_of_h10` extends the defining bound
`|⨍_U h ψ| ≤ ‖h‖_{H̲^{-1}(U)} ‖ψ‖_{H̲^1(U)}` from smooth tests to every `v ∈ H¹₀(U)`, through the
smooth approximants carried by `PDE.H10Function`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The normalized `W^{1,q}(U)` norm `|U|^{-1/d} ‖ψ‖_{L̲^q(U)} + ∑_i ‖∂_i ψ‖_{L̲^q(U)}` of (B.1). -/
def sobolevOneTestNorm (q : ℝ≥0∞) (U : Set (Vec d)) (ψ : Vec d → ℝ) : ℝ :=
  (volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U q ψ).toReal +
    ∑ i : Fin d, (PDE.eLpMeanNormOn U q (coordinateDerivative i ψ)).toReal

/-- The normalized pairing `⨍_U h ψ = ⨍_U (f ψ - F · ∇ψ)` of `h = f + ∇·F` with a test `ψ`. -/
def distributionPairing (U : Set (Vec d)) (f : Vec d → ℝ) (F : Vec d → Vec d)
    (ψ : Vec d → ℝ) : ℝ :=
  ⨍ x in U, (f x * ψ x - dot (F x) (gradient ψ x)) ∂volume

/-- The normalized `W^{-1,p}(U)` norm of `h = f + ∇·F`, Definition B.4 and (0.29):
the supremum of `|⨍_U h ψ|` over `ψ ∈ C_c^∞(U)` with `‖ψ‖_{W̲^{1,p/(p-1)}(U)} ≤ 1`. For `p = 2`
this is the normalized `H^{-1}(U)` norm. -/
def negativeSobolevOneNorm (p : ℝ) (U : Set (Vec d)) (f : Vec d → ℝ) (F : Vec d → Vec d) :
    ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧
      sobolevOneTestNorm (ENNReal.ofReal (p / (p - 1))) U ψ ≤ 1},
    ENNReal.ofReal |distributionPairing U f F ψ.1|

/-- The normalized `H¹(U)` norm `|U|^{-1/d} ‖v‖_{L̲²(U)} + ∑_i ‖∂_i v‖_{L̲²(U)}` of an `H¹₀(U)`
function. -/
def h10TestNorm (U : Set (Vec d)) (v : PDE.H10Function U) : ℝ :=
  (volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 v.toH1Function.toFun).toReal +
    ∑ i : Fin d, (PDE.eLpMeanNormOn U 2 (fun x => v.toH1Function.grad x i)).toReal

theorem sobolevOneTestNorm_nonneg (q : ℝ≥0∞) (U : Set (Vec d)) (ψ : Vec d → ℝ) :
    0 ≤ sobolevOneTestNorm q U ψ :=
  add_nonneg (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) ENNReal.toReal_nonneg)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

theorem coordinateDerivative_const_mul {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ)
    (i : Fin d) :
    coordinateDerivative i (fun x => c * ψ x) = fun x => c * coordinateDerivative i ψ x := by
  funext x
  simp only [coordinateDerivative]
  rw [fderiv_const_mul ((hψ.differentiable (by simp)) x)]
  simp

theorem eLpMeanNormOn_const_mul (U : Set (Vec d)) (q : ℝ≥0∞) (ψ : Vec d → ℝ) {c : ℝ}
    (hc : 0 ≤ c) :
    (PDE.eLpMeanNormOn U q (fun x => c * ψ x)).toReal =
      c * (PDE.eLpMeanNormOn U q ψ).toReal := by
  simp only [PDE.eLpMeanNormOn]
  have he : (fun x => c * ψ x) = c • ψ := rfl
  rw [he, eLpNorm_const_smul, ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm,
    Real.norm_of_nonneg hc]

theorem sobolevOneTestNorm_const_mul {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (q : ℝ≥0∞) (U : Set (Vec d)) {c : ℝ} (hc : 0 ≤ c) :
    sobolevOneTestNorm q U (fun x => c * ψ x) = c * sobolevOneTestNorm q U ψ := by
  simp only [sobolevOneTestNorm, coordinateDerivative_const_mul hψ c,
    eLpMeanNormOn_const_mul U q _ hc, mul_add, Finset.mul_sum]
  ring

theorem isSpatialTest_const_mul {U : Set (Vec d)} {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ)
    (c : ℝ) : IsSpatialTest U (fun x => c * ψ x) :=
  ⟨contDiff_const.mul hψ.1, hψ.2.1.mul_left,
    (tsupport_mul_subset_right (f := fun _ => c)).trans hψ.2.2⟩

theorem gradient_const_mul {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) (x : Vec d) :
    gradient (fun x => c * ψ x) x = c • gradient ψ x := by
  funext i
  simp only [gradient, coordinateDerivative_const_mul hψ c i, Pi.smul_apply, smul_eq_mul]

theorem distributionPairing_const_mul {U : Set (Vec d)} (f : Vec d → ℝ) (F : Vec d → Vec d)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) :
    distributionPairing U f F (fun x => c * ψ x) = c * distributionPairing U f F ψ := by
  simp only [distributionPairing, gradient_const_mul hψ c]
  have hpt : ∀ x, f x * (c * ψ x) - dot (F x) (c • gradient ψ x) =
      c * (f x * ψ x - dot (F x) (gradient ψ x)) := by
    intro x
    have hs : ∑ i, F x i * (c • gradient ψ x) i = c * ∑ i, F x i * gradient ψ x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    simp only [dot, hs]
    ring
  simp_rw [hpt]
  rw [setAverage_eq, setAverage_eq, integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- The defining bound of the normalized `W^{-1,p}(U)` norm, `|⨍_U h ψ| ≤ H ‖ψ‖_{W̲^{1,p'}(U)}`,
for every smooth test when `‖h‖_{W̲^{-1,p}(U)} ≤ H`. -/
theorem abs_distributionPairing_le {p : ℝ} {U : Set (Vec d)} {f : Vec d → ℝ}
    {F : Vec d → Vec d} {H : ℝ} (hH0 : 0 ≤ H)
    (hH : negativeSobolevOneNorm p U f F ≤ ENNReal.ofReal H) {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest U ψ) :
    |distributionPairing U f F ψ| ≤
      H * sobolevOneTestNorm (ENNReal.ofReal (p / (p - 1))) U ψ := by
  set q := ENNReal.ofReal (p / (p - 1))
  set T := sobolevOneTestNorm q U ψ
  have hT : 0 ≤ T := sobolevOneTestNorm_nonneg q U ψ
  have key : ∀ ε : ℝ, 0 < ε → |distributionPairing U f F ψ| ≤ H * (T + ε) := by
    intro ε hε
    set c := (T + ε)⁻¹
    have hc : 0 < c := inv_pos.mpr (by linarith)
    have htest : IsSpatialTest U (fun x => c * ψ x) := isSpatialTest_const_mul hψ c
    have hnorm : sobolevOneTestNorm q U (fun x => c * ψ x) ≤ 1 := by
      rw [sobolevOneTestNorm_const_mul hψ.1 q U hc.le]
      rw [inv_mul_le_iff₀ (by linarith)]
      linarith
    have hle : ENNReal.ofReal |distributionPairing U f F (fun x => c * ψ x)| ≤
        negativeSobolevOneNorm p U f F :=
      le_iSup (fun ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧ sobolevOneTestNorm q U ψ ≤ 1} =>
        ENNReal.ofReal |distributionPairing U f F ψ.1|) ⟨_, htest, hnorm⟩
    have h2 := (ENNReal.ofReal_le_ofReal_iff hH0).mp (hle.trans hH)
    rw [distributionPairing_const_mul f F hψ.1 c, abs_mul, abs_of_pos hc] at h2
    have h3 : |distributionPairing U f F ψ| ≤ H / c := by
      rw [le_div_iff₀ hc]
      linarith
    calc |distributionPairing U f F ψ| ≤ H / c := h3
      _ = H * (T + ε) := by rw [div_eq_mul_inv, inv_inv]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := key (ε / (H + 1)) (div_pos hε (by linarith))
  have hHε : H * (ε / (H + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  linarith [mul_add H T (ε / (H + 1))]

theorem tendsto_toReal_eLpMeanNormOn_two {U : Set (Vec d)} (hfin : volume U ≠ ⊤)
    {ψ : ℕ → Vec d → ℝ} {v : Vec d → ℝ} (hψ : ∀ n, MemLp (ψ n) 2 (volume.restrict U))
    (hv : MemLp v 2 (volume.restrict U))
    (h : Tendsto (fun n => eLpNorm (fun x => ψ n x - v x) 2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => (PDE.eLpMeanNormOn U 2 (ψ n)).toReal) atTop
      (𝓝 (PDE.eLpMeanNormOn U 2 v).toReal) := by
  have hLp : Tendsto (fun n => (hψ n).toLp (ψ n)) atTop (𝓝 (hv.toLp v)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' ψ hψ v hv).mpr h
  have hnorm := (continuous_norm.tendsto _).comp hLp
  simp only [Function.comp_def, Lp.norm_toLp] at hnorm
  have hc : ∀ φ : Vec d → ℝ, (PDE.eLpMeanNormOn U 2 φ).toReal =
      (((volume U)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal *
        (eLpNorm φ 2 (volume.restrict U)).toReal := by
    intro φ
    by_cases h0 : volume U = 0
    · have hr : volume.restrict U = 0 := Measure.restrict_eq_zero.mpr h0
      simp [PDE.eLpMeanNormOn, PDE.normalizedVolumeOn, hr]
    · rw [PDE.eLpMeanNormOn, PDE.normalizedVolumeOn,
        eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hfin), smul_eq_mul,
        ENNReal.toReal_mul]
  simp only [hc]
  exact hnorm.const_mul _

theorem basisVec_eq_unitVector (i : Fin d) : PDE.basisVec i = unitVector i := rfl

/-- **The `H^{-1}` bound on `H¹₀` tests.** If `‖f + ∇·F‖_{H̲^{-1}(U)} ≤ H`, then for every
`v ∈ H¹₀(U)`, `|∫_U f v - ∫_U F · ∇v| ≤ |U| H ‖v‖_{H̲¹(U)}`. -/
theorem abs_integral_pairing_le_of_h10 {U : Set (Vec d)} (hfin : volume U ≠ ⊤)
    {f : Vec d → ℝ} {F : Vec d → Vec d} (hf : MemLp f 2 (volume.restrict U))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : negativeSobolevOneNorm 2 U f F ≤ ENNReal.ofReal H) (v : PDE.H10Function U) :
    |(∫ x in U, f x * v.toH1Function x) -
        ∫ x in U, PDE.vecDot (F x) (v.toH1Function.grad x)| ≤
      volume.real U * (H * h10TestNorm U v) := by
  have hq : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
  let φn : ℕ → PDE.WeakTestFunction U := fun n => v.toWeakTestFunction n
  have hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (φn n).grad x i - v.toH1Function.grad x i)
        (2 : ℝ≥0∞) (PDE.volumeOn U)) atTop (𝓝 0) := by
    intro i
    simpa only [φn, PDE.H10Function.toWeakTestFunction, PDE.WeakTestFunction.grad_apply,
      PDE.WeakTestFunction.partialDeriv] using! v.tendsto_approx_grad i
  have hvalue : Tendsto
      (fun n => eLpNorm (fun x => φn n x - v.toH1Function x) (2 : ℝ≥0∞) (PDE.volumeOn U))
        atTop (𝓝 0) := by
    simpa only [φn, PDE.H10Function.toWeakTestFunction_toFun] using v.tendsto_approx
  have hsource := PDE.tendsto_setIntegral_mul_of_tendsto_eLpNorm hf
    (fun n => (φn n).memL2On) v.toH1Function.memL2 hvalue
  have hforcing := PDE.tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm hF
    (fun n => (φn n).grad_memVectorL2On) v.toH1Function.gradMemL2 hgrad
  have hlhs := (hsource.sub hforcing).abs
  have hnorm0 := tendsto_toReal_eLpMeanNormOn_two hfin (fun n => (φn n).memL2On)
    v.toH1Function.memL2 hvalue
  have hnormi : ∀ i : Fin d, Tendsto
      (fun n => (PDE.eLpMeanNormOn U 2 (fun x => (φn n).grad x i)).toReal) atTop
        (𝓝 (PDE.eLpMeanNormOn U 2 (fun x => v.toH1Function.grad x i)).toReal) :=
    fun i => tendsto_toReal_eLpMeanNormOn_two hfin (fun n => (φn n).grad_memVectorL2On i)
      (v.toH1Function.gradMemL2 i) (hgrad i)
  have hrhs : Tendsto (fun n => volume.real U * (H *
      ((volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 (φn n)).toReal +
        ∑ i : Fin d, (PDE.eLpMeanNormOn U 2 (fun x => (φn n).grad x i)).toReal))) atTop
      (𝓝 (volume.real U * (H * h10TestNorm U v))) := by
    refine ((((hnorm0.const_mul _).add (tendsto_finsetSum _ fun i _ => hnormi i)).const_mul
      H).const_mul _)
  refine le_of_tendsto_of_tendsto' hlhs hrhs fun n => ?_
  have htest : IsSpatialTest U (φn n).toFun :=
    ⟨(φn n).contDiff, (φn n).hasCompactSupport, (φn n).tsupport_subset⟩
  have hb := abs_distributionPairing_le (p := 2) hH0 hH htest
  rw [hq] at hb
  have hint1 : Integrable (fun x => f x * (φn n) x) (volume.restrict U) :=
    hf.integrable_mul (φn n).memL2On
  have hint2 : Integrable (fun x => PDE.vecDot (F x) ((φn n).grad x)) (volume.restrict U) := by
    unfold PDE.vecDot
    exact integrable_finsetSum _ fun i _ => (hF i).integrable_mul ((φn n).grad_memVectorL2On i)
  have hpair : distributionPairing U f F (φn n).toFun =
      (volume.real U)⁻¹ * ((∫ x in U, f x * (φn n) x) -
        ∫ x in U, PDE.vecDot (F x) ((φn n).grad x)) := by
    rw [distributionPairing, setAverage_eq, smul_eq_mul, ← integral_sub hint1 hint2]
    rfl
  have hT : sobolevOneTestNorm 2 U (φn n).toFun =
      (volume U).toReal ^ (-(1 : ℝ) / d) * (PDE.eLpMeanNormOn U 2 (φn n)).toReal +
        ∑ i : Fin d, (PDE.eLpMeanNormOn U 2 (fun x => (φn n).grad x i)).toReal := rfl
  rw [hpair, hT, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg] at hb
  by_cases h0 : volume.real U = 0
  · have hU0 : volume U = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h0
      exact h0.resolve_right hfin
    have hr : volume.restrict U = 0 := Measure.restrict_eq_zero.mpr hU0
    rw [h0, zero_mul]
    simp [hr]
  · have hpos : 0 < volume.real U := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
    rw [inv_mul_le_iff₀ hpos] at hb
    exact hb

end QSH
