import QuantitativeStochasticHomogenization.AppC.InteriorMeyers
import QuantitativeStochasticHomogenization.Ch01.Sec02.TestPoincare

/-!
# The global Caccioppoli estimate: the energy bound

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, Lemma C.8, the estimate (C.17): for a bounded domain `U`, `h ∈ H^{-1}(U)` and
`u ∈ H¹₀(U)` solving `-∇·(a∇u) = h` in `U`, `‖∇u‖_{L̲²(U)} ≤ C ‖h‖_{H̲^{-1}(U)}` with
`C(U, d, Λ) < ∞`. The proof is the book's: test the equation with `u`. The test is admissible by
the extension of the weak formulation to `H¹₀(U)` tests of the elliptic regularity library, and
the normalized `H¹(U)` norm of `u` is controlled by `‖∇u‖_{L̲²(U)}` through the Poincaré inequality
in `H¹₀(U)` (`setIntegral_sq_le_of_H01`). The estimate holds for every bounded open `U`.

The file also defines the geometric constant `κ_U` of (C.13).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The geometric constant `κ_U` of (C.13):
`sup_{z ∈ U, r > 0} |B_r(z) ∩ U| / |B_{r/2}(z) ∩ U| + sup_{z ∈ ∂U, r > 0} |B_r| / |B_r(z) \ U|`. -/
def kappaConstant (U : Set (Vec d)) : ℝ≥0∞ :=
  (⨆ (z : Vec d) (_ : z ∈ U) (r : ℝ) (_ : 0 < r),
      volume (ball z r ∩ U) / volume (ball z (r / 2) ∩ U)) +
    ⨆ (z : Vec d) (_ : z ∈ frontier U) (r : ℝ) (_ : 0 < r),
      volume (ball z r) / volume (ball z r \ U)

theorem tendsto_eLpNorm_two_of_tendsto_integral_sq {μ : Measure (Vec d)} {F : ℕ → Vec d → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (h : Tendsto (fun n => ∫ x, F n x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (F n) 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, F n x ^ 2 ∂μ)) := by
    intro n
    rw [(hF n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, ← one_div]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ‖F n x‖ ^ (2 : ℝ) = F n x ^ 2
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  have h2 : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (∫ x, F n x ^ 2 ∂μ))) atTop
      (𝓝 (ENNReal.ofReal (Real.sqrt 0))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp h)
  simpa using h2

/-- The `H¹₀(U)` function of the elliptic regularity library given by `H01` data: the same
function and gradient, with the approximating tests of `H01`. -/
def H01.toH10Function {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d} (h : H01 U u g) :
    PDE.H10Function U where
  toH1Function := toH1FunctionOn h.1 (fun i => MemLp.eval h.2.1 i) h.2.2.1
  approx := Classical.choose h.2.2.2
  approx_smooth n := ((Classical.choose_spec h.2.2.2).1 n).1
  approx_hasCompactSupport n := ((Classical.choose_spec h.2.2.2).1 n).2.1
  approx_support_subset n := ((Classical.choose_spec h.2.2.2).1 n).2.2
  tendsto_approx := by
    obtain ⟨hv, hconv, -⟩ := Classical.choose_spec h.2.2.2
    exact tendsto_eLpNorm_two_of_tendsto_integral_sq
      (fun n => ((hv n).memLp_two _).sub h.1) hconv
  tendsto_approx_grad := by
    intro i
    obtain ⟨hv, -, hgconv⟩ := Classical.choose_spec h.2.2.2
    refine tendsto_eLpNorm_two_of_tendsto_integral_sq
      (fun n => (MemLp.eval ((hv n).memLp_gradient _) i).sub (MemLp.eval h.2.1 i)) ?_
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hgconv
    refine integral_mono
      ((MemLp.eval (((hv n).memLp_gradient _).sub h.2.1) i).integrable_sq) ?_ fun x => ?_
    · exact integrable_euclideanSq_of_memLp (((hv n).memLp_gradient _).sub h.2.1)
    · change (coordinateDerivative i (Classical.choose h.2.2.2 n) x - g x i) ^ 2 ≤ _
      have e : coordinateDerivative i (Classical.choose h.2.2.2 n) x - g x i =
          (gradient (Classical.choose h.2.2.2 n) x - g x) i := rfl
      rw [e]
      exact sq_apply_le_vecNormSq _ i

theorem H01.toH10Function_apply {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : H01 U u g) (x : Vec d) : h.toH10Function.toH1Function x = u x := rfl

theorem H01.toH10Function_grad {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : H01 U u g) (x : Vec d) : h.toH10Function.toH1Function.grad x = g x := rfl

/-- **Lemma C.8, the energy estimate (C.17).** For a bounded open set `U` of positive measure
there is `C(U, d, Λ) < ∞` such that, for `h = f + ∇·F ∈ H^{-1}(U)` with `f ∈ L²(U)`,
`F ∈ L²(U; ℝ^d)` and `u ∈ H¹₀(U)` solving `-∇·(a∇u) = h` in `U`,
`‖∇u‖_{L̲²(U)} ≤ C ‖h‖_{H̲^{-1}(U)}`. -/
theorem lemma_C_8_energy {Λ : ℝ} (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hU0 : volume U ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoefficientField d Λ) (u : Vec d → ℝ) (g : Vec d → Vec d)
      (f : Vec d → ℝ) (F : Vec d → Vec d), H01 U u g →
      MemLp f 2 (volume.restrict U) →
      (∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) →
      HasWeakDivergence U (fun x => (a x).mulVec (g x) + F x) (fun x => -f x) →
      ENNReal.ofReal (vectorRms volume U g) ≤
        ENNReal.ofReal C * negativeSobolevOneNorm 2 U f F := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine ⟨1, one_pos, fun a u g f F _ _ _ _ => ?_⟩
    have h0 : vectorRms volume U g = 0 := by
      simp [vectorRms, euclideanSq, dot]
    rw [h0, ENNReal.ofReal_zero]
    exact bot_le
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨R, hR, hUR⟩ := exists_subset_cube_of_isBounded hUb
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hUm : MeasurableSet U := hUo.measurableSet
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  set P := testPoincareConstant d with hPdef
  have hP : 0 ≤ P := testPoincareConstant_nonneg d
  set V := (volume U).toReal ^ (-(1 : ℝ) / d) with hVdef
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set K := V * Real.sqrt (P * R ^ 2) + d with hKdef
  have hK : 0 < K := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : 0 ≤ V * Real.sqrt (P * R ^ 2) := mul_nonneg hV (Real.sqrt_nonneg _)
    linarith
  refine ⟨K, hK, fun a u g f F hu hf hF hdiv => ?_⟩
  by_cases hHtop : negativeSobolevOneNorm 2 U f F = ⊤
  · rw [hHtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK).ne']
    exact le_top
  obtain ⟨H, hHdef⟩ : ∃ H, H = (negativeSobolevOneNorm 2 U f F).toReal := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := hHdef ▸ ENNReal.toReal_nonneg
  have hHeq : negativeSobolevOneNorm 2 U f F = ENNReal.ofReal H := by
    rw [hHdef, ENNReal.ofReal_toReal hHtop]
  have hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => MemLp.eval hu.2.1 i
  have hg' : PDE.MemVectorL2On U g := hg
  -- the elliptic library's objects
  obtain ⟨A, hAdef⟩ : ∃ A, A = ellipticFieldOf a := ⟨_, rfl⟩
  have hEll : PDE.IsEllipticFieldOn 1 Λ U A := hAdef ▸ isEllipticFieldOn_ellipticFieldOf hΛ a hUm
  have hAx : ∀ x, PDE.IsEllipticMatrix 1 Λ (A x) := hAdef ▸ isEllipticMatrix_ellipticFieldOf hΛ a
  have hsol : PDE.IsWeakDivergenceFormSolutionOn A U (toH1FunctionOn hu.1 hg hu.2.2.1) f F :=
    hAdef ▸ isWeakDivergenceFormSolutionOn_toH1FunctionOn hΛ a hUm hu.1 hg hu.2.2.1 hf hF hdiv
  have hsol10 := hsol.toH10SolutionOn_of_isEllipticFieldOn hEll hf hF
  set v := hu.toH10Function with hvdef
  have hid := (hsol10 v).2
  have hpair := abs_integral_pairing_le_of_h10 hUt hf hF hH0 hHeq.le v
  -- the energy
  set G := vectorRms volume U g with hGdef
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hUreal : 0 < volume.real U := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hU0 hUt
  have hsq_int : IntegrableOn (fun x => euclideanSq (g x)) U :=
    PDE.integrableOn_vecDot_of_memVectorL2On hg' hg'
  have hflux_int : IntegrableOn
      (fun x => PDE.vecDot (PDE.matVecMul (A x) (g x)) (g x)) U :=
    PDE.integrableOn_vecDot_of_memVectorL2On
      (PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hg') hg'
  have hGsq : volume.real U * G ^ 2 = ∫ x in U, euclideanSq (g x) := by
    have havg : ⨍ x in U, euclideanSq (g x) ∂volume =
        (volume.real U)⁻¹ * ∫ x in U, euclideanSq (g x) := by
      rw [setAverage_eq, smul_eq_mul]
    have hnn : 0 ≤ ⨍ x in U, euclideanSq (g x) ∂volume := by
      rw [havg]
      exact mul_nonneg (inv_nonneg.mpr hUreal.le)
        (integral_nonneg fun x => euclideanSq_nonneg' (g x))
    rw [hGdef, vectorRms, Real.sq_sqrt hnn, havg, ← mul_assoc, mul_inv_cancel₀ hUreal.ne',
      one_mul]
  have hlow : volume.real U * G ^ 2 ≤
      ∫ x in U, PDE.vecDot (PDE.matVecMul (A x) (g x)) (g x) := by
    rw [hGsq]
    refine setIntegral_mono hsq_int hflux_int fun x => ?_
    have h1 := (hAx x).2.2.1 (g x)
    rw [one_mul, PDE.vecDot_comm] at h1
    exact h1
  -- the normalized `H¹` norm of `u`
  have hT : h10TestNorm U v ≤ K * G := by
    have hu2 : (PDE.eLpMeanNormOn U 2 v.toH1Function.toFun).toReal ≤ Real.sqrt (P * R ^ 2) * G := by
      have e := eLpMeanNormOn_two_eq_ofReal_scalarRms hU0 hu.1
      change (PDE.eLpMeanNormOn U 2 u).toReal ≤ _
      rw [e, scalarRms, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hGdef, vectorRms,
        ← Real.sqrt_mul (mul_nonneg hP (sq_nonneg R))]
      refine Real.sqrt_le_sqrt ?_
      have hpo := setIntegral_sq_le_of_H01 0 hR hUR hu
      rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
      have hinv : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr hUreal.le
      calc (volume.real U)⁻¹ * ∫ x in U, u x ^ 2
          ≤ (volume.real U)⁻¹ * (P * R ^ 2 * ∫ x in U, euclideanSq (g x)) :=
            mul_le_mul_of_nonneg_left hpo hinv
        _ = P * R ^ 2 * ((volume.real U)⁻¹ * ∫ x in U, euclideanSq (g x)) := by ring
    have hgi : ∀ i : Fin d, (PDE.eLpMeanNormOn U 2
        (fun x => v.toH1Function.grad x i)).toReal ≤ G := by
      intro i
      have h := eLpMeanNormOn_two_le_ofReal_sqrt hU0 (hg i).aestronglyMeasurable
        (G := fun x => euclideanSq (g x)) hsq_int
        (Eventually.of_forall fun x => sq_apply_le_vecNormSq (g x) i)
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
      rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
      exact le_rfl
    unfold h10TestNorm
    calc V * (PDE.eLpMeanNormOn U 2 v.toH1Function.toFun).toReal +
          ∑ i : Fin d, (PDE.eLpMeanNormOn U 2 (fun x => v.toH1Function.grad x i)).toReal
        ≤ V * (Real.sqrt (P * R ^ 2) * G) + ∑ _i : Fin d, G :=
          add_le_add (mul_le_mul_of_nonneg_left hu2 hV) (Finset.sum_le_sum fun i _ => hgi i)
      _ = K * G := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKdef]
          ring
  -- the tested equation
  have hflux_eq : ∫ x in U, PDE.vecDot (PDE.matVecMul (A x) (g x)) (g x) =
      (∫ x in U, f x * v.toH1Function x) -
        ∫ x in U, PDE.vecDot (F x) (v.toH1Function.grad x) := hid
  have hmain : volume.real U * G ^ 2 ≤ volume.real U * (H * (K * G)) := by
    calc volume.real U * G ^ 2
        ≤ ∫ x in U, PDE.vecDot (PDE.matVecMul (A x) (g x)) (g x) := hlow
      _ ≤ |(∫ x in U, f x * v.toH1Function x) -
            ∫ x in U, PDE.vecDot (F x) (v.toH1Function.grad x)| := by
          rw [hflux_eq]
          exact le_abs_self _
      _ ≤ volume.real U * (H * h10TestNorm U v) := hpair
      _ ≤ volume.real U * (H * (K * G)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hH0) measureReal_nonneg
  have hGle : G ≤ K * H := by
    have h2 : G ^ 2 ≤ H * (K * G) := le_of_mul_le_mul_left hmain hUreal
    rcases hG0.eq_or_lt with hG | hG
    · rw [← hG]
      exact mul_nonneg hK.le hH0
    · nlinarith [h2, hG]
  rw [hHeq, ← ENNReal.ofReal_mul hK.le]
  exact ENNReal.ofReal_le_ofReal hGle

end QSH
