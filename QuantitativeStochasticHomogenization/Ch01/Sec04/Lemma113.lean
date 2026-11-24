import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition110
import QuantitativeStochasticHomogenization.Ch03.Sec04.LinearWeakGradient
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.EuclideanNormalized
import Homogenization.Sobolev.Foundations.CubePoisson.Solver

/-!
# Lemma 1.13: the `L²` oscillation is bounded by the `Ĥ⁻¹` norm of the gradient

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, Lemma 1.13, (1.44): there is `C(d) < ∞` such that, for every `m ∈ ℕ` and
`u ∈ H¹(□_m)`, `‖u - (u)_{□_m}‖_{L̲²(□_m)} ≤ C ‖∇u‖_{Ĥ̲⁻¹(□_m)}` (`lemma_1_13_first`).

The proof is the book's. The Neumann problem `-Δw = u - (u)_{□_m}` in `□_m`, `n·∇w = 0` on `∂□_m`,
has a solution in `H²(□_m)` with `‖∇²w‖_{L̲²(□_m)} ≤ C ‖u - (u)_{□_m}‖_{L̲²(□_m)}` (1.48), from
Lemma B.19: the Neumann solver and the Calderón–Zygmund estimate on cubes of the coarse-graining
library (`Homogenization.meanZeroNeumannPoissonSolutionOfCoerciveEstimate`,
`Homogenization.originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply`). Testing the equation
with `x ↦ x_i` bounds `|(∂_i w)_{□_m}| ≤ 3^m ‖u - (u)_{□_m}‖`, the Poincaré inequality (1.43) bounds
`‖∂_i w‖_{H̲¹(□_m)}`, and testing with `u` gives
`‖u - (u)_{□_m}‖² = ⨍ ∇u·∇w ≤ Σ_i ‖∂_i u‖_{Ĥ̲⁻¹} ‖∂_i w‖_{H̲¹}`.

The `Ĥ̲⁻¹` norm of a vector field is the sum of the norms of its components
(`vectorHatNegativeSobolevNorm`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

open _root_.Homogenization (H1Function H1MeanZeroFunction originCube openCubeSet cubeAverage
  cubeVolume cubeFluctuation normalizedCubeMeasure cubeLpNorm HasWeakHessianOn vecDot basisVec)

variable {d : ℕ}

open BaseExponent

/-! ## The triadic cube `□_m` in the coarse-graining library -/

theorem openCubeSet_originCube_eq (m : ℕ) :
    openCubeSet (originCube d (m : ℤ)) = triadicCube d m := by
  ext x
  rw [mem_triadicCube_iff]
  have hdef : x ∈ openCubeSet (originCube d (m : ℤ)) ↔ ∀ i,
      (((originCube d (m : ℤ)).index i : ℝ) - 1 / 2) *
          _root_.Homogenization.cubeScaleFactor (originCube d (m : ℤ)) < x i ∧
        x i < (((originCube d (m : ℤ)).index i : ℝ) + 1 / 2) *
          _root_.Homogenization.cubeScaleFactor (originCube d (m : ℤ)) := Iff.rfl
  have hscale : _root_.Homogenization.cubeScaleFactor (originCube d (m : ℤ)) = (3 : ℝ) ^ m := by
    simp [_root_.Homogenization.cubeScaleFactor, originCube, zpow_natCast]
  have hidx (i : Fin d) : ((originCube d (m : ℤ)).index i : ℝ) = 0 := by
    simp [originCube]
  rw [hdef, hscale]
  simp only [hidx, abs_lt]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

theorem cubeVolume_originCube_eq (m : ℕ) :
    cubeVolume (originCube d (m : ℤ)) = volume.real (triadicCube d m) := by
  rw [volumeReal_triadicCube]
  simp [cubeVolume, _root_.Homogenization.cubeScaleFactor, originCube]

theorem cubeAverage_originCube_eq (m : ℕ) (f : Vec d → ℝ) :
    cubeAverage (originCube d (m : ℤ)) f = ⨍ x in triadicCube d m, f x := by
  rw [cubeAverage, setAverage_eq, smul_eq_mul, cubeVolume_originCube_eq,
    setIntegral_congr_set (_root_.Homogenization.cubeSet_ae_eq_openCubeSet _),
    openCubeSet_originCube_eq]

theorem cubeLpNorm_two_originCube_eq (m : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (m : ℤ)))) :
    cubeLpNorm (originCube d (m : ℤ)) 2 f = scalarRms volume (triadicCube d m) f := by
  have h1 : cubeLpNorm (originCube d (m : ℤ)) 2 f ^ 2 = ⨍ x in triadicCube d m, f x ^ 2 := by
    rw [cubeLpNorm, _root_.Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hf,
      ← _root_.Homogenization.cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_originCube_eq]
  have h0 : 0 ≤ cubeLpNorm (originCube d (m : ℤ)) 2 f := ENNReal.toReal_nonneg
  rw [scalarRms, ← h1, Real.sqrt_sq h0]

/-- An `H¹(□_m)` function as an `H¹` function of the coarse-graining library. -/
def H1.toH1Function {m : ℕ} {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H1 (triadicCube d m) u g) :
    H1Function (openCubeSet (originCube d (m : ℤ))) where
  toFun := u
  grad := g
  memL2 := by
    rw [openCubeSet_originCube_eq]
    exact hu.1
  gradMemL2 := fun i => by
    rw [openCubeSet_originCube_eq]
    exact hu.2.1.eval i
  hasWeakGradient := by
    rw [openCubeSet_originCube_eq]
    intro i φ hφ hc hs
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      (hu.2.2 i).2.2 φ ⟨hφ, hc, hs⟩

theorem hasWeakGradient_of_hasWeakGradientOn' {U : Set (Vec d)} {u : Vec d → ℝ}
    {G : Vec d → Vec d} (h : _root_.Homogenization.HasWeakGradientOn U u G)
    (hu : LocallyIntegrableOn u U volume) (hG : ∀ i, LocallyIntegrableOn (fun x => G x i) U volume) :
    HasWeakGradient U u G := fun i =>
  ⟨hu, hG i, fun φ hφ => by
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      h i φ hφ.1 hφ.2.1 hφ.2.2⟩

/-! ## Scaling of `H¹` functions and the pairing with `Ĥ⁻¹` -/

theorem H1.const_mul {U : Set (Vec d)} {v : Vec d → ℝ} {G : Vec d → Vec d} (hv : H1 U v G)
    (c : ℝ) : H1 U (fun x => c * v x) (fun x => c • G x) := by
  refine ⟨hv.1.const_mul c, hv.2.1.const_smul c, fun i => ⟨?_, ?_, fun φ hφ => ?_⟩⟩
  · intro x hx
    obtain ⟨t, ht, hint⟩ := (hv.2.2 i).1 x hx
    exact ⟨t, ht, hint.const_mul c⟩
  · intro x hx
    obtain ⟨t, ht, hint⟩ := (hv.2.2 i).2.1 x hx
    refine ⟨t, ht, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hint.const_mul c
  · have h := (hv.2.2 i).2.2 φ hφ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_const_mul, h]
    ring

theorem vectorRms_const_smul {U : Set (Vec d)} (G : Vec d → Vec d) (c : ℝ) :
    vectorRms volume U (fun x => c • G x) = |c| * vectorRms volume U G := by
  have h : ∀ x, euclideanSq (c • G x) = c ^ 2 * euclideanSq (G x) := fun x => by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [vectorRms, h, setAverage_eq, smul_eq_mul, integral_const_mul]
  rw [mul_left_comm, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **The pairing of `Ĥ⁻¹(U)` with `H¹(U)`**: if `‖v‖_{H̲¹(U)} ≤ T` with `T > 0`, then
`|⨍_U f v| ≤ ‖f‖_{Ĥ̲⁻¹(U)} T`. -/
theorem ofReal_abs_setAverage_mul_le {U : Set (Vec d)} {f v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : H1 U v G) {T : ℝ} (hT : 0 < T) (hvT : h1Norm U v G ≤ T) :
    ENNReal.ofReal |⨍ x in U, f x * v x| ≤ hatNegativeSobolevNorm U f * ENNReal.ofReal T := by
  have hv' := hv.const_mul T⁻¹
  have hn : h1Norm U (fun x => T⁻¹ * v x) (fun x => T⁻¹ • G x) ≤ 1 := by
    rw [h1Norm, scalarRms_const_mul, vectorRms_const_smul, abs_of_pos (inv_pos.mpr hT)]
    rw [h1Norm] at hvT
    calc (volume U).toReal ^ ((-1 : ℝ) / d) * (T⁻¹ * scalarRms volume U v) +
          T⁻¹ * vectorRms volume U G
        = T⁻¹ * ((volume U).toReal ^ ((-1 : ℝ) / d) * scalarRms volume U v +
          vectorRms volume U G) := by ring
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_left hvT (inv_pos.mpr hT).le
      _ = 1 := inv_mul_cancel₀ hT.ne'
  have h1 : ENNReal.ofReal |⨍ x in U, f x * (T⁻¹ * v x)| ≤ hatNegativeSobolevNorm U f := by
    unfold hatNegativeSobolevNorm
    exact le_iSup (fun w : {w : (Vec d → ℝ) × (Vec d → Vec d) // H1 U w.1 w.2 ∧
      h1Norm U w.1 w.2 ≤ 1} => ENNReal.ofReal |⨍ x in U, f x * w.1.1 x ∂volume|)
      ⟨((fun x => T⁻¹ * v x), (fun x => T⁻¹ • G x)), hv', hn⟩
  have h2 : |⨍ x in U, f x * (T⁻¹ * v x)| = T⁻¹ * |⨍ x in U, f x * v x| := by
    have : (fun x => f x * (T⁻¹ * v x)) = fun x => T⁻¹ * (f x * v x) := by
      funext x
      ring
    rw [this, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, integral_const_mul,
      mul_left_comm, abs_mul, abs_of_pos (inv_pos.mpr hT)]
  rw [h2] at h1
  calc ENNReal.ofReal |⨍ x in U, f x * v x|
      = ENNReal.ofReal (T * (T⁻¹ * |⨍ x in U, f x * v x|)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
    _ = ENNReal.ofReal (T⁻¹ * |⨍ x in U, f x * v x|) * ENNReal.ofReal T := by
        rw [mul_comm T, ENNReal.ofReal_mul (by positivity)]
    _ ≤ hatNegativeSobolevNorm U f * ENNReal.ofReal T := by gcongr

theorem scalarRms_le_two_mul {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) (a : ℝ) :
    scalarRms volume U f ≤ 2 * (scalarRms volume U (fun x => f x - a) + |a|) := by
  have := isFiniteMeasure_restrict.mpr hU
  have hfa : MemLp (fun x => f x - a) 2 (volume.restrict U) := hf.sub (memLp_const a)
  have hI : IntegrableOn (fun x => (f x - a) ^ 2) U := hfa.integrable_sq
  have hI2 : IntegrableOn (fun x => 2 * (f x - a) ^ 2 + 2 * a ^ 2) U :=
    (hI.const_mul 2).add (integrableOn_const hU)
  have h1 := setAverage_mono_of_integrableOn (U := U) hf.integrable_sq hI2 fun x => by
    nlinarith [sq_nonneg (f x - 2 * a)]
  rw [setAverage_mul_add_const hU0 hU hI] at h1
  have hr := Real.sqrt_nonneg (⨍ x in U, (f x - a) ^ 2)
  have hs := Real.sq_sqrt (setAverage_nonneg_of_nonneg fun x => sq_nonneg (f x - a) :
    0 ≤ ⨍ x in U, (f x - a) ^ 2)
  rw [scalarRms, scalarRms]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, sq_abs a, mul_nonneg hr (abs_nonneg a)]

/-! ## The Neumann problem on `□_m` -/

theorem vecDot_basisVec_left (i : Fin d) (x : Vec d) : vecDot (basisVec i) x = x i := by
  simp [vecDot, basisVec, Pi.single_apply]

theorem vecDot_basisVec_right (i : Fin d) (x : Vec d) : vecDot x (basisVec i) = x i := by
  simp [vecDot, basisVec, Pi.single_apply]

/-- The coordinate `x ↦ x_i` as an `H¹` function on `□_m`. -/
def affineH1 (m : ℕ) (i : Fin d) : H1Function (openCubeSet (originCube d (m : ℤ))) where
  toFun := fun x => vecDot (basisVec i) x
  grad := fun _ => basisVec i
  memL2 := by
    rw [openCubeSet_originCube_eq]
    have : IsFiniteMeasure (volume.restrict (triadicCube d m)) :=
      isFiniteMeasure_restrict.mpr (volume_triadicCube_ne_top d m)
    refine MemLp.of_bound (contDiff_vecDot_left (basisVec i)).continuous.aestronglyMeasurable
      ((3 : ℝ) ^ m) ((ae_restrict_iff' (isOpen_triadicCube m).measurableSet).mpr
        (Eventually.of_forall fun x hx => ?_))
    rw [vecDot_basisVec_left, Real.norm_eq_abs]
    have h := mem_triadicCube_iff.mp hx i
    have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    linarith
  gradMemL2 := fun j => by
    rw [openCubeSet_originCube_eq]
    have : IsFiniteMeasure (volume.restrict (triadicCube d m)) :=
      isFiniteMeasure_restrict.mpr (volume_triadicCube_ne_top d m)
    exact memLp_const _
  hasWeakGradient := by
    have e : (fun x j => fderiv ℝ (fun y => vecDot (basisVec i) y) x (basisVec j)) =
        fun _ => basisVec (d := d) i := by
      funext x j
      exact fderiv_vecDot_left_apply _ x j
    have h := _root_.Homogenization.HasWeakGradientOn.of_contDiff
      (U := openCubeSet (originCube d (m : ℤ))) (contDiff_vecDot_left (basisVec (d := d) i))
    rw [e] at h
    exact h

/-- **(1.44) for one `u`**: `‖u - (u)_{□_m}‖_{L̲²(□_m)} ≤ C₀ ‖∇u‖_{Ĥ̲⁻¹(□_m)}` with
`C₀ = (2C_P^{1/2} + 1) C_N + 2`, `C_P` the constant of (1.43) and `C_N` the constant of (1.48). -/
theorem scalarRms_sub_setAverage_le [NeZero d] (m : ℕ) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : H1 (triadicCube d m) u g) :
    ENNReal.ofReal (scalarRms volume (triadicCube d m)
        (fun x => u x - ⨍ y in triadicCube d m, u y)) ≤
      ENNReal.ofReal ((2 * √(cubePoincareConstant d) + 1) *
          _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2) *
        vectorHatNegativeSobolevNorm (triadicCube d m) g := by
  have hCN := _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant_nonneg d
  have hK := cubePoincareConstant_nonneg d
  have hsK := Real.sqrt_nonneg (cubePoincareConstant d)
  have hQW : openCubeSet (originCube d (m : ℤ)) = triadicCube d m := openCubeSet_originCube_eq m
  have hW0 : volume (triadicCube d m) ≠ 0 := volume_triadicCube_ne_zero d m
  have hWt : volume (triadicCube d m) ≠ ⊤ := volume_triadicCube_ne_top d m
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) := isFiniteMeasure_restrict.mpr hWt
  have : IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn
      (openCubeSet (originCube d (m : ℤ)))) := by
    rw [_root_.Homogenization.volumeMeasureOn, hQW]
    exact isFiniteMeasure_restrict.mpr hWt
  have hvol : 0 < volume.real (triadicCube d m) := ENNReal.toReal_pos hW0 hWt
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hρ0 : 0 ≤ scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y) :=
    Real.sqrt_nonneg _
  rcases hρ0.eq_or_lt with hρz | hρpos
  · rw [← hρz, ENNReal.ofReal_zero]
    exact bot_le
  -- the Neumann solution and its Hessian
  have hF : MemLp u 2 (normalizedCubeMeasure (originCube d (m : ℤ))) :=
    hu.toH1Function.memL2_normalizedCubeMeasure
  have hFc : MemLp (cubeFluctuation (originCube d (m : ℤ)) u) 2
      (normalizedCubeMeasure (originCube d (m : ℤ))) := hF.sub (memLp_const _)
  have Wsol : _root_.Homogenization.MeanZeroNeumannPoissonSolution (originCube d (m : ℤ))
      (cubeFluctuation (originCube d (m : ℤ)) u) :=
    _root_.Homogenization.meanZeroNeumannPoissonSolutionOfCoerciveEstimate
      (originCube d (m : ℤ)) (cubeFluctuation (originCube d (m : ℤ)) u) hFc
  obtain ⟨H, hH⟩ := _root_.Homogenization.originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply
    d (m : ℤ) u hF Wsol
  have hcav : cubeAverage (originCube d (m : ℤ)) u = ⨍ y in triadicCube d m, u y :=
    cubeAverage_originCube_eq m u
  have hcent : _root_.Homogenization.centeredCubeNormalizedL2 (originCube d (m : ℤ)) u hF =
      scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y) := by
    rw [_root_.Homogenization.centeredCubeNormalizedL2_eq_cubeLpNorm,
      cubeLpNorm_two_originCube_eq m hFc, ← hcav]
    rfl
  have hfrob : H.frobeniusNormalizedL2 (originCube d (m : ℤ)) =
      scalarRms volume (triadicCube d m) H.frobeniusMagnitude := by
    rw [H.frobeniusNormalizedL2_eq_frobeniusMagnitudeNormalizedLpNorm]
    change (eLpNorm H.frobeniusMagnitude 2
      (_root_.Homogenization.cubeBoundedMeasurableDomain (originCube d (m : ℤ))).normalizedVolume).toReal = _
    rw [_root_.Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact cubeLpNorm_two_originCube_eq m (H.frobeniusMagnitude_memLp_normalizedCubeMeasure _)
  rw [hfrob, hcent] at hH
  -- the rows of the Hessian
  have hres : volume.restrict (openCubeSet (originCube d (m : ℤ))) =
      volume.restrict (triadicCube d m) := by rw [hQW]
  have hhess : ∀ i j, MemLp (H.hess i j) 2 (volume.restrict (triadicCube d m)) := fun i j => by
    have := H.hess_memL2 i j
    rw [_root_.Homogenization.MemScalarL2, _root_.Homogenization.volumeMeasureOn, hres] at this
    exact this
  have hrow_mem : ∀ i, MemLp (fun x => fun j => H.hess i j x) 2
      (volume.restrict (triadicCube d m)) := fun i => memLp_pi_iff.mpr fun j => hhess i j
  have hrow : ∀ i, vectorRms volume (triadicCube d m) (fun x => fun j => H.hess i j x) ≤
      scalarRms volume (triadicCube d m) H.frobeniusMagnitude := by
    intro i
    have e1 : scalarRms volume (triadicCube d m) H.frobeniusMagnitude =
        √(⨍ x in triadicCube d m, ∑ i', ∑ j, H.hess i' j x ^ 2) := by
      rw [scalarRms]
      congr 1
      congr 1
      funext x
      exact H.sq_frobeniusMagnitude x
    have e2 : vectorRms volume (triadicCube d m) (fun x => fun j => H.hess i j x) =
        √(⨍ x in triadicCube d m, ∑ j, H.hess i j x ^ 2) := by
      rw [vectorRms]
      congr 1
      congr 1
      funext x
      simp [euclideanSq, dot, pow_two]
    rw [e1, e2]
    refine Real.sqrt_le_sqrt (setAverage_mono_of_integrableOn
      (integrable_finsetSum _ fun j _ => (hhess i j).integrable_sq)
      (integrable_finsetSum _ fun i' _ => integrable_finsetSum _ fun j _ => (hhess i' j).integrable_sq)
      fun x => ?_)
    exact Finset.single_le_sum (f := fun i' => ∑ j, H.hess i' j x ^ 2)
      (fun i' _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  -- the gradient of the solution
  have hwi : ∀ i, H1 (triadicCube d m) (fun x => Wsol.w.toH1Function.grad x i)
      (fun x => fun j => H.hess i j x) := by
    intro i
    have hm : MemLp (fun x => Wsol.w.toH1Function.grad x i) 2
        (volume.restrict (triadicCube d m)) := by
      have := Wsol.w.toH1Function.gradMemL2 i
      rw [_root_.Homogenization.MemL2On, hres] at this
      exact this
    refine ⟨hm, hrow_mem i, ?_⟩
    have hw : _root_.Homogenization.HasWeakGradientOn (triadicCube d m)
        (fun x => Wsol.w.toH1Function.grad x i) (fun x => fun j => H.hess i j x) := by
      intro j φ hφ hc hs
      have := H.weak_second i j φ hφ hc (by rw [hQW]; exact hs)
      rw [hres] at this
      exact this
    exact hasWeakGradient_of_hasWeakGradientOn' hw
      (IntegrableOn.locallyIntegrableOn (hm.integrable one_le_two))
      (fun j => IntegrableOn.locallyIntegrableOn ((hhess i j).integrable one_le_two))
  -- testing the equation with `u`
  have hia : ∀ f : Vec d → ℝ, _root_.Homogenization.integralAverage
      (openCubeSet (originCube d (m : ℤ))) f = ⨍ x in triadicCube d m, f x := fun f => by
    rw [_root_.Homogenization.integralAverage, hQW, setAverage_eq, smul_eq_mul, measureReal_def]
  have heq := Wsol.equation hu.toH1Function.toMeanZero
  simp only [_root_.Homogenization.H1Function.toMeanZero_toH1Function,
    _root_.Homogenization.H1Function.grad_subAverage,
    _root_.Homogenization.H1Function.subAverage_apply] at heq
  rw [hres, hia] at heq
  have heq' : ∫ x in triadicCube d m, ∑ i, Wsol.w.toH1Function.grad x i * g x i =
      ∫ x in triadicCube d m, (u x - ⨍ y in triadicCube d m, u y) *
        (u x - ⨍ y in triadicCube d m, u y) := by
    have h1 : ∫ x in triadicCube d m, ∑ i, Wsol.w.toH1Function.grad x i * g x i =
        ∫ x in triadicCube d m, (u x - cubeAverage (originCube d (m : ℤ)) u) *
          (u x - ⨍ y in triadicCube d m, u y) := heq
    rw [h1, hcav]
  -- testing the equation with `x ↦ x_i`: the averages of `∂_i w`
  have hai : ∀ i, |⨍ x in triadicCube d m, Wsol.w.toH1Function.grad x i| ≤
      (3 : ℝ) ^ m * scalarRms volume (triadicCube d m)
        (fun x => u x - ⨍ y in triadicCube d m, u y) := by
    intro i
    have heqi := Wsol.equation (affineH1 m i).toMeanZero
    simp only [_root_.Homogenization.H1Function.toMeanZero_toH1Function,
      _root_.Homogenization.H1Function.grad_subAverage,
      _root_.Homogenization.H1Function.subAverage_apply] at heqi
    rw [hres, hia] at heqi
    have e1 : ∀ x, vecDot (Wsol.w.toH1Function.grad x) ((affineH1 m i).grad x) =
        Wsol.w.toH1Function.grad x i := fun x => vecDot_basisVec_right i _
    have e2 : ∀ x : Vec d, (affineH1 m i).toFun x = x i := fun x => vecDot_basisVec_left i x
    simp only [e1, e2] at heqi
    have heqi' : ∫ x in triadicCube d m, Wsol.w.toH1Function.grad x i =
        ∫ x in triadicCube d m, (u x - ⨍ y in triadicCube d m, u y) *
          (x i - ⨍ y in triadicCube d m, y i) := by
      have h1 : ∫ x in triadicCube d m, Wsol.w.toH1Function.grad x i =
          ∫ x in triadicCube d m, (u x - cubeAverage (originCube d (m : ℤ)) u) *
            (x i - ⨍ y in triadicCube d m, y i) := heqi
      rw [h1, hcav]
    have hc : |⨍ y in triadicCube d m, y i| ≤ (3 : ℝ) ^ m / 2 := by
      rw [setAverage_eq, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hvol)]
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun y : Vec d => y i)
        (C := (3 : ℝ) ^ m / 2) hWt.lt_top fun y hy => by
          rw [Real.norm_eq_abs]
          exact (mem_triadicCube_iff.mp hy i).le
      rw [Real.norm_eq_abs] at this
      calc (volume.real (triadicCube d m))⁻¹ * |∫ y in triadicCube d m, y i|
          ≤ (volume.real (triadicCube d m))⁻¹ *
              ((3 : ℝ) ^ m / 2 * volume.real (triadicCube d m)) :=
            mul_le_mul_of_nonneg_left this (inv_pos.mpr hvol).le
        _ = (3 : ℝ) ^ m / 2 := by field_simp
    have hx : MemLp (fun x : Vec d => x i) 2 (volume.restrict (triadicCube d m)) := by
      have h := (affineH1 (d := d) m i).memL2
      rw [_root_.Homogenization.MemL2On, hres] at h
      have e : (affineH1 (d := d) m i).toFun = fun x => x i := funext e2
      rw [e] at h
      exact h
    have hxmem : MemLp (fun x : Vec d => x i - ⨍ y in triadicCube d m, y i) 2
        (volume.restrict (triadicCube d m)) := hx.sub (memLp_const _)
    have humem : MemLp (fun x => u x - ⨍ y in triadicCube d m, u y) 2
        (volume.restrict (triadicCube d m)) := hu.1.sub (memLp_const _)
    have hcs := abs_setIntegral_mul_le humem hxmem
    rw [← heqi', sqrt_setIntegral_sq_eq hW0 hWt (fun x => u x - ⨍ y in triadicCube d m, u y)] at hcs
    have hx2 : ∫ x in triadicCube d m, (x i - ⨍ y in triadicCube d m, y i) ^ 2 ≤
        ((3 : ℝ) ^ m) ^ 2 * volume.real (triadicCube d m) := by
      have h := setIntegral_mono_on hxmem.integrable_sq (integrableOn_const hWt (C := ((3 : ℝ) ^ m) ^ 2))
        (isOpen_triadicCube m).measurableSet fun x hx => by
          have h1 := mem_triadicCube_iff.mp hx i
          have h2 : |x i - ⨍ y in triadicCube d m, y i| ≤ (3 : ℝ) ^ m := by
            have := abs_sub (x i) (⨍ y in triadicCube d m, y i)
            linarith
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      rw [setIntegral_const, smul_eq_mul] at h
      linarith
    have hsx : √(∫ x in triadicCube d m, (x i - ⨍ y in triadicCube d m, y i) ^ 2) ≤
        (3 : ℝ) ^ m * √(volume.real (triadicCube d m)) := by
      calc _ ≤ √(((3 : ℝ) ^ m) ^ 2 * volume.real (triadicCube d m)) := Real.sqrt_le_sqrt hx2
        _ = (3 : ℝ) ^ m * √(volume.real (triadicCube d m)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h3m.le]
    have hvv := Real.mul_self_sqrt hvol.le
    rw [setAverage_eq, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hvol)]
    calc (volume.real (triadicCube d m))⁻¹ * |∫ x in triadicCube d m, Wsol.w.toH1Function.grad x i|
        ≤ (volume.real (triadicCube d m))⁻¹ * ((√(volume.real (triadicCube d m)) *
            scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y)) *
              ((3 : ℝ) ^ m * √(volume.real (triadicCube d m)))) :=
          mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hsx
            (mul_nonneg (Real.sqrt_nonneg _) hρ0))) (inv_pos.mpr hvol).le
      _ = (3 : ℝ) ^ m * scalarRms volume (triadicCube d m)
            (fun x => u x - ⨍ y in triadicCube d m, u y) := by
          rw [show (√(volume.real (triadicCube d m)) *
              scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y)) *
              ((3 : ℝ) ^ m * √(volume.real (triadicCube d m))) =
              (3 : ℝ) ^ m * scalarRms volume (triadicCube d m)
                (fun x => u x - ⨍ y in triadicCube d m, u y) *
                (√(volume.real (triadicCube d m)) * √(volume.real (triadicCube d m))) by ring, hvv]
          field_simp
  -- the `H¹` norms of the components of `∇w`
  have hh1 : ∀ i, h1Norm (triadicCube d m) (fun x => Wsol.w.toH1Function.grad x i)
      (fun x => fun j => H.hess i j x) ≤
      ((2 * √(cubePoincareConstant d) + 1) *
          _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2) *
        scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y) := by
    intro i
    have hwc : H1 (cube 0 ((3 : ℝ) ^ m)) (fun x => Wsol.w.toH1Function.grad x i)
        (fun x => fun j => H.hess i j x) := by
      rw [← triadicCube_eq_cube d m]
      exact hwi i
    have hP := setIntegral_sq_sub_setAverage_le (0 : Vec d) h3m hwc
    rw [← triadicCube_eq_cube d m] at hP
    have hrms1 : scalarRms volume (triadicCube d m) (fun x => Wsol.w.toH1Function.grad x i -
        ⨍ y in triadicCube d m, Wsol.w.toH1Function.grad y i) ≤
        √(cubePoincareConstant d) * (3 : ℝ) ^ m *
          vectorRms volume (triadicCube d m) (fun x => fun j => H.hess i j x) := by
      set a := ⨍ y in triadicCube d m, Wsol.w.toH1Function.grad y i with ha
      have hle : ⨍ x in triadicCube d m, (Wsol.w.toH1Function.grad x i - a) ^ 2 ≤
          cubePoincareConstant d * ((3 : ℝ) ^ m) ^ 2 *
            ⨍ x in triadicCube d m, euclideanSq (fun j => H.hess i j x) := by
        rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
        calc (volume.real (triadicCube d m))⁻¹ * ∫ x in triadicCube d m,
              (Wsol.w.toH1Function.grad x i - a) ^ 2
            ≤ (volume.real (triadicCube d m))⁻¹ * (cubePoincareConstant d * ((3 : ℝ) ^ m) ^ 2 *
                ∫ x in triadicCube d m, euclideanSq (fun j => H.hess i j x)) :=
              mul_le_mul_of_nonneg_left hP (inv_pos.mpr hvol).le
          _ = cubePoincareConstant d * ((3 : ℝ) ^ m) ^ 2 * ((volume.real (triadicCube d m))⁻¹ *
                ∫ x in triadicCube d m, euclideanSq (fun j => H.hess i j x)) := by ring
      rw [scalarRms, vectorRms]
      calc √(⨍ x in triadicCube d m, (Wsol.w.toH1Function.grad x i - a) ^ 2)
          ≤ √(cubePoincareConstant d * ((3 : ℝ) ^ m) ^ 2 *
              ⨍ x in triadicCube d m, euclideanSq (fun j => H.hess i j x)) := Real.sqrt_le_sqrt hle
        _ = √(cubePoincareConstant d) * (3 : ℝ) ^ m *
              √(⨍ x in triadicCube d m, euclideanSq (fun j => H.hess i j x)) := by
            rw [Real.sqrt_mul (mul_nonneg hK (sq_nonneg _)), Real.sqrt_mul hK, Real.sqrt_sq h3m.le]
    have hrms2 := scalarRms_le_two_mul hW0 hWt (hwi i).1
      (⨍ y in triadicCube d m, Wsol.w.toH1Function.grad y i)
    have hrowi := (hrow i).trans hH
    have hA : scalarRms volume (triadicCube d m) (fun x => Wsol.w.toH1Function.grad x i) ≤
        (3 : ℝ) ^ m * (2 * √(cubePoincareConstant d) *
          vectorRms volume (triadicCube d m) (fun x => fun j => H.hess i j x) +
          2 * scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y)) := by
      have := hai i
      nlinarith
    have hA' := (inv_mul_le_iff₀ h3m).mpr hA
    rw [h1Norm, toReal_volume_triadicCube_rpow m]
    have h2 := mul_le_mul_of_nonneg_left hrowi (by positivity : (0 : ℝ) ≤ 2 * √(cubePoincareConstant d))
    nlinarith
  -- the pairing
  have hρ2 : scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y) ^ 2 =
      ∑ i, ⨍ x in triadicCube d m, g x i * Wsol.w.toH1Function.grad x i := by
    rw [scalarRms, Real.sq_sqrt (setAverage_nonneg_of_nonneg fun x => sq_nonneg _), setAverage_eq,
      smul_eq_mul]
    have h : ∫ x in triadicCube d m, (u x - ⨍ y in triadicCube d m, u y) ^ 2 =
        ∫ x in triadicCube d m, ∑ i, Wsol.w.toH1Function.grad x i * g x i := by
      rw [heq']
      congr 1
      funext x
      ring
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)), Integrable
        (fun x => Wsol.w.toH1Function.grad x i * g x i) (volume.restrict (triadicCube d m)) :=
      fun i _ => (hwi i).1.integrable_mul (hu.2.1.eval i)
    rw [h, integral_finsetSum _ hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setAverage_eq, smul_eq_mul]
    congr 2
    funext x
    ring
  set C₀ := (2 * √(cubePoincareConstant d) + 1) *
    _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2 with hC₀
  have hC₀0 : 0 < C₀ := by
    rw [hC₀]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) hCN) (by norm_num)
  have hpair : ∀ i, ENNReal.ofReal |⨍ x in triadicCube d m, g x i * Wsol.w.toH1Function.grad x i| ≤
      hatNegativeSobolevNorm (triadicCube d m) (fun x => g x i) *
        ENNReal.ofReal (C₀ * scalarRms volume (triadicCube d m)
          (fun x => u x - ⨍ y in triadicCube d m, u y)) := fun i =>
    ofReal_abs_setAverage_mul_le (hwi i) (mul_pos hC₀0 hρpos) (hh1 i)
  have hmain : ENNReal.ofReal (scalarRms volume (triadicCube d m)
      (fun x => u x - ⨍ y in triadicCube d m, u y) ^ 2) ≤
      vectorHatNegativeSobolevNorm (triadicCube d m) g *
        ENNReal.ofReal (C₀ * scalarRms volume (triadicCube d m)
          (fun x => u x - ⨍ y in triadicCube d m, u y)) := by
    rw [hρ2]
    calc ENNReal.ofReal (∑ i, ⨍ x in triadicCube d m, g x i * Wsol.w.toH1Function.grad x i)
        ≤ ENNReal.ofReal (∑ i, |⨍ x in triadicCube d m, g x i * Wsol.w.toH1Function.grad x i|) :=
          ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun i _ => le_abs_self _)
      _ = ∑ i, ENNReal.ofReal |⨍ x in triadicCube d m, g x i * Wsol.w.toH1Function.grad x i| :=
          ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _
      _ ≤ ∑ i, hatNegativeSobolevNorm (triadicCube d m) (fun x => g x i) *
            ENNReal.ofReal (C₀ * scalarRms volume (triadicCube d m)
              (fun x => u x - ⨍ y in triadicCube d m, u y)) :=
          Finset.sum_le_sum fun i _ => hpair i
      _ = _ := by rw [← Finset.sum_mul]; rfl
  rw [pow_two, ENNReal.ofReal_mul hρ0, ENNReal.ofReal_mul hC₀0.le, ← mul_assoc] at hmain
  rw [mul_comm (ENNReal.ofReal C₀)]
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hρpos).ne' ENNReal.ofReal_ne_top).mp
    hmain

/-- **Lemma 1.13**, (1.44): there is `C(d) < ∞` such that, for every `m ∈ ℕ` and `u ∈ H¹(□_m)`,
`‖u - (u)_{□_m}‖_{L̲²(□_m)} ≤ C ‖∇u‖_{Ĥ̲⁻¹(□_m)}`. -/
theorem lemma_1_13_first [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (u : Vec d → ℝ) (g : Vec d → Vec d), H1 (triadicCube d m) u g →
      ENNReal.ofReal (scalarRms volume (triadicCube d m)
          (fun x => u x - ⨍ y in triadicCube d m, u y)) ≤
        ENNReal.ofReal C * vectorHatNegativeSobolevNorm (triadicCube d m) g :=
  ⟨(2 * √(cubePoincareConstant d) + 1) *
      _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2,
    add_nonneg (mul_nonneg (by positivity)
      (_root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant_nonneg d)) (by norm_num),
    fun m _ _ hu => scalarRms_sub_setAverage_le m hu⟩

/-! ## The second estimate (1.45) -/

theorem memLp_coord_triadicCube (m : ℕ) (i : Fin d) :
    MemLp (fun x : Vec d => x i) 2 (volume.restrict (triadicCube d m)) := by
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) :=
    isFiniteMeasure_restrict.mpr (volume_triadicCube_ne_top d m)
  refine MemLp.of_bound (continuous_apply i).aestronglyMeasurable ((3 : ℝ) ^ m)
    ((ae_restrict_iff' (isOpen_triadicCube m).measurableSet).mpr
      (Eventually.of_forall fun x hx => ?_))
  rw [Real.norm_eq_abs]
  have h := mem_triadicCube_iff.mp hx i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  linarith

/-- For a test `v` of `U`, `∫_U v = -∫_U ∂_i v x_i`. -/
theorem IsSpatialTest.setIntegral_eq_neg_mul_coord {U : Set (Vec d)} {v : Vec d → ℝ}
    (hv : IsSpatialTest U v) (i : Fin d) :
    ∫ x in U, v x = -∫ x in U, gradient v x i * x i := by
  have hvc : Continuous v := hv.1.continuous
  have hdv : Continuous fun x => fderiv ℝ v x (unitVector i) :=
    (hv.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcoord : ∀ x, fderiv ℝ (fun y : Vec d => y i) x (unitVector i) = 1 := fun x => by
    rw [(hasFDerivAt_apply i x).fderiv]
    simp [unitVector]
  have hvint : Integrable v := hvc.integrable_of_hasCompactSupport hv.2.1
  have e : (fun x => v x * fderiv ℝ (fun y : Vec d => y i) x (unitVector i)) = v :=
    funext fun x => by rw [hcoord, mul_one]
  have h1 : ∫ x in U, v x = ∫ x, v x * fderiv ℝ (fun y : Vec d => y i) x (unitVector i) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hv.2.2 h), e]
  have h2 : ∫ x in U, gradient v x i * x i = ∫ x, fderiv ℝ v x (unitVector i) * x i := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport v := fun h => hx (hv.2.2 h)
    simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  rw [h1, h2]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdv.mul (continuous_apply i)).integrable_of_hasCompactSupport
      ((hv.2.1.fderiv_apply (𝕜 := ℝ) (unitVector i)).mul_right))
    (by rw [e]; exact hvint)
    ((hvc.mul (continuous_apply i)).integrable_of_hasCompactSupport hv.2.1.mul_right)
    (fun x _ => hv.differentiable x) (fun x _ => (hasFDerivAt_apply i x).differentiableAt)

/-- For `v ∈ H¹₀(□_m)` with weak gradient `g`, `∫_{□_m} v = -∫_{□_m} g_i x_i`. -/
theorem setIntegral_eq_neg_of_H01_triadicCube (m : ℕ) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : H01 (triadicCube d m) v g) (i : Fin d) :
    ∫ x in triadicCube d m, v x = -∫ x in triadicCube d m, g x i * x i := by
  obtain ⟨hv2, hg2, -, w, hw, hconv1, hconv2⟩ := hv
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) :=
    isFiniteMeasure_restrict.mpr (volume_triadicCube_ne_top d m)
  have hx := memLp_coord_triadicCube (d := d) m i
  have h1 := tendsto_integral_mul_of_tendsto_integral_sq_sub hv2 (memLp_const (1 : ℝ))
    (fun n => (hw n).memLp_two _) hconv1
  have hgi : Tendsto (fun n => ∫ x in triadicCube d m, (gradient (w n) x i - g x i) ^ 2) atTop
      (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hconv2
    exact integral_mono
      (((((hw n).memLp_gradient (volume.restrict (triadicCube d m))).eval i).sub
        (hg2.eval i)).integrable_sq)
      (integrable_euclideanSq_of_memLp (((hw n).memLp_gradient _).sub hg2))
      fun x => sq_apply_le_euclideanSq (gradient (w n) x - g x) i
  have h2 := tendsto_integral_mul_of_tendsto_integral_sq_sub (hg2.eval i) hx
    (fun n => ((hw n).memLp_gradient _).eval i) hgi
  have heq : ∀ n, ∫ x in triadicCube d m, w n x * 1 =
      -∫ x in triadicCube d m, gradient (w n) x i * x i := fun n => by
    simp only [mul_one]
    exact (hw n).setIntegral_eq_neg_mul_coord i
  have h3 := (h2.neg).congr fun n => (heq n).symm
  have h4 := tendsto_nhds_unique h1 h3
  simpa only [mul_one] using h4

theorem h1Norm_coord_le [NeZero d] (m : ℕ) (i : Fin d) :
    h1Norm (triadicCube d m) (fun x : Vec d => x i) (fun _ => unitVector i) ≤ 3 / 2 := by
  have hW0 : volume (triadicCube d m) ≠ 0 := volume_triadicCube_ne_zero d m
  have hWt : volume (triadicCube d m) ≠ ⊤ := volume_triadicCube_ne_top d m
  have hvol : 0 < volume.real (triadicCube d m) := ENNReal.toReal_pos hW0 hWt
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  rw [h1Norm, toReal_volume_triadicCube_rpow m]
  have hv : vectorRms volume (triadicCube d m) (fun _ : Vec d => unitVector i) = 1 := by
    rw [vectorRms]
    simp only [euclideanSq_unitVector]
    rw [setAverage_const hW0 hWt, Real.sqrt_one]
  have hs : scalarRms volume (triadicCube d m) (fun x : Vec d => x i) ≤ (3 : ℝ) ^ m / 2 := by
    rw [scalarRms, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ m / 2)]
    refine Real.sqrt_le_sqrt ?_
    have : IsFiniteMeasure (volume.restrict (triadicCube d m)) := isFiniteMeasure_restrict.mpr hWt
    have h := setIntegral_mono_on (memLp_coord_triadicCube (d := d) m i).integrable_sq
      (integrableOn_const hWt (C := ((3 : ℝ) ^ m / 2) ^ 2))
      (isOpen_triadicCube m).measurableSet fun x hx => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (mem_triadicCube_iff.mp hx i).le 2
    rw [setIntegral_const, smul_eq_mul] at h
    rw [setAverage_eq, smul_eq_mul]
    calc (volume.real (triadicCube d m))⁻¹ * ∫ x in triadicCube d m, x i ^ 2
        ≤ (volume.real (triadicCube d m))⁻¹ *
            (volume.real (triadicCube d m) * ((3 : ℝ) ^ m / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h (inv_pos.mpr hvol).le
      _ = ((3 : ℝ) ^ m / 2) ^ 2 := by field_simp
  rw [hv]
  have := mul_le_mul_of_nonneg_left hs (inv_pos.mpr h3).le
  rw [show ((3 : ℝ) ^ m)⁻¹ * ((3 : ℝ) ^ m / 2) = 1 / 2 by field_simp] at this
  linarith

theorem H1_coord (m : ℕ) (i : Fin d) :
    H1 (triadicCube d m) (fun x : Vec d => x i) (fun _ => unitVector i) := by
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) :=
    isFiniteMeasure_restrict.mpr (volume_triadicCube_ne_top d m)
  refine ⟨memLp_coord_triadicCube m i, memLp_const _, ?_⟩
  have e : (fun x j => fderiv ℝ (fun y => vecDot (basisVec i) y) x (basisVec j)) =
      fun _ => basisVec (d := d) i := by
    funext x j
    exact fderiv_vecDot_left_apply _ x j
  have h := _root_.Homogenization.HasWeakGradientOn.of_contDiff
    (U := triadicCube d m) (contDiff_vecDot_left (basisVec (d := d) i))
  rw [e] at h
  have e2 : (fun y : Vec d => vecDot (basisVec i) y) = fun y => y i :=
    funext fun y => vecDot_basisVec_left i y
  rw [e2] at h
  exact hasWeakGradient_of_hasWeakGradientOn' h
    ((continuous_apply i).locallyIntegrable.locallyIntegrableOn _)
    (fun j => (continuous_const).locallyIntegrable.locallyIntegrableOn _)

/-- **(1.45) for one `v ∈ H¹₀(□_m)`**: `‖v‖_{L̲²(□_m)} ≤ (C₀ + 3/2) ‖∇v‖_{Ĥ̲⁻¹(□_m)}`. -/
theorem scalarRms_le_of_H01 [NeZero d] (m : ℕ) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : H01 (triadicCube d m) v g) :
    ENNReal.ofReal (scalarRms volume (triadicCube d m) v) ≤
      ENNReal.ofReal ((2 * √(cubePoincareConstant d) + 1) *
          _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2 + 3 / 2) *
        vectorHatNegativeSobolevNorm (triadicCube d m) g := by
  have hC₀ : 0 ≤ (2 * √(cubePoincareConstant d) + 1) *
      _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2 :=
    add_nonneg (mul_nonneg (by positivity)
      (_root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant_nonneg d)) (by norm_num)
  have hW0 : volume (triadicCube d m) ≠ 0 := volume_triadicCube_ne_zero d m
  have hWt : volume (triadicCube d m) ≠ ⊤ := volume_triadicCube_ne_top d m
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) := isFiniteMeasure_restrict.mpr hWt
  have hvol : 0 < volume.real (triadicCube d m) := ENNReal.toReal_pos hW0 hWt
  have hH1 : H1 (triadicCube d m) v g := ⟨hv.1, hv.2.1, hv.2.2.1⟩
  have h44 := scalarRms_sub_setAverage_le m hH1
  let i₀ : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hint := setIntegral_eq_neg_of_H01_triadicCube m hv i₀
  have havg : |⨍ y in triadicCube d m, v y| = |⨍ x in triadicCube d m, g x i₀ * x i₀| := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, hint, mul_neg, abs_neg]
  have hpair := ofReal_abs_setAverage_mul_le (f := fun x => g x i₀) (H1_coord m i₀)
    (by norm_num : (0 : ℝ) < 3 / 2) (h1Norm_coord_le m i₀)
  rw [← havg] at hpair
  -- `‖v‖ ≤ ‖v - (v)‖ + |(v)|`
  have hrms : scalarRms volume (triadicCube d m) v ≤
      scalarRms volume (triadicCube d m) (fun x => v x - ⨍ y in triadicCube d m, v y) +
        |⨍ y in triadicCube d m, v y| := by
    have hvc : MemLp (fun x => v x - ⨍ y in triadicCube d m, v y) 2
        (volume.restrict (triadicCube d m)) := hv.1.sub (memLp_const _)
    have h := scalarRms_add_le hvc (memLp_const (⨍ y in triadicCube d m, v y))
    have hc : scalarRms volume (triadicCube d m) (fun _ : Vec d => ⨍ y in triadicCube d m, v y) =
        |⨍ y in triadicCube d m, v y| := by
      rw [scalarRms, setAverage_const hW0 hWt, Real.sqrt_sq_eq_abs]
    rw [hc] at h
    simp only [sub_add_cancel] at h
    exact h
  have hsingle : hatNegativeSobolevNorm (triadicCube d m) (fun x => g x i₀) ≤
      vectorHatNegativeSobolevNorm (triadicCube d m) g :=
    Finset.single_le_sum (f := fun j => hatNegativeSobolevNorm (triadicCube d m) (fun x => g x j))
      (fun j _ => bot_le) (Finset.mem_univ i₀)
  calc ENNReal.ofReal (scalarRms volume (triadicCube d m) v)
      ≤ ENNReal.ofReal (scalarRms volume (triadicCube d m)
          (fun x => v x - ⨍ y in triadicCube d m, v y)) +
        ENNReal.ofReal |⨍ y in triadicCube d m, v y| := by
        rw [← ENNReal.ofReal_add (scalarRms_nonneg _ _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hrms
    _ ≤ ENNReal.ofReal ((2 * √(cubePoincareConstant d) + 1) *
            _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2) *
          vectorHatNegativeSobolevNorm (triadicCube d m) g +
        vectorHatNegativeSobolevNorm (triadicCube d m) g * ENNReal.ofReal (3 / 2) :=
        add_le_add h44 (hpair.trans (mul_le_mul' hsingle le_rfl))
    _ = _ := by
        rw [ENNReal.ofReal_add hC₀ (by norm_num)]
        ring

/-- **Lemma 1.13**, (1.44) and (1.45): there is `C(d) < ∞` such that, for every `m ∈ ℕ`,
`‖u - (u)_{□_m}‖_{L̲²(□_m)} ≤ C ‖∇u‖_{Ĥ̲⁻¹(□_m)}` for `u ∈ H¹(□_m)` and
`‖v‖_{L̲²(□_m)} ≤ C ‖∇v‖_{Ĥ̲⁻¹(□_m)}` for `v ∈ H¹₀(□_m)`. -/
theorem lemma_1_13 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (u : Vec d → ℝ) (g : Vec d → Vec d),
      (H1 (triadicCube d m) u g →
        ENNReal.ofReal (scalarRms volume (triadicCube d m)
            (fun x => u x - ⨍ y in triadicCube d m, u y)) ≤
          ENNReal.ofReal C * vectorHatNegativeSobolevNorm (triadicCube d m) g) ∧
      (H01 (triadicCube d m) u g →
        ENNReal.ofReal (scalarRms volume (triadicCube d m) u) ≤
          ENNReal.ofReal C * vectorHatNegativeSobolevNorm (triadicCube d m) g) := by
  have hC₀ : 0 ≤ (2 * √(cubePoincareConstant d) + 1) *
      _root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant d + 2 :=
    add_nonneg (mul_nonneg (by positivity)
      (_root_.Homogenization.originCubeNeumannW22CalderonZygmundConstant_nonneg d)) (by norm_num)
  refine ⟨_, add_nonneg hC₀ (by norm_num : (0 : ℝ) ≤ 3 / 2), fun m u g => ⟨fun hu => ?_,
    fun hu => scalarRms_le_of_H01 m hu⟩⟩
  refine (scalarRms_sub_setAverage_le m hu).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  linarith

end QSH
