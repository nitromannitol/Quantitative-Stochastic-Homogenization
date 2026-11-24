import QuantitativeStochasticHomogenization.Ch01.Sec04.HatNegativeSobolev
import QuantitativeStochasticHomogenization.Ch01.Sec03.MinimizerOscillation

/-!
# The Poincaré inequality for `H¹` functions on cubes

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(1.43): for `u ∈ H¹(□_R(z))` with weak gradient `g`,
`∫_{□_R(z)} (u - (u)_{□_R(z)})² ≤ C R² ∫_{□_R(z)} |g|²` with `C` depending only on `d`
(`setIntegral_sq_sub_setAverage_le`), from the mean-zero Poincaré inequality on axis cubes of the
coarse-graining library (`Homogenization.scaled_meanZero_poincare`). The subcubes `z + □_n` of the
partition of `□_{n+r}` are cubes `□_{3^n}(z)` (`partitionCube_eq_cube`).

Also: the restriction of `H¹(U)` to subsets (`H1.mono`) and the Cauchy–Schwarz inequalities for
set integrals and finite sums used in the proof of Proposition 1.12.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The constant of the Poincaré inequality (1.43) on a cube of side `1`. -/
def cubePoincareConstant (d : ℕ) : ℝ :=
  d * _root_.Homogenization.unitMeanZeroPoincareConst d ^ 2

theorem cubePoincareConstant_nonneg (d : ℕ) : 0 ≤ cubePoincareConstant d := by
  unfold cubePoincareConstant
  positivity

theorem H1.mono {U V : Set (Vec d)} (hVU : V ⊆ U) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : H1 U u g) : H1 V u g := by
  refine ⟨hu.1.mono_measure (Measure.restrict_mono hVU le_rfl),
    hu.2.1.mono_measure (Measure.restrict_mono hVU le_rfl), fun i =>
      ⟨(hu.2.2 i).1.mono_set hVU, (hu.2.2 i).2.1.mono_set hVU, fun φ hφ => ?_⟩⟩
  have hφU : IsSpatialTest U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have h := (hu.2.2 i).2.2 φ hφU
  have hd0 : ∀ x, x ∉ tsupport φ → coordinateDerivative i φ x = 0 := fun x hx => by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have e1 : ∫ x in V, u x * coordinateDerivative i φ x = ∫ x in U, u x * coordinateDerivative i φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hd0 x fun h => hx (hφ.2.2 h), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hd0 x fun h => hx (hVU (hφ.2.2 h)), mul_zero]]
  have e2 : ∫ x in V, g x i * φ x = ∫ x in U, g x i * φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφ0 x fun h => hx (hφ.2.2 h), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφ0 x fun h => hx (hVU (hφ.2.2 h)), mul_zero]]
  rw [e1, e2]
  exact h

private theorem toReal_eLpNorm_two_sq {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have h1 : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x h1
    rw [h1]
    simp [pow_two]
  rw [← h1, Lp.norm_toLp]

/-- **The Poincaré inequality (1.43) on cubes**: for `u ∈ H¹(□_R(z))` with weak gradient `g`,
`∫ (u - (u)_{□_R(z)})² ≤ C R² ∫ |g|²`. -/
theorem setIntegral_sq_sub_setAverage_le (z : Vec d) {R : ℝ} (hR : 0 < R) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : H1 (cube z R) u g) :
    ∫ x in cube z R, (u x - ⨍ y in cube z R, u y) ^ 2 ≤
      cubePoincareConstant d * R ^ 2 * ∫ x in cube z R, euclideanSq (g x) := by
  rw [cube_eq_axisCube z R] at hu ⊢
  set Q := _root_.Homogenization.axisCube (fun i => z i - R / 2) R with hQ
  have : IsFiniteMeasure (volume.restrict Q) :=
    _root_.Homogenization.isFiniteMeasure_volumeMeasureOn_axisCube _ R
  have hw : _root_.Homogenization.HasWeakGradientOn Q u g := fun i φ hφ hc hs => by
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      (hu.2.2 i).2.2 φ ⟨hφ, hc, hs⟩
  have hdQ : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict Q) := fun i => hu.2.1.eval i
  let w : _root_.Homogenization.H1Function Q := ⟨u, g, hu.1, hdQ, hw⟩
  have h := _root_.Homogenization.scaled_meanZero_poincare (fun i => z i - R / 2) hR w
  set K := _root_.Homogenization.unitMeanZeroPoincareConst d
  have hK : 0 ≤ K := _root_.Homogenization.unitMeanZeroPoincareConst_nonneg d
  set a := ⨍ y in Q, u y with ha
  have hsub : w.subAverage.toFun = fun x => u x - a := by
    funext x
    rw [_root_.Homogenization.H1Function.subAverage_apply]
    show u x - _root_.Homogenization.integralAverage Q u = u x - a
    simp only [_root_.Homogenization.integralAverage, ha, setAverage_eq, measureReal_def,
      smul_eq_mul]
  rw [hsub] at h
  change (eLpNorm (fun x => u x - a) 2 (volume.restrict Q)).toReal ≤ K * R *
    ∑ i : Fin d, (eLpNorm (fun x => g x i) 2 (volume.restrict Q)).toReal at h
  have hlhs : (eLpNorm (fun x => u x - a) 2 (volume.restrict Q)).toReal ^ 2 =
      ∫ x in Q, (u x - a) ^ 2 :=
    toReal_eLpNorm_two_sq (hu.1.sub (memLp_const a))
  have hrhs : ∑ i : Fin d, (eLpNorm (fun x => g x i) 2 (volume.restrict Q)).toReal ^ 2 =
      ∫ x in Q, euclideanSq (g x) := by
    rw [Finset.sum_congr rfl fun i _ => toReal_eLpNorm_two_sq (hdQ i)]
    rw [← integral_finsetSum _ fun i _ => (hdQ i).integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, pow_two]
  set S := ∑ i : Fin d, (eLpNorm (fun x => g x i) 2 (volume.restrict Q)).toReal
  have hS : S ^ 2 ≤ d * ∑ i : Fin d, (eLpNorm (fun x => g x i) 2 (volume.restrict Q)).toReal ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => (eLpNorm (fun x => g x i) 2 (volume.restrict Q)).toReal)
    simpa using this
  have h0 : 0 ≤ (eLpNorm (fun x => u x - a) 2 (volume.restrict Q)).toReal := ENNReal.toReal_nonneg
  have hsq := pow_le_pow_left₀ h0 h 2
  rw [hlhs] at hsq
  rw [← hrhs]
  calc ∫ x in Q, (u x - a) ^ 2 ≤ (K * R * S) ^ 2 := hsq
    _ = K ^ 2 * R ^ 2 * S ^ 2 := by ring
    _ ≤ K ^ 2 * R ^ 2 * (d * ∑ i : Fin d,
          (eLpNorm (fun x => g x i) 2 (volume.restrict Q)).toReal ^ 2) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by unfold cubePoincareConstant; ring

/-- The subcube `z_k + □_n` of the partition of `□_{n+r}` is the cube `□_{3^n}(z_k)`. -/
theorem partitionCube_eq_cube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    partitionCube n r k = cube (latticeShift (partitionCenter n r k)) ((3 : ℝ) ^ n) := by
  ext x
  change x - latticeShift (partitionCenter n r k) ∈ triadicCube d n ↔
    ∀ i, |x i - latticeShift (partitionCenter n r k) i| < (3 : ℝ) ^ n / 2
  rw [mem_triadicCube_iff]
  rfl

/-- **The Poincaré inequality (1.43) on the subcubes `z + □_n`.** -/
theorem setIntegral_sq_sub_setAverage_le_partitionCube (n r : ℕ) (k : Fin d → Fin (3 ^ r))
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H1 (partitionCube n r k) u g) :
    ∫ x in partitionCube n r k, (u x - ⨍ y in partitionCube n r k, u y) ^ 2 ≤
      cubePoincareConstant d * ((3 : ℝ) ^ n) ^ 2 *
        ∫ x in partitionCube n r k, euclideanSq (g x) := by
  rw [partitionCube_eq_cube] at hu ⊢
  exact setIntegral_sq_sub_setAverage_le _ (by positivity) hu

/-- The Cauchy–Schwarz inequality for set integrals. -/
theorem sq_setIntegral_mul_le {U : Set (Vec d)} {f h : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U)) :
    (∫ x in U, f x * h x) ^ 2 ≤ (∫ x in U, f x ^ 2) * ∫ x in U, h x ^ 2 := by
  have hff : Integrable (fun x => f x ^ 2) (volume.restrict U) := hf.integrable_sq
  have hhh : Integrable (fun x => h x ^ 2) (volume.restrict U) := hh.integrable_sq
  have hfh : Integrable (fun x => f x * h x) (volume.restrict U) := hf.integrable_mul hh
  have key : ∀ t : ℝ, 0 ≤ (∫ x in U, f x ^ 2) * (t * t) + (-2 * ∫ x in U, f x * h x) * t +
      ∫ x in U, h x ^ 2 := by
    intro t
    have e : (fun x => (t * f x - h x) ^ 2) =
        fun x => (t * t) * f x ^ 2 + (-2 * t) * (f x * h x) + h x ^ 2 := by
      funext x; ring
    have hI : ∫ x in U, (t * f x - h x) ^ 2 = (∫ x in U, f x ^ 2) * (t * t) +
        (-2 * ∫ x in U, f x * h x) * t + ∫ x in U, h x ^ 2 := by
      have i1 : Integrable (fun x => t * t * f x ^ 2) (volume.restrict U) := hff.const_mul _
      have i2 : Integrable (fun x => -2 * t * (f x * h x)) (volume.restrict U) :=
        hfh.const_mul _
      have i12 : Integrable (fun x => t * t * f x ^ 2 + -2 * t * (f x * h x))
          (volume.restrict U) := i1.add i2
      rw [e, integral_add i12 hhh, integral_add i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← hI]
    exact integral_nonneg fun x => sq_nonneg _
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith

/-- The Cauchy–Schwarz inequality for set integrals, with square roots. -/
theorem abs_setIntegral_mul_le {U : Set (Vec d)} {f h : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U)) :
    |∫ x in U, f x * h x| ≤ √(∫ x in U, f x ^ 2) * √(∫ x in U, h x ^ 2) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt (sq_setIntegral_mul_le hf hh)

/-- The Cauchy–Schwarz inequality for finite sums, with an absolute value. -/
theorem abs_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, f i * g i| ≤ √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2) := by
  rw [abs_le]
  refine ⟨?_, Real.sum_mul_le_sqrt_mul_sqrt s f g⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => -f i) g
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
  linarith

/-- `∫_U f = |U| ⨍_U f`. -/
theorem setIntegral_eq_volume_mul_setAverage {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (f : Vec d → ℝ) :
    ∫ x in U, f x = volume.real U * ⨍ x in U, f x := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]

/-- `√(∫_U f²) = |U|^{1/2} ‖f‖_{L̲²(U)}`. -/
theorem sqrt_setIntegral_sq_eq {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (f : Vec d → ℝ) :
    √(∫ x in U, f x ^ 2) = √(volume.real U) * scalarRms volume U f := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  rw [scalarRms, setAverage_eq, smul_eq_mul, ← Real.sqrt_mul hV.le, ← mul_assoc,
    mul_inv_cancel₀ hV.ne', one_mul]

/-- `√(∫_U |G|²) = |U|^{1/2} ‖G‖_{L̲²(U)}`. -/
theorem sqrt_setIntegral_euclideanSq_eq {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (G : Vec d → Vec d) :
    √(∫ x in U, euclideanSq (G x)) = √(volume.real U) * vectorRms volume U G := by
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  rw [vectorRms, setAverage_eq, smul_eq_mul, ← Real.sqrt_mul hV.le, ← mul_assoc,
    mul_inv_cancel₀ hV.ne', one_mul]

end QSH
