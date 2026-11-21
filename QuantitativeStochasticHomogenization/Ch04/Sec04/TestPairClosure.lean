import QuantitativeStochasticHomogenization.Ch04.Sec04.CoefficientEnergyForm

/-!
# Test pairs and the closed space of mean-zero test limits

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 155: the `a`-harmonic extension used to approximate the admissible class.

A *gradient pair* is a pair whose gradient components are the weak gradient of its potential in
`B_T(z)`. For a test function `φ` in `B_T(z)`, the test pair is `(φ - (φ)_{B_T(z)}, ∇φ)`. The
closure `T₀` of the span of the test pairs consists of mean-zero gradient pairs; the Poincaré
inequality on the ball controls their potentials by their gradients, and they are orthogonal
for the energy form to every harmonic pair, the weak harmonicity of a pair being its energy
pairing with the test pairs.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {z : Vec d} {T : ℝ}

/-! ## Gradient pairs -/

/-- A pair whose gradient components are the weak gradient of its potential in `B_T(z)`. -/
def IsGradientPair (F : PairSpace d z T) : Prop :=
  ∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest (ball z T) φ) (i : Fin d), gradConstraint hφ i F = 0

theorem isClosed_setOf_isGradientPair :
    IsClosed {F : PairSpace d z T | IsGradientPair F} := by
  simp only [IsGradientPair, Set.ofPred_forall]
  exact isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_iInter fun i =>
    isClosed_eq (continuous_gradConstraint hφ i) continuous_const

theorem IsGradientPair.add {F G : PairSpace d z T} (hF : IsGradientPair F)
    (hG : IsGradientPair G) : IsGradientPair (F + G) := fun φ hφ i => by
  rw [gradConstraint_add, hF φ hφ i, hG φ hφ i, add_zero]

theorem IsGradientPair.smul {F : PairSpace d z T} (hF : IsGradientPair F) (c : ℝ) :
    IsGradientPair (c • F) := fun φ hφ i => by
  rw [gradConstraint_smul, hF φ hφ i, mul_zero]

theorem IsGradientPair.sub {F G : PairSpace d z T} (hF : IsGradientPair F)
    (hG : IsGradientPair G) : IsGradientPair (F - G) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ G]
  exact hF.add (hG.smul _)

theorem isGradientPair_zero : IsGradientPair (0 : PairSpace d z T) := fun φ hφ i => by
  simp [gradConstraint]

/-! ## Poincaré inequality for gradient pairs -/

/-- **Poincaré inequality for gradient pairs** on `B_T(z)`. -/
theorem integral_sub_average_sq_le_of_isGradientPair (F : PairSpace d z T)
    (hF : IsGradientPair F) (hT : 0 < T) :
    ∫ x in ball z T, (F.1 x - ⨍ y in ball z T, F.1 y) ^ 2 ≤
      (2 ^ d * (2 * T)) ^ 2 * pairGradEnergy F := by
  set U := PDE.euclideanBall z T
  have hU : ball z T = U := ball_eq_euclideanBall z hT
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by rw [h2]; exact one_le_two⟩
  have : IsFiniteMeasure (PDE.volumeOn U) := by
    rw [PDE.volumeOn, ← hU]; infer_instance
  have hgrad : ∀ i, MemLp (fun x => (F.2 i : Vec d → ℝ) x) 2 (ballMeasure z T) :=
    fun i => Lp.memLp (F.2 i)
  let u : PDE.W1pFunction U (ENNReal.ofReal 2) :=
    { toFun := F.1
      grad := fun x i => F.2 i x
      memLp := by
        show MemLp _ _ (volume.restrict U)
        rw [← hU, h2]; exact Lp.memLp F.1
      gradMemLp := fun i => by
        show MemLp _ _ (volume.restrict U)
        rw [← hU, h2]; exact hgrad i
      hasWeakGradient := fun i φ hφ hcs hsupp => by
        have hφ' : IsSpatialTest (ball z T) φ := ⟨hφ, hcs, by rw [hU]; exact hsupp⟩
        have h := hF φ hφ' i
        rw [gradConstraint_eq] at h
        rw [← hU]
        show (∫ x in ball z T, F.1 x * coordinateDerivative i φ x) = _
        linarith }
  have hUpos : 0 < volume U := hU ▸ volume_ball_pos z hT
  have hUtop : volume U < ∞ := hU ▸ volume_ball_lt_top z T
  have hmean := u.meanZeroOn_subAverage hUpos hUtop
  have hP := PDE.meanZeroPoincare_on_euclideanBall_unnormalized (p := 2) one_le_two z hT
    u.subAverage hmean
  simp only [PDE.eLpNormOn, PDE.euclideanFieldELpNormOn, PDE.volumeOn, h2] at hP
  set c := ⨍ y in ball z T, F.1 y
  have hc : PDE.integralAverage U u.toFun = c := by
    simp only [PDE.integralAverage, c, setAverage_eq, smul_eq_mul, Measure.real, ← hU]
    rfl
  have hfun : u.subAverage.toFun = fun x => F.1 x - c := by
    funext x
    rw [← hc]
    exact PDE.W1pFunction.subAverage_apply u x
  have hgradfun : u.subAverage.grad = fun x i => F.2 i x := by
    funext x
    exact PDE.W1pFunction.subAverage_grad u x
  rw [hfun, hgradfun, show PDE.euclideanBall z T = ball z T from hU.symm] at hP
  have hmemA : MemLp (fun x => F.1 x - c) 2 (ballMeasure z T) :=
    (Lp.memLp F.1).sub (memLp_const c)
  have hmemB : MemLp (fun x => PDE.vecEuclideanNorm (fun i => (F.2 i : Vec d → ℝ) x)) 2
      (ballMeasure z T) := by
    have hmeas : AEStronglyMeasurable (fun x => euclideanNorm fun i => (F.2 i : Vec d → ℝ) x)
        (ballMeasure z T) := by
      have h : AEStronglyMeasurable
          (fun x => ∑ i, (F.2 i : Vec d → ℝ) x * (F.2 i : Vec d → ℝ) x) (ballMeasure z T) :=
        Finset.aestronglyMeasurable_fun_sum _
          fun i _ => (Lp.aestronglyMeasurable (F.2 i)).mul (Lp.aestronglyMeasurable (F.2 i))
      exact Real.continuous_sqrt.comp_aestronglyMeasurable h
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    have hsum : Integrable (fun x => ∑ i, (F.2 i : Vec d → ℝ) x ^ 2) (ballMeasure z T) :=
      integrable_finsetSum _ fun i _ => (Lp.memLp (F.2 i)).integrable_sq
    refine hsum.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [sq_euclideanNorm]
    simp only [euclideanSq, dot, sq]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    hmemB.eLpNorm_ne_top) hP
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
  rw [mul_pow, sq_toReal_eLpNorm_two hmemA, sq_toReal_eLpNorm_two hmemB] at hsq
  have hB : ∫ x in ball z T, PDE.vecEuclideanNorm (fun i => (F.2 i : Vec d → ℝ) x) ^ 2 =
      pairGradEnergy F := by
    rw [pairGradEnergy_eq_integral]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show Real.sqrt (euclideanSq _) ^ 2 = euclideanSq _
    rw [Real.sq_sqrt (zero_le_euclideanSq _)]
  rw [hB] at hsq
  exact hsq

/-- The mean of the potential of a pair over `B_T(z)`. -/
def pairMean (F : PairSpace d z T) : ℝ := ∫ x in ball z T, F.1 x

theorem pairMean_eq_inner (F : PairSpace d z T) : pairMean F = ⟪oneLp z T, F.1⟫_ℝ := by
  rw [pairMean, oneLp, inner_toLp_left]
  simp

theorem continuous_pairMean : Continuous (pairMean : PairSpace d z T → ℝ) := by
  have : (pairMean : PairSpace d z T → ℝ) = fun F => ⟪oneLp z T, F.1⟫_ℝ := by
    funext F; exact pairMean_eq_inner F
  rw [this]
  exact continuous_const.inner continuous_fst

/-- For mean-zero gradient pairs, the potential is controlled by the gradient. -/
theorem norm_fst_sq_le_of_isGradientPair (F : PairSpace d z T) (hF : IsGradientPair F)
    (hT : 0 < T) (hm : pairMean F = 0) :
    ‖F.1‖ ^ 2 ≤ (2 ^ d * (2 * T)) ^ 2 * pairGradEnergy F := by
  have h := integral_sub_average_sq_le_of_isGradientPair F hF hT
  have havg : (⨍ y in ball z T, F.1 y) = 0 := by
    rw [setAverage_eq]
    rw [pairMean] at hm
    rw [hm, smul_zero]
  rw [havg] at h
  rw [norm_sq_eq_integral]
  simpa using h

/-! ## Test pairs -/

variable (z T) in
/-- The mean-zero potential `φ - (φ)_{B_T(z)}` of a test pair. -/
def testPotential (φ : Vec d → ℝ) (x : Vec d) : ℝ := φ x - ⨍ y in ball z T, φ y

theorem IsSpatialTest.memLp_testPotential {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) :
    MemLp (testPotential z T φ) 2 (ballMeasure z T) :=
  (hφ.memLp _).sub (memLp_const _)

/-- **The test pair** `(φ - (φ)_{B_T(z)}, ∇φ)` of a test function `φ` in `B_T(z)`. -/
def testPair {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) : PairSpace d z T :=
  (hφ.memLp_testPotential.toLp _,
    fun k => (hφ.memLp_coordinateDerivative k (ballMeasure z T)).toLp _)

theorem isGradientPair_testPair {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) :
    IsGradientPair (testPair hφ) := by
  intro ψ hψ i
  rw [gradConstraint_eq]
  have h1 : (∫ x in ball z T, (testPair hφ).1 x * coordinateDerivative i ψ x) =
      ∫ x in ball z T, testPotential z T φ x * coordinateDerivative i ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hφ.memLp_testPotential.coeFn_toLp] with x hx
    rw [testPair, hx]
  have h2 : (∫ x in ball z T, (testPair hφ).2 i x * ψ x) =
      ∫ x in ball z T, coordinateDerivative i φ x * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [(hφ.memLp_coordinateDerivative i (ballMeasure z T)).coeFn_toLp] with x hx
    rw [testPair, hx]
  rw [h1, h2]
  have hcd : ContDiff ℝ 1 (testPotential z T φ) :=
    (hφ.1.of_le (by simp)).sub contDiff_const
  have hER := PDE.HasWeakPartialDerivOn.of_contDiff (U := ball z T) (i := i) hcd ψ hψ.1 hψ.2.1
    hψ.2.2
  have hfd : ∀ x, fderiv ℝ (testPotential z T φ) x = fderiv ℝ φ x := fun x =>
    fderiv_sub_const _
  simp only [hfd] at hER
  have e1 : (∫ x in ball z T, testPotential z T φ x * coordinateDerivative i ψ x) =
      ∫ x in ball z T, testPotential z T φ x * (fderiv ℝ ψ x) (PDE.basisVec i) := rfl
  have e2 : (∫ x in ball z T, coordinateDerivative i φ x * ψ x) =
      ∫ x in ball z T, (fderiv ℝ φ x) (PDE.basisVec i) * ψ x := rfl
  rw [e1, e2, hER]
  ring

theorem pairMean_testPair (hT : 0 < T) {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) :
    pairMean (testPair hφ) = 0 := by
  rw [pairMean]
  have h1 : (∫ x in ball z T, (testPair hφ).1 x) = ∫ x in ball z T, testPotential z T φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hφ.memLp_testPotential.coeFn_toLp] with x hx
    rw [testPair, hx]
  rw [h1]
  unfold testPotential
  have hint : Integrable φ (ballMeasure z T) := (hφ.memLp _).integrable one_le_two
  rw [integral_sub hint (integrable_const _), setIntegral_const, setAverage_eq, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (volume_real_ball_pos z hT).ne', one_mul, sub_self]

/-- The weak harmonicity constraint is the energy pairing with the test pair. -/
theorem harmConstraint_eq_energyForm (a : CoefficientField d Λ) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z T) φ) (F : PairSpace d z T) :
    harmConstraint a hφ F = energyForm a F (testPair hφ) := by
  rw [harmConstraint, energyForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_toLp_left]
  unfold coefficientTest weightedPairing
  rw [← integral_finsetSum _ fun k _ => integrable_weighted
    (aestronglyMeasurable_coefficient_ball a k l) (coefficient_bound a k l) _ _]
  have hk := ae_all_iff.2 fun k =>
    (hφ.memLp_coordinateDerivative k (ballMeasure z T)).coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [hk] with x hx
  simp only [testPair, hx, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The closure of the test pairs -/

/-- The span of the test pairs. -/
def testPairSpan (d : ℕ) (z : Vec d) (T : ℝ) : Submodule ℝ (PairSpace d z T) :=
  Submodule.span ℝ (Set.range fun φ : {φ : Vec d → ℝ // IsSpatialTest (ball z T) φ} =>
    testPair φ.2)

/-- **The closed space `T₀` of limits of test pairs.** -/
def testPairClosure (d : ℕ) (z : Vec d) (T : ℝ) : Submodule ℝ (PairSpace d z T) :=
  (testPairSpan d z T).topologicalClosure

theorem isClosed_testPairClosure : IsClosed (testPairClosure d z T : Set (PairSpace d z T)) :=
  Submodule.isClosed_topologicalClosure _

theorem testPair_mem_testPairClosure {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball z T) φ) :
    testPair hφ ∈ testPairClosure d z T :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨φ, hφ⟩, rfl⟩)

theorem testPairClosure_induction {P : PairSpace d z T → Prop} (hP : IsClosed {t | P t})
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : ℝ) x, P x → P (c • x))
    (hgen : ∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest (ball z T) φ), P (testPair hφ))
    {t : PairSpace d z T} (ht : t ∈ testPairClosure d z T) : P t := by
  have hspan : ∀ x ∈ testPairSpan d z T, P x := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨φ, hφ⟩, rfl⟩ := hx
      exact hgen φ hφ
    | zero => exact h0
    | add x y _ _ hx hy => exact hadd x y hx hy
    | smul c x _ hx => exact hsmul c x hx
  have hsub : (testPairClosure d z T : Set (PairSpace d z T)) ⊆ {t | P t} := by
    rw [testPairClosure, Submodule.topologicalClosure_coe]
    exact closure_minimal hspan hP
  exact hsub ht

theorem IsGradientPair.of_mem_testPairClosure {t : PairSpace d z T}
    (ht : t ∈ testPairClosure d z T) : IsGradientPair t :=
  testPairClosure_induction isClosed_setOf_isGradientPair isGradientPair_zero
    (fun _ _ hx hy => hx.add hy) (fun c _ hx => hx.smul c)
    (fun _ hφ => isGradientPair_testPair hφ) ht

theorem pairMean_add (F G : PairSpace d z T) : pairMean (F + G) = pairMean F + pairMean G := by
  rw [pairMean_eq_inner, pairMean_eq_inner, pairMean_eq_inner, Prod.fst_add, inner_add_right]

theorem pairMean_smul (c : ℝ) (F : PairSpace d z T) : pairMean (c • F) = c * pairMean F := by
  rw [pairMean_eq_inner, pairMean_eq_inner, Prod.smul_fst, real_inner_smul_right]

theorem pairMean_eq_zero_of_mem (hT : 0 < T) {t : PairSpace d z T}
    (ht : t ∈ testPairClosure d z T) : pairMean t = 0 :=
  testPairClosure_induction (P := fun t => pairMean t = 0)
    (isClosed_eq continuous_pairMean continuous_const)
    (by rw [pairMean_eq_inner]; simp)
    (fun x y hx hy => by rw [pairMean_add, hx, hy, add_zero])
    (fun c x hx => by rw [pairMean_smul, hx, mul_zero])
    (fun _ hφ => pairMean_testPair hT hφ) ht

/-- Harmonic pairs are orthogonal to `T₀` for the energy form. -/
theorem energyForm_eq_zero_of_isHarmonicPair (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ)
    {F : PairSpace d z T} (hF : IsHarmonicPair a F) {t : PairSpace d z T}
    (ht : t ∈ testPairClosure d z T) : energyForm a F t = 0 :=
  testPairClosure_induction (P := fun t => energyForm a F t = 0)
    (isClosed_eq ((continuous_energyForm a hΛ).comp (continuous_const.prodMk continuous_id))
      continuous_const)
    (by simpa using energyForm_smul_right a 0 F 0)
    (fun x y hx hy => by rw [energyForm_add_right, hx, hy, add_zero])
    (fun c x hx => by rw [energyForm_smul_right, hx, mul_zero])
    (fun _ hφ => by rw [← harmConstraint_eq_energyForm]; exact hF.2 _ hφ) ht

end QSH
