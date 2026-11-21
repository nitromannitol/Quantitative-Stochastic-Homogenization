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
    rw [euclideanNorm_sq]
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
    rw [Real.sq_sqrt (euclideanSq_nonneg _)]
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

end QSH
