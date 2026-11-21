import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationObjectivePair
import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
import PDEFoundation.Sobolev.W1p.Mean

/-!
# Coercivity of the objective `I` on the admissible class

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 155. On the admissible pairs (harmonic pairs with gradient energy at most
`C² |B_T(z)|`), the sublevel sets of the objective `I` are bounded in `L²(B_T(z))`.

The oscillation of the potential is controlled by the Poincaré inequality on the ball
(`PDE.meanZeroPoincare_on_euclideanBall_unnormalized` of the elliptic regularity library). Its
mean `c` is controlled by the objective: the Gaussian observation of the constant function `1` is
bounded below on the observation ball `B_{S/θ}(z)`, and
`c ⟨Φ_y, 1⟩ = ⟨Φ_y, u - ℓ_i⟩ + ⟨Φ_y, ℓ_i⟩ - ⟨Φ_y, u - c⟩`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {z : Vec d} {T : ℝ} {Λ : ℝ} {a : CoefficientField d Λ}

theorem ball_eq_euclideanBall (z : Vec d) {T : ℝ} (hT : 0 < T) :
    ball z T = PDE.euclideanBall z T := by
  ext x
  simp only [ball, PDE.euclideanBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot,
    euclideanNorm, euclideanSq, dot, Set.mem_ofPred_eq]
  exact Real.sqrt_lt' hT

theorem sq_toReal_eLpNorm_two {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← Lp.norm_toLp f hf, norm_toLp_sq_eq_integral]

/-- **Poincaré inequality for harmonic pairs** on `B_T(z)`, from the mean-zero Poincaré
inequality on Euclidean balls of the elliptic regularity library. -/
theorem integral_sub_average_sq_le (F : PairSpace d z T) (hF : IsHarmonicPair a F) (hT : 0 < T) :
    ∫ x in ball z T, (F.1 x - ⨍ y in ball z T, F.1 y) ^ 2 ≤
      (2 ^ d * (2 * T)) ^ 2 * pairGradEnergy F := by
  set U := PDE.euclideanBall z T
  have hU : ball z T = U := ball_eq_euclideanBall z hT
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by rw [h2]; exact one_le_two⟩
  have : IsFiniteMeasure (PDE.volumeOn U) := by
    rw [PDE.volumeOn, ← hU]; infer_instance
  set w := ofPair a F hF
  have hgrad : ∀ i, MemLp (fun x => w.grad x i) 2 (ballMeasure z T) := fun i => w.memLp_grad i
  let u : PDE.W1pFunction U (ENNReal.ofReal 2) :=
    { toFun := w.potential
      grad := w.grad
      memLp := by
        show MemLp _ _ (volume.restrict U)
        rw [← hU, h2]; exact w.square_integrable
      gradMemLp := fun i => by
        show MemLp _ _ (volume.restrict U)
        rw [← hU, h2]; exact hgrad i
      hasWeakGradient := fun i φ hφ hcs hsupp => by
        have h := (w.weak_gradient i).2.2 φ ⟨hφ, hcs, hU ▸ hsupp⟩
        rw [← hU]
        exact h }
  have hUpos : 0 < volume U := hU ▸ volume_ball_pos z hT
  have hUtop : volume U < ∞ := hU ▸ volume_ball_lt_top z T
  have hmean := u.meanZeroOn_subAverage hUpos hUtop
  have hP := PDE.meanZeroPoincare_on_euclideanBall_unnormalized (p := 2) one_le_two z hT
    u.subAverage hmean
  simp only [PDE.eLpNormOn, PDE.euclideanFieldELpNormOn, PDE.volumeOn, h2] at hP
  -- the two sides as real numbers
  set c := ⨍ y in ball z T, F.1 y
  have hc : PDE.integralAverage U u.toFun = c := by
    simp only [PDE.integralAverage, c, setAverage_eq, smul_eq_mul, Measure.real, ← hU]
    rfl
  have hfun : u.subAverage.toFun = fun x => F.1 x - c := by
    funext x
    rw [← hc]
    exact PDE.W1pFunction.subAverage_apply u x
  have hgradfun : u.subAverage.grad = w.grad := by
    funext x
    exact PDE.W1pFunction.subAverage_grad u x
  rw [hfun, hgradfun, show PDE.euclideanBall z T = ball z T from hU.symm] at hP
  have hmemA : MemLp (fun x => F.1 x - c) 2 (ballMeasure z T) :=
    (Lp.memLp F.1).sub (memLp_const c)
  have hmemB : MemLp (fun x => PDE.vecEuclideanNorm (w.grad x)) 2 (ballMeasure z T) :=
    w.gradient_square_integrable
  have hAfin := hmemA.eLpNorm_ne_top
  have hBfin := hmemB.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin) hP
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
  rw [mul_pow, sq_toReal_eLpNorm_two hmemA, sq_toReal_eLpNorm_two hmemB] at hsq
  have hB : ∫ x in ball z T, PDE.vecEuclideanNorm (w.grad x) ^ 2 = pairGradEnergy F := by
    rw [← toPair_ofPair F hF, ← w.integral_euclideanSq_grad]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show Real.sqrt (euclideanSq (w.grad x)) ^ 2 = euclideanSq (w.grad x)
    rw [Real.sq_sqrt (zero_le_euclideanSq (w.grad x))]
  rw [hB] at hsq
  exact hsq

/-! ## The mean of the potential -/

/-- The constant function `1` in `L²(B_T(z))`. -/
def oneLp (z : Vec d) (T : ℝ) : Lp ℝ 2 (ballMeasure z T) := (memLp_const (1 : ℝ)).toLp _

theorem norm_oneLp_sq (z : Vec d) (T : ℝ) : ‖oneLp z T‖ ^ 2 = volume.real (ball z T) := by
  rw [oneLp, norm_toLp_sq_eq_integral]
  simp

/-- The Gaussian observation of `1` is bounded below on the observation ball. -/
theorem inner_heatLp_oneLp_ge {S σ θ : ℝ} (hσS : σ * S ≠ 0) {y : Vec d}
    (hy : y ∈ ball z (S / θ)) :
    heatKernelPeak d (σ * S) * Real.exp (-((T + S / θ) ^ 2) / (4 * (σ * S) ^ 2)) *
        volume.real (ball z T) ≤ ⟪heatLp z T y hσS, oneLp z T⟫_ℝ := by
  rw [inner_heatLp]
  have h1 : (∫ x in ball z T, heatKernel y (σ * S) x * (oneLp z T) x) =
      ∫ x in ball z T, heatKernel y (σ * S) x := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_const (μ := ballMeasure z T) (p := 2) (1 : ℝ)).coeFn_toLp] with x hx
    rw [oneLp, hx, mul_one]
  rw [h1]
  have hint : Integrable (fun x => heatKernel y (σ * S) x) (ballMeasure z T) :=
    (memLp_heatKernel (z := z) (T := T) y hσS).integrable one_le_two
  have hmono := integral_mono_ae (integrable_const
      (heatKernelPeak d (σ * S) * Real.exp (-((T + S / θ) ^ 2) / (4 * (σ * S) ^ 2)))) hint
    (by
      filter_upwards [ae_restrict_mem (measurableSet_ball z T)] with x hx
      refine heatKernel_ge y hσS ?_
      have h2 := euclideanNorm_sub_le_sub_add x y z
      rw [euclideanNorm_sub_comm z y] at h2
      have h3 : euclideanNorm (y - z) < S / θ := hy
      have h4 : euclideanNorm (x - z) < T := hx
      linarith)
  rw [integral_const, smul_eq_mul] at hmono
  simpa [mul_comm] using hmono

/-- **Coercivity.** On the admissible pairs, the sublevel sets of the objective are bounded for
the quadratic gauge `‖u‖² + ∑_i ‖g_i‖²`. -/
theorem bddAbove_pairGauge_sublevel (hT : 0 < T) {S σ θ C : ℝ} (hσS : σ * S ≠ 0)
    (hSθ : 0 < S / θ) (i : Fin d) (t : ℝ) :
    BddAbove (pairGauge '' {F | F ∈ admissiblePairs a z T C ∧
      pairObjective z T S σ θ i F ≤ t}) := by
  set M := heatLpBound z T (σ * S)
  set P := 2 ^ d * (2 * T)
  set V := volume.real (ball z T)
  set V' := volume.real (ball z (S / θ))
  set ε := heatKernelPeak d (σ * S) * Real.exp (-((T + S / θ) ^ 2) / (4 * (σ * S) ^ 2)) * V
  have hV : 0 < V := volume_real_ball_pos z hT
  have hV' : 0 < V' := volume_real_ball_pos z hSθ
  have hε : 0 < ε := mul_pos (mul_pos (heatKernelPeak_pos hσS) (Real.exp_pos _)) hV
  set ℓ := coordinateLp z T i
  set K := 3 * (M * ‖ℓ‖) ^ 2 + 3 * (M ^ 2 * (P ^ 2 * (C ^ 2 * V)))
  refine ⟨2 * (P ^ 2 * (C ^ 2 * V)) + 2 * ((3 * t + K) / ε ^ 2 * V) + C ^ 2 * V, ?_⟩
  rintro _ ⟨F, ⟨hFK, hFt⟩, rfl⟩
  set u := F.1
  set c := ⨍ y in ball z T, u y
  set cLp : Lp ℝ 2 (ballMeasure z T) := c • oneLp z T
  have hE : pairGradEnergy F ≤ C ^ 2 * V := hFK.2
  have hdiff : ‖u - cLp‖ ^ 2 = ∫ x in ball z T, (u x - c) ^ 2 := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u cLp, Lp.coeFn_smul c (oneLp z T),
      (memLp_const (μ := ballMeasure z T) (p := 2) (1 : ℝ)).coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, oneLp, h3, smul_eq_mul, mul_one]
  have hpoinc : ‖u - cLp‖ ^ 2 ≤ P ^ 2 * (C ^ 2 * V) := by
    rw [hdiff]
    exact (integral_sub_average_sq_le F hFK.1 hT).trans
      (mul_le_mul_of_nonneg_left hE (sq_nonneg _))
  have hpt : ∀ y ∈ ball z (S / θ),
      c ^ 2 * ε ^ 2 ≤ 3 * ⟪heatLp z T y hσS, u - ℓ⟫_ℝ ^ 2 + K := by
    intro y hy
    set φ := heatLp z T y hσS
    have hid : c * ⟪φ, oneLp z T⟫_ℝ = ⟪φ, u - ℓ⟫_ℝ + ⟪φ, ℓ⟫_ℝ - ⟪φ, u - cLp⟫_ℝ := by
      simp only [cLp, inner_sub_right, real_inner_smul_right]; ring
    have hlow : ε ≤ ⟪φ, oneLp z T⟫_ℝ := inner_heatLp_oneLp_ge hσS hy
    have h1 : c ^ 2 * ε ^ 2 ≤ (c * ⟪φ, oneLp z T⟫_ℝ) ^ 2 := by
      rw [mul_pow c ⟪φ, oneLp z T⟫_ℝ 2]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hlow 2) (sq_nonneg c)
    have hβ : ⟪φ, ℓ⟫_ℝ ^ 2 ≤ (M * ‖ℓ‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_inner_heatLp_le y hσS ℓ) 2
    have hγ : ⟪φ, u - cLp⟫_ℝ ^ 2 ≤ M ^ 2 * (P ^ 2 * (C ^ 2 * V)) := by
      rw [← sq_abs]
      refine (pow_le_pow_left₀ (abs_nonneg _) (abs_inner_heatLp_le y hσS (u - cLp)) 2).trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hpoinc (sq_nonneg _)
    rw [hid] at h1
    nlinarith [sq_nonneg (⟪φ, u - ℓ⟫_ℝ - ⟪φ, ℓ⟫_ℝ), sq_nonneg (⟪φ, u - ℓ⟫_ℝ + ⟪φ, u - cLp⟫_ℝ),
      sq_nonneg (⟪φ, ℓ⟫_ℝ + ⟪φ, u - cLp⟫_ℝ)]
  have hint : ∫ y in ball z (S / θ), c ^ 2 * ε ^ 2 ≤
      ∫ y in ball z (S / θ), (3 * ⟪heatLp z T y hσS, u - ℓ⟫_ℝ ^ 2 + K) :=
    setIntegral_mono_on (integrableOn_const (C := c ^ 2 * ε ^ 2)
      (volume_ball_lt_top z (S / θ)).ne)
    (((integrableOn_inner_heatLp_sq hσS (S / θ) (u - ℓ)).const_mul 3).add
      (integrableOn_const (C := K) (volume_ball_lt_top z (S / θ)).ne))
    (measurableSet_ball z (S / θ)) hpt
  rw [setIntegral_const,
    integral_add ((integrableOn_inner_heatLp_sq hσS (S / θ) (u - ℓ)).const_mul 3)
      (integrableOn_const (C := K) (volume_ball_lt_top z (S / θ)).ne), integral_const_mul,
    setIntegral_const, smul_eq_mul, smul_eq_mul] at hint
  have hobj : pairObjective z T S σ θ i F =
      V'⁻¹ * ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, u - ℓ⟫_ℝ ^ 2 := by
    rw [pairObjective_eq hσS, setAverage_eq, smul_eq_mul]
  have hI : ∫ y in ball z (S / θ), ⟪heatLp z T y hσS, u - ℓ⟫_ℝ ^ 2 ≤ V' * t := by
    have := hFt
    rw [hobj, inv_mul_le_iff₀ hV'] at this
    exact this
  have hc2 : c ^ 2 * ε ^ 2 ≤ 3 * t + K := by
    have h := hint.trans (add_le_add_left (mul_le_mul_of_nonneg_left hI (by norm_num)) _)
    have h' : V' * (c ^ 2 * ε ^ 2) ≤ V' * (3 * t + K) := by linarith
    exact le_of_mul_le_mul_left h' hV'
  have hc2' : c ^ 2 ≤ (3 * t + K) / ε ^ 2 := by
    rw [le_div_iff₀ (pow_pos hε 2)]; exact hc2
  have hcLp : ‖cLp‖ ^ 2 = c ^ 2 * V := by
    rw [norm_smul, mul_pow, norm_oneLp_sq, Real.norm_eq_abs, sq_abs]
  have hu : ‖u‖ ^ 2 ≤ 2 * ‖u - cLp‖ ^ 2 + 2 * ‖cLp‖ ^ 2 := by
    have h1 : ‖u‖ ≤ ‖u - cLp‖ + ‖cLp‖ := by
      calc ‖u‖ = ‖(u - cLp) + cLp‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - cLp‖ + ‖cLp‖ := norm_add_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖u - cLp‖ - ‖cLp‖)]
  show ‖F.1‖ ^ 2 + pairGradEnergy F ≤ _
  have hcV : c ^ 2 * V ≤ (3 * t + K) / ε ^ 2 * V := mul_le_mul_of_nonneg_right hc2' hV.le
  nlinarith

end QSH
