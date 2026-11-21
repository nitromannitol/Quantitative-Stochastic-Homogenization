import QuantitativeStochasticHomogenization.Ch04.Sec04.ConcaveEnergyPerturbation
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedEnergyJointMeasurability

/-!
# Lemma 4.22: from the approximation of `A₁` by `V_r^δ` to the localization error

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.22 and its proof, (4.104).

On the ball `B_T(z)`, the energy `∫_{B_T(z)} Φ_{z,r} (-½ g·a g - p·a g + q·g)` of a gradient field
`g` with `L²` components is a concave quadratic energy of the rescaled field `√Φ_{z,r} g`: its
quadratic part is the energy form of `a`, bounded by `d²Λ` and bounded below by the square of the
norm, and its linear part is bounded. Hence, by `IsConcaveEnergy.abs_sSup_sub_sSup_le`, if every
gradient of `A₁` of bounded weighted norm is `η`-close in the weighted norm on `B_T(z)` to the
span `V_r^δ` of a localized basis and conversely, and if the energies of the elements of `A₁` on
`ℝ^d` and on `B_T(z)` differ by at most `τ` (the tail (4.104)), then
`|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)| ≤ C η + τ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {z : Vec d} {T r : ℝ}

/-! ## The rescaling by `√Φ_{z,r}` -/

/-- The square root of the heat kernel `Φ_{z,r}`. -/
def sqrtHeat (z : Vec d) (r : ℝ) (x : Vec d) : ℝ := Real.sqrt (heatKernel z r x)

theorem sqrtHeat_mul_self (hr : r ≠ 0) (x : Vec d) :
    sqrtHeat z r x * sqrtHeat z r x = heatKernel z r x :=
  Real.mul_self_sqrt (heatKernel_pos z hr x).le

theorem continuous_sqrtHeat (z : Vec d) (r : ℝ) : Continuous (sqrtHeat z r) :=
  Real.continuous_sqrt.comp (continuous_heatKernel_right z r)

theorem abs_sqrtHeat_le (hr : r ≠ 0) (x : Vec d) :
    |sqrtHeat z r x| ≤ Real.sqrt (heatKernelPeak d r) := by
  unfold sqrtHeat
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (heatKernel_le z hr x)

theorem memLp_sqrtHeat_mul (hr : r ≠ 0) {f : Vec d → ℝ} (hf : MemLp f 2 (ballMeasure z T)) :
    MemLp (fun x => sqrtHeat z r x * f x) 2 (ballMeasure z T) := by
  refine (hf.const_mul (Real.sqrt (heatKernelPeak d r))).of_le
    ((continuous_sqrtHeat z r).aestronglyMeasurable.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg (heatKernelPeak d r))]
  exact mul_le_mul_of_nonneg_right (abs_sqrtHeat_le hr x) (abs_nonneg _)

/-- The rescaling `u ↦ √Φ_{z,r} u` on `L²(B_T(z))`. -/
def scaleLp (hr : r ≠ 0) (u : Lp ℝ 2 (ballMeasure z T)) : Lp ℝ 2 (ballMeasure z T) :=
  (memLp_sqrtHeat_mul hr (Lp.memLp u)).toLp _

theorem scaleLp_ae (hr : r ≠ 0) (u : Lp ℝ 2 (ballMeasure z T)) :
    (scaleLp hr u : Vec d → ℝ) =ᵐ[ballMeasure z T] fun x => sqrtHeat z r x * u x :=
  (memLp_sqrtHeat_mul hr (Lp.memLp u)).coeFn_toLp

/-- `√Φ_{z,r}` as an element of `L²(B_T(z))`. -/
def sqrtHeatLp (z : Vec d) (T : ℝ) (hr : r ≠ 0) : Lp ℝ 2 (ballMeasure z T) :=
  (memLp_of_continuous_of_bound (continuous_sqrtHeat z r) (abs_sqrtHeat_le (z := z) hr)).toLp _

theorem sqrtHeatLp_ae (hr : r ≠ 0) :
    (sqrtHeatLp z T hr : Vec d → ℝ) =ᵐ[ballMeasure z T] sqrtHeat z r :=
  (memLp_of_continuous_of_bound (continuous_sqrtHeat z r) (abs_sqrtHeat_le (z := z) hr)).coeFn_toLp

/-! ## The concave energy on rescaled gradient tuples -/

/-- The quadratic part `B(h, h') = ∑ ∫ a_{kl} h_l h'_k`. -/
def tupleForm (a : CoefficientField d Λ) (h h' : Fin d → Lp ℝ 2 (ballMeasure z T)) : ℝ :=
  energyForm a ((0 : Lp ℝ 2 (ballMeasure z T)), h) (0, h')

/-- The linear part `ℓ(h) = ∑ -p_k ∫ a_{kl} h_l √Φ + ∑ q_k ∫ h_k √Φ`. -/
def tupleLinear (a : CoefficientField d Λ) (hr : r ≠ 0) (p q : Vec d)
    (h : Fin d → Lp ℝ 2 (ballMeasure z T)) : ℝ :=
  (∑ k, ∑ l, -p k * weightedPairing (ballMeasure z T) (fun x => a x k l) (h l)
      (sqrtHeatLp z T hr)) +
    ∑ k, q k * weightedPairing (ballMeasure z T) (fun _ => 1) (h k) (sqrtHeatLp z T hr)

/-- The constant of the linear part. -/
def tupleLinearConstant (d : ℕ) (Λ : ℝ) (p q : Vec d) (s : ℝ) : ℝ :=
  ((∑ k, |p k|) * d * Λ + ∑ k, |q k|) * s

theorem isConcaveEnergy_tuple (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (hr : r ≠ 0)
    (p q : Vec d) :
    IsConcaveEnergy (tupleForm (z := z) (T := T) a) (tupleLinear a hr p q) ((d : ℝ) ^ 2 * Λ)
      (tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖) := by
  have hpair : ∀ h h' : Fin d → Lp ℝ 2 (ballMeasure z T),
      (((0 : Lp ℝ 2 (ballMeasure z T)), h) + (0, h') : PairSpace d z T) = (0, h + h') := by
    intro h h'; simp
  have hsmul : ∀ (c : ℝ) (h : Fin d → Lp ℝ 2 (ballMeasure z T)),
      (c • ((0 : Lp ℝ 2 (ballMeasure z T)), h) : PairSpace d z T) = (0, c • h) := by
    intro c h; simp
  have hnorm : ∀ h : Fin d → Lp ℝ 2 (ballMeasure z T),
      ‖(((0 : Lp ℝ 2 (ballMeasure z T)), h) : PairSpace d z T)‖ = ‖h‖ := by
    intro h; rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have hρ := fun k l => aestronglyMeasurable_coefficient_ball (z := z) (T := T) a k l
  have hM := fun k l => coefficient_bound (z := z) (T := T) a k l
  have h1ρ : AEStronglyMeasurable (fun _ : Vec d => (1 : ℝ)) (ballMeasure z T) :=
    aestronglyMeasurable_const
  have h1M : ∀ᵐ x ∂ballMeasure z T, |(fun _ : Vec d => (1 : ℝ)) x| ≤ 1 :=
    Eventually.of_forall fun x => by simp
  refine
    { add_left := fun g g' h => ?_
      smul_left := fun c g h => ?_
      symm := fun g h => energyForm_symm a _ _
      coercive := fun g => ?_
      bound := fun g h => ?_
      linear_sub := fun g h => ?_
      linear_bound := fun g => ?_
      L_nonneg := ?_
      Λ_nonneg := mul_nonneg (sq_nonneg _) hΛ }
  · simp only [tupleForm]
    rw [← energyForm_add_left, hpair]
  · simp only [tupleForm]
    rw [← energyForm_smul_left, hsmul]
  · have h1 := pairGradEnergy_le_energyForm a (((0 : Lp ℝ 2 (ballMeasure z T)), g) :
      PairSpace d z T)
    have h2 : ‖g‖ ^ 2 ≤ pairGradEnergy (((0 : Lp ℝ 2 (ballMeasure z T)), g) : PairSpace d z T) := by
      have := isQuadraticGauge_pairGauge.norm_sq_le
        (((0 : Lp ℝ 2 (ballMeasure z T)), g) : PairSpace d z T)
      rw [hnorm] at this
      simpa [pairGauge] using this
    exact h2.trans h1
  · have := abs_energyForm_le a hΛ (((0 : Lp ℝ 2 (ballMeasure z T)), g) : PairSpace d z T)
      ((0, h) : PairSpace d z T)
    rwa [hnorm, hnorm] at this
  · simp only [tupleLinear]
    have e1 : ∀ k l, weightedPairing (ballMeasure z T) (fun x => a x k l) ((g - h) l)
        (sqrtHeatLp z T hr) = weightedPairing (ballMeasure z T) (fun x => a x k l) (g l)
          (sqrtHeatLp z T hr) - weightedPairing (ballMeasure z T) (fun x => a x k l) (h l)
          (sqrtHeatLp z T hr) := by
      intro k l
      rw [Pi.sub_apply, sub_eq_add_neg, weightedPairing_add_left (hρ k l) (hM k l),
        ← neg_one_smul ℝ (h l), weightedPairing_smul_left]
      ring
    have e2 : ∀ k, weightedPairing (ballMeasure z T) (fun _ => 1) ((g - h) k)
        (sqrtHeatLp z T hr) = weightedPairing (ballMeasure z T) (fun _ => 1) (g k)
          (sqrtHeatLp z T hr) - weightedPairing (ballMeasure z T) (fun _ => 1) (h k)
          (sqrtHeatLp z T hr) := by
      intro k
      rw [Pi.sub_apply, sub_eq_add_neg, weightedPairing_add_left h1ρ h1M,
        ← neg_one_smul ℝ (h k), weightedPairing_smul_left]
      ring
    simp only [e1, e2, mul_sub, Finset.sum_sub_distrib]
    ring
  · set s := ‖sqrtHeatLp z T hr‖
    have hs : 0 ≤ s := norm_nonneg _
    have hgk : ∀ k, ‖g k‖ ≤ ‖g‖ := fun k => norm_le_pi_norm g k
    have hA : |∑ k, ∑ l, -p k * weightedPairing (ballMeasure z T) (fun x => a x k l) (g l)
        (sqrtHeatLp z T hr)| ≤ (∑ k, |p k|) * d * Λ * ‖g‖ * s := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ k, |∑ l, -p k * weightedPairing (ballMeasure z T) (fun x => a x k l) (g l)
          (sqrtHeatLp z T hr)| ≤ |p k| * (d * (Λ * (‖g‖ * s))) := by
        intro k
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ l, |-p k * weightedPairing (ballMeasure z T) (fun x => a x k l) (g l)
              (sqrtHeatLp z T hr)| ≤ ∑ _l : Fin d, |p k| * (Λ * (‖g‖ * s)) := by
              refine Finset.sum_le_sum fun l _ => ?_
              rw [abs_mul, abs_neg]
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              refine (abs_weightedPairing_le (hρ k l) hΛ (hM k l) _ _).trans ?_
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hgk l) hs) hΛ
          _ = |p k| * (d * (Λ * (‖g‖ * s))) := by simp; ring
      calc ∑ k, |∑ l, -p k * weightedPairing (ballMeasure z T) (fun x => a x k l) (g l)
            (sqrtHeatLp z T hr)| ≤ ∑ k, |p k| * (d * (Λ * (‖g‖ * s))) :=
            Finset.sum_le_sum fun k _ => this k
        _ = (∑ k, |p k|) * d * Λ * ‖g‖ * s := by rw [← Finset.sum_mul]; ring
    have hB : |∑ k, q k * weightedPairing (ballMeasure z T) (fun _ => 1) (g k)
        (sqrtHeatLp z T hr)| ≤ (∑ k, |q k|) * ‖g‖ * s := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |q k * weightedPairing (ballMeasure z T) (fun _ => 1) (g k) (sqrtHeatLp z T hr)|
          ≤ ∑ k, |q k| * (‖g‖ * s) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine (abs_weightedPairing_le h1ρ zero_le_one h1M _ _).trans ?_
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right (hgk k) hs
        _ = (∑ k, |q k|) * ‖g‖ * s := by rw [← Finset.sum_mul]; ring
    simp only [tupleLinear, tupleLinearConstant]
    refine (abs_add_le _ _).trans ?_
    nlinarith [hA, hB]
  · exact mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ =>
      abs_nonneg _) (Nat.cast_nonneg d)) hΛ) (Finset.sum_nonneg fun k _ => abs_nonneg _))
      (norm_nonneg _)

/-! ## The energy identity -/

theorem weightedPairing_heat_eq (a : CoefficientField d Λ) (hr : r ≠ 0) (k l : Fin d)
    (u v : Lp ℝ 2 (ballMeasure z T)) :
    weightedPairing (ballMeasure z T) (heatCoefficient a z r k l) u v =
      weightedPairing (ballMeasure z T) (fun x => a x k l) (scaleLp hr v) (scaleLp hr u) := by
  unfold weightedPairing
  refine integral_congr_ae ?_
  filter_upwards [scaleLp_ae (z := z) (T := T) hr u, scaleLp_ae (z := z) (T := T) hr v] with x hu hv
  rw [hu, hv, heatCoefficient, ← sqrtHeat_mul_self hr x]
  ring

theorem weightedPairing_heat_one_eq (a : CoefficientField d Λ) (hr : r ≠ 0) (k l : Fin d)
    (u : Lp ℝ 2 (ballMeasure z T)) :
    weightedPairing (ballMeasure z T) (heatCoefficient a z r k l) u (oneLp z T) =
      weightedPairing (ballMeasure z T) (fun x => a x k l) (scaleLp hr u) (sqrtHeatLp z T hr) := by
  unfold weightedPairing
  refine integral_congr_ae ?_
  filter_upwards [scaleLp_ae (z := z) (T := T) hr u, sqrtHeatLp_ae (z := z) (T := T) hr,
    (memLp_const (μ := ballMeasure z T) (p := 2) (1 : ℝ)).coeFn_toLp] with x hu hs h1
  rw [hu, hs, oneLp, h1, heatCoefficient, ← sqrtHeat_mul_self hr x]
  ring

theorem weightedPairing_heatKernel_one_eq (hr : r ≠ 0) (u : Lp ℝ 2 (ballMeasure z T)) :
    weightedPairing (ballMeasure z T) (heatKernel z r) u (oneLp z T) =
      weightedPairing (ballMeasure z T) (fun _ => 1) (scaleLp hr u) (sqrtHeatLp z T hr) := by
  unfold weightedPairing
  refine integral_congr_ae ?_
  filter_upwards [scaleLp_ae (z := z) (T := T) hr u, sqrtHeatLp_ae (z := z) (T := T) hr,
    (memLp_const (μ := ballMeasure z T) (p := 2) (1 : ℝ)).coeFn_toLp] with x hu hs h1
  rw [hu, hs, oneLp, h1, ← sqrtHeat_mul_self hr x]
  ring

/-- **The energy identity**: the weighted energy of a gradient tuple is the concave energy of its
rescaling by `√Φ_{z,r}`. -/
theorem pairEnergy_eq_tuple (a : CoefficientField d Λ) (hr : r ≠ 0) (p q : Vec d)
    (G : Fin d → Lp ℝ 2 (ballMeasure z T)) :
    pairEnergy a z T r p q G =
      -(1 / 2 : ℝ) * tupleForm a (fun k => scaleLp hr (G k)) (fun k => scaleLp hr (G k)) +
        tupleLinear a hr p q (fun k => scaleLp hr (G k)) := by
  unfold pairEnergy tupleForm tupleLinear energyForm
  dsimp only
  simp only [weightedPairing_heat_one_eq a hr]
  simp only [weightedPairing_heat_eq a hr, weightedPairing_heatKernel_one_eq hr]
  have e : ∀ (X Y : Fin d → Fin d → ℝ) (Z : Fin d → ℝ),
      (∑ k, ∑ l, (-(1 / 2 : ℝ) * X k l - p k * Y k l)) + ∑ k, q k * Z k =
        -(1 / 2 : ℝ) * (∑ k, ∑ l, X k l) + ((∑ k, ∑ l, -p k * Y k l) + ∑ k, q k * Z k) := by
    intro X Y Z
    have h : (∑ k, ∑ l, (-(1 / 2 : ℝ) * X k l - p k * Y k l)) =
        -(1 / 2 : ℝ) * (∑ k, ∑ l, X k l) + ∑ k, ∑ l, -p k * Y k l := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [h]
    ring
  exact e _ _ _

theorem scaleLp_zero (hr : r ≠ 0) : scaleLp (z := z) (T := T) hr 0 = 0 := by
  refine Lp.ext ?_
  filter_upwards [scaleLp_ae (z := z) (T := T) hr 0, Lp.coeFn_zero ℝ 2 (ballMeasure z T)] with
    x h1 h2
  rw [h1, h2]
  simp

/-! ## The zero element of `A₁` and the gradients of `A₁` on the ball -/

/-- The zero `a`-harmonic function. -/
def zeroHarmonicA1' (a : CoefficientField d Λ) : HarmonicA1 a where
  potential := fun _ => 0
  grad := fun _ => 0
  weak_gradient := fun i => ⟨locallyIntegrableOn_const 0, locallyIntegrableOn_const 0,
    fun φ _ => by simp⟩
  local_energy := fun R _ => ⟨memLp_const 0, by simp [euclideanNorm, euclideanSq, dot]⟩
  harmonic := ⟨fun k => by simpa using locallyIntegrableOn_const (0 : ℝ),
    locallyIntegrableOn_const 0, fun φ _ => by simp [dot]⟩
  growth := by simp

theorem ball_subset_originBall (z : Vec d) (T : ℝ) :
    ball z T ⊆ ball 0 (euclideanNorm z + |T| + 1) := by
  intro y hy
  show euclideanNorm (y - 0) < _
  rw [sub_zero]
  have h1 := euclideanNorm_add_le (y - z) z
  rw [sub_add_cancel] at h1
  have h2 : euclideanNorm (y - z) < T := hy
  have h3 : T ≤ |T| := le_abs_self T
  linarith

theorem HarmonicA1.memLp_grad_ball {a : CoefficientField d Λ} (w : HarmonicA1 a) (k : Fin d) :
    MemLp (fun x => w.grad x k) 2 (ballMeasure z T) := by
  have hR : 0 < euclideanNorm z + |T| + 1 := by
    have := euclideanNorm_nonneg z; have := abs_nonneg T; linarith
  have hball := (w.local_energy _ hR).2.mono_measure
    (Measure.restrict_mono (ball_subset_originBall z T) le_rfl)
  refine hball.of_le ?_ (Eventually.of_forall fun x => ?_)
  · exact ((w.weak_gradient k).2.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (Set.subset_univ _) le_rfl))
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)]
    exact abs_apply_le_euclideanNorm (w.grad x) k

/-- The `L²(B_T(z))` classes of the gradient components of an element of `A₁`. -/
def HarmonicA1.ballGrad {a : CoefficientField d Λ} (w : HarmonicA1 a) (z : Vec d) (T : ℝ)
    (k : Fin d) : Lp ℝ 2 (ballMeasure z T) :=
  (w.memLp_grad_ball (z := z) (T := T) k).toLp _

end QSH
