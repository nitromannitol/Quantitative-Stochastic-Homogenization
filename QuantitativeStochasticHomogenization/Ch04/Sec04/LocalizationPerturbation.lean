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

theorem ballGrad_zero (a : CoefficientField d Λ) (k : Fin d) :
    (zeroHarmonicA1' a).ballGrad z T k = 0 := by
  refine Lp.ext ?_
  filter_upwards [((zeroHarmonicA1' a).memLp_grad_ball (z := z) (T := T) k).coeFn_toLp,
    Lp.coeFn_zero ℝ 2 (ballMeasure z T)] with x h1 h2
  rw [HarmonicA1.ballGrad, h1, h2]
  rfl

/-! ## Lemma 4.22 -/

/-- Suprema of two pointwise `τ`-close real families differ by at most `τ`. -/
theorem abs_sSup_range_sub_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ}
    (hg : BddAbove (Set.range g)) {τ : ℝ} (h : ∀ i, |f i - g i| ≤ τ) :
    |sSup (Set.range f) - sSup (Set.range g)| ≤ τ := by
  have hf : BddAbove (Set.range f) := by
    obtain ⟨M, hM⟩ := hg
    refine ⟨M + τ, ?_⟩
    rintro _ ⟨i, rfl⟩
    have := hM ⟨i, rfl⟩
    linarith [(abs_le.1 (h i)).2]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine csSup_le (Set.range_nonempty f) ?_
    rintro _ ⟨i, rfl⟩
    have := le_csSup hg ⟨i, rfl⟩
    linarith [(abs_le.1 (h i)).2]
  · rw [sub_le_iff_le_add]
    refine csSup_le (Set.range_nonempty g) ?_
    rintro _ ⟨i, rfl⟩
    have := le_csSup hf ⟨i, rfl⟩
    linarith [(abs_le.1 (h i)).1]

/-- The energy `∫ Φ_{z,r} (-½ ∇w·a∇w - p·a∇w + q·∇w)` of an element of `A₁`. -/
def a1Energy (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) (p q : Vec d) (w : HarmonicA1 a) :
    ℝ :=
  ∫ x, heatKernel z r x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
    dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))

/-- The same energy restricted to `B_T(z)`. -/
def a1BallEnergy (a : CoefficientField d Λ) (z : Vec d) (T r : ℝ) (p q : Vec d)
    (w : HarmonicA1 a) : ℝ :=
  ∫ x in ball z T, heatKernel z r x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
    dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))

theorem J1Heat_eq_sSup_range (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) (p q : Vec d) :
    J1Heat a z r p q = sSup (Set.range (a1Energy a z r p q)) := by
  unfold J1Heat J1 a1Energy
  congr 1
  ext e
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.symm⟩, fun ⟨w, hw⟩ => ⟨w, hw.symm⟩⟩

theorem a1BallEnergy_eq (a : CoefficientField d Λ) (hr : r ≠ 0) (p q : Vec d)
    (w : HarmonicA1 a) :
    a1BallEnergy a z T r p q w =
      -(1 / 2 : ℝ) * tupleForm a (fun k => scaleLp hr (w.ballGrad z T k))
        (fun k => scaleLp hr (w.ballGrad z T k)) +
        tupleLinear a hr p q (fun k => scaleLp hr (w.ballGrad z T k)) := by
  rw [← pairEnergy_eq_tuple a hr p q, a1BallEnergy]
  refine integral_energy_eq_pairEnergy a hr p q _ ?_
  have h := ae_all_iff.2 fun k => (w.memLp_grad_ball (z := z) (T := T) k).coeFn_toLp
  filter_upwards [h] with x hx
  funext k
  exact (hx k).symm

/-- The whole-space and ball suprema of the energies of `A₁` differ by at most `τ` when the
near maximizers on `ℝ^d` lie in the bounded part, where the two energies differ by at most `τ`. -/
theorem abs_sSup_a1Energy_sub_le {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ) (hr : r ≠ 0)
    (p q : Vec d) {τ : ℝ}
    (htail : ∀ w : HarmonicA1 a,
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
      |a1Energy a z r p q w - a1BallEnergy a z T r p q w| ≤ τ)
    (hnear : ∀ w : HarmonicA1 a, -(1 / 4 : ℝ) ≤ a1Energy a z r p q w →
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) :
    |sSup (Set.range (a1Energy a z r p q)) - sSup (Set.range (a1BallEnergy a z T r p q))| ≤ τ := by
  set L := tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖
  have hE := isConcaveEnergy_tuple (z := z) (T := T) a hΛ hr p q
  have hball : ∀ w : HarmonicA1 a, a1BallEnergy a z T r p q w ≤ L ^ 2 / 2 := fun w => by
    rw [a1BallEnergy_eq a hr p q w]; exact hE.energy_le _
  have hballnorm : ∀ w : HarmonicA1 a, -(1 / 2 : ℝ) ≤ a1BallEnergy a z T r p q w →
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ 2 * L + 1 := fun w hw => by
    rw [a1BallEnergy_eq a hr p q w] at hw; exact hE.norm_le_of_energy_ge hw
  have hzero : a1Energy a z r p q (zeroHarmonicA1' a) = 0 := by
    simp [a1Energy, zeroHarmonicA1', dot]
  have hzeroB : a1BallEnergy a z T r p q (zeroHarmonicA1' a) = 0 := by
    simp [a1BallEnergy, zeroHarmonicA1', dot]
  have hbddB : BddAbove (Set.range (a1BallEnergy a z T r p q)) :=
    ⟨L ^ 2 / 2, by rintro _ ⟨w, rfl⟩; exact hball w⟩
  have hbddE : BddAbove (Set.range (a1Energy a z r p q)) := by
    refine ⟨max (-(1 / 4 : ℝ)) (L ^ 2 / 2 + τ), ?_⟩
    rintro _ ⟨w, rfl⟩
    by_cases hw : -(1 / 4 : ℝ) ≤ a1Energy a z r p q w
    · have h1 := (abs_le.1 (htail w (hnear w hw))).2
      have h2 := hball w
      exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (le_of_lt (not_le.1 hw))
  have hneE : (Set.range (a1Energy a z r p q)).Nonempty := ⟨_, zeroHarmonicA1' a, rfl⟩
  have hneB : (Set.range (a1BallEnergy a z T r p q)).Nonempty := ⟨_, zeroHarmonicA1' a, rfl⟩
  have hsupE0 : 0 ≤ sSup (Set.range (a1Energy a z r p q)) :=
    hzero ▸ le_csSup hbddE ⟨zeroHarmonicA1' a, rfl⟩
  have hsupB0 : 0 ≤ sSup (Set.range (a1BallEnergy a z T r p q)) :=
    hzeroB ▸ le_csSup hbddB ⟨zeroHarmonicA1' a, rfl⟩
  rw [abs_sub_le_iff]
  constructor
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    set ε' := min ε (1 / 4)
    have hε' : 0 < ε' := lt_min hε (by norm_num)
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := exists_lt_of_lt_csSup hneE
      (show sSup (Set.range (a1Energy a z r p q)) - ε' < _ by linarith)
    have hw' : -(1 / 4 : ℝ) ≤ a1Energy a z r p q w := by
      have : ε' ≤ 1 / 4 := min_le_right _ _
      linarith
    have h1 := (abs_le.1 (htail w (hnear w hw'))).2
    have h2 := le_csSup hbddB ⟨w, rfl⟩
    have : ε' ≤ ε := min_le_left _ _
    linarith
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    set ε' := min ε (1 / 4)
    have hε' : 0 < ε' := lt_min hε (by norm_num)
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := exists_lt_of_lt_csSup hneB
      (show sSup (Set.range (a1BallEnergy a z T r p q)) - ε' < _ by linarith)
    have hw' : -(1 / 2 : ℝ) ≤ a1BallEnergy a z T r p q w := by
      have : ε' ≤ 1 / 4 := min_le_right _ _
      linarith
    have h1 := (abs_le.1 (htail w (hballnorm w hw'))).1
    have h2 := le_csSup hbddE ⟨w, rfl⟩
    have : ε' ≤ ε := min_le_left _ _
    linarith

/-- **Lemma 4.22**: if the gradients of `A₁` of bounded weighted norm are, after rescaling by
`√Φ_{z,r}` on `B_T(z)`, `η`-close to the rescaled span of a localized basis and conversely, the
energies of the bounded part of `A₁` on `ℝ^d` and on `B_T(z)` differ by at most `τ`, and the
near maximizers on `ℝ^d` lie in the bounded part, then
`|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)| ≤ τ + C η`. -/
theorem abs_J1Heat_sub_localizedJ1_le {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ) (hr : r ≠ 0)
    {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C) (p q : Vec d) {η τ : ℝ} (hη : 0 ≤ η)
    (htail : ∀ w : HarmonicA1 a,
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
      |a1Energy a z r p q w - a1BallEnergy a z T r p q w| ≤ τ)
    (hnear : ∀ w : HarmonicA1 a, -(1 / 4 : ℝ) ≤ a1Energy a z r p q w →
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1)
    (hAV : ∀ w : HarmonicA1 a,
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
      ∃ c : Vec d, ‖(fun k => scaleLp hr (w.ballGrad z T k)) -
        (fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k))‖ ≤ η)
    (hVA : ∀ c : Vec d,
      ‖(fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
      ∃ w : HarmonicA1 a,
        ‖(fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k)) -
          (fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ η) :
    |J1Heat a z r p q - localizedJ1 W r p q| ≤
      τ + ((d : ℝ) ^ 2 * Λ * (2 * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) +
        η) / 2 + tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖) * η := by
  set L := tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖
  set E : (Fin d → Lp ℝ 2 (ballMeasure z T)) → ℝ := fun h =>
    -(1 / 2 : ℝ) * tupleForm a h h + tupleLinear a hr p q h
  have hE := isConcaveEnergy_tuple (z := z) (T := T) a hΛ hr p q
  set sg : HarmonicA1 a → Fin d → Lp ℝ 2 (ballMeasure z T) :=
    fun w k => scaleLp hr (w.ballGrad z T k)
  set sc : Vec d → Fin d → Lp ℝ 2 (ballMeasure z T) :=
    fun c k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k)
  set A := Set.range sg
  set V := Set.range sc
  have hA0 : (0 : Fin d → Lp ℝ 2 (ballMeasure z T)) ∈ A := by
    refine ⟨zeroHarmonicA1' a, ?_⟩
    funext k
    simp only [sg, ballGrad_zero, scaleLp_zero, Pi.zero_apply]
  have hV0 : (0 : Fin d → Lp ℝ 2 (ballMeasure z T)) ∈ V := by
    refine ⟨0, ?_⟩
    funext k
    simp only [sc, pairCombination, Pi.zero_apply, zero_smul, Finset.sum_const_zero, scaleLp_zero]
  have hAV' : ∀ g ∈ A, ‖g‖ ≤ 2 * L + 1 → ∃ h ∈ V, ‖g - h‖ ≤ η := by
    rintro _ ⟨w, rfl⟩ hw
    obtain ⟨c, hc⟩ := hAV w hw
    exact ⟨sc c, ⟨c, rfl⟩, hc⟩
  have hVA' : ∀ h ∈ V, ‖h‖ ≤ 2 * L + 1 → ∃ g ∈ A, ‖h - g‖ ≤ η := by
    rintro _ ⟨c, rfl⟩ hc
    obtain ⟨w, hw⟩ := hVA c hc
    exact ⟨sg w, ⟨w, rfl⟩, hw⟩
  have habs := hE.abs_sSup_sub_sSup_le hA0 hV0 hη hAV' hVA'
  have hrangeA : Set.range (a1BallEnergy a z T r p q) = E '' A := by
    show Set.range _ = E '' Set.range sg
    rw [← Set.range_comp]
    congr 1
    funext w
    exact a1BallEnergy_eq a hr p q w
  have hrangeV : localizedJ1 W r p q = sSup (E '' V) := by
    rw [localizedJ1_eq_sSup W hr p q]
    show sSup _ = sSup (E '' Set.range sc)
    rw [← Set.range_comp]
    congr 1
    congr 1
    funext c
    exact pairEnergy_eq_tuple a hr p q _
  have htailsup := abs_sSup_a1Energy_sub_le hΛ hr p q htail hnear
  rw [J1Heat_eq_sSup_range, hrangeV]
  rw [hrangeA] at htailsup
  calc |sSup (Set.range (a1Energy a z r p q)) - sSup (E '' V)|
      ≤ |sSup (Set.range (a1Energy a z r p q)) - sSup (E '' A)| +
        |sSup (E '' A) - sSup (E '' V)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add htailsup habs

/-! ## Near maximizers on the whole space lie in the bounded part -/

/-- The coefficient `c₀ = (∑|p_k|) d Λ + ∑ |q_k|` of the linear part of the integrand. -/
def linearCoefficient (d : ℕ) (Λ : ℝ) (p q : Vec d) : ℝ := (∑ k, |p k|) * d * Λ + ∑ k, |q k|

theorem energy_integrand_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (p q : Vec d) (x : Vec d)
    (g : Vec d) :
    -(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g) + dot q g ≤
      linearCoefficient d Λ p q ^ 2 / 2 := by
  have hquad : euclideanSq g ≤ dot g ((a x).mulVec g) := (a.elliptic x g).1
  have hgk : ∀ k, |g k| ≤ euclideanNorm g := fun k => abs_apply_le_euclideanNorm g k
  have hp : |dot p ((a x).mulVec g)| ≤ (∑ k, |p k|) * d * Λ * euclideanNorm g := by
    simp only [dot, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |p k * ∑ l, a x k l * g l| ≤ ∑ k, |p k| * (d * (Λ * euclideanNorm g)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ l, |a x k l * g l| ≤ ∑ _l : Fin d, Λ * euclideanNorm g := by
                refine Finset.sum_le_sum fun l _ => ?_
                rw [abs_mul]
                exact mul_le_mul (a.abs_apply_le x k l) (hgk l) (abs_nonneg _) hΛ
            _ = d * (Λ * euclideanNorm g) := by simp
      _ = (∑ k, |p k|) * d * Λ * euclideanNorm g := by rw [← Finset.sum_mul]; ring
  have hq : |dot q g| ≤ (∑ k, |q k|) * euclideanNorm g := by
    simp only [dot]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |q k * g k| ≤ ∑ k, |q k| * euclideanNorm g := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hgk k) (abs_nonneg _)
      _ = (∑ k, |q k|) * euclideanNorm g := by rw [← Finset.sum_mul]
  have hsq : euclideanSq g = euclideanNorm g ^ 2 := (euclideanNorm_sq g).symm
  have hn := euclideanNorm_nonneg g
  unfold linearCoefficient
  nlinarith [abs_le.1 hp, abs_le.1 hq,
    sq_nonneg (euclideanNorm g - ((∑ k, |p k|) * d * Λ + ∑ k, |q k|))]

/-- **Near maximizers on `ℝ^d` lie in the bounded part** when the Gaussian mass outside the ball
is small and the energies are integrable. -/
theorem norm_scaled_ballGrad_le_of_near {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ) (hr : r ≠ 0)
    (p q : Vec d) {ε₀ : ℝ}
    (hΦ : IntegrableOn (heatKernel z r) (ball z T)ᶜ volume)
    (hmass : ∫ x in (ball z T)ᶜ, heatKernel z r x ≤ ε₀)
    (hε₀ : linearCoefficient d Λ p q ^ 2 / 2 * ε₀ ≤ 1 / 4)
    (w : HarmonicA1 a)
    (hint : Integrable (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))))
    (hw : -(1 / 4 : ℝ) ≤ a1Energy a z r p q w) :
    ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
      2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 := by
  have hE := isConcaveEnergy_tuple (z := z) (T := T) a hΛ hr p q
  have hsplit := integral_add_compl (measurableSet_ball z T) hint
  have hout : (∫ x in (ball z T)ᶜ, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) ≤
      linearCoefficient d Λ p q ^ 2 / 2 * ε₀ := by
    calc _ ≤ ∫ x in (ball z T)ᶜ, heatKernel z r x * (linearCoefficient d Λ p q ^ 2 / 2) := by
          refine setIntegral_mono_on hint.integrableOn (hΦ.mul_const _)
            (measurableSet_ball z T).compl fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (energy_integrand_le a hΛ p q x _)
            (heatKernel_pos z hr x).le
      _ = linearCoefficient d Λ p q ^ 2 / 2 * ∫ x in (ball z T)ᶜ, heatKernel z r x := by
          rw [integral_mul_const]; ring
      _ ≤ linearCoefficient d Λ p q ^ 2 / 2 * ε₀ :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
  have hball : -(1 / 2 : ℝ) ≤ a1BallEnergy a z T r p q w := by
    unfold a1Energy at hw
    unfold a1BallEnergy
    linarith
  rw [a1BallEnergy_eq a hr p q w] at hball
  exact hE.norm_le_of_energy_ge hball

/-! ## The tail outside the ball for the bounded part -/

theorem abs_energy_integrand_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (p q : Vec d)
    (x : Vec d) (g : Vec d) :
    |-(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g) + dot q g| ≤
      ((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) * euclideanSq g +
        linearCoefficient d Λ p q / 2 := by
  have hgk : ∀ k, |g k| ≤ euclideanNorm g := fun k => abs_apply_le_euclideanNorm g k
  have hn := euclideanNorm_nonneg g
  have hsq : euclideanSq g = euclideanNorm g ^ 2 := (euclideanNorm_sq g).symm
  have hAg : ∀ u : Vec d, |dot u ((a x).mulVec g)| ≤
      (∑ k, |u k|) * d * Λ * euclideanNorm g := by
    intro u
    simp only [dot, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |u k * ∑ l, a x k l * g l| ≤ ∑ k, |u k| * (d * (Λ * euclideanNorm g)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ l, |a x k l * g l| ≤ ∑ _l : Fin d, Λ * euclideanNorm g := by
                refine Finset.sum_le_sum fun l _ => ?_
                rw [abs_mul]
                exact mul_le_mul (a.abs_apply_le x k l) (hgk l) (abs_nonneg _) hΛ
            _ = d * (Λ * euclideanNorm g) := by simp
      _ = (∑ k, |u k|) * d * Λ * euclideanNorm g := by rw [← Finset.sum_mul]; ring
  have hgg : |dot g ((a x).mulVec g)| ≤ d * Λ * euclideanSq g := by
    have h1 : dot g ((a x).mulVec g) ≤ Λ * euclideanSq g := (a.elliptic x g).2
    have h2 : 0 ≤ dot g ((a x).mulVec g) := (euclideanSq_nonneg g).trans (a.elliptic x g).1
    rw [abs_of_nonneg h2]
    have hd : (1 : ℝ) ≤ d ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · right; exact h
      · left; exact_mod_cast h
    rcases hd with hd | hd
    · nlinarith [euclideanSq_nonneg g]
    · subst hd
      have : euclideanSq g = 0 := by simp [euclideanSq, dot]
      have h3 : dot g ((a x).mulVec g) = 0 := by simp [dot]
      rw [h3]; simp
  have hp := hAg p
  have hq : |dot q g| ≤ (∑ k, |q k|) * euclideanNorm g := by
    simp only [dot]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |q k * g k| ≤ ∑ k, |q k| * euclideanNorm g := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hgk k) (abs_nonneg _)
      _ = (∑ k, |q k|) * euclideanNorm g := by rw [← Finset.sum_mul]
  have hc0 : 0 ≤ linearCoefficient d Λ p q := by
    unfold linearCoefficient
    exact add_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)
      (Nat.cast_nonneg d)) hΛ) (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hlin : |dot p ((a x).mulVec g)| + |dot q g| ≤ linearCoefficient d Λ p q * euclideanNorm g := by
    unfold linearCoefficient; nlinarith
  have hamgm : linearCoefficient d Λ p q * euclideanNorm g ≤
      linearCoefficient d Λ p q / 2 * euclideanSq g + linearCoefficient d Λ p q / 2 := by
    rw [hsq]; nlinarith [sq_nonneg (euclideanNorm g - 1)]
  calc |-(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g) + dot q g|
      ≤ (1 / 2 : ℝ) * |dot g ((a x).mulVec g)| + |dot p ((a x).mulVec g)| + |dot q g| := by
        have := abs_add_le (-(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g))
          (dot q g)
        have h2 := abs_sub (-(1 / 2 : ℝ) * dot g ((a x).mulVec g)) (dot p ((a x).mulVec g))
        rw [abs_mul, show |(-(1 / 2 : ℝ))| = 1 / 2 by norm_num] at h2
        linarith
    _ ≤ _ := by nlinarith

/-- **The tail (4.104) for the bounded part**: if the Gaussian energy of `∇w` outside `B_T(z)` is
at most `κ` times its energy inside, the energies of the bounded part of `A₁` on `ℝ^d` and on
`B_T(z)` differ by an explicit multiple of `κ` and of the Gaussian mass outside the ball. -/
theorem abs_a1Energy_sub_a1BallEnergy_le {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ) (hr : r ≠ 0)
    (p q : Vec d) {ε₀ κ : ℝ} (hκ : 0 ≤ κ)
    (hΦ : IntegrableOn (heatKernel z r) (ball z T)ᶜ volume)
    (hmass : ∫ x in (ball z T)ᶜ, heatKernel z r x ≤ ε₀)
    (w : HarmonicA1 a)
    (hint : Integrable (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))))
    (hint2 : IntegrableOn (fun x => heatKernel z r x * euclideanSq (w.grad x)) (ball z T)ᶜ volume)
    (houter : ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x) ≤
      κ * ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x))
    (hw : ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
      2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) :
    |a1Energy a z r p q w - a1BallEnergy a z T r p q w| ≤
      ((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
          (κ * (d * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) ^ 2)) +
        linearCoefficient d Λ p q / 2 * ε₀ := by
  set L := tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖
  set c0 := linearCoefficient d Λ p q
  have hc0 : 0 ≤ c0 := by
    simp only [c0, linearCoefficient]
    exact add_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)
      (Nat.cast_nonneg d)) hΛ) (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hsplit := integral_add_compl (measurableSet_ball z T) hint
  have hdiff : a1Energy a z r p q w - a1BallEnergy a z T r p q w =
      ∫ x in (ball z T)ᶜ, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)) := by
    unfold a1Energy a1BallEnergy
    linarith
  -- the energy inside the ball
  have hin : ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x) ≤
      d * (2 * L + 1) ^ 2 := by
    have hk : ∀ k, ‖scaleLp hr (w.ballGrad z T k)‖ ^ 2 =
        ∫ x in ball z T, heatKernel z r x * w.grad x k ^ 2 := by
      intro k
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [scaleLp_ae (z := z) (T := T) hr (w.ballGrad z T k),
        (w.memLp_grad_ball (z := z) (T := T) k).coeFn_toLp] with x h1 h2
      rw [h1, HarmonicA1.ballGrad, h2, mul_pow, sq (sqrtHeat z r x), sqrtHeat_mul_self hr]
    have hsum : ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x) =
        ∑ k, ‖scaleLp hr (w.ballGrad z T k)‖ ^ 2 := by
      simp_rw [hk]
      rw [← integral_finsetSum _ fun k _ => ?_]
      · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [euclideanSq, dot, Finset.mul_sum, sq]
      · have := (memLp_sqrtHeat_mul (z := z) (T := T) hr
          (w.memLp_grad_ball (z := z) (T := T) k)).integrable_sq
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only
        rw [mul_pow, sq (sqrtHeat z r x), sqrtHeat_mul_self hr]
    rw [hsum]
    calc ∑ k, ‖scaleLp hr (w.ballGrad z T k)‖ ^ 2 ≤ ∑ _k : Fin d, (2 * L + 1) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
            ((norm_le_pi_norm _ k).trans hw) 2
      _ = d * (2 * L + 1) ^ 2 := by simp
  have hout : ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x) ≤
      κ * (d * (2 * L + 1) ^ 2) := houter.trans (mul_le_mul_of_nonneg_left hin hκ)
  rw [hdiff]
  calc |∫ x in (ball z T)ᶜ, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))|
      ≤ ∫ x in (ball z T)ᶜ, |heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))| := abs_integral_le_integral_abs
    _ ≤ ∫ x in (ball z T)ᶜ, ((d * Λ / 2 + c0 / 2) * (heatKernel z r x * euclideanSq (w.grad x)) +
          c0 / 2 * heatKernel z r x) := by
        refine setIntegral_mono_on hint.integrableOn.abs
          ((hint2.const_mul _).add (hΦ.const_mul _)) (measurableSet_ball z T).compl
          fun x _ => ?_
        rw [abs_mul, abs_of_pos (heatKernel_pos z hr x)]
        have := abs_energy_integrand_le a hΛ p q x (w.grad x)
        have hk := (heatKernel_pos z hr x).le
        nlinarith [mul_le_mul_of_nonneg_left this hk]
    _ = (d * Λ / 2 + c0 / 2) * (∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x)) +
          c0 / 2 * ∫ x in (ball z T)ᶜ, heatKernel z r x := by
        rw [integral_add (hint2.const_mul _) (hΦ.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        have h1 : 0 ≤ (d : ℝ) * Λ / 2 + c0 / 2 := by
          have := mul_nonneg (Nat.cast_nonneg d) hΛ; linarith
        exact add_le_add (mul_le_mul_of_nonneg_left hout h1)
          (mul_le_mul_of_nonneg_left hmass (by linarith))

/-- **Lemma 4.22 with the tail (4.104)**: under integrability of the Gaussian energies of `A₁`,
a small Gaussian mass `ε₀` outside `B_T(z)`, control `κ` of the outer Gaussian energy of `A₁` by
the inner one, and the approximation property of Lemma 4.21 with error `η`, the localization error
`|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)|` is bounded by an explicit multiple of `κ + ε₀ + η`. -/
theorem abs_J1Heat_sub_localizedJ1_le_of_tail {a : CoefficientField d Λ} (hΛ : 0 ≤ Λ)
    (hr : r ≠ 0) {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C) (p q : Vec d)
    {η ε₀ κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hΦ : IntegrableOn (heatKernel z r) (ball z T)ᶜ volume)
    (hmass : ∫ x in (ball z T)ᶜ, heatKernel z r x ≤ ε₀)
    (hε₀ : linearCoefficient d Λ p q ^ 2 / 2 * ε₀ ≤ 1 / 4)
    (hint : ∀ w : HarmonicA1 a, Integrable (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))))
    (hint2 : ∀ w : HarmonicA1 a,
      IntegrableOn (fun x => heatKernel z r x * euclideanSq (w.grad x)) (ball z T)ᶜ volume)
    (houter : ∀ w : HarmonicA1 a,
      ∫ x in (ball z T)ᶜ, heatKernel z r x * euclideanSq (w.grad x) ≤
        κ * ∫ x in ball z T, heatKernel z r x * euclideanSq (w.grad x))
    (hAV : ∀ w : HarmonicA1 a,
      ‖(fun k => scaleLp hr (w.ballGrad z T k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
      ∃ c : Vec d, ‖(fun k => scaleLp hr (w.ballGrad z T k)) -
        (fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k))‖ ≤ η)
    (hVA : ∀ c : Vec d,
      ‖(fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k))‖ ≤
        2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1 →
      ∃ w : HarmonicA1 a,
        ‖(fun k => scaleLp hr (pairCombination (fun i => (W.coordinate i).toPair) c k)) -
          (fun k => scaleLp hr (w.ballGrad z T k))‖ ≤ η) :
    |J1Heat a z r p q - localizedJ1 W r p q| ≤
      (((d : ℝ) * Λ / 2 + linearCoefficient d Λ p q / 2) *
          (κ * (d * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) ^ 2)) +
        linearCoefficient d Λ p q / 2 * ε₀) +
      ((d : ℝ) ^ 2 * Λ * (2 * (2 * tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖ + 1) +
        η) / 2 + tupleLinearConstant d Λ p q ‖sqrtHeatLp z T hr‖) * η :=
  abs_J1Heat_sub_localizedJ1_le hΛ hr W p q hη
    (fun w hw => abs_a1Energy_sub_a1BallEnergy_le hΛ hr p q hκ hΦ hmass w (hint w) (hint2 w)
      (houter w) hw)
    (fun w hw => norm_scaled_ballGrad_le_of_near hΛ hr p q hΦ hmass hε₀ w (hint w) hw) hAV hVA

/-! ## The weighted `L²` form of the approximation hypotheses -/

/-- The distance of rescaled gradient tuples is at most the weighted `L²(Φ_{z,r}, B_T(z))`
distance of the gradient fields, the form of Lemma 4.21. -/
theorem norm_scaleLp_sub_le (hr : r ≠ 0) (u v : Fin d → Lp ℝ 2 (ballMeasure z T)) :
    ‖(fun k => scaleLp hr (u k)) - (fun k => scaleLp hr (v k))‖ ≤
      Real.sqrt (∫ x in ball z T, heatKernel z r x *
        euclideanSq (fun k => (u k : Vec d → ℝ) x - (v k : Vec d → ℝ) x)) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
  refine Real.le_sqrt_of_sq_le ?_
  have hint : ∀ j, Integrable (fun x => heatKernel z r x *
      ((u j : Vec d → ℝ) x - (v j : Vec d → ℝ) x) ^ 2) (ballMeasure z T) := by
    intro j
    have := (memLp_sqrtHeat_mul (z := z) (T := T) hr ((Lp.memLp (u j)).sub
      (Lp.memLp (v j)))).integrable_sq
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [mul_pow, sq (sqrtHeat z r x), sqrtHeat_mul_self hr]
  have hk : ‖((fun k => scaleLp hr (u k)) - (fun k => scaleLp hr (v k))) k‖ ^ 2 =
      ∫ x in ball z T, heatKernel z r x * ((u k : Vec d → ℝ) x - (v k : Vec d → ℝ) x) ^ 2 := by
    rw [Pi.sub_apply, norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (scaleLp hr (u k)) (scaleLp hr (v k)),
      scaleLp_ae (z := z) (T := T) hr (u k), scaleLp_ae (z := z) (T := T) hr (v k)] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, ← mul_sub, mul_pow, sq (sqrtHeat z r x), sqrtHeat_mul_self hr]
  rw [hk]
  refine integral_mono_ae (hint k) ?_ (Eventually.of_forall fun x => ?_)
  · have := integrable_finsetSum Finset.univ fun j _ => hint j
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [euclideanSq, dot, ← Finset.mul_sum, sq]
  · have hΦ := (heatKernel_pos z hr x).le
    refine mul_le_mul_of_nonneg_left ?_ hΦ
    show ((u k : Vec d → ℝ) x - (v k : Vec d → ℝ) x) ^ 2 ≤
      ∑ j, ((u j : Vec d → ℝ) x - (v j : Vec d → ℝ) x) * ((u j : Vec d → ℝ) x - (v j : Vec d → ℝ) x)
    rw [sq]
    exact Finset.single_le_sum (f := fun j => ((u j : Vec d → ℝ) x - (v j : Vec d → ℝ) x) *
      ((u j : Vec d → ℝ) x - (v j : Vec d → ℝ) x)) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ k)

theorem norm_scaleLp_le (hr : r ≠ 0) (u : Fin d → Lp ℝ 2 (ballMeasure z T)) :
    ‖(fun k => scaleLp hr (u k))‖ ≤
      Real.sqrt (∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x)) := by
  have h := norm_scaleLp_sub_le (z := z) (T := T) hr u 0
  have e1 : (fun k => scaleLp hr (u k)) - (fun k => scaleLp hr ((0 : Fin d → Lp ℝ 2
      (ballMeasure z T)) k)) = fun k => scaleLp hr (u k) := by
    funext k; simp [scaleLp_zero]
  rw [e1] at h
  refine h.trans (Real.sqrt_le_sqrt (le_of_eq (integral_congr_ae ?_)))
  filter_upwards [Lp.coeFn_zero ℝ 2 (ballMeasure z T)] with x hx
  rw [Pi.zero_apply] at hx
  simp only [Pi.zero_apply, hx, sub_zero]

theorem integral_heat_euclideanSq_le (hr : r ≠ 0) (u : Fin d → Lp ℝ 2 (ballMeasure z T)) :
    ∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x) ≤
      d * ‖(fun k => scaleLp hr (u k))‖ ^ 2 := by
  have hk : ∀ k, ‖scaleLp hr (u k)‖ ^ 2 =
      ∫ x in ball z T, heatKernel z r x * (u k : Vec d → ℝ) x ^ 2 := by
    intro k
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [scaleLp_ae (z := z) (T := T) hr (u k)] with x h1
    rw [h1, mul_pow, sq (sqrtHeat z r x), sqrtHeat_mul_self hr]
  have hint : ∀ k, Integrable (fun x => heatKernel z r x * (u k : Vec d → ℝ) x ^ 2)
      (ballMeasure z T) := by
    intro k
    have := (memLp_sqrtHeat_mul (z := z) (T := T) hr (Lp.memLp (u k))).integrable_sq
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_pow, sq (sqrtHeat z r x), sqrtHeat_mul_self hr]
  have hsum : ∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x) =
      ∑ k, ‖scaleLp hr (u k)‖ ^ 2 := by
    simp_rw [hk]
    rw [← integral_finsetSum _ fun k _ => hint k]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [euclideanSq, dot, Finset.mul_sum, sq])
  rw [hsum]
  calc ∑ k, ‖scaleLp hr (u k)‖ ^ 2 ≤ ∑ _k : Fin d, ‖(fun k => scaleLp hr (u k))‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_le_pi_norm (fun k => scaleLp hr (u k)) k) 2
    _ = d * ‖(fun k => scaleLp hr (u k))‖ ^ 2 := by simp

/-- **The relative weighted form of the approximation of Lemma 4.21 gives the hypothesis of
Lemma 4.22**: if every gradient tuple `u` of a set is within relative weighted distance `η` of a
second set, then on the bounded part `‖√Φ u‖ ≤ M` it is within `η √d M` in the rescaled norm. -/
theorem exists_close_of_relative (hr : r ≠ 0) {A B : Set (Fin d → Lp ℝ 2 (ballMeasure z T))}
    {η M : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M)
    (h : ∀ u ∈ A, ∃ v ∈ B, ∫ x in ball z T, heatKernel z r x *
        euclideanSq (fun k => (u k : Vec d → ℝ) x - (v k : Vec d → ℝ) x) ≤
      η ^ 2 * ∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x))
    {u : Fin d → Lp ℝ 2 (ballMeasure z T)} (hu : u ∈ A)
    (hub : ‖(fun k => scaleLp hr (u k))‖ ≤ M) :
    ∃ v ∈ B, ‖(fun k => scaleLp hr (u k)) - (fun k => scaleLp hr (v k))‖ ≤
      η * Real.sqrt d * M := by
  obtain ⟨v, hv, huv⟩ := h u hu
  refine ⟨v, hv, (norm_scaleLp_sub_le hr u v).trans ?_⟩
  have h1 := integral_heat_euclideanSq_le (z := z) (T := T) hr u
  have h2 : η ^ 2 * ∫ x in ball z T, heatKernel z r x *
      euclideanSq (fun k => (u k : Vec d → ℝ) x) ≤ (η * Real.sqrt d * M) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hub 2
    have h4 : ∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x) ≤
        d * M ^ 2 := h1.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d))
    calc η ^ 2 * ∫ x in ball z T, heatKernel z r x * euclideanSq (fun k => (u k : Vec d → ℝ) x)
        ≤ η ^ 2 * (d * M ^ 2) := mul_le_mul_of_nonneg_left h4 (sq_nonneg η)
      _ = η ^ 2 * d * M ^ 2 := by ring
  exact Real.sqrt_le_left (by positivity) |>.2 (huv.trans h2)

end QSH
