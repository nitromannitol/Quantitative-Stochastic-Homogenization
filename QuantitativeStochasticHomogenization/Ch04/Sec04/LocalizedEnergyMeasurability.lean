import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerExistence
import QuantitativeStochasticHomogenization.Ch04.Sec04.MeasurableLexicographicMinimizer
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalCoefficientRepresentative

/-!
# Measurability of the localized energy

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 156 and (4.103): `J₁^{(δ)}(z, r, p, q)` is `F(B_{r^{1+δ}}(z))`-measurable.

For a basis with `L²(B_T(z))` gradient classes `u_{ik}` (coordinate `i`, component `k`), the
energy of the combination with coefficients `c` is the polynomial
`∑ -½ c_i c_j ∫ Φ a_{kl} u_{ik} u_{jl} - ∑ c_i p_k ∫ Φ a_{kl} u_{il} + ∑ c_i q_k ∫ Φ u_{ik}`
in `c`. The weighted pairings `∫ Φ a_{kl} u v` are measurable in `a` (local test integrals
against integrable functions) and continuous in `(u, v)`, hence jointly measurable; composed
with measurable coordinate minimizers they are measurable, and so is the supremum over a
countable dense set of coefficient vectors, which is `J₁^{(δ)}`.

The coordinate minimizers are measurable as soon as the admissible class contains a measurable
dense sequence (`measurable_lexicographic_minimizer`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Borel structure on `L²` -/

/-- The Borel σ-algebra on `L²`. -/
instance instMeasurableSpaceLp {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    MeasurableSpace (Lp ℝ 2 μ) :=
  borel _

instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

instance instBorelSpaceLp {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    BorelSpace (Lp ℝ 2 μ) :=
  ⟨rfl⟩

instance secondCountableTopology_Lp_ball (z : Vec d) (T : ℝ) :
    SecondCountableTopology (Lp ℝ 2 (ballMeasure z T)) :=
  inferInstance

/-! ## Weighted pairings -/

variable {μ : Measure (Vec d)}

theorem integral_abs_mul_abs_le (u v : Lp ℝ 2 μ) :
    ∫ x, |u x| * |v x| ∂μ ≤ ‖u‖ * ‖v‖ := by
  have hu := (Lp.memLp u).abs
  have hv := (Lp.memLp v).abs
  have h1 := real_inner_le_norm (hu.toLp _) (hv.toLp _)
  rw [inner_toLp_toLp] at h1
  have hnu : ‖hu.toLp _‖ = ‖u‖ := by
    have : ‖hu.toLp _‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_toLp_sq_eq_integral, norm_sq_eq_integral]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp)
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hnv : ‖hv.toLp _‖ = ‖v‖ := by
    have : ‖hv.toLp _‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_toLp_sq_eq_integral, norm_sq_eq_integral]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp)
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  rw [hnu, hnv] at h1
  calc ∫ x, |u x| * |v x| ∂μ = ∫ x, (|v| : Vec d → ℝ) x * (|u| : Vec d → ℝ) x ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x => by simp [mul_comm])
    _ ≤ ‖u‖ * ‖v‖ := h1

/-- The pairing `∫ ρ u v` with a bounded weight. -/
def weightedPairing (μ : Measure (Vec d)) (ρ : Vec d → ℝ) (u v : Lp ℝ 2 μ) : ℝ :=
  ∫ x, ρ x * u x * v x ∂μ

theorem integrable_weighted {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, |ρ x| ≤ M) (u v : Lp ℝ 2 μ) :
    Integrable (fun x => ρ x * u x * v x) μ := by
  have huv : Integrable (fun x => u x * v x) μ := (Lp.memLp u).integrable_mul (Lp.memLp v)
  have := huv.bdd_mul hρ (hM.mono fun x hx => by rwa [Real.norm_eq_abs])
  exact this.congr (Eventually.of_forall fun x => by simp only; ring)

theorem abs_weightedPairing_sub_le {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ μ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, |ρ x| ≤ M) (u v u' v' : Lp ℝ 2 μ) :
    |weightedPairing μ ρ u v - weightedPairing μ ρ u' v'| ≤
      M * (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) := by
  unfold weightedPairing
  rw [← integral_sub (integrable_weighted hρ hM u v) (integrable_weighted hρ hM u' v')]
  have hA : Integrable (fun x => |(u - u') x| * |v x|) μ :=
    ((Lp.memLp (u - u')).abs.integrable_mul (Lp.memLp v).abs).congr
      (Eventually.of_forall fun x => by simp)
  have hB : Integrable (fun x => |u' x| * |(v - v') x|) μ :=
    ((Lp.memLp u').abs.integrable_mul (Lp.memLp (v - v')).abs).congr
      (Eventually.of_forall fun x => by simp)
  have hle : ∀ᵐ x ∂μ, |ρ x * u x * v x - ρ x * u' x * v' x| ≤
      M * (|(u - u') x| * |v x| + |u' x| * |(v - v') x|) := by
    filter_upwards [hM, Lp.coeFn_sub u u', Lp.coeFn_sub v v'] with x hx h1 h2
    rw [h1, h2]
    simp only [Pi.sub_apply]
    have : ρ x * u x * v x - ρ x * u' x * v' x =
        ρ x * ((u x - u' x) * v x + u' x * (v x - v' x)) := by ring
    rw [this, abs_mul]
    refine mul_le_mul hx ((abs_add_le _ _).trans (by rw [abs_mul, abs_mul])) (abs_nonneg _) hM0
  calc |∫ x, (ρ x * u x * v x - ρ x * u' x * v' x) ∂μ|
      ≤ ∫ x, |ρ x * u x * v x - ρ x * u' x * v' x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, M * (|(u - u') x| * |v x| + |u' x| * |(v - v') x|) ∂μ :=
        integral_mono_ae ((integrable_weighted hρ hM u v).sub
          (integrable_weighted hρ hM u' v')).abs ((hA.add hB).const_mul M) hle
    _ = M * ((∫ x, |(u - u') x| * |v x| ∂μ) + ∫ x, |u' x| * |(v - v') x| ∂μ) := by
        rw [integral_const_mul, integral_add hA hB]
    _ ≤ M * (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (integral_abs_mul_abs_le _ _)
          (integral_abs_mul_abs_le _ _)) hM0

theorem continuous_weightedPairing {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ μ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, |ρ x| ≤ M) :
    Continuous fun uv : Lp ℝ 2 μ × Lp ℝ 2 μ => weightedPairing μ ρ uv.1 uv.2 := by
  rw [continuous_iff_continuousAt]
  intro uv₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun uv : Lp ℝ 2 μ × Lp ℝ 2 μ =>
    M * (‖uv.1 - uv₀.1‖ * ‖uv.2‖ + ‖uv₀.1‖ * ‖uv.2 - uv₀.2‖)) (fun _ => norm_nonneg _)
    (fun uv => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_weightedPairing_sub_le hρ hM0 hM uv.1 uv.2 uv₀.1 uv₀.2
  · have hc : Continuous fun uv : Lp ℝ 2 μ × Lp ℝ 2 μ =>
        M * (‖uv.1 - uv₀.1‖ * ‖uv.2‖ + ‖uv₀.1‖ * ‖uv.2 - uv₀.2‖) := by fun_prop
    simpa using hc.tendsto uv₀

theorem ae_coeFn_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → Lp ℝ 2 μ) :
    (⇑(∑ i ∈ s, c i • u i) : Vec d → ℝ) =ᵐ[μ] fun x => ∑ i ∈ s, c i * u i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (c j • u j) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c j) (u j), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

/-! ## Measurability of the weighted pairings with the coefficients -/

variable {Λ : ℝ} {z : Vec d} {T : ℝ}

theorem aestronglyMeasurable_heat_coefficient (a : CoefficientField d Λ) (r : ℝ) (k l : Fin d) :
    AEStronglyMeasurable (fun x => heatKernel z r x * a x k l) (ballMeasure z T) :=
  (continuous_heatKernel_right z r).aestronglyMeasurable.mul
    (a.aestronglyMeasurable_apply k l _ Measure.restrict_le_self.absolutelyContinuous)

theorem abs_heat_coefficient_le (a : CoefficientField d Λ) {r : ℝ} (hr : r ≠ 0) (k l : Fin d)
    (x : Vec d) : |heatKernel z r x * a x k l| ≤ heatKernelPeak d r * Λ := by
  rw [abs_mul]
  exact mul_le_mul (abs_heatKernel_le z hr x) (a.abs_apply_le x k l) (abs_nonneg _)
    (heatKernelPeak_pos hr).le

theorem coefficientField_bound_nonneg (a : CoefficientField d Λ) (hd : 0 < d) : 0 ≤ Λ :=
  (abs_nonneg _).trans (a.abs_apply_le 0 ⟨0, hd⟩ ⟨0, hd⟩)

/-- **The weighted pairings with the coefficients are measurable** for the local σ-algebra,
along measurable `L²`-valued maps. -/
theorem measurable_weightedPairing_coefficient (hΛ0 : 0 ≤ Λ) {r : ℝ} (hr : r ≠ 0) (k l : Fin d)
    {u v : CoefficientField d Λ → Lp ℝ 2 (ballMeasure z T)}
    (hu : @Measurable _ _ (localSigma (ball z T)) _ u)
    (hv : @Measurable _ _ (localSigma (ball z T)) _ v) :
    @Measurable _ ℝ (localSigma (ball z T)) _ fun a =>
      weightedPairing (ballMeasure z T) (fun x => heatKernel z r x * a x k l) (u a) (v a) := by
  let _ : MeasurableSpace (CoefficientField d Λ) := localSigma (ball z T)
  have hjoint : Measurable (Function.uncurry fun (uv : Lp ℝ 2 (ballMeasure z T) ×
      Lp ℝ 2 (ballMeasure z T)) (a : CoefficientField d Λ) =>
        weightedPairing (ballMeasure z T) (fun x => heatKernel z r x * a x k l) uv.1 uv.2) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun a => ?_) (fun uv => ?_)
    · exact continuous_weightedPairing (aestronglyMeasurable_heat_coefficient a r k l)
        (mul_nonneg (heatKernelPeak_pos hr).le hΛ0)
        (Eventually.of_forall fun x => abs_heat_coefficient_le a hr k l x)
    · have hg : Integrable (fun x => heatKernel z r x * uv.1 x * uv.2 x) (ballMeasure z T) :=
        integrable_weighted (continuous_heatKernel_right z r).aestronglyMeasurable
          (Eventually.of_forall fun x => abs_heatKernel_le z hr x) uv.1 uv.2
      have heq : (fun a : CoefficientField d Λ => weightedPairing (ballMeasure z T)
          (fun x => heatKernel z r x * a x k l) uv.1 uv.2) =
          fun a => ∫ x in ball z T, (heatKernel z r x * uv.1 x * uv.2 x) * a x k l := by
        funext a
        exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
      rw [heq]
      exact measurable_setIntegral_mul_coefficient z T hg k l
  exact hjoint.comp ((hu.prodMk hv).prodMk measurable_id)

/-! ## The energy of a combination as a polynomial in the pairings -/

/-- The weight `Φ_{z,r} a_{kl}`. -/
def heatCoefficient (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) (k l : Fin d) (x : Vec d) :
    ℝ :=
  heatKernel z r x * a x k l

/-- The energy `∫_{B_T(z)} Φ_{z,r} (-½ G·aG - p·aG + q·G)` of a gradient field with `L²` classes
`G_k`, written with the weighted pairings. -/
def pairEnergy (a : CoefficientField d Λ) (z : Vec d) (T r : ℝ) (p q : Vec d)
    (G : Fin d → Lp ℝ 2 (ballMeasure z T)) : ℝ :=
  (∑ k, ∑ l, (-(1 / 2 : ℝ) * weightedPairing (ballMeasure z T) (heatCoefficient a z r k l) (G k) (G l) -
      p k * weightedPairing (ballMeasure z T) (heatCoefficient a z r k l) (G l) (oneLp z T))) +
    ∑ k, q k * weightedPairing (ballMeasure z T) (heatKernel z r) (G k) (oneLp z T)

theorem energy_integrand_eq (Φ : ℝ) (A : Mat d) (g p q : Vec d) (o : ℝ) (ho : o = 1) :
    Φ * (-(1 / 2 : ℝ) * dot g (A.mulVec g) - dot p (A.mulVec g) + dot q g) =
      (∑ k, ∑ l, (-(1 / 2 : ℝ) * (Φ * A k l * g k * g l) - p k * (Φ * A k l * g l * o))) +
        ∑ k, q k * (Φ * g k * o) := by
  subst ho
  have e1 : dot g (A.mulVec g) = ∑ k, ∑ l, A k l * g k * g l := by
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have e2 : dot p (A.mulVec g) = ∑ k, ∑ l, p k * A k l * g l := by
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have e3 : dot q g = ∑ k, q k * g k := rfl
  rw [e1, e2, e3]
  simp only [Finset.sum_sub_distrib, mul_add, mul_sub, Finset.mul_sum]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun k _ => by ring

theorem aestronglyMeasurable_heatCoefficient (a : CoefficientField d Λ) (r : ℝ) (k l : Fin d) :
    AEStronglyMeasurable (heatCoefficient a z r k l) (ballMeasure z T) :=
  aestronglyMeasurable_heat_coefficient a r k l

theorem integral_energy_eq_pairEnergy (a : CoefficientField d Λ) {r : ℝ} (hr : r ≠ 0)
    (p q : Vec d) (G : Fin d → Lp ℝ 2 (ballMeasure z T)) {g : Vec d → Vec d}
    (hg : ∀ᵐ x ∂ballMeasure z T, g x = fun k => G k x) :
    ∫ x in ball z T, heatKernel z r x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x)) = pairEnergy a z T r p q G := by
  have hρ := fun k l => aestronglyMeasurable_heatCoefficient (z := z) (T := T) a r k l
  have hM := fun k l => (Eventually.of_forall fun x => abs_heat_coefficient_le a hr k l x :
    ∀ᵐ x ∂ballMeasure z T, |heatCoefficient a z r k l x| ≤ heatKernelPeak d r * Λ)
  have hΦ : AEStronglyMeasurable (heatKernel z r) (ballMeasure z T) :=
    (continuous_heatKernel_right z r).aestronglyMeasurable
  have hΦM : ∀ᵐ x ∂ballMeasure z T, |heatKernel z r x| ≤ heatKernelPeak d r :=
    Eventually.of_forall fun x => abs_heatKernel_le z hr x
  have hone : ∀ᵐ x ∂ballMeasure z T, (oneLp z T : Vec d → ℝ) x = 1 := by
    filter_upwards [(memLp_const (μ := ballMeasure z T) (p := 2) (1 : ℝ)).coeFn_toLp] with x hx
    rw [oneLp, hx]
  have hpt : (fun x => heatKernel z r x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x))) =ᵐ[ballMeasure z T] fun x =>
      (∑ k, ∑ l, (-(1 / 2 : ℝ) * (heatCoefficient a z r k l x * G k x * G l x) -
        p k * (heatCoefficient a z r k l x * G l x * oneLp z T x))) +
      ∑ k, q k * (heatKernel z r x * G k x * oneLp z T x) := by
    filter_upwards [hg, hone] with x hx ho
    rw [hx, energy_integrand_eq _ _ _ _ _ _ ho]
    simp only [heatCoefficient]
  rw [integral_congr_ae hpt]
  have hI1 : ∀ k l, Integrable (fun x => -(1 / 2 : ℝ) * (heatCoefficient a z r k l x * G k x * G l x) -
      p k * (heatCoefficient a z r k l x * G l x * oneLp z T x)) (ballMeasure z T) := fun k l =>
    ((integrable_weighted (hρ k l) (hM k l) _ _).const_mul _).sub
      ((integrable_weighted (hρ k l) (hM k l) _ _).const_mul _)
  have hI2 : ∀ k, Integrable (fun x => q k * (heatKernel z r x * G k x * oneLp z T x))
      (ballMeasure z T) := fun k => (integrable_weighted hΦ hΦM _ _).const_mul _
  rw [integral_add (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hI1 k l)
    (integrable_finsetSum _ fun k _ => hI2 k), integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hI1 k l, integral_finsetSum _ fun k _ => hI2 k]
  unfold pairEnergy
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hI1 k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_sub ((integrable_weighted (hρ k l) (hM k l) _ _).const_mul _)
      ((integrable_weighted (hρ k l) (hM k l) _ _).const_mul _), integral_const_mul,
      integral_const_mul]
    rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    rfl

/-! ## The supremum over coefficient vectors -/

theorem sSup_range_eq_iSup_of_denseRange {X : Type*} [TopologicalSpace X] [Nonempty X]
    {f : X → ℝ} (hf : Continuous f) {u : ℕ → X} (hu : DenseRange u) :
    sSup (Set.range f) = ⨆ n, f (u n) := by
  have key : ∀ M, (∀ n, f (u n) ≤ M) → ∀ x, f x ≤ M := by
    intro M hM x
    by_contra h
    obtain ⟨n, hn⟩ := hu.exists_mem_open (isOpen_lt continuous_const hf) ⟨x, not_le.1 h⟩
    exact absurd (hM n) (not_le.2 hn)
  by_cases hb : BddAbove (Set.range f)
  · have hb' : BddAbove (Set.range fun n => f (u n)) :=
      hb.mono (by rintro _ ⟨n, rfl⟩; exact ⟨u n, rfl⟩)
    apply le_antisymm
    · refine csSup_le (Set.range_nonempty f) ?_
      rintro _ ⟨x, rfl⟩
      exact key _ (fun n => le_ciSup hb' n) x
    · exact ciSup_le fun n => le_csSup hb ⟨u n, rfl⟩
  · rw [Real.sSup_of_not_bddAbove hb, Real.iSup_of_not_bddAbove]
    rintro ⟨M, hM⟩
    exact hb ⟨M, by rintro _ ⟨x, rfl⟩; exact key M (fun n => hM ⟨n, rfl⟩) x⟩

/-- The combination `∑_i c_i g_{i,k}` of the gradient classes of `d` pairs. -/
def pairCombination (F : Fin d → PairSpace d z T) (c : Vec d) (k : Fin d) :
    Lp ℝ 2 (ballMeasure z T) :=
  ∑ i, c i • (F i).2 k

theorem continuous_pairCombination_left (c : Vec d) (k : Fin d) :
    Continuous fun F : Fin d → PairSpace d z T => pairCombination F c k := by
  unfold pairCombination
  fun_prop

theorem continuous_pairCombination_right (F : Fin d → PairSpace d z T) (k : Fin d) :
    Continuous fun c : Vec d => pairCombination F c k :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

theorem continuous_pairEnergy (a : CoefficientField d Λ) (hΛ0 : 0 ≤ Λ) {r : ℝ} (hr : r ≠ 0)
    (p q : Vec d) : Continuous (pairEnergy a z T r p q) := by
  have hW : ∀ k l, Continuous fun uv : Lp ℝ 2 (ballMeasure z T) × Lp ℝ 2 (ballMeasure z T) =>
      weightedPairing (ballMeasure z T) (heatCoefficient a z r k l) uv.1 uv.2 := fun k l =>
    continuous_weightedPairing (aestronglyMeasurable_heatCoefficient a r k l)
      (mul_nonneg (heatKernelPeak_pos hr).le hΛ0)
      (Eventually.of_forall fun x => abs_heat_coefficient_le a hr k l x)
  have hW0 : Continuous fun uv : Lp ℝ 2 (ballMeasure z T) × Lp ℝ 2 (ballMeasure z T) =>
      weightedPairing (ballMeasure z T) (heatKernel z r) uv.1 uv.2 :=
    continuous_weightedPairing (continuous_heatKernel_right z r).aestronglyMeasurable
      (heatKernelPeak_pos hr).le (Eventually.of_forall fun x => abs_heatKernel_le z hr x)
  unfold pairEnergy
  refine (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_).add
    (continuous_finsetSum _ fun k _ => ?_)
  · have h1 : Continuous fun G : Fin d → Lp ℝ 2 (ballMeasure z T) => (G k, G l) :=
      (continuous_apply k).prodMk (continuous_apply l)
    have h2 : Continuous fun G : Fin d → Lp ℝ 2 (ballMeasure z T) => (G l, oneLp z T) :=
      (continuous_apply l).prodMk continuous_const
    exact (continuous_const.mul ((hW k l).comp h1)).sub (continuous_const.mul ((hW k l).comp h2))
  · have h3 : Continuous fun G : Fin d → Lp ℝ 2 (ballMeasure z T) => (G k, oneLp z T) :=
      (continuous_apply k).prodMk continuous_const
    exact continuous_const.mul (hW0.comp h3)

variable {S σ θ C : ℝ}

theorem localizedJ1_eq_sSup {a : CoefficientField d Λ} (W : LocalizedBasis a z T S σ θ C) {r : ℝ} (hr : r ≠ 0)
    (p q : Vec d) :
    localizedJ1 W r p q = sSup (Set.range fun c =>
      pairEnergy a z T r p q (pairCombination (fun i => (W.coordinate i).toPair) c)) := by
  unfold localizedJ1
  congr 1
  ext e
  refine exists_congr fun c => ?_
  rw [integral_energy_eq_pairEnergy a hr p q _ ?_]
  · exact ⟨fun h => h.symm, fun h => h.symm⟩
  · have hk : ∀ k, ∀ᵐ x ∂ballMeasure z T, localizedGradient W c x k =
        (pairCombination (fun i => (W.coordinate i).toPair) c k : Vec d → ℝ) x := by
      intro k
      have h1 := ae_coeFn_sum_smul (μ := ballMeasure z T) Finset.univ c
        (fun i => (W.coordinate i).toPair.2 k)
      have h2 := ae_all_iff.2 fun i => (W.coordinate i).toPair_snd_ae k
      filter_upwards [h1, h2] with x hx1 hx2
      rw [pairCombination, hx1]
      simp only [localizedGradient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [hx2 i]
    filter_upwards [ae_all_iff.2 hk] with x hx
    funext k
    exact hx k

/-- **Measurability of the localized energy** along measurable selected bases. -/
theorem measurable_localizedJ1 (hΛ0 : 0 ≤ Λ) {r : ℝ} (hr : r ≠ 0) (p q : Vec d)
    (W : ∀ a : CoefficientField d Λ, LocalizedBasis a z T S σ θ C)
    (hW : ∀ i, @Measurable _ _ (localSigma (ball z T)) _ fun a => ((W a).coordinate i).toPair) :
    @Measurable _ ℝ (localSigma (ball z T)) _ fun a => localizedJ1 (W a) r p q := by
  obtain ⟨cs, hcs⟩ := TopologicalSpace.exists_dense_seq (Vec d)
  have heq : (fun a => localizedJ1 (W a) r p q) = fun a => ⨆ n, pairEnergy a z T r p q
      (pairCombination (fun i => ((W a).coordinate i).toPair) (cs n)) := by
    funext a
    have hcont : Continuous fun c => pairEnergy a z T r p q
        (pairCombination (fun i => ((W a).coordinate i).toPair) c) :=
      (continuous_pairEnergy a hΛ0 hr p q).comp (continuous_pi fun k =>
        continuous_pairCombination_right (fun i => ((W a).coordinate i).toPair) k)
    rw [localizedJ1_eq_sSup (W a) hr p q, sSup_range_eq_iSup_of_denseRange hcont hcs]
  rw [heq]
  let _ : MeasurableSpace (CoefficientField d Λ) := localSigma (ball z T)
  refine Measurable.iSup fun n => ?_
  have hF : Measurable fun a => fun i => ((W a).coordinate i).toPair := measurable_pi_iff.2 hW
  have hG : ∀ k, Measurable fun a =>
      pairCombination (fun i => ((W a).coordinate i).toPair) (cs n) k := fun k =>
    (continuous_pairCombination_left (cs n) k).measurable.comp hF
  have hW0 : Continuous fun uv : Lp ℝ 2 (ballMeasure z T) × Lp ℝ 2 (ballMeasure z T) =>
      weightedPairing (ballMeasure z T) (heatKernel z r) uv.1 uv.2 :=
    continuous_weightedPairing (continuous_heatKernel_right z r).aestronglyMeasurable
      (heatKernelPeak_pos hr).le (Eventually.of_forall fun x => abs_heatKernel_le z hr x)
  unfold pairEnergy
  refine (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_).add
    (Finset.measurable_sum _ fun k _ => ?_)
  · exact ((measurable_weightedPairing_coefficient hΛ0 hr k l (hG k) (hG l)).const_mul _).sub
      ((measurable_weightedPairing_coefficient hΛ0 hr k l (hG l) measurable_const).const_mul _)
  · exact (hW0.measurable.comp ((hG k).prodMk measurable_const)).const_mul _

/-- **Measurability of the least-norm coordinate minimizers** from a measurable dense sequence
in the admissible class. -/
theorem measurable_toPair_of_denseSeq (hT : 0 < T) (hσS : σ * S ≠ 0) (hSθ : 0 < S / θ)
    (hC : 0 ≤ C) (i : Fin d) (h : ℕ → CoefficientField d Λ → PairSpace d z T)
    (hh : ∀ n, @Measurable _ _ (localSigma (ball z T)) _ (h n))
    (hmem : ∀ n a, h n a ∈ admissiblePairs a z T C)
    (hdense : ∀ a, admissiblePairs a z T C ⊆ closure (Set.range fun n => h n a))
    (w : ∀ a : CoefficientField d Λ, LocalHarmonic a z T)
    (hw : ∀ a, IsLeastNormCoordinateMinimizer S σ θ C i (w a)) :
    @Measurable _ _ (localSigma (ball z T)) _ fun a => (w a).toPair := by
  have hcoord : ∀ (a : CoefficientField d Λ) (y : PairSpace d z T)
      (hy : y ∈ admissiblePairs a z T C),
      (∀ v ∈ admissiblePairs a z T C, pairObjective z T S σ θ i y ≤ pairObjective z T S σ θ i v) →
      IsCoordinateMinimizer S σ θ C i (ofPair a y hy.1) := by
    intro a y hy hmin
    refine ⟨((ofPair a y hy.1).admissible_iff hC hT).2 ((toPair_ofPair y hy.1).symm ▸ hy.2),
      fun v hv => ?_⟩
    rw [(ofPair a y hy.1).objective_eq, v.objective_eq, toPair_ofPair]
    exact hmin _ (v.toPair_mem hC hT hv)
  refine measurable_lexicographic_minimizer (mΩ := localSigma (ball z T))
    isQuadraticGauge_pairGauge
    ((continuous_fst.norm.pow 2).add continuous_pairGradEnergy)
    (K := fun a => admissiblePairs a z T C) (fun a => isClosed_admissiblePairs a z T C)
    (continuous_pairObjective (θ := θ) hσS i)
    (fun a => (convexOn_pairObjective hσS i).subset (Set.subset_univ _)
      (convex_admissiblePairs a z T C))
    (fun a y _ => pairObjective_nonneg i y) (g := fun F => ‖F.1‖ ^ 2)
    (continuous_fst.norm.pow 2)
    (fun a => convexOn_norm_fst_sq.subset (Set.subset_univ _) (convex_admissiblePairs a z T C))
    (fun a y _ => sq_nonneg _) (fun a t => bddAbove_pairGauge_sublevel hT hσS hSθ i t)
    h hh hmem hdense (fun a => (w a).toPair) (fun a => (w a).toPair_mem hC hT (hw a).1.1)
    (fun a y hy => ?_) (fun a y hy hfy => ?_) (fun a y hy hfy hgy => ?_)
  · have h1 := (hw a).1.2 (ofPair a y hy.1)
      (((ofPair a y hy.1).admissible_iff hC hT).2 ((toPair_ofPair y hy.1).symm ▸ hy.2))
    rwa [(w a).objective_eq, (ofPair a y hy.1).objective_eq, toPair_ofPair] at h1
  · have hmin : ∀ v ∈ admissiblePairs a z T C,
        pairObjective z T S σ θ i y ≤ pairObjective z T S σ θ i v := by
      intro v hv
      refine hfy.trans ?_
      have h1 := (hw a).1.2 (ofPair a v hv.1)
        (((ofPair a v hv.1).admissible_iff hC hT).2 ((toPair_ofPair v hv.1).symm ▸ hv.2))
      rwa [(w a).objective_eq, (ofPair a v hv.1).objective_eq, toPair_ofPair] at h1
    have h2 := (hw a).2 (ofPair a y hy.1) (hcoord a y hy hmin)
    rwa [(w a).integral_potential_sq, (ofPair a y hy.1).integral_potential_sq,
      toPair_ofPair] at h2
  · have hcm := hcoord a y hy hfy
    have hln : IsLeastNormCoordinateMinimizer S σ θ C i (ofPair a y hy.1) := by
      refine ⟨hcm, fun v hv => ?_⟩
      rw [(ofPair a y hy.1).integral_potential_sq, v.integral_potential_sq, toPair_ofPair]
      refine hgy _ (v.toPair_mem hC hT hv.1) ?_
      have h1 := hv.2 (ofPair a y hy.1) hcm.1
      rwa [v.objective_eq, (ofPair a y hy.1).objective_eq, toPair_ofPair] at h1
    have := hln.toPair_eq hT hσS hC (hw a)
    rwa [toPair_ofPair] at this

end QSH
