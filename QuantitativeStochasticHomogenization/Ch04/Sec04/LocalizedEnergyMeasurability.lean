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
      rw [norm_toLp_sq, norm_sq_eq_integral]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp)
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hnv : ‖hv.toLp _‖ = ‖v‖ := by
    have : ‖hv.toLp _‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_toLp_sq, norm_sq_eq_integral]
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

end QSH
