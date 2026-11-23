import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationTails
import QuantitativeStochasticHomogenization.Ch04.Sec03.AveragesFromEnergy

/-!
# Stochastic integrability of the segment averages of the Gaussian gradient averages

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the stochastic part of the observation of the smoothed correctors. Moving the center of a Gaussian
costs a factor: `Φ_{p,ρ} ≤ 2^{d/2} e^{|p-p₀|²/(4ρ²)} Φ_{p₀,√2ρ}`; hence the Gaussian average
`p ↦ ∫ Φ_{p,ρ} v` of a field whose Gaussian energies are finite is continuous. If `N(p) ≤ O_s(θ₀)`
for every center `p` with `1 < s < 2`, then the average of `N²` over the segments from `z` to the
points of `B_{R₁}(z)` is `O_{s/2}` (Lemma A.4 below the exponent one), and its square root is
`O_s(K_s^{1/2} θ₀)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanSq_sub_le_two_mul (x p p₀ : Vec d) :
    euclideanSq (x - p₀) ≤ 2 * euclideanSq (x - p) + 2 * euclideanSq (p - p₀) := by
  have h := euclideanNorm_sub_le_sub_add x p₀ p
  rw [← sq_euclideanNorm, ← sq_euclideanNorm, ← sq_euclideanNorm]
  have h0 := zero_le_euclideanNorm (x - p₀)
  have h1 := zero_le_euclideanNorm (x - p)
  have h2 := zero_le_euclideanNorm (p - p₀)
  nlinarith [sq_nonneg (euclideanNorm (x - p) - euclideanNorm (p - p₀))]

/-- **Moving the center of a Gaussian**: `Φ_{p,ρ} ≤ 2^{d/2} e^{|p-p₀|²/(4ρ²)} Φ_{p₀,√2ρ}`. -/
theorem heatKernel_le_shift (p p₀ x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    heatKernel p ρ x ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (euclideanSq (p - p₀) / (4 * ρ ^ 2)) *
      heatKernel p₀ (Real.sqrt 2 * ρ) x := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [heatKernel_eq, heatKernel_eq, heatKernelPeak_eq_mul_sqrt_two d ρ]
  have hs : (Real.sqrt 2 * ρ) ^ 2 = 2 * ρ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs]
  have h := euclideanSq_sub_le_two_mul x p p₀
  have h1 : Real.exp (-euclideanSq (x - p) / (4 * ρ ^ 2)) ≤
      Real.exp (euclideanSq (p - p₀) / (4 * ρ ^ 2)) *
        Real.exp (-euclideanSq (x - p₀) / (4 * (2 * ρ ^ 2))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have e : euclideanSq (p - p₀) / (4 * ρ ^ 2) + -euclideanSq (x - p₀) / (4 * (2 * ρ ^ 2)) =
        (2 * euclideanSq (p - p₀) - euclideanSq (x - p₀)) / (8 * ρ ^ 2) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hP : 0 ≤ heatKernelPeak d (Real.sqrt 2 * ρ) :=
    (heatKernelPeak_pos (by positivity : Real.sqrt 2 * ρ ≠ 0)).le
  have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := by positivity
  calc 2 ^ ((d : ℝ) / 2) * heatKernelPeak d (Real.sqrt 2 * ρ) *
        Real.exp (-euclideanSq (x - p) / (4 * ρ ^ 2))
      ≤ 2 ^ ((d : ℝ) / 2) * heatKernelPeak d (Real.sqrt 2 * ρ) *
        (Real.exp (euclideanSq (p - p₀) / (4 * ρ ^ 2)) *
          Real.exp (-euclideanSq (x - p₀) / (4 * (2 * ρ ^ 2)))) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 hP)
    _ = _ := by ring

theorem norm_le_one_add_euclideanSq (v : Vec d) : ‖v‖ ≤ 1 + euclideanSq v := by
  refine (norm_le_euclideanNorm v).trans ?_
  rw [← sq_euclideanNorm]
  nlinarith [sq_nonneg (euclideanNorm v - 1)]

/-- **Continuity of Gaussian averages in the center** for a field with finite Gaussian
energies. -/
theorem continuous_heatKernel_average {v : Vec d → Vec d} (hvm : AEStronglyMeasurable v volume)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hv : ∀ p : Vec d, Integrable (fun x => heatKernel p (Real.sqrt 2 * ρ) x * euclideanSq (v x))) :
    Continuous fun p : Vec d => ∫ x, heatKernel p ρ x • v x := by
  rw [continuous_iff_continuousAt]
  intro p₀
  have hρ' : 0 < Real.sqrt 2 * ρ := by positivity
  set K : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / (4 * ρ ^ 2)) with hK
  have hcont : ∀ x, Continuous fun p : Vec d => heatKernel p ρ x := fun x =>
    (continuous_heatKernel_uncurry (d := d) ρ).comp (continuous_id.prodMk continuous_const)
  refine MeasureTheory.continuousAt_of_dominated (bound := fun x =>
      K * (heatKernel p₀ (Real.sqrt 2 * ρ) x * (1 + euclideanSq (v x)))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p =>
      ((contDiff_heatKernel_top p ρ).continuous.aestronglyMeasurable).smul hvm
  · have hb : ∀ᶠ p in 𝓝 p₀, euclideanSq (p - p₀) < 1 := by
      have hc : Continuous fun p : Vec d => euclideanSq (p - p₀) := by
        unfold euclideanSq dot
        fun_prop
      have h0 : euclideanSq (p₀ - p₀) < 1 := by
        rw [sub_self, ← sq_euclideanNorm]
        have : euclideanNorm (0 : Vec d) = 0 := by
          have h := euclideanNorm_smul_of_zero_le (0 : ℝ) le_rfl (0 : Vec d)
          rwa [zero_smul, zero_mul] at h
        rw [this]
        norm_num
      exact hc.continuousAt.eventually_lt continuousAt_const h0
    filter_upwards [hb] with p hp
    refine Eventually.of_forall fun x => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_pos p hρ x).le]
    have h1 := heatKernel_le_shift p p₀ x hρ
    have h2 : Real.exp (euclideanSq (p - p₀) / (4 * ρ ^ 2)) ≤ Real.exp (1 / (4 * ρ ^ 2)) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right hp.le (by positivity))
    have h3 : heatKernel p ρ x ≤ K * heatKernel p₀ (Real.sqrt 2 * ρ) x := by
      refine h1.trans ?_
      rw [hK]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h2 (by positivity)) (heatKernel_pos p₀ hρ' x).le
    have h4 := norm_le_one_add_euclideanSq (v x)
    calc heatKernel p ρ x * ‖v x‖
        ≤ (K * heatKernel p₀ (Real.sqrt 2 * ρ) x) * (1 + euclideanSq (v x)) :=
          mul_le_mul h3 h4 (norm_nonneg _)
            (mul_nonneg (by rw [hK]; positivity) (heatKernel_pos p₀ hρ' x).le)
      _ = _ := by ring
  · refine Integrable.const_mul ?_ K
    have e : (fun x => heatKernel p₀ (Real.sqrt 2 * ρ) x * (1 + euclideanSq (v x))) =
        fun x => heatKernel p₀ (Real.sqrt 2 * ρ) x +
          heatKernel p₀ (Real.sqrt 2 * ρ) x * euclideanSq (v x) := by
      funext x; ring
    rw [e]
    exact (integrable_heatKernel p₀ hρ').add (hv p₀)
  · exact Eventually.of_forall fun x => ((hcont x).smul continuous_const).continuousAt

/-- The measure of the segments from `z` to the points of `B_{R₁}(z)`: the points `y` of the
ball and the times `t ∈ (0, 1]`. -/
def segmentMeasure (z : Vec d) (R₁ : ℝ) : Measure (Vec d × ℝ) :=
  (volume.restrict (ball z R₁)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))

instance (z : Vec d) (R₁ : ℝ) : IsFiniteMeasure (segmentMeasure z R₁) := by
  have : IsFiniteMeasure (volume.restrict (ball z R₁)) :=
    isFiniteMeasure_restrict.2 (volume_ball_lt_top z R₁).ne
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  unfold segmentMeasure
  infer_instance

theorem segmentMeasure_real_univ (z : Vec d) (R₁ : ℝ) :
    (segmentMeasure z R₁).real Set.univ = volume.real (ball z R₁) := by
  unfold segmentMeasure
  rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  rfl

/-- **The segment average** of `N(p)²` over the segments from `z` to the points of `B_{R₁}(z)`. -/
def segmentAverage {Ω : Type*} (N : Vec d → Ω → ℝ) (z : Vec d) (R₁ : ℝ) (ω : Ω) : ℝ :=
  ∫ w, (volume.real (ball z R₁))⁻¹ * N (z + w.2 • (w.1 - z)) ω ^ (2 : ℝ) ∂segmentMeasure z R₁

/-- The constant of Lemma A.4 at the exponent `s/2 < 1`. -/
def segmentConstant (s : ℝ) : ℝ := (1 + (1 - s / 2) / (s / 2 * Real.log 2)) ^ (s / 2)⁻¹

theorem segmentConstant_pos {s : ℝ} (hs : 0 < s) (hs2 : s < 2) : 0 < segmentConstant s := by
  unfold segmentConstant
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 0 < 1 - s / 2 := by linarith
  have h2 : 0 < s / 2 * Real.log 2 := by positivity
  positivity

/-- **The square root of the segment average** of `N² ≤ O_{s/2}(θ₀²)` is `O_s(K_s^{1/2} θ₀)`. -/
theorem osBound_sqrt_segmentAverage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : Vec d → Ω → ℝ} (hNm : Measurable (Function.uncurry N))
    (hN0 : ∀ p ω, 0 ≤ N p ω) {s θ₀ : ℝ} (hs : 0 < s) (hs2 : s < 2) (hθ₀ : 0 < θ₀)
    (hN : ∀ p, OsBound P (N p) s θ₀) (z : Vec d) {R₁ : ℝ} (hR₁ : 0 < R₁) :
    OsBound P (fun ω => segmentAverage N z R₁ ω ^ (1 / 2 : ℝ)) s
      (segmentConstant s ^ (1 / 2 : ℝ) * θ₀) := by
  have hB : 0 < volume.real (ball z R₁) := volume_real_ball_pos z hR₁
  set X : Vec d × ℝ → Ω → ℝ := fun w ω =>
    (volume.real (ball z R₁))⁻¹ * N (z + w.2 • (w.1 - z)) ω ^ (2 : ℝ) with hX
  have hmap : Measurable fun q : (Vec d × ℝ) × Ω => (z + q.1.2 • (q.1.1 - z), q.2) := by
    refine Measurable.prodMk ?_ measurable_snd
    exact measurable_const.add ((measurable_snd.comp measurable_fst).smul
      ((measurable_fst.comp measurable_fst).sub measurable_const))
  have hXm : Measurable (Function.uncurry X) := by
    have h := (hNm.comp hmap).pow_const (2 : ℝ)
    exact h.const_mul _
  have hX0 : ∀ w ω, 0 ≤ X w ω := fun w ω =>
    mul_nonneg (inv_nonneg.2 hB.le) (Real.rpow_nonneg (hN0 _ _) _)
  have hXos : ∀ w, OsBound P (X w) (s / 2) ((volume.real (ball z R₁))⁻¹ * θ₀ ^ (2 : ℝ)) :=
    fun w => ((hN _).rpow (hN0 _) (by norm_num : (0 : ℝ) < 2)).const_mul (inv_pos.2 hB)
  have hθi : Integrable (fun _ : Vec d × ℝ => (volume.real (ball z R₁))⁻¹ * θ₀ ^ (2 : ℝ))
      (segmentMeasure z R₁) := integrable_const _
  have hθ : ∫ _ : Vec d × ℝ, (volume.real (ball z R₁))⁻¹ * θ₀ ^ (2 : ℝ) ∂segmentMeasure z R₁ =
      θ₀ ^ (2 : ℝ) := by
    rw [integral_const, smul_eq_mul, segmentMeasure_real_univ, ← mul_assoc, mul_inv_cancel₀ hB.ne',
      one_mul]
  have hθpos : 0 < θ₀ ^ (2 : ℝ) := Real.rpow_pos_of_pos hθ₀ _
  obtain ⟨-, hQ⟩ := osBound_integral_of_lt_one (P := P) (μ := segmentMeasure z R₁)
    (by linarith : s / 2 < 1) hXm hX0 measurable_const hθi (by rw [hθ]; exact hθpos) hXos
  rw [hθ] at hQ
  have hQ0 : ∀ ω, 0 ≤ ∫ w, X w ω ∂segmentMeasure z R₁ := fun ω => integral_nonneg fun w => hX0 w ω
  have h := hQ.rpow hQ0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hs' : s / 2 / (1 / 2) = s := by ring
  have hc : ((1 + (1 - s / 2) / (s / 2 * Real.log 2)) ^ (s / 2)⁻¹ * θ₀ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      segmentConstant s ^ (1 / 2 : ℝ) * θ₀ := by
    have hK := segmentConstant_pos hs hs2
    unfold segmentConstant at hK ⊢
    rw [Real.mul_rpow hK.le hθpos.le, ← Real.rpow_mul hθ₀.le]
    norm_num
  rw [hs', hc] at h
  exact h

end QSH
