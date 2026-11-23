import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationAverage

/-!
# The smoothed observation of one function from its oscillation and energy on large balls

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, the observation of the smoothed correctors for one coefficient field. Let `φ` have the weak gradient
`g`, with oscillation `∫_{B_t(z)} (φ - c_t)² ≤ V t` and energy `∫_{B_t(z)} |g|² ≤ M |B_t|` for
`t ≥ t₀`. For the scales `S, σ, θ, R, T` with `4 S/θ ≤ R ≤ T`, `t₀ ≤ R`, `σ S ≥ 1` and a cutoff of
`B_R(z)`, the cut-off Gaussian mean `c` satisfies
`I_{z,T,S,σ,θ}[φ - c] ≤ 2 (S/θ)² d Q + 2 E²` and every Gaussian gradient average `∫ Φ_{p,σS} g`
with `|p - z| ≤ S/θ` is bounded by an explicit `G`, with `Q` the segment average of these averages.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The Gaussian vector average of a field with finite Gaussian energy is integrable. -/
theorem integrable_heatKernel_smul_of_energy {g : Vec d → Vec d} (hgm : AEStronglyMeasurable g volume)
    {q : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hgi : Integrable (fun x => heatKernel q ρ x * euclideanSq (g x))) :
    Integrable (fun x => heatKernel q ρ x • g x) := by
  refine ((integrable_heatKernel_mask q hρ.ne').add hgi).mono'
    ((contDiff_heatKernel q ρ).continuous.aestronglyMeasurable.smul hgm) ?_
  refine Eventually.of_forall fun x => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_pos q hρ x).le]
  calc heatKernel q ρ x * ‖g x‖ ≤ heatKernel q ρ x * (1 + euclideanSq (g x)) :=
        mul_le_mul_of_nonneg_left (norm_le_one_add_euclideanSq _) (heatKernel_pos q hρ x).le
    _ = heatKernel q ρ x + heatKernel q ρ x * euclideanSq (g x) := by ring

/-- The energy on balls in the form of `integral_heatKernel_mul_le_of_ball`. -/
theorem lintegral_ball_euclideanSq_le {g : Vec d → Vec d} {z : Vec d} {t M : ℝ} (ht : 0 < t)
    (hgB : IntegrableOn (fun x => euclideanSq (g x)) (ball z t))
    (hen : ∫ x in ball z t, euclideanSq (g x) ≤ M * volume.real (ball z t)) :
    ∫⁻ y in ball z t, ENNReal.ofReal (euclideanSq (g y)) ≤
      ENNReal.ofReal (M * volume.real (ball (0 : Vec d) 1) * t ^ d) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hgB
    (Eventually.of_forall fun x => zero_le_euclideanSq _)]
  refine ENNReal.ofReal_le_ofReal (hen.trans (le_of_eq ?_))
  rw [volume_real_ball_eq_mul z ht]
  ring

/-- **The smoothed observation of one function**, pathwise. -/
theorem smoothed_observation_pathwise {φ : Vec d → ℝ} {g : Vec d → Vec d} {z : Vec d}
    (hφl : LocallyIntegrable φ volume) (hφg : HasWeakGradient Set.univ φ g)
    (hgm' : Measurable g)
    (hφloc : ∀ t : ℝ, MemLp φ 2 (volume.restrict (ball z t)))
    (hgloc : ∀ t : ℝ, IntegrableOn (fun x => euclideanSq (g x)) (ball z t))
    (hgi : ∀ (q : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel q r x * euclideanSq (g x)))
    {t₀ M : ℝ} {V : ℝ → ℝ} (ht₀ : 1 ≤ t₀) (hM : 0 ≤ M)
    (hosc : ∀ t, t₀ ≤ t → ∃ c, ∫ x in ball z t, (φ x - c) ^ 2 ≤ V t)
    (hen : ∀ t, t₀ ≤ t → ∫ x in ball z t, euclideanSq (g x) ≤ M * volume.real (ball z t))
    {S σ θ R T D : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hθ : 0 < θ) (hρ1 : 1 ≤ σ * S)
    (h4 : 4 * (S / θ) ≤ R) (hRT : R ≤ T) (ht₀R : t₀ ≤ R) (hD : 0 ≤ D)
    (hsmall : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (8 * (σ * S) ^ 2)) ≤ 1 / 2)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0) (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2) :
    let ρ := σ * S
    let c := (∫ y, χ y * heatKernel z ρ y * φ y) / ∫ y, χ y * heatKernel z ρ y
    let Eg := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((S / θ) ^ 2 / (4 * (Real.sqrt 2 * ρ) ^ 2)) *
      (gaussianBallConstant d * (M * volume.real (ball (0 : Vec d) 1)) * t₀ ^ d)
    let W := 2 * V T + 8 * heatKernelPeak d ρ ^ 2 * volume.real (ball z T) ^ 2 * V T
    (localizationObjective z T S σ θ (fun x => φ x - c) ≤
      2 * (S / θ) ^ 2 * d * (∫ w, (volume.real (ball z (S / θ)))⁻¹ *
          euclideanNorm (∫ x, heatKernel (z + w.2 • (w.1 - z)) ρ x • g x) ^ (2 : ℝ)
            ∂segmentMeasure z (S / θ)) +
        2 * ((S / θ) * (d * (gaussTail' d R ρ * Real.sqrt Eg +
          D / R * gaussTail d R ρ * Real.sqrt (volume.real (ball z R) * W))) +
          gaussTail d R ρ * Real.sqrt (volume.real (ball z T) * W)) ^ 2) ∧
    ∀ p : Vec d, euclideanNorm (p - z) ≤ S / θ →
      euclideanNorm (∫ x, heatKernel p ρ x • g x) ≤
        Real.sqrt d * (((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) *
          (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) + D / R * heatKernelPeak d ρ) *
            Real.sqrt (volume.real (ball z R) * V R) + gaussTail' d R ρ * Real.sqrt Eg) := by
  intro ρ c Eg W
  have hgm : AEStronglyMeasurable g volume := hgm'.aestronglyMeasurable
  have hρ : 0 < ρ := mul_pos hσ hS
  have hR₁ : 0 < S / θ := div_pos hS hθ
  have hR : 0 < R := by linarith
  have ht₀0 : 0 < t₀ := zero_lt_one.trans_le ht₀
  have hρ' : 1 ≤ Real.sqrt 2 * ρ := by
    have : 1 ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  have hgv : ∀ q : Vec d, Integrable (fun x => heatKernel q ρ x • g x) := fun q =>
    integrable_heatKernel_smul_of_energy hgm hρ (hgi q ρ hρ)
  -- the Gaussian energies near `z`
  have hball : ∀ t : ℝ, t₀ ≤ t → ∫⁻ y in ball z t, ENNReal.ofReal (euclideanSq (g y)) ≤
      ENNReal.ofReal (M * volume.real (ball (0 : Vec d) 1) * t ^ d) := fun t ht =>
    lintegral_ball_euclideanSq_le (ht₀0.trans_le ht) (hgloc t) (hen t ht)
  have hgmeas : Measurable fun x => euclideanSq (g x) := by
    have h2 : Continuous fun v : Vec d => euclideanSq v := by
      unfold euclideanSq dot
      fun_prop
    exact h2.measurable.comp hgm'
  have hEg : ∀ q, euclideanNorm (q - z) ≤ S / θ →
      ∫ x, heatKernel q (Real.sqrt 2 * ρ) x * euclideanSq (g x) ≤ Eg := fun q hq =>
    integral_heatKernel_mul_le_of_ball_near hgmeas (fun x => zero_le_euclideanSq _)
      (mul_nonneg hM measureReal_nonneg) ht₀ z hball hρ' hq (hgi q _ (by linarith))
      (hgi z _ (mul_pos (Real.sqrt_pos.2 two_pos) (by linarith)))
  -- the oscillation around the cut-off mean
  obtain ⟨cT, hcT⟩ := hosc T (ht₀R.trans hRT)
  have hW : ∫ x in ball z T, (φ x - c) ^ 2 ≤ W :=
    integral_sub_cutoffMean_sq_le hR.le hRT hρ hχ.continuous hχ01 hχ1 hχR hsmall (hφloc T) hcT
  have hc : ∫ x, χ x * heatKernel z ρ x * (φ x - c) = 0 :=
    integral_cutoff_heatKernel_sub_mean hφl hχ.continuous hχc z (by
      have := half_le_integral_cutoff_heatKernel hR.le hρ hχ.continuous hχ01 hχ1 hsmall
      linarith)
  refine ⟨localizationObjective_le_segment hφl hφg hgm hgi hS hσ hθ h4 hRT hD hgv hχ hχc hχ01
    hχ1 hχR hχD (hφloc T) hc hEg hW, fun p hp => ?_⟩
  obtain ⟨cR, hcR⟩ := hosc R ht₀R
  have hp4 : euclideanNorm (p - z) ≤ R / 4 := by linarith
  exact euclideanNorm_heatKernel_average_le hR hD hρ hχ hχc hχ01 hχ1 hχR hχD hφl hφg (hφloc R)
    hcR hgm hp4 (hgi p _ (by linarith)) (hEg p hp) (hgv p)

end QSH
