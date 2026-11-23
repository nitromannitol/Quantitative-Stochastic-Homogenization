import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationPathwise
import QuantitativeStochasticHomogenization.Ch04.Sec03.AverageMeasurability

/-!
# The smoothed observation of the correctors above the minimal scale

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (SCOTT-localization (5)). For a coefficient field at which the correctors
have weak gradients, are locally square integrable, have finite Gaussian energies, and satisfy the
oscillation and energy bounds of E8 on the balls `B_t(z)` with `t ≥ t₀`, the smoothed observation
of `smoothed_observation_pathwise` applies to every corrector `φ_{e_i}`. On the same coefficient
fields the linear quantity `∫ Φ_{p,ρ} (e_i + ∇φ_{e_i}) - e_i` is the Gaussian average of `∇φ_{e_i}`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {P : Measure (CoefficientField d Λ)}

theorem correctedField_unitVector' (S : HomogenizationData P) (a : CoefficientField d Λ)
    (i : Fin d) (x : Vec d) :
    correctedField S a (unitVector i) x = unitVector i + (S.corrector (unitVector i)).grad a x := by
  unfold correctedField
  rw [Finset.sum_eq_single i]
  · simp [unitVector, correctedCoordinate]
  · intro k _ hk
    simp [unitVector, Pi.single_apply, hk]
  · simp

/-- **The linear quantity is the Gaussian average of the corrector gradient.** -/
theorem gradientAverage_sub_unitVector (S : HomogenizationData P) (a : CoefficientField d Λ)
    (i : Fin d) {p : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hgv : Integrable (fun x => heatKernel p ρ x • (S.corrector (unitVector i)).grad a x)) :
    gradientAverage S a p ρ (unitVector i) - unitVector i =
      ∫ x, heatKernel p ρ x • (S.corrector (unitVector i)).grad a x := by
  unfold gradientAverage
  have e : (fun x => heatKernel p ρ x • correctedField S a (unitVector i) x) =
      fun x => heatKernel p ρ x • unitVector i +
        heatKernel p ρ x • (S.corrector (unitVector i)).grad a x := by
    funext x
    rw [correctedField_unitVector', smul_add]
  rw [e, integral_add ((integrable_heatKernel_mask p hρ.ne').smul_const _) hgv,
    integral_smul_const, integral_heatKernel_mask p hρ.ne', one_smul, add_sub_cancel_left]

theorem euclideanSq_grad_le (S : HomogenizationData P) (a : CoefficientField d Λ) (i : Fin d)
    (x : Vec d) :
    euclideanSq ((S.corrector (unitVector i)).grad a x) ≤
      2 * euclideanSq (correctorColumn S a i x) + 2 := by
  have e : (S.corrector (unitVector i)).grad a x = correctorColumn S a i x + -unitVector i := by
    unfold correctorColumn
    abel
  rw [e]
  have h := euclideanSq_add_le (correctorColumn S a i x) (-unitVector i)
  have h1 : euclideanSq (-unitVector i : Vec d) = 1 := by
    rw [← euclideanSq_unitVector i]
    simp [euclideanSq, dot]
  linarith

/-- The oscillation bound of E8 at the radius `t`. -/
def correctorOscillation (d : ℕ) (C₈ κ t : ℝ) : ℝ :=
  2 ^ d * (C₈ * (2 * t) ^ (1 - κ)) ^ 2 * (t ^ d * volume.real (ball (0 : Vec d) 1))

/-- The energy density of the corrector gradients from E8. -/
def correctorEnergyDensity (d : ℕ) (C₈ : ℝ) : ℝ := 2 * (2 ^ (d + 1) * (1 + C₈ ^ 2)) + 2

/-- **The smoothed observation of one corrector above the minimal scale.** -/
theorem corrector_smoothed_observation (S : HomogenizationData P) (a : CoefficientField d Λ)
    (i : Fin d)
    (hwg : HasWeakGradient Set.univ ((S.corrector (unitVector i)).potential a)
      ((S.corrector (unitVector i)).grad a))
    (hloc : ∀ R : ℝ, 0 < R →
      MemLp ((S.corrector (unitVector i)).potential a) 2 (volume.restrict (ball 0 R)) ∧
      MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R)))
    (hgauss : ∀ (q : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel q r x * euclideanSq (correctorColumn S a i x)))
    {z : Vec d} {t₀ C₈ κ : ℝ} (ht₀ : 1 ≤ t₀)
    (hosc : ∀ t, t₀ ≤ t → ∃ c, ∫ x in ball z t, ((S.corrector (unitVector i)).potential a x - c) ^ 2 ≤
      2 ^ d * (C₈ * (2 * t) ^ (1 - κ)) ^ 2 * volume.real (ball z t))
    (hen : ∀ t, t₀ ≤ t → ∫ x in ball z t, euclideanSq (correctorColumn S a i x) ≤
      2 ^ (d + 1) * (1 + C₈ ^ 2) * volume.real (ball z t))
    {Sr σ θ R T D : ℝ} (hS : 0 < Sr) (hσ : 0 < σ) (hθ : 0 < θ) (hρ1 : 1 ≤ σ * Sr)
    (h4 : 4 * (Sr / θ) ≤ R) (hRT : R ≤ T) (ht₀R : t₀ ≤ R) (hD : 0 ≤ D)
    (hsmall : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((R / 2) ^ 2) / (8 * (σ * Sr) ^ 2)) ≤ 1 / 2)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0) (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2) :
    let φ := (S.corrector (unitVector i)).potential a
    let g := (S.corrector (unitVector i)).grad a
    let ρ := σ * Sr
    let c := (∫ y, χ y * heatKernel z ρ y * φ y) / ∫ y, χ y * heatKernel z ρ y
    let V := correctorOscillation d C₈ κ
    let M := correctorEnergyDensity d C₈
    let Eg := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((Sr / θ) ^ 2 / (4 * (Real.sqrt 2 * ρ) ^ 2)) *
      (gaussianBallConstant d * (M * volume.real (ball (0 : Vec d) 1)) * t₀ ^ d)
    let W := 2 * V T + 8 * heatKernelPeak d ρ ^ 2 * volume.real (ball z T) ^ 2 * V T
    (localizationObjective z T Sr σ θ (fun x => φ x - c) ≤
      2 * (Sr / θ) ^ 2 * d * (∫ w, (volume.real (ball z (Sr / θ)))⁻¹ *
          euclideanNorm (∫ x, heatKernel (z + w.2 • (w.1 - z)) ρ x • g x) ^ (2 : ℝ)
            ∂segmentMeasure z (Sr / θ)) +
        2 * ((Sr / θ) * (d * (gaussTail' d R ρ * Real.sqrt Eg +
          D / R * gaussTail d R ρ * Real.sqrt (volume.real (ball z R) * W))) +
          gaussTail d R ρ * Real.sqrt (volume.real (ball z T) * W)) ^ 2) ∧
    ∀ p : Vec d, euclideanNorm (p - z) ≤ Sr / θ →
      euclideanNorm (∫ x, heatKernel p ρ x • g x) ≤
        Real.sqrt d * (((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) *
          (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) + D / R * heatKernelPeak d ρ) *
            Real.sqrt (volume.real (ball z R) * V R) + gaussTail' d R ρ * Real.sqrt Eg) := by
  intro φ g ρ c V M Eg W
  have ht₀0 : 0 < t₀ := zero_lt_one.trans_le ht₀
  have hφl : LocallyIntegrable φ volume := by
    have := (hwg i).1; rwa [locallyIntegrableOn_univ] at this
  have hgm : Measurable g := (S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left
  have hball0 : ∀ t : ℝ, 0 < euclideanNorm z + |t| + 1 := fun t => by
    have := zero_le_euclideanNorm z; have := abs_nonneg t; linarith
  have hφloc : ∀ t : ℝ, MemLp φ 2 (volume.restrict (ball z t)) := fun t =>
    ((hloc _ (hball0 t)).1).mono_measure
      (Measure.restrict_mono (ball_subset_originBall' z t) le_rfl)
  have hgloc : ∀ t : ℝ, IntegrableOn (fun x => euclideanSq (g x)) (ball z t) := fun t => by
    have hg := ((hloc _ (hball0 t)).2).mono_measure
      (Measure.restrict_mono (ball_subset_originBall' z t) le_rfl)
    exact integrableOn_euclideanSq_of_memLp fun k => memLp_pi_iff.mp hg k
  have hccloc : ∀ t : ℝ, IntegrableOn (fun x => euclideanSq (correctorColumn S a i x)) (ball z t) :=
    fun t => by
      have hg := ((hloc _ (hball0 t)).2).mono_measure
        (Measure.restrict_mono (ball_subset_originBall' z t) le_rfl)
      exact integrableOn_euclideanSq_of_memLp fun k =>
        (memLp_const (unitVector i k)).add (memLp_pi_iff.mp hg k)
  have hgi : ∀ (q : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel q r x * euclideanSq (g x)) := fun q r hr => by
    refine (((hgauss q r hr).const_mul 2).add ((integrable_heatKernel_mask q hr.ne').const_mul 2)).mono'
      ((contDiff_heatKernel q r).continuous.aestronglyMeasurable.mul
        (by
          have h2 : Continuous fun v : Vec d => euclideanSq v := by
            unfold euclideanSq dot
            fun_prop
          exact (h2.measurable.comp hgm).aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_pos q hr x).le
      (zero_le_euclideanSq _))]
    have := euclideanSq_grad_le S a i x
    have h0 := (heatKernel_pos q hr x).le
    calc heatKernel q r x * euclideanSq (g x) ≤
          heatKernel q r x * (2 * euclideanSq (correctorColumn S a i x) + 2) :=
          mul_le_mul_of_nonneg_left this h0
      _ = 2 * (heatKernel q r x * euclideanSq (correctorColumn S a i x)) +
          2 * heatKernel q r x := by ring
  have hosc' : ∀ t, t₀ ≤ t → ∃ c, ∫ x in ball z t, (φ x - c) ^ 2 ≤ V t := fun t ht => by
    obtain ⟨c, hc⟩ := hosc t ht
    refine ⟨c, hc.trans (le_of_eq ?_)⟩
    simp only [V, correctorOscillation]
    rw [volume_real_ball_eq_mul z (ht₀0.trans_le ht)]
  have hen' : ∀ t, t₀ ≤ t → ∫ x in ball z t, euclideanSq (g x) ≤ M * volume.real (ball z t) :=
    fun t ht => by
      have h1 : ∫ x in ball z t, euclideanSq (g x) ≤
          ∫ x in ball z t, (2 * euclideanSq (correctorColumn S a i x) + 2) :=
        setIntegral_mono_on (hgloc t) (((hccloc t).const_mul 2).add (integrableOn_const
          (volume_ball_lt_top z t).ne)) (measurableSet_ball z t)
          fun x _ => euclideanSq_grad_le S a i x
      rw [integral_add ((hccloc t).const_mul 2) (integrableOn_const (volume_ball_lt_top z t).ne),
        integral_const_mul, setIntegral_const, smul_eq_mul] at h1
      have h2 := hen t ht
      simp only [M, correctorEnergyDensity]
      nlinarith [measureReal_nonneg (μ := volume) (s := ball z t)]
  have hM0 : 0 ≤ M := by
    show 0 ≤ correctorEnergyDensity d C₈
    unfold correctorEnergyDensity
    positivity
  exact smoothed_observation_pathwise hφl hwg hgm hφloc hgloc hgi ht₀
    hM0 hosc' hen' hS hσ hθ hρ1 h4 hRT ht₀R hD hsmall
    hχ hχc hχ01 hχ1 hχR hχD

end QSH
