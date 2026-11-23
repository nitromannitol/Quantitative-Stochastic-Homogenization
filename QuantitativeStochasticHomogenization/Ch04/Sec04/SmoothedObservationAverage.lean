import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationEnergy

/-!
# The localization objective of a function with a weak gradient by its segment average

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (SCOTT-localization (5)). Averaging the squared truncated observations over
`y ∈ B_{S/θ}(z)` gives, for the cut-off Gaussian mean `c`,
`I_{z,T,S,σ,θ}[φ - c] ≤ 2 (S/θ)² d Q + 2 E²`, where `Q` is the segment average of the squared
Gaussian gradient averages `|∫ Φ_{p,σS} ∇φ|²` and `E` collects the three error terms; and `Q` is at
most the square of any bound of these averages on `B_{S/θ}(z)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem segmentMeasure_eq_restrict (z : Vec d) (R₁ : ℝ) :
    segmentMeasure z R₁ = ((volume : Measure (Vec d)).prod (volume : Measure ℝ)).restrict
      (ball z R₁ ×ˢ Set.Ioc (0 : ℝ) 1) := by
  unfold segmentMeasure
  rw [Measure.prod_restrict]

/-- A continuous function is integrable for the segment measure. -/
theorem integrable_segmentMeasure_of_continuous {F : Vec d × ℝ → ℝ} (hF : Continuous F)
    (z : Vec d) (R₁ : ℝ) : Integrable F (segmentMeasure z R₁) := by
  rw [segmentMeasure_eq_restrict]
  have hK : IsCompact (Metric.closedBall z R₁ ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall z R₁).prod isCompact_Icc
  refine (hF.continuousOn.integrableOn_compact hK).mono_set ?_
  exact Set.prod_mono (ball_subset_metric_closedBall z R₁) Set.Ioc_subset_Icc_self

theorem mem_ball_of_segment {z y : Vec d} {R₁ t : ℝ} (hy : y ∈ ball z R₁) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    euclideanNorm (z + t • (y - z) - z) ≤ R₁ := by
  rw [add_sub_cancel_left, euclideanNorm_smul_of_zero_le t ht.1.le]
  have hy' : euclideanNorm (y - z) < R₁ := hy
  have : t * euclideanNorm (y - z) ≤ 1 * euclideanNorm (y - z) :=
    mul_le_mul_of_nonneg_right ht.2 (zero_le_euclideanNorm _)
  linarith

/-- **The segment average is at most the square of a bound on the ball.** -/
theorem segmentAverage_le_sq {Ω : Type*} {N : Vec d → Ω → ℝ} {z : Vec d} {R₁ M : ℝ}
    (hR₁ : 0 < R₁) (ω : Ω) (hN0 : ∀ p, 0 ≤ N p ω)
    (hN : ∀ p, euclideanNorm (p - z) ≤ R₁ → N p ω ≤ M) :
    segmentAverage N z R₁ ω ≤ M ^ 2 := by
  have hB : 0 < volume.real (ball z R₁) := volume_real_ball_pos z hR₁
  unfold segmentAverage
  have hle : ∀ᵐ w ∂segmentMeasure z R₁,
      (volume.real (ball z R₁))⁻¹ * N (z + w.2 • (w.1 - z)) ω ^ (2 : ℝ) ≤
        (volume.real (ball z R₁))⁻¹ * M ^ 2 := by
    rw [segmentMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_ball z R₁ |>.prod measurableSet_Ioc)] with w hw
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hB.le)
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (hN0 _) (hN _ (mem_ball_of_segment hw.1 hw.2)) 2
  calc ∫ w, (volume.real (ball z R₁))⁻¹ * N (z + w.2 • (w.1 - z)) ω ^ (2 : ℝ) ∂segmentMeasure z R₁
      ≤ ∫ _w, (volume.real (ball z R₁))⁻¹ * M ^ 2 ∂segmentMeasure z R₁ :=
        integral_mono_of_nonneg (Eventually.of_forall fun w =>
          mul_nonneg (inv_nonneg.2 hB.le) (Real.rpow_nonneg (hN0 _) _))
          (integrable_const _) hle
    _ = M ^ 2 := by
        rw [integral_const, smul_eq_mul, segmentMeasure_real_univ, ← mul_assoc,
          mul_inv_cancel₀ hB.ne', one_mul]

/-- **The localization objective at the cut-off Gaussian mean** by the segment average of the
squared Gaussian gradient averages and the error terms. -/
theorem localizationObjective_le_segment {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hφl : LocallyIntegrable φ volume) (hφg : HasWeakGradient Set.univ φ g)
    (hgm : AEStronglyMeasurable g volume)
    (hgi : ∀ (q : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel q r x * euclideanSq (g x)))
    {z : Vec d} {S σ θ R T D c Eg W : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hθ : 0 < θ)
    (h4 : 4 * (S / θ) ≤ R) (hRT : R ≤ T) (hD : 0 ≤ D)
    (hgv : ∀ q : Vec d, Integrable (fun x => heatKernel q (σ * S) x • g x))
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ ball z (R / 2), χ x = 1)
    (hχR : ∀ x, x ∉ ball z R → χ x = 0) (hχD : ∀ x, euclideanSq (gradient χ x) ≤ (D / R) ^ 2)
    (hφT : MemLp φ 2 (volume.restrict (ball z T)))
    (hc : ∫ x, χ x * heatKernel z (σ * S) x * (φ x - c) = 0)
    (hEg : ∀ q, euclideanNorm (q - z) ≤ S / θ →
      ∫ x, heatKernel q (Real.sqrt 2 * (σ * S)) x * euclideanSq (g x) ≤ Eg)
    (hW : ∫ x in ball z T, (φ x - c) ^ 2 ≤ W) :
    localizationObjective z T S σ θ (fun x => φ x - c) ≤
      2 * (S / θ) ^ 2 * d * (∫ w, (volume.real (ball z (S / θ)))⁻¹ *
          euclideanNorm (∫ x, heatKernel (z + w.2 • (w.1 - z)) (σ * S) x • g x) ^ (2 : ℝ)
            ∂segmentMeasure z (S / θ)) +
        2 * ((S / θ) * (d * (gaussTail' d R (σ * S) * Real.sqrt Eg +
          D / R * gaussTail d R (σ * S) * Real.sqrt (volume.real (ball z R) * W))) +
          gaussTail d R (σ * S) * Real.sqrt (volume.real (ball z T) * W)) ^ 2 := by
  have hR₁ : 0 < S / θ := div_pos hS hθ
  have hρ : 0 < σ * S := mul_pos hσ hS
  set R₁ := S / θ with hR₁def
  set ρ := σ * S with hρdef
  set E := R₁ * (d * (gaussTail' d R ρ * Real.sqrt Eg +
    D / R * gaussTail d R ρ * Real.sqrt (volume.real (ball z R) * W))) +
      gaussTail d R ρ * Real.sqrt (volume.real (ball z T) * W) with hE
  have hB : 0 < volume.real (ball z R₁) := volume_real_ball_pos z hR₁
  have hρ' : 0 < Real.sqrt 2 * ρ := mul_pos (Real.sqrt_pos.2 two_pos) hρ
  set Gv : Vec d → Vec d := fun p => ∫ x, heatKernel p ρ x • g x with hGv
  have hGc : Continuous Gv := continuous_heatKernel_average hgm hρ fun p => hgi p _ hρ'
  set F₂ : Vec d × ℝ → ℝ := fun w => euclideanSq (Gv (z + w.2 • (w.1 - z))) with hF₂
  have hF₂c : Continuous F₂ := by
    have h1 : Continuous fun w : Vec d × ℝ => z + w.2 • (w.1 - z) :=
      continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))
    have h2 : Continuous fun v : Vec d => euclideanSq v := by
      unfold euclideanSq dot
      fun_prop
    exact h2.comp (hGc.comp h1)
  have hF₂i := integrable_segmentMeasure_of_continuous hF₂c z R₁
  have hF₂i' : Integrable F₂ ((volume.restrict (ball z R₁)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) := hF₂i
  have hIy := hF₂i'.integral_prod_left
  -- the pointwise bound
  have hpt : ∀ y ∈ ball z R₁, (∫ x in ball z T, heatKernel y ρ x * (φ x - c)) ^ 2 ≤
      2 * R₁ ^ 2 * d * (∫ t in Set.Ioc (0 : ℝ) 1, F₂ (y, t)) + 2 * E ^ 2 := fun y hy => by
    have h := sq_truncated_observation_le hφl hφg hgm hgi hR₁ h4 hRT hρ hD hgv hχ hχc hχ01 hχ1
      hχR hχD hφT hc hEg hW hy
    rw [intervalIntegral.integral_of_le zero_le_one] at h
    exact h
  have hgi2 : Integrable (fun y => 2 * R₁ ^ 2 * d * (∫ t in Set.Ioc (0 : ℝ) 1, F₂ (y, t)) +
      2 * E ^ 2) (volume.restrict (ball z R₁)) :=
    (hIy.const_mul _).add (integrable_const _)
  have hmono : ∫ y in ball z R₁, (∫ x in ball z T, heatKernel y ρ x * (φ x - c)) ^ 2 ≤
      ∫ y in ball z R₁, (2 * R₁ ^ 2 * d * (∫ t in Set.Ioc (0 : ℝ) 1, F₂ (y, t)) + 2 * E ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) hgi2
      ((ae_restrict_mem (measurableSet_ball z R₁)).mono fun y hy => hpt y hy)
  have hfub : ∫ y in ball z R₁, (∫ t in Set.Ioc (0 : ℝ) 1, F₂ (y, t)) =
      ∫ w, F₂ w ∂segmentMeasure z R₁ := (integral_prod F₂ hF₂i').symm
  rw [integral_add (hIy.const_mul _) (integrable_const _), integral_const_mul, hfub,
    setIntegral_const, smul_eq_mul] at hmono
  have hQ : ∫ w, (volume.real (ball z R₁))⁻¹ * euclideanNorm (Gv (z + w.2 • (w.1 - z))) ^ (2 : ℝ)
      ∂segmentMeasure z R₁ = (volume.real (ball z R₁))⁻¹ * ∫ w, F₂ w ∂segmentMeasure z R₁ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hF₂, Real.rpow_two, sq_euclideanNorm]
  unfold localizationObjective
  rw [setAverage_eq, smul_eq_mul, hQ]
  have hBinv : 0 < (volume.real (ball z R₁))⁻¹ := inv_pos.2 hB
  have key := mul_le_mul_of_nonneg_left hmono hBinv.le
  calc (volume.real (ball z R₁))⁻¹ *
        ∫ y in ball z R₁, (∫ x in ball z T, heatKernel y ρ x * (φ x - c)) ^ 2
      ≤ (volume.real (ball z R₁))⁻¹ * (2 * R₁ ^ 2 * d * ∫ w, F₂ w ∂segmentMeasure z R₁ +
          volume.real (ball z R₁) * (2 * E ^ 2)) := key
    _ = 2 * R₁ ^ 2 * d * ((volume.real (ball z R₁))⁻¹ * ∫ w, F₂ w ∂segmentMeasure z R₁) +
          2 * E ^ 2 := by
        field_simp

end QSH
