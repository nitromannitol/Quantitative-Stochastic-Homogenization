import QuantitativeStochasticHomogenization.Ch04.Sec01.J1Quadratic
import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorSublinear
import QuantitativeStochasticHomogenization.Ch06.Sec01.GaussianWeightedEnergy
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatHessianL2
import QuantitativeStochasticHomogenization.Ch03.Sec04.BallMeanSquareScaling
import QuantitativeStochasticHomogenization.Ch04.Sec06.GaussianAverageSquares

/-!
# Finite weighted energy of the corrector columns at the heat kernel masks

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1: almost surely, for every center `z` and radius `r > 0`, the corrector columns
`Wᵢ = eᵢ + ∇φ_{eᵢ}` have finite energy against the heat kernel mask `Φ_{z,r}`. This follows from
the energy bound of Lemma 3.17 above the random scale of `sublinearCorrectors`: the energy of
`Wᵢ` on `B_R` is at most `M R^d` for large `R`, and the heat kernel is dominated by a sum of
indicator functions of dilated balls.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem euclideanSq_add_le (u v : Vec d) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  change ∑ k, (u + v) k * (u + v) k ≤ 2 * ∑ k, u k * u k + 2 * ∑ k, v k * v k
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (u k - v k)]

theorem euclideanSq_unitVector (i : Fin d) : euclideanSq (unitVector i) = 1 := by
  simp [euclideanSq, dot, unitVector, Pi.single_apply]

/-- **Gaussian integrability from polynomial growth on balls.** If `f ≥ 0` is measurable and
`∫_{B_R} f ≤ M R^d` for every `R ≥ R₀`, then `Φ_{z,r} f` is integrable for every center `z` and
radius `r > 0`. -/
theorem integrable_heatKernel_mul_of_lintegral_ball_le {f : Vec d → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {M R₀ : ℝ} (hM0 : 0 ≤ M) (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ENNReal.ofReal (f y) ≤ ENNReal.ofReal (M * R ^ d))
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => heatKernel z r x * f x) := by
  set s : ℝ := max (r ^ 2) (max (R₀ ^ 2) (euclideanNorm z ^ 2)) with hs
  have hrs : r ^ 2 ≤ s := le_max_left _ _
  have hR₀s : R₀ ^ 2 ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hzs : euclideanNorm z ≤ Real.sqrt s := by
    have hz0 : 0 ≤ euclideanNorm z := Real.sqrt_nonneg _
    calc euclideanNorm z = Real.sqrt (euclideanNorm z ^ 2) := (Real.sqrt_sq hz0).symm
      _ ≤ Real.sqrt s := Real.sqrt_le_sqrt ((le_max_right _ _).trans (le_max_right _ _))
  have hr2 : 0 < r ^ 2 := by positivity
  have hlint := lintegral_mul_heatKernel_le (f := fun y =>
    ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hfm)
    hM0 hR₀ hball hR₀s hzs
  have hnonneg : ∀ x, 0 ≤ heatKernel z r x * f x := fun x =>
    mul_nonneg (euclideanHeatKernel_nonneg (sq_nonneg r) _) (hf0 x)
  have hmeas : AEStronglyMeasurable
      (fun x => heatKernel z r x * f x) volume := by
    refine (Measurable.mul ?_ hfm).aestronglyMeasurable
    exact ((continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mpr ?_⟩
  set c₀ : ℝ := (s / r ^ 2) ^ ((d : ℝ) / 2) with hc₀
  calc ∫⁻ x, ENNReal.ofReal (heatKernel z r x * f x)
      ≤ ∫⁻ x, ENNReal.ofReal c₀ * (ENNReal.ofReal (f x) *
          ENNReal.ofReal (euclideanHeatKernel s (x - z))) := by
        refine lintegral_mono fun x => ?_
        have hk := euclideanHeatKernel_le_mul (d := d) hr2 hrs (x - z)
        have hsq : 0 ≤ f x := hf0 x
        have hks : 0 ≤ euclideanHeatKernel s (x - z) :=
          euclideanHeatKernel_nonneg (le_trans hr2.le hrs) _
        rw [← ENNReal.ofReal_mul hsq, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc heatKernel z r x * f x
            ≤ (c₀ * euclideanHeatKernel s (x - z)) * f x :=
              mul_le_mul_of_nonneg_right hk hsq
          _ = c₀ * (f x * euclideanHeatKernel s (x - z)) := by
              ring
    _ = ENNReal.ofReal c₀ * ∫⁻ x, ENNReal.ofReal (f x) *
          ENNReal.ofReal (euclideanHeatKernel s (x - z)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)

/-- **Finite Gaussian energy of the corrector columns.** Almost surely, for every `i`, every
center `z` and every radius `r > 0`, `Φ_{z,r} |eᵢ + ∇φ_{eᵢ}|²` is integrable. -/
theorem ae_integrable_heatKernel_mul_euclideanSq_correctorColumn (hd : 2 ≤ d) {Λ : ℝ}
    (hΛ : 1 < Λ) {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (S : HomogenizationData P) :
    ∀ᵐ a ∂P, ∀ (i : Fin d) (z : Vec d) (r : ℝ), 0 < r →
      Integrable (fun x => heatKernel z r x * euclideanSq (correctorColumn S a i x)) := by
  obtain ⟨β, C, -, hC, hE8⟩ := sublinearCorrectors d hd Λ hΛ
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  obtain ⟨Cs, -, hE8s⟩ := hE8 1 one_pos hd1
  have hunit : ∀ i : Fin d, euclideanNorm (unitVector i) = 1 := fun i => by
    rw [euclideanNorm, euclideanSq_unitVector, Real.sqrt_one]
  have hall : ∀ᵐ a ∂P, ∀ i : Fin d, ∃ R₀ : ℝ, 0 < R₀ ∧
      (∀ R : ℝ, R₀ ≤ R → Real.sqrt (⨍ x in ball 0 R,
        euclideanSq ((S.corrector (unitVector i)).grad a x)) ≤ C) ∧
      (∀ R : ℝ, 0 < R →
        MemLp ((S.corrector (unitVector i)).grad a) 2 (volume.restrict (ball 0 R))) := by
    rw [ae_all_iff]
    intro i
    obtain ⟨⟨F⟩, hF⟩ := hE8s P hP (unitVector i) (hunit i) (S.corrector (unitVector i))
    obtain ⟨X, -, -, hX⟩ := hF F
    filter_upwards [hX, (S.corrector (unitVector i)).locally_square_integrable] with a ha hloc
    exact ⟨X a, by linarith [ha.1], fun R hR => (ha.2 R hR).2, fun R hR => (hloc R hR).2⟩
  filter_upwards [hall] with a ha
  intro i z r hr
  obtain ⟨R₀, hR₀, hbd, hmem⟩ := ha i
  set g := (S.corrector (unitVector i)).grad a with hg
  have hgm : Measurable g :=
    Measurable.of_uncurry_left (f := fun a y => (S.corrector (unitVector i)).grad a y)
      (S.corrector (unitVector i)).measurable_grad
  have hsqc : Continuous fun v : Vec d => euclideanSq v := by
    unfold euclideanSq dot
    fun_prop
  have hWm : Measurable fun y => euclideanSq (correctorColumn S a i y) :=
    hsqc.measurable.comp (measurable_const.add hgm)
  set V₁ := volume.real (ball (0 : Vec d) 1) with hV₁
  have hV₁0 : 0 < V₁ := ball_volume_pos_finite d 1 one_pos
  set M : ℝ := 2 * (1 + C ^ 2) * V₁ with hM
  have hM0 : 0 ≤ M := by positivity
  have hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R,
      ENNReal.ofReal (euclideanSq (correctorColumn S a i y)) ≤ ENNReal.ofReal (M * R ^ d) := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
    have hV : volume.real (ball (0 : Vec d) R) = R ^ d * V₁ := volume_real_euclideanBall R hRpos
    have hVpos : 0 < volume.real (ball (0 : Vec d) R) := ball_volume_pos_finite d R hRpos
    have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hVpos).2.ne
    have hint : Integrable (fun y => euclideanSq (g y)) (volume.restrict (ball 0 R)) := by
      refine (((hmem R hRpos).norm.integrable_sq).const_mul (d : ℝ)).mono'
        (hsqc.measurable.comp hgm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have h0 : 0 ≤ euclideanSq (g y) := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact euclideanSq_le_card_mul_norm_sq _
    have hint2 : Integrable (fun y => 2 + 2 * euclideanSq (g y)) (volume.restrict (ball 0 R)) :=
      (integrable_const _).add (hint.const_mul _)
    have hnn : 0 ≤ᵐ[volume.restrict (ball (0 : Vec d) R)] fun y => 2 + 2 * euclideanSq (g y) :=
      Filter.Eventually.of_forall fun y => by
        have : 0 ≤ euclideanSq (g y) := by
          unfold euclideanSq dot
          exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
        show (0 : ℝ) ≤ 2 + 2 * euclideanSq (g y)
        linarith
    have havg : ⨍ x in ball (0 : Vec d) R, euclideanSq (g x) ≤ C ^ 2 := by
      have h0 : 0 ≤ ⨍ x in ball (0 : Vec d) R, euclideanSq (g x) := by
        rw [setAverage_eq, smul_eq_mul]
        refine mul_nonneg (inv_nonneg.mpr hVpos.le) (integral_nonneg fun x => ?_)
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
      calc ⨍ x in ball (0 : Vec d) R, euclideanSq (g x)
          = (Real.sqrt (⨍ x in ball (0 : Vec d) R, euclideanSq (g x))) ^ 2 :=
            (Real.sq_sqrt h0).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hbd R hR) 2
    have hintR : ∫ x in ball (0 : Vec d) R, euclideanSq (g x) =
        volume.real (ball (0 : Vec d) R) * ⨍ x in ball (0 : Vec d) R, euclideanSq (g x) := by
      rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]
    calc ∫⁻ y in ball 0 R, ENNReal.ofReal (euclideanSq (correctorColumn S a i y))
        ≤ ∫⁻ y in ball 0 R, ENNReal.ofReal (2 + 2 * euclideanSq (g y)) := by
          refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
          have h := euclideanSq_add_le (unitVector i) (g y)
          rw [euclideanSq_unitVector] at h
          simpa [correctorColumn, hg] using h
      _ = ENNReal.ofReal (∫ y in ball 0 R, (2 + 2 * euclideanSq (g y))) :=
          (ofReal_integral_eq_lintegral_ofReal hint2 hnn).symm
      _ ≤ ENNReal.ofReal (M * R ^ d) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul,
            setIntegral_const, smul_eq_mul, hintR]
          have hVR : 0 ≤ volume.real (ball (0 : Vec d) R) := hVpos.le
          calc volume.real (ball (0 : Vec d) R) * 2 +
                2 * (volume.real (ball (0 : Vec d) R) * ⨍ x in ball (0 : Vec d) R, euclideanSq (g x))
              ≤ volume.real (ball (0 : Vec d) R) * 2 +
                2 * (volume.real (ball (0 : Vec d) R) * C ^ 2) := by gcongr
            _ = M * R ^ d := by rw [hV, hM]; ring
  exact integrable_heatKernel_mul_of_lintegral_ball_le hWm
    (fun x => by unfold euclideanSq dot; exact Finset.sum_nonneg fun l _ => mul_self_nonneg _)
    hM0 hR₀ hball z hr

end QSH
