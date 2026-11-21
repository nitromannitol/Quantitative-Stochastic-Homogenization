import QuantitativeStochasticHomogenization.Ch04.Sec03.AveragesFromEnergy

/-!
# The energy bound below the scale from Proposition 3.21

The mask `Φ_{z,r}` is at most `(R/r)^d Φ_{z,R}` for `r ≤ R` (`heatKernel_le_mul`). Above the
scale of Proposition 3.21 the averaged energy is at most `(K + 2C) |ξ|²` when `ξ·āξ ≤ K |ξ|²`;
below it, comparing with the mask at the scale gives `(X/r)^d (K + 2C) |ξ|²`. Hence Proposition
3.21 gives the energy bound below the scale (`gaussianEnergyBound_of_rate`), and (5.58) holds
without it and without the integrability of the averages and of the trial
(`estimate558_of_heatIdentityBound`).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- `Φ_{z,r} ≤ (R/r)^d Φ_{z,R}` for `0 < r ≤ R`. -/
theorem heatKernel_le_mul (z : Vec d) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (x : Vec d) :
    heatKernel z r x ≤ (R / r) ^ d * heatKernel z R x := by
  have hR : 0 < R := hr.trans_le hrR
  unfold heatKernel euclideanHeatKernel
  have hq : 0 ≤ euclideanSq (x - z) := euclideanSq_nonneg _
  have hexp : Real.exp (-euclideanSq (x - z) / (4 * r ^ 2)) ≤
      Real.exp (-euclideanSq (x - z) / (4 * R ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hq (by positivity) (by nlinarith)
  have hpre : (4 * Real.pi * r ^ 2) ^ (-(d : ℝ) / 2) =
      (R / r) ^ d * (4 * Real.pi * R ^ 2) ^ (-(d : ℝ) / 2) := by
    have e1 : 4 * Real.pi * r ^ 2 = (4 * Real.pi * R ^ 2) * (r / R) ^ 2 := by
      field_simp
    have hrR0 : 0 ≤ r / R := div_nonneg hr.le hR.le
    rw [e1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (r / R) 2,
      ← Real.rpow_mul hrR0, show ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by push_cast; ring,
      Real.rpow_neg hrR0, Real.rpow_natCast, ← inv_pow, inv_div, mul_comm]
  rw [hpre, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp
    (Real.rpow_nonneg (by positivity) _)) (pow_nonneg (div_nonneg hR.le hr.le) _)

/-- **The energy bound below the scale from Proposition 3.21** and an upper bound
`ξ·āξ ≤ K |ξ|²`. -/
theorem gaussianEnergyBound_of_rate {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    (S : HomogenizationData P) {K : ℝ}
    (hK : ∀ ξ : Vec d, dot ξ (S.homogenized.mulVec ξ) ≤ K * euclideanSq ξ) {τ C μ : ℝ}
    (hτ : 0 < τ) (hμ : 0 ≤ μ) (hrate : GaussianCorrectorRate P S τ C μ) :
    ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN := by
  obtain ⟨X, hXm, hX⟩ := hrate
  have hC : 0 < C := (hX 0).1.scale_pos
  set CM : ℝ := (2 : ℝ) ^ τ⁻¹ * max C (1 / Real.log 2 ^ τ⁻¹) with hCMdef
  have hX'os : ∀ z, OsBound P (fun a => max (X a z) 1) τ CM := fun z =>
    osBound_max (hX z).1 (osBound_of_le_const measurable_const hτ one_pos
      (Eventually.of_forall fun _ => le_rfl))
  have hCM : 0 < CM := (hX'os 0).scale_pos
  set CE : ℝ := K + 2 * C with hCEdef
  have hCN0 : 0 ≤ max CM CE := le_max_of_le_left hCM.le
  refine ⟨max CM CE, lt_max_of_lt_left hCM, fun a z => max (X a z) 1, hXm.max measurable_const,
    fun a z => le_max_right _ _, fun z => (hX'os z).mono_scale (le_max_left _ _), fun z => ?_⟩
  filter_upwards [(hX z).2] with a ha
  intro r hr ξ
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hs := euclideanSq_nonneg ξ
  -- above the scale
  have hup : ∀ R : ℝ, 1 ≤ R → X a z ≤ R →
      Integrable (fun x => heatKernel z R x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∧
      (∫ x, heatKernel z R x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ≤
        CE * euclideanSq ξ := by
    intro R hR1 hXR
    obtain ⟨-, -, h3, -, -, h6⟩ := ha R hR1 hXR ξ
    refine ⟨h3, ?_⟩
    have hε : C * R ^ (-μ) ≤ C :=
      mul_le_of_le_one_right hC.le (Real.rpow_le_one_of_one_le_of_nonpos hR1 (neg_nonpos.mpr hμ))
    rw [euclideanNorm_sq] at h6
    have h6' := (abs_le.mp h6).2
    have h7 : 2 * (C * R ^ (-μ)) * euclideanSq ξ ≤ 2 * C * euclideanSq ξ := by nlinarith
    have h8 := hK ξ
    rw [hCEdef]
    nlinarith
  by_cases hXr : X a z ≤ r
  · obtain ⟨h1, h2⟩ := hup r hr hXr
    refine ⟨h1, h2.trans ?_⟩
    have ht : 0 ≤ (max (X a z) 1 / r) ^ d :=
      pow_nonneg (div_nonneg (zero_le_one.trans (le_max_right _ _)) hr0.le) _
    have h9 : max CM CE ≤ max CM CE * (1 + (max (X a z) 1 / r) ^ d) :=
      le_mul_of_one_le_right hCN0 (by linarith)
    calc CE * euclideanSq ξ ≤ max CM CE * euclideanSq ξ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hs
      _ ≤ max CM CE * (1 + (max (X a z) 1 / r) ^ d) * euclideanSq ξ :=
          mul_le_mul_of_nonneg_right h9 hs
  · have hrX : r < X a z := not_le.mp hXr
    have hR1 : 1 ≤ X a z := hr.trans hrX.le
    have hR0 : 0 < X a z := zero_lt_one.trans_le hR1
    obtain ⟨h1, h2⟩ := hup (X a z) hR1 le_rfl
    have he : ∀ x, 0 ≤ dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) :=
      fun x => (euclideanSq_nonneg _).trans (a.elliptic x _).1
    have hpt : ∀ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) ≤
        (X a z / r) ^ d * (heatKernel z (X a z) x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) := fun x => by
      calc heatKernel z r x *
            dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))
          ≤ ((X a z / r) ^ d * heatKernel z (X a z) x) *
            dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) :=
            mul_le_mul_of_nonneg_right (heatKernel_le_mul z hr0 hrX.le x) (he x)
        _ = (X a z / r) ^ d * (heatKernel z (X a z) x *
            dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) := by ring
    have hm : AEStronglyMeasurable (fun x => heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) volume := by
      have hc : Continuous fun x => heatKernel z r x / heatKernel z (X a z) x :=
        ((continuous_heatKernel_uncurry r).comp (continuous_const.prodMk continuous_id)).div
          ((continuous_heatKernel_uncurry (X a z)).comp (continuous_const.prodMk continuous_id))
          fun x => (heatKernel_pos z hR0 x).ne'
      refine (hc.aestronglyMeasurable.mul h1.aestronglyMeasurable).congr
        (Eventually.of_forall fun x => ?_)
      have := (heatKernel_pos z hR0 x).ne'
      simp only [Pi.mul_apply]
      field_simp
    have hi : Integrable (fun x => heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) :=
      (h1.const_mul ((X a z / r) ^ d)).mono' hm (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg _ _ _) (he x))]
        exact hpt x)
    refine ⟨hi, ?_⟩
    have ht : 0 ≤ (X a z / r) ^ d := pow_nonneg (div_nonneg hR0.le hr0.le) _
    have hCE : CE ≤ max CM CE := le_max_right _ _
    calc (∫ x, heatKernel z r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)))
        ≤ ∫ x, (X a z / r) ^ d * (heatKernel z (X a z) x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) :=
          integral_mono hi (h1.const_mul _) hpt
      _ = (X a z / r) ^ d * ∫ x, heatKernel z (X a z) x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) :=
          integral_const_mul _ _
      _ ≤ (X a z / r) ^ d * (CE * euclideanSq ξ) := mul_le_mul_of_nonneg_left h2 ht
      _ ≤ max CM CE * (1 + (max (X a z) 1 / r) ^ d) * euclideanSq ξ := by
          rw [max_eq_left hR1]
          nlinarith [mul_nonneg hCN0 hs, mul_nonneg (mul_nonneg ht hs) (sub_nonneg.mpr hCE)]

/-- **(5.58) and Theorem 4.6 (ii)** from the inputs of `estimate558_of_heat`, without the energy
bound below the scale and the integrability of the averages and of the trial (consequences of
Proposition 3.21 and of the bounds on `ā`). -/
theorem estimate558_of_heatIdentityBound {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hd : 2 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hμ : ∀ (n : ℕ) (ξ : Vec d),
      AEStronglyMeasurable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hrate : ∀ τ : ℝ, 0 < τ → τ < d → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
      GaussianCorrectorRate P S τ C μ)
    (hexp : ∀ β : ℝ, 0 < β → β ≤ d → ExpectedAveragesEstimate P S β)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hmeasL : ∀ (r : ℝ) (p q k : Vec d),
      Measurable fun w : Vec d × CoefficientField d Λ => trialValue S w.2 w.1 r p q k)
    (hmeasF : ∀ ξ : Vec d, Measurable fun w : (Vec d × ℝ) × CoefficientField d Λ =>
      fluxAverage S w.2 w.1.1 w.1.2 ξ)
    {Ck : ℝ} (hheat : HeatIdentityBound P S Ck)
    (h411 : LocalizationEstimates P localSigma J1Heat)
    (h412 : FluctuationEstimates P localSigma J1Heat) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ExpectationJ1Estimate P S.homogenized d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        OsBound P (fun a => |J1Heat a z r p q - homogenizedJ1 S.homogenized p q|) s
          (C * r ^ (-((d : ℝ) / 2))) := by
  have hA := homogenizedMatrixBounds_of_aestronglyMeasurable S hΛ.le hμ
  have hN : ∀ τ : ℝ, 0 < τ → τ < d → ∃ CN : ℝ, 0 < CN ∧ GaussianEnergyBound P S τ CN :=
    fun τ hτ0 hτd => by
      obtain ⟨C, μ, -, hμ', hr⟩ := hrate τ hτ0 hτd
      exact gaussianEnergyBound_of_rate S (fun ξ => (hA ξ).2) hτ0 hμ'.le hr
  have hd1 : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨CN, -, hN1⟩ := hN 1 one_pos hd1
  exact estimate558_of_heat hd S hΛ hμ hspan hrate hN hexp
    (averagesIntegrable_of_energyBound S hΛ.le hN1) (trialIntegrable_of_energyBound S hΛ.le hN1)
    hmeasJ hmeasL hmeasF hheat h411 h412 hs0 hs2

end QSH
