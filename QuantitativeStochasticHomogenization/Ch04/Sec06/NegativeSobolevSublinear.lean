import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevLinearEstimates
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatFormula
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatGram

/-!
# Section 4.6: (4.126) from the commutator estimate and the linear estimate

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126). The Gaussian energy of `e + ∇φ_e(·/ε)` at the unit scale needed in
`negativeSobolevCorrector_of_corrector_energy_bounds` follows from the energy bound of
Lemma 3.17 above the minimal scale (`sublinearCorrectors`):

* if `∫_{B_R} f ≤ M R^d` for `R ≥ X ≥ 1`, then `∫ Φ_{0,ρ} f ≤ K_d M X^d` for every `ρ ≥ 1`, from the
  shell decomposition of the heat kernel above the scale `X` and the comparison
  `Φ_{0,ρ} ≤ (X/ρ)^d Φ_{0,X}` below it (`integral_heatKernel_mul_le_of_ball`);
* `|G ξ|² ≤ |ξ|² ∑ᵢ |eᵢ + ∇φ_{eᵢ}|²`, so the scales `Xᵢ = O_{d/2}(C)` of the coordinate correctors
  give `(∫ |e + ∇φ_e(ε⁻¹ x)|² e^{-‖x‖²/32} dx)^{1/2} ≤ B ∑ᵢ Xᵢ^{d/2} = O_1(B d C^{d/2})` for the
  linearized correctors (`unitScaleEnergy_of_sublinear`).

The same bound gives the integrability of the Gaussian averages of the corrected fields for every
law (`averagesIntegrable_of_lawHypotheses`). Hence the frozen statement follows from the commutator
estimate (4.34) and the linear estimate at the exponents `1` and `d/2` with constants uniform over
the laws (`negativeSobolevCorrector_of_commutator_linear`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Gaussian averages from averages on balls -/

/-- The constant `(4π)^{-d/2} (2^d + ∑ₖ e^{-(k+1)²/4} (k+3)^d)` of `lintegral_mul_heatKernel_le`. -/
def gaussianBallConstant (d : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ d + gaussianShellSum d)

theorem gaussianBallConstant_pos (d : ℕ) : 0 < gaussianBallConstant d := by
  unfold gaussianBallConstant
  have := gaussianShellSum_nonneg d
  positivity

/-- **Gaussian averages at every radius `ρ ≥ 1`** from `∫_{B_R} f ≤ M R^d` for `R ≥ X ≥ 1`:
`∫ Φ_{0,ρ} f ≤ K_d M X^d`. -/
theorem integral_heatKernel_mul_le_of_ball {f : Vec d → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {M X : ℝ} (hM0 : 0 ≤ M) (hX : 1 ≤ X)
    (hball : ∀ R : ℝ, X ≤ R → ∫⁻ y in ball 0 R, ENNReal.ofReal (f y) ≤ ENNReal.ofReal (M * R ^ d))
    {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∫ x, heatKernel 0 ρ x * f x ≤ gaussianBallConstant d * M * X ^ d := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hK0 := (gaussianBallConstant_pos d).le
  have hKM : 0 ≤ gaussianBallConstant d * M := mul_nonneg hK0 hM0
  have hint : ∀ r : ℝ, 0 < r → Integrable (fun x => heatKernel 0 r x * f x) := fun r hr =>
    integrable_heatKernel_mul_of_lintegral_ball_le hfm hf0 hM0 hX0 hball 0 hr
  have habove : ∀ R : ℝ, X ≤ R → ∫ x, heatKernel 0 R x * f x ≤ gaussianBallConstant d * M := by
    intro R hR
    have hR0 : 0 < R := hX0.trans_le hR
    have hs : X ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hX0.le hR 2
    have hx : euclideanNorm (0 : Vec d) ≤ Real.sqrt (R ^ 2) := by
      rw [Real.sqrt_sq hR0.le]
      simp [euclideanNorm, euclideanSq, dot, hR0.le]
    have hl := lintegral_mul_heatKernel_le (f := fun y => ENNReal.ofReal (f y))
      (ENNReal.measurable_ofReal.comp hfm) hM0 hX0 hball hs hx
    have hnn : ∀ x, 0 ≤ heatKernel 0 R x * f x := fun x =>
      mul_nonneg (heatKernel_nonneg 0 R x) (hf0 x)
    have heq : ENNReal.ofReal (∫ x, heatKernel 0 R x * f x) =
        ∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (euclideanHeatKernel (R ^ 2) (y - 0)) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hint R hR0) (Eventually.of_forall hnn)]
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.ofReal_mul (hf0 y), mul_comm]
      rfl
    exact (ENNReal.ofReal_le_ofReal_iff hKM).1 (heq.trans_le hl)
  have hXd : 1 ≤ X ^ d := one_le_pow₀ hX
  rcases le_or_gt X ρ with hXρ | hρX
  · calc ∫ x, heatKernel 0 ρ x * f x ≤ gaussianBallConstant d * M := habove ρ hXρ
      _ ≤ gaussianBallConstant d * M * X ^ d := le_mul_of_one_le_right hKM hXd
  · have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
    have hle : ∀ x, heatKernel 0 ρ x * f x ≤ (X / ρ) ^ d * (heatKernel 0 X x * f x) := fun x => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (heatKernel_le_mul 0 hρ0 hρX.le x) (hf0 x)
    have hXρd : (X / ρ) ^ d ≤ X ^ d :=
      pow_le_pow_left₀ (div_nonneg hX0.le hρ0.le) (div_le_self hX0.le hρ) d
    calc ∫ x, heatKernel 0 ρ x * f x ≤ ∫ x, (X / ρ) ^ d * (heatKernel 0 X x * f x) :=
          integral_mono (hint ρ hρ0) ((hint X hX0).const_mul _) hle
      _ = (X / ρ) ^ d * ∫ x, heatKernel 0 X x * f x := integral_const_mul _ _
      _ ≤ X ^ d * (gaussianBallConstant d * M) :=
          mul_le_mul hXρd (habove X le_rfl) (integral_nonneg fun x =>
            mul_nonneg (heatKernel_nonneg 0 X x) (hf0 x)) (zero_le_one.trans hXd)
      _ = gaussianBallConstant d * M * X ^ d := by ring

/-- **The energy of a corrected coordinate on large balls**: if the normalized `L²(B_R)` norm of
`g` is at most `C` for `R ≥ R₀`, then `∫_{B_R} |eᵢ + g|² ≤ 2 (1 + C²) |B_1| R^d` for `R ≥ R₀`. -/
theorem lintegral_ball_unitVector_add_le {g : Vec d → Vec d} (hgm : Measurable g) {C R₀ : ℝ}
    (hR₀ : 0 < R₀)
    (hbd : ∀ R : ℝ, R₀ ≤ R → Real.sqrt (⨍ x in ball 0 R, euclideanSq (g x)) ≤ C)
    (hmem : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R))) (i : Fin d) :
    ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ENNReal.ofReal (euclideanSq (unitVector i + g y)) ≤
      ENNReal.ofReal (2 * (1 + C ^ 2) * volume.real (ball (0 : Vec d) 1) * R ^ d) := by
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
  have hV : volume.real (ball (0 : Vec d) R) = R ^ d * volume.real (ball (0 : Vec d) 1) :=
    volume_real_euclideanBall R hRpos
  have hVpos : 0 < volume.real (ball (0 : Vec d) R) := ball_volume_pos_finite d R hRpos
  have hsqm : Measurable fun y => euclideanSq (g y) := measurable_euclideanSq.comp hgm
  have hint : Integrable (fun y => euclideanSq (g y)) (volume.restrict (ball 0 R)) :=
    integrable_euclideanSq_of_memLp (hmem R hRpos)
  have hint2 : Integrable (fun y => 2 + 2 * euclideanSq (g y)) (volume.restrict (ball 0 R)) :=
    (integrable_const _).add (hint.const_mul _)
  have hnn : 0 ≤ᵐ[volume.restrict (ball (0 : Vec d) R)] fun y => 2 + 2 * euclideanSq (g y) :=
    Eventually.of_forall fun y => by
      have := euclideanSq_nonneg (g y)
      change (0 : ℝ) ≤ 2 + 2 * euclideanSq (g y)
      linarith
  have havg : ⨍ x in ball (0 : Vec d) R, euclideanSq (g x) ≤ C ^ 2 := by
    have h0 : 0 ≤ ⨍ x in ball (0 : Vec d) R, euclideanSq (g x) :=
      setAverage_nonneg_of_nonneg fun x => euclideanSq_nonneg _
    calc ⨍ x in ball (0 : Vec d) R, euclideanSq (g x)
        = (Real.sqrt (⨍ x in ball (0 : Vec d) R, euclideanSq (g x))) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hbd R hR) 2
  have hintR : ∫ x in ball (0 : Vec d) R, euclideanSq (g x) =
      volume.real (ball (0 : Vec d) R) * ⨍ x in ball (0 : Vec d) R, euclideanSq (g x) := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]
  calc ∫⁻ y in ball 0 R, ENNReal.ofReal (euclideanSq (unitVector i + g y))
      ≤ ∫⁻ y in ball 0 R, ENNReal.ofReal (2 + 2 * euclideanSq (g y)) := by
        refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        have h := euclideanSq_add_le (unitVector i) (g y)
        rw [euclideanSq_unitVector] at h
        linarith
    _ = ENNReal.ofReal (∫ y in ball 0 R, (2 + 2 * euclideanSq (g y))) :=
        (ofReal_integral_eq_lintegral_ofReal hint2 hnn).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul,
          setIntegral_const, smul_eq_mul, hintR]
        have hVR : 0 ≤ volume.real (ball (0 : Vec d) R) := hVpos.le
        calc volume.real (ball (0 : Vec d) R) * 2 +
              2 * (volume.real (ball (0 : Vec d) R) * ⨍ x in ball (0 : Vec d) R, euclideanSq (g x))
            ≤ volume.real (ball (0 : Vec d) R) * 2 +
              2 * (volume.real (ball (0 : Vec d) R) * C ^ 2) := by gcongr
          _ = _ := by rw [hV]; ring

/-! ## The corrected fields through the corrected coordinates -/

section Fields

variable {P : Measure (CoefficientField d Λ)}

/-- `|G ξ|² ≤ |ξ|² ∑ᵢ |eᵢ + ∇φ_{eᵢ}|²`. -/
theorem euclideanSq_correctedField_le (S : HomogenizationData P) (a : CoefficientField d Λ)
    (ξ y : Vec d) :
    euclideanSq (correctedField S a ξ y) ≤
      euclideanSq ξ * ∑ i, euclideanSq (correctorColumn S a i y) := by
  have h1 : euclideanNorm (correctedField S a ξ y) ≤
      ∑ i, |ξ i| * euclideanNorm (correctorColumn S a i y) := by
    change euclideanNorm (∑ i, ξ i • correctedCoordinate S a i y) ≤ _
    refine (euclideanNorm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [euclideanNorm_smul]
    rfl
  have h2 : (∑ i, |ξ i| * euclideanNorm (correctorColumn S a i y)) ^ 2 ≤
      (∑ i, |ξ i| ^ 2) * ∑ i, euclideanNorm (correctorColumn S a i y) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i, |ξ i| ^ 2 = euclideanSq ξ := by
    change ∑ i, |ξ i| ^ 2 = ∑ i, ξ i * ξ i
    exact Finset.sum_congr rfl fun i _ => by rw [sq_abs, sq]
  have h4 : ∑ i, euclideanNorm (correctorColumn S a i y) ^ 2 =
      ∑ i, euclideanSq (correctorColumn S a i y) :=
    Finset.sum_congr rfl fun i _ => euclideanNorm_sq _
  calc euclideanSq (correctedField S a ξ y) = euclideanNorm (correctedField S a ξ y) ^ 2 :=
        (euclideanNorm_sq _).symm
    _ ≤ (∑ i, |ξ i| * euclideanNorm (correctorColumn S a i y)) ^ 2 :=
        pow_le_pow_left₀ (euclideanNorm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = _ := by rw [h3, h4]

/-- **The Gaussian averages of the corrected fields exist** for every law satisfying the
assumptions. -/
theorem averagesIntegrable_of_lawHypotheses (hd : 2 ≤ d) (hΛ : 1 < Λ) (hP : LawHypotheses P)
    (S : HomogenizationData P) : AveragesIntegrable P S := by
  intro z
  filter_upwards [ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S] with a ha
  intro r hr ξ
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hGm : Measurable (fun x => correctedField S a ξ x) :=
    (measurable_correctedField S ξ).comp measurable_prodMk_left
  have hsum : Integrable (fun x => Λ * (euclideanSq ξ *
      ∑ i, heatKernel z r x * euclideanSq (correctorColumn S a i x))) :=
    ((integrable_finsetSum _ fun i _ => ha i z r hr0).const_mul _).const_mul _
  have hE : Integrable fun x => heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
    have hm : AEStronglyMeasurable (fun x => heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) volume := by
      refine (measurable_heatKernel z r).aestronglyMeasurable.mul ?_
      have h := aestronglyMeasurable_dot_mulVec a Set.univ hGm.aestronglyMeasurable
      rwa [Measure.restrict_univ] at h
    refine hsum.mono' hm (Eventually.of_forall fun x => ?_)
    have hk := heatKernel_nonneg z r x
    have hel := a.elliptic x (correctedField S a ξ x)
    have h0 : 0 ≤ dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) :=
      (euclideanSq_nonneg _).trans hel.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk h0), ← Finset.mul_sum]
    have h1 := euclideanSq_correctedField_le S a ξ x
    have hΛ0 : 0 ≤ Λ := by linarith
    calc heatKernel z r x * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))
        ≤ heatKernel z r x * (Λ * euclideanSq (correctedField S a ξ x)) :=
          mul_le_mul_of_nonneg_left hel.2 hk
      _ ≤ heatKernel z r x * (Λ * (euclideanSq ξ * ∑ i, euclideanSq (correctorColumn S a i x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hΛ0) hk
      _ = Λ * (euclideanSq ξ * (heatKernel z r x * ∑ i, euclideanSq (correctorColumn S a i x))) := by
          ring
  obtain ⟨h1, h2⟩ := integrable_averages_of_energy a (by linarith) z hr0 hGm.aestronglyMeasurable hE
  exact ⟨h1, h2, hE⟩

/-! ## The Gaussian energy at the unit scale from Lemma 3.17 -/

/-- **The Gaussian energy of `e + ∇φ_e(ε⁻¹ ·)` at the unit scale** for the linearized correctors of
any homogenization data of any law satisfying the assumptions, with a constant depending only on
`d` and `Λ`, from the energy bound of Lemma 3.17 above the minimal scale. -/
theorem unitScaleEnergy_of_sublinear (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ R : CoefficientField d Λ → ℝ, OsBound P R 1 C₁ ∧
          ∀ᵐ a ∂P, vectorGaussianEnergy (fun x => e + (S.linearize.corrector e).grad a (ε⁻¹ • x)) ^
            (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a) := by
  obtain ⟨β, C, hβ, hC, hE8⟩ := sublinearCorrectors d hd Λ hΛ
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hτ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  obtain ⟨Cs, hCs, hE8s⟩ := hE8 ((d : ℝ) / 2) hτ (by linarith)
  set V₁ : ℝ := volume.real (ball (0 : Vec d) 1) with hV₁
  have hV₁0 : 0 < V₁ := ball_volume_pos_finite d 1 one_pos
  set M : ℝ := 2 * (1 + C ^ 2) * V₁ with hM
  have hM0 : 0 < M := by positivity
  set K : ℝ := gaussianBallConstant d with hK
  have hK0 : 0 < K := gaussianBallConstant_pos d
  set c : ℝ := ((4 * Real.pi * (8 * d)) ^ (-(d : ℝ) / 2))⁻¹ with hcdef
  have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  set B : ℝ := Real.sqrt (c * (K * M)) with hBdef
  have hB : 0 < B := Real.sqrt_pos.mpr (by positivity)
  refine ⟨B * (d * Cs ^ ((d : ℝ) / 2)), by positivity, fun P hP S e he ε hε hε2 => ?_⟩
  have hunit : ∀ i : Fin d, euclideanNorm (unitVector i) = 1 := fun i => by
    rw [euclideanNorm, euclideanSq_unitVector, Real.sqrt_one]
  have hX : ∀ i : Fin d, ∃ X : CoefficientField d Λ → ℝ, Measurable X ∧
      OsBound P X ((d : ℝ) / 2) Cs ∧ ∀ᵐ a ∂P, 1 ≤ X a ∧ ∀ r : ℝ, X a ≤ r →
        Real.sqrt (⨍ x in ball 0 r, euclideanSq ((S.corrector (unitVector i)).grad a x)) ≤ C := by
    intro i
    obtain ⟨hne, hall⟩ := hE8s P hP (unitVector i) (hunit i) (S.corrector (unitVector i))
    obtain ⟨X, hXm, hXo, hXa⟩ := hall (Classical.choice hne)
    refine ⟨X, hXm, hXo, ?_⟩
    filter_upwards [hXa] with a ha
    exact ⟨ha.1, fun r hr => (ha.2 r hr).2⟩
  choose X hXm hXo hXa using hX
  set Y : Fin d → CoefficientField d Λ → ℝ := fun i a => max (X i a) 1 with hYdef
  have hY0 : ∀ i a, 0 ≤ Y i a := fun i a => zero_le_one.trans (le_max_right _ _)
  have hYo : ∀ i, OsBound P (fun a => Y i a ^ ((d : ℝ) / 2)) 1 (Cs ^ ((d : ℝ) / 2)) := by
    intro i
    have h := ((hXo i).of_le_ae ((hXm i).max measurable_const) ?_).rpow (hY0 i) hτ
    · simpa only [div_self hτ.ne'] using h
    · filter_upwards [hXa i] with a ha
      exact max_le le_rfl ha.1
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  refine ⟨fun a => B * ∑ i, Y i a ^ ((d : ℝ) / 2), ?_, ?_⟩
  · have h := (osBound_finset_sum Finset.univ hne le_rfl fun i _ => hYo i).const_mul hB
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  filter_upwards [ae_all_iff.2 hXa,
    ae_all_iff.2 fun i => (S.corrector (unitVector i)).locally_square_integrable,
    ae_integrable_heatKernel_mul_euclideanSq_correctorColumn hd hΛ hP S] with a hXa' hloc hint
  have hYX : ∀ i, Y i a = X i a := fun i => max_eq_left (hXa' i).1
  set ρ : ℝ := ε⁻¹ * Real.sqrt (8 * d) with hρdef
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr (by linarith)
  have hsq8 : 1 ≤ Real.sqrt (8 * d) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hρ : 1 ≤ ρ := one_le_mul_of_one_le_of_one_le hεi hsq8
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hcol : ∀ i, ∫ x, heatKernel 0 ρ x * euclideanSq (correctorColumn S a i x) ≤
      K * M * Y i a ^ d := by
    intro i
    have hgm : Measurable ((S.corrector (unitVector i)).grad a) :=
      (S.corrector (unitVector i)).measurable_grad.comp measurable_prodMk_left
    have hb := lintegral_ball_unitVector_add_le hgm (zero_lt_one.trans_le (hXa' i).1)
      (hXa' i).2 (fun R hR => (hloc i R hR).2) i
    rw [hYX]
    exact integral_heatKernel_mul_le_of_ball (measurable_euclideanSq.comp
      (measurable_correctorColumn S a i)) (fun x => euclideanSq_nonneg _) hM0.le (hXa' i).1 hb hρ
  have hF : (fun x => e + (S.linearize.corrector e).grad a (ε⁻¹ • x)) =
      fun x => correctedField S a e (ε⁻¹ • x) := by
    funext x
    exact S.add_linearize_grad e a _
  rw [hF]
  have he1 := euclideanSq_le_one_of_euclideanNorm_lt_one he
  have hpt : ∀ x, heatKernel 0 ρ x * euclideanSq (correctedField S a e x) ≤
      ∑ i, heatKernel 0 ρ x * euclideanSq (correctorColumn S a i x) := by
    intro x
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((euclideanSq_correctedField_le S a e x).trans ?_)
      (heatKernel_nonneg 0 ρ x)
    have h0 : 0 ≤ ∑ i, euclideanSq (correctorColumn S a i x) :=
      Finset.sum_nonneg fun i _ => euclideanSq_nonneg _
    nlinarith
  have hsumi : Integrable (fun x => ∑ i, heatKernel 0 ρ x * euclideanSq (correctorColumn S a i x)) :=
    integrable_finsetSum _ fun i _ => hint i 0 ρ hρ0
  have hGm : Measurable (fun x => correctedField S a e x) :=
    (measurable_correctedField S e).comp measurable_prodMk_left
  have hi : Integrable (fun x => heatKernel 0 ρ x * euclideanSq (correctedField S a e x)) := by
    refine hsumi.mono' ((measurable_heatKernel 0 ρ).mul
      (measurable_euclideanSq.comp hGm)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg _ _ _)
      (euclideanSq_nonneg _))]
    exact hpt x
  have h1 := vectorGaussianEnergy_rescaled_le (by omega) (correctedField S a e) hε hi
  have h2 : ∫ x, heatKernel 0 ρ x * euclideanSq (correctedField S a e x) ≤
      ∑ i, K * M * Y i a ^ d := by
    refine (integral_mono hi hsumi hpt).trans ?_
    rw [integral_finsetSum _ fun i _ => hint i 0 ρ hρ0]
    exact Finset.sum_le_sum fun i _ => hcol i
  have hsq : ∀ i, Y i a ^ d = (Y i a ^ ((d : ℝ) / 2)) ^ 2 := fun i => by
    rw [← Real.rpow_natCast (Y i a ^ ((d : ℝ) / 2)), ← Real.rpow_mul (hY0 i a),
      ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have h3 : ∑ i, Y i a ^ d ≤ (∑ i, Y i a ^ ((d : ℝ) / 2)) ^ 2 := by
    simp only [hsq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Real.rpow_nonneg (hY0 i a) _
  have hB2 : B ^ 2 = c * (K * M) := Real.sq_sqrt (by positivity)
  have h5 : vectorGaussianEnergy (fun x => correctedField S a e (ε⁻¹ • x)) ≤
      ENNReal.ofReal ((B * ∑ i, Y i a ^ ((d : ℝ) / 2)) ^ 2) := by
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_pow, hB2]
    calc c * ∫ x, heatKernel 0 ρ x * euclideanSq (correctedField S a e x)
        ≤ c * ∑ i, K * M * Y i a ^ d := mul_le_mul_of_nonneg_left h2 hc.le
      _ = c * (K * M) * ∑ i, Y i a ^ d := by rw [← Finset.mul_sum]; ring
      _ ≤ c * (K * M) * (∑ i, Y i a ^ ((d : ℝ) / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hR0 : 0 ≤ B * ∑ i, Y i a ^ ((d : ℝ) / 2) :=
    mul_nonneg hB.le (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hY0 i a) _)
  calc vectorGaussianEnergy (fun x => correctedField S a e (ε⁻¹ • x)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ((B * ∑ i, Y i a ^ ((d : ℝ) / 2)) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h5 (by norm_num)
    _ = ENNReal.ofReal (((B * ∑ i, Y i a ^ ((d : ℝ) / 2)) ^ 2) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal (B * ∑ i, Y i a ^ ((d : ℝ) / 2)) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hR0]

end Fields

/-! ## The frozen statement -/

/-- **(4.126) from the commutator estimate (4.34) and the linear estimate** at the stochastic
exponent `1` and the spatial exponent `d/2`, with constants depending only on `d` and `Λ`. -/
theorem negativeSobolevCorrector_of_commutator_linear
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Cc Cl : ℝ, 0 < Cc ∧ 0 < Cl ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P,
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
            OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
              S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) 1
                (Cc * r ^ (-((d : ℝ) / 2)))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
            OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) -
              ξ)) 1 (Cl * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2))))) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_corrector_energy_bounds fun d hd Λ hΛ => ?_
  obtain ⟨Cc, Cl, hCc, hCl, hP⟩ := h d hd Λ hΛ
  obtain ⟨C₁, hC₁, hE⟩ := unitScaleEnergy_of_sublinear hd hΛ
  have hd1 : 1 ≤ d := by omega
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨d * Cc + 2 * Λ * Cl, C₁, by positivity, hC₁, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨S, hcom, hlin⟩ := hP P hPl
  have hint := averagesIntegrable_of_lawHypotheses hd hΛ hPl S
  have hA := S.homogenizedMatrixBounds hΛ0.le
  refine ⟨S.linearize, hA, fun e he => ⟨fun z r hr => ?_, fun z r hr => ?_,
    fun ε hε hε2 => hE P hPl S e he ε hε hε2⟩⟩
  · obtain ⟨h1, h2⟩ := gradientAverages_linearize S hint hCl.le hlin he z hr
    refine ⟨h1, h2.mono_scale ?_⟩
    have hrp : 0 ≤ r ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have : 2 * Cl ≤ d * Cc + 2 * Λ * Cl := by
      have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      nlinarith
    exact mul_le_mul_of_nonneg_right this hrp
  · exact fluxAverages_linearize hd1 S hΛ0 hA hint hCl.le hcom hlin he z hr

end QSH
