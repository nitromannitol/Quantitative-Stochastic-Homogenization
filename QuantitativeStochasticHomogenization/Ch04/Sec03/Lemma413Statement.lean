import QuantitativeStochasticHomogenization.Ch04.Sec03.Lemma413
import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAverages

/-!
# Lemma 4.13 at every center and scale

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13, (4.34), for the corrected coordinates `eⱼ + ∇φ_{eⱼ}`.

`lemma413`: under `Fluc(s, α)` (`α ≤ d/2`), Proposition 3.21 (`GaussianCorrectorRate`) and the
energy bound below the scale (`GaussianEnergyBound`) at an exponent `τ ≥ s d/2`, the expectations
of the averages at the rate `r^{-α}` (`ExpectedAveragesEstimate`), their integrability and
measurability, the commutator estimate `CommutatorEstimate P S s α` holds.

At large scales the bound is `commutator_osBound_large`; below the threshold where the means of
the polarization vectors are close to `ā⁻¹ eᵢ`, the commutator is bounded by the energy
(`commutator_small`).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Conclusion

variable {P : Measure (CoefficientField d Λ)}

/-- Measurability of the norm of a commutator. -/
theorem measurable_commutator {Ω : Type*} [MeasurableSpace Ω] (M : Mat d) {Pv Fv : Ω → Vec d}
    (hP : Measurable Pv) (hF : Measurable Fv) :
    Measurable fun ω => euclideanNorm (Fv ω - M.mulVec (Pv ω)) := by
  have hc : Measurable fun ω => Fv ω - M.mulVec (Pv ω) :=
    hF.sub ((Matrix.mulVecLin M).continuous_of_finiteDimensional.measurable.comp hP)
  simp only [euclideanNorm, euclideanSq, dot]
  exact (Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp hc).mul ((measurable_pi_apply k).comp hc)).sqrt

/-- **The commutator at any scale from the energy**: `|F eⱼ - ā P eⱼ| ≤ 2Λ √C_N (1 + X^{d/2})`,
hence `O_s` of a constant order. -/
theorem commutator_small [IsProbabilityMeasure P] (hd : 1 ≤ d) (S : HomogenizationData P)
    (hΛ : 0 < Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ) {s τ CN : ℝ} (hs0 : 0 < s)
    (hCN : 0 < CN) (y : Vec d) {r : ℝ} (hr : 1 ≤ r) (XN : CoefficientField d Λ → ℝ)
    (hXN1 : ∀ a, 1 ≤ XN a) (hτs : s ≤ τ / ((d : ℝ) / 2)) (hXNos : OsBound P XN τ CN)
    (havg : ∀ᵐ a ∂P, ∀ l : Fin d,
      (Integrable (fun x => heatKernel y r x • correctedField S a (unitVector l) x) ∧
        Integrable (fun x => heatKernel y r x • (a x).mulVec (correctedField S a (unitVector l) x)) ∧
        Integrable (fun x => heatKernel y r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x)))) ∧
      (∫ x, heatKernel y r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x))) ≤
        CN * (1 + (XN a / r) ^ d) * euclideanSq (unitVector l : Vec d))
    (j : Fin d) (hPm : Measurable fun a => gradientAverage S a y r (unitVector j))
    (hFm : Measurable fun a => fluxAverage S a y r (unitVector j)) :
    OsBound P (fun a => euclideanNorm (fluxAverage S a y r (unitVector j) -
      S.homogenized.mulVec (gradientAverage S a y r (unitVector j)))) s
      (2 * Λ * (Real.sqrt CN * (2 * (2 : ℝ) ^ s⁻¹ * (1 / Real.log 2 ^ s⁻¹ +
        (2 * Real.exp 1 - 1) ^ s⁻¹ * CN ^ ((d : ℝ) / 2))))) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hN := (size_bound hd hs0 hCN XN hXN1 hτs hXNos).const_mul (by positivity : 0 < 2 * Λ)
  refine hN.of_le_ae (measurable_commutator _ hPm hFm) ?_
  filter_upwards [havg] with a ha
  have hX0 : 0 ≤ XN a := zero_le_one.trans (hXN1 a)
  obtain ⟨hP, hF⟩ := averages_le_of_energy S a hΛ.le y hr0 hCN.le hX0 j (ha j).1 (ha j).2
  have hop := euclideanNorm_homogenized_mulVec_le S.symmetric hA hΛ.le
    (gradientAverage S a y r (unitVector j))
  have h3 : (XN a / r) ^ ((d : ℝ) / 2) ≤ XN a ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (div_nonneg hX0 hr0.le) (div_le_self hX0 hr) (by positivity)
  have h5 : Real.sqrt CN * (1 + (XN a / r) ^ ((d : ℝ) / 2)) ≤
      Real.sqrt CN * (1 + XN a ^ ((d : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
  have h6 := mul_le_mul_of_nonneg_left h5 hΛ.le
  have h4 := mul_le_mul_of_nonneg_left hP hΛ.le
  calc euclideanNorm (fluxAverage S a y r (unitVector j) -
        S.homogenized.mulVec (gradientAverage S a y r (unitVector j)))
      ≤ euclideanNorm (fluxAverage S a y r (unitVector j)) +
          euclideanNorm (S.homogenized.mulVec (gradientAverage S a y r (unitVector j))) :=
        euclideanNorm_sub_le _ _
    _ ≤ Λ * (Real.sqrt CN * (1 + XN a ^ ((d : ℝ) / 2))) +
          Λ * (Real.sqrt CN * (1 + XN a ^ ((d : ℝ) / 2))) :=
        add_le_add (hF.trans h6) (hop.trans (h4.trans h6))
    _ = 2 * Λ * (Real.sqrt CN * (1 + XN a ^ ((d : ℝ) / 2))) := by ring

/-- Markov's inequality for a nonnegative `X ≤ O_τ(θ)`: `P(r ≤ X) ≤ (1 + 2⌈1/τ⌉!) θ / r`. -/
theorem measureReal_le_of_osBound [IsProbabilityMeasure P] {X : CoefficientField d Λ → ℝ}
    {τ θ : ℝ} (h : OsBound P X τ θ) (hX0 : ∀ a, 0 ≤ X a) {r : ℝ} (hr : 0 < r) :
    P.real {a | r ≤ X a} ≤ momentConstant τ * θ * r⁻¹ := by
  obtain ⟨hXi, hXm⟩ := h.integral_le_factorial_mul hX0
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hX0) hXi r
  rw [← div_eq_mul_inv, le_div_iff₀ hr, mul_comm]
  exact hmk.trans hXm

/-- **Lemma 4.13**: the commutator estimate (4.34) under `Fluc(s, α)` and the inputs listed in the
module docstring. -/
theorem lemma413 [IsProbabilityMeasure P] (hd : 1 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {s α CF : ℝ} (hs0 : 0 < s) (hα0 : 0 ≤ α) (hα : α ≤ (d : ℝ) / 2) (hCF : 0 < CF)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J1Heat a z r p q) P ∧
      OsBound P (fun a => |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|) s (CF * r ^ (-α)))
    {τ CR μ CN : ℝ} (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ CR μ)
    (hN : GaussianEnergyBound P S τ CN) (hτs : s ≤ τ / ((d : ℝ) / 2))
    (hint : AveragesIntegrable P S) (hexp : ExpectedAveragesEstimate P S α)
    (hmeasA : ∀ (z : Vec d) (r : ℝ) (ξ : Vec d), Measurable (fun a => gradientAverage S a z r ξ) ∧
      Measurable (fun a => fluxAverage S a z r ξ)) :
    CommutatorEstimate P S s α := by
  obtain ⟨Xg, -, hXg⟩ := hrate
  obtain ⟨XN, -, hXN1, hXNos, hXNe⟩ := hN
  obtain ⟨CE, hCE, hE⟩ := hexp
  have hCR : 0 < CR := (hXg 0).1.scale_pos
  have hCN : 0 < CN := (hXNos 0).scale_pos
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set CM : ℝ := (2 : ℝ) ^ τ⁻¹ * max CR CN with hCMdef
  have hMos : ∀ z, OsBound P (fun a => max (Xg a z) (XN a z)) τ CM := fun z =>
    osBound_max (hXg z).1 (hXNos z)
  have hCM : 0 < CM := (hMos 0).scale_pos
  have hM0 : ∀ z a, 0 ≤ max (Xg a z) (XN a z) := fun z a =>
    zero_le_one.trans ((hXN1 a z).trans (le_max_right _ _))
  -- the probability of the bad scales
  have hbad : ∀ z (r : ℝ), 0 < r → P.real {a | r ≤ Xg a z} ≤ momentConstant τ * CM * r⁻¹ := by
    intro z r hr0
    refine (measureReal_mono fun a ha => le_trans ha (le_max_left (Xg a z) (XN a z))).trans ?_
    exact measureReal_le_of_osBound (hMos z) (hM0 z) hr0
  -- the threshold
  set X1 : ℝ := Λ * (Real.sqrt d * (Real.sqrt d * (9 + Real.sqrt d))) with hX1
  set Y1 : ℝ := Λ * (Real.sqrt d * (Real.sqrt d * (16 * (Λ + 1) + 1))) with hY1
  have hX10 : 0 ≤ X1 := by positivity
  have hY10 : 0 ≤ Y1 := by positivity
  set A : ℝ := CR * (X1 + 1 + Real.sqrt d) with hAdef
  set B : ℝ := Y1 * (momentConstant τ * CM) with hBdef
  have ht : Tendsto (fun r : ℝ => A * r ^ (-μ) + B * r⁻¹) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hμ).const_mul A).add (tendsto_inv_atTop_zero.const_mul B)
    simpa using this
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  set R : ℝ := max r₁ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  set θ₀ : ℝ := 2 * Λ * (Real.sqrt CN * (2 * (2 : ℝ) ^ s⁻¹ * (1 / Real.log 2 ^ s⁻¹ +
    (2 * Real.exp 1 - 1) ^ s⁻¹ * CN ^ ((d : ℝ) / 2)))) with hθ₀
  have hθ₀0 : 0 < θ₀ := by
    have hl : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
    have he : 0 ≤ (2 * Real.exp 1 - 1) ^ s⁻¹ :=
      Real.rpow_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
    have : 0 < Real.sqrt CN := Real.sqrt_pos.mpr hCN
    rw [hθ₀]
    have : 0 ≤ (2 * Real.exp 1 - 1) ^ s⁻¹ * CN ^ ((d : ℝ) / 2) :=
      mul_nonneg he (Real.rpow_nonneg hCN.le _)
    positivity
  refine ⟨max (commutatorScale d Λ s α CF CM CN τ CE 1) (θ₀ * R ^ α),
    lt_max_of_lt_right (mul_pos hθ₀0 (Real.rpow_pos_of_pos hR0 _)), fun z r hr j => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hρα : 0 ≤ r ^ (-α) := Real.rpow_nonneg hr0.le _
  -- the inputs at `z` and `r`
  have havg : ∀ᵐ a ∂P, ∀ l : Fin d,
      (Integrable (fun x => heatKernel z r x • correctedField S a (unitVector l) x) ∧
        Integrable (fun x => heatKernel z r x • (a x).mulVec (correctedField S a (unitVector l) x)) ∧
        Integrable (fun x => heatKernel z r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x)))) ∧
      (∫ x, heatKernel z r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x))) ≤
        CN * (1 + (XN a z / r) ^ d) * euclideanSq (unitVector l : Vec d) := by
    filter_upwards [hint, hXNe] with a ha hb
    exact fun l => ⟨ha z r hr0 (unitVector l), (hb z r hr (unitVector l)).2⟩
  by_cases hrR : R ≤ r
  · -- large scales
    have hr₁r : r₁ ≤ r := le_trans (le_max_left _ _) hrR
    have h := hr₁ r hr₁r
    have hρ : 0 ≤ r ^ (-μ) := Real.rpow_nonneg hr0.le _
    have hι : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    have hpB := hbad z r hr0
    have hpB0 : 0 ≤ P.real {a | r ≤ Xg a z} := measureReal_nonneg
    have hCRρ : 0 ≤ CR * r ^ (-μ) := mul_nonneg hCR.le hρ
    have e1 : A * r ^ (-μ) = X1 * (CR * r ^ (-μ)) + CR * r ^ (-μ) +
        Real.sqrt d * (CR * r ^ (-μ)) := by rw [hAdef]; ring
    have e2 : B * r⁻¹ = Y1 * (momentConstant τ * CM * r⁻¹) := by rw [hBdef]; ring
    have h1 : 0 ≤ X1 * (CR * r ^ (-μ)) := mul_nonneg hX10 hCRρ
    have h2 : 0 ≤ Real.sqrt d * (CR * r ^ (-μ)) := mul_nonneg hsd hCRρ
    have h3 : Y1 * P.real {a | r ≤ Xg a z} ≤ Y1 * (momentConstant τ * CM * r⁻¹) :=
      mul_le_mul_of_nonneg_left hpB hY10
    have h4 : 0 ≤ Y1 * P.real {a | r ≤ Xg a z} := mul_nonneg hY10 hpB0
    have hε : CR * r ^ (-μ) ≤ 1 / 4 := by linarith
    have hεd : Real.sqrt d * (CR * r ^ (-μ)) ≤ 1 / 2 := by linarith
    have hδ : Λ * (Real.sqrt d * (Real.sqrt d * ((9 + Real.sqrt d) * (CR * r ^ (-μ)) +
        (16 * (Λ + 1) + 1) * P.real {a | r ≤ Xg a z}))) ≤ 1 / 2 := by
      have e3 : Λ * (Real.sqrt d * (Real.sqrt d * ((9 + Real.sqrt d) * (CR * r ^ (-μ)) +
          (16 * (Λ + 1) + 1) * P.real {a | r ≤ Xg a z}))) =
          X1 * (CR * r ^ (-μ)) + Y1 * P.real {a | r ≤ Xg a z} := by rw [hX1, hY1]; ring
      linarith
    have hgood : ∀ᵐ a ∂P, ¬ r ≤ Xg a z →
        GaussianAverageBounds a S.homogenized (correctedField S a) z r (CR * r ^ (-μ)) := by
      filter_upwards [(hXg z).2] with a ha hn
      exact ha r hr (not_le.mp hn).le
    have hEP : ∀ l, euclideanNorm ((fun k => ∫ a, gradientAverage S a z r (unitVector l) k ∂P) -
        unitVector l) ≤ CE * r ^ (-α) := by
      intro l
      obtain ⟨hi1, -, -, hb1, -, -⟩ := hE z r hr (unitVector l)
      have hfun : (fun k => ∫ a, gradientAverage S a z r (unitVector l) k ∂P) =
          ∫ a, gradientAverage S a z r (unitVector l) ∂P := by
        funext k
        exact (eval_integral (Integrable.eval hi1) k).symm
      rw [hfun]
      rw [euclideanNorm_unitVector, mul_one] at hb1
      exact hb1
    have hEF : ∀ l, euclideanNorm ((fun k => ∫ a, fluxAverage S a z r (unitVector l) k ∂P) -
        S.homogenized.mulVec (unitVector l)) ≤ CE * r ^ (-α) := by
      intro l
      obtain ⟨-, hi2, -, -, hb2, -⟩ := hE z r hr (unitVector l)
      have hfun : (fun k => ∫ a, fluxAverage S a z r (unitVector l) k ∂P) =
          ∫ a, fluxAverage S a z r (unitVector l) ∂P := by
        funext k
        exact (eval_integral (Integrable.eval hi2) k).symm
      rw [hfun]
      rw [euclideanNorm_unitVector, mul_one] at hb2
      exact hb2
    have hL := commutator_osBound_large hd S hΛ hA hspan hmeasJ hs0 hCF hF z hr hCRρ hε hεd
      (fun a => Xg a z) (fun a => XN a z) (fun a => max (Xg a z) (XN a z)) (hXg z).1.1
      (hXNos z).1 (fun a => zero_le_one.trans (hXN1 a z))
      (fun a => (hXN1 a z).trans (le_max_right _ _)) (fun a => le_max_right _ _)
      (fun a h => h.trans (le_max_left _ _)) hCN hτs (hMos z) hgood hδ havg
      (fun l => (hmeasA z r (unitVector l)).1) (fun l => (hmeasA z r (unitVector l)).2)
      (mul_pos hCE (Real.rpow_pos_of_pos hr0 _))
      (fun l k => Integrable.eval (hE z r hr (unitVector l)).1 k)
      (fun l k => Integrable.eval (hE z r hr (unitVector l)).2.1 k) hEP hEF j
    refine hL.mono_scale ((commutatorScale_le hΛ.le hCF hCM.le hr hα).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hρα
  · -- small scales
    have hS := commutator_small hd S hΛ hA hs0 hCN z hr (fun a => XN a z) (fun a => hXN1 a z) hτs
      (hXNos z) havg j (hmeasA z r (unitVector j)).1 (hmeasA z r (unitVector j)).2
    refine hS.mono_scale ?_
    have hRr : r ≤ R := (not_le.mp hrR).le
    have h1 : 1 ≤ R ^ α * r ^ (-α) := by
      rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, ← Real.div_rpow hR0.le hr0.le]
      exact Real.one_le_rpow ((one_le_div hr0).mpr hRr) hα0
    calc θ₀ ≤ θ₀ * (R ^ α * r ^ (-α)) := le_mul_of_one_le_right hθ₀0.le h1
      _ = θ₀ * R ^ α * r ^ (-α) := by ring
      _ ≤ max (commutatorScale d Λ s α CF CM CN τ CE 1) (θ₀ * R ^ α) * r ^ (-α) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hρα

end Conclusion

end QSH
