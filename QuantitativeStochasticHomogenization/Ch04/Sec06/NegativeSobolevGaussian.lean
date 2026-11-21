import QuantitativeStochasticHomogenization.Ch04.Sec06.HeatScaleBounds

/-!
# Section 4.6: (4.126) from Gaussian estimates of the corrector fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126). The Gaussian estimate of a random field at the scale `ε` (`GaussianFieldEstimate`) asks
for a jointly measurable version of the field with Gaussian moments at every center, a Gaussian
`L²` norm `O_1(C₁)` at the unit scale, and Gaussian averages `O_1(C₂ ε^{d/2} t^{-d/4})` at every
center for the heat times `ε² ≤ t ≤ 1/2`. For the rescaled corrector gradient these are the energy
estimate and the estimate (4.2) of the averages at the radii `√t/ε ≥ 1`; for the rescaled flux they
are the energy estimate and (4.3). From these estimates for the `2d` components of the two fields,
`negativeSobolevCorrector_of_gaussian` gives the frozen statement for every integer `m > d/2`.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The Gaussian estimate** of a random field `F` at the scale `ε`, through a jointly measurable
version `F'` agreeing with `F` almost everywhere in space for every sample. -/
def GaussianFieldEstimate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → Vec d → ℝ)
    (C₁ C₂ ε : ℝ) : Prop :=
  ∃ F' : Ω → Vec d → ℝ, Measurable (Function.uncurry F') ∧ (∀ a, F' a =ᵐ[volume] F a) ∧
    (∀ᵐ a ∂P, ∀ τ : ℝ, 0 < τ → ∀ y,
      Integrable (fun x => F' a x * euclideanHeatKernel τ (x - y))) ∧
    (∃ R : Ω → ℝ, OsBound P R 1 C₁ ∧ ∀ᵐ a ∂P, (∫⁻ x, ‖F' a x‖ₑ ^ (2 : ℝ) *
      ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 32))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)) ∧
    ∀ t : ℝ, ε ^ 2 ≤ t → t ≤ 1 / 2 → ∀ u,
      OsBound P (fun a => |heatAverage t (F' a) u|) 1 (C₂ * ε ^ ((d : ℝ) / 2) * t ^ (-(d : ℝ) / 4))

theorem heatDerivativeAverage_congr {k : ℕ} (β : Fin d → Fin (k + 1)) (s : ℝ)
    {F G : Vec d → ℝ} (h : F =ᵐ[volume] G) :
    heatDerivativeAverage β s F = heatDerivativeAverage β s G := funext fun y => by
  unfold heatDerivativeAverage
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

theorem HeatScaleEstimate.congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {F F' : Ω → Vec d → ℝ} {c ε : ℝ} (h : HeatScaleEstimate P n F' c ε)
    (hF : ∀ a, F' a =ᵐ[volume] F a) : HeatScaleEstimate P n F c ε := by
  have heq : ∀ a k (w : Fin k → Fin d) s, heatDerivativeAverage (countIndex w) s (F a) =
      heatDerivativeAverage (countIndex w) s (F' a) := fun a k w s =>
    heatDerivativeAverage_congr _ s (hF a).symm
  obtain ⟨Q, hQm, hQ0, hYm, hQ, hY⟩ := h
  refine ⟨Q, hQm, hQ0, ?_, hQ, ?_⟩
  · intro k w
    simp_rw [heq]
    exact hYm k w
  · intro k w hk s hs
    simp_rw [heq]
    exact hY k w hk s hs

theorem integrable_mul_exp_of_euclideanHeatKernel (hd : 1 ≤ d) {G : Vec d → ℝ}
    (hGm : AEStronglyMeasurable G volume)
    (hG : Integrable (fun x => G x * euclideanHeatKernel (4 * d) (x - 0))) :
    Integrable (fun x => G x * Real.exp (-(‖x‖ ^ 2) / 16)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set c := (4 * Real.pi * (4 * d)) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  refine (hG.norm.const_mul c⁻¹).mono' (hGm.mul (by fun_prop : Continuous fun x : Vec d =>
    Real.exp (-(‖x‖ ^ 2) / 16)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (euclideanHeatKernel_nonneg (by positivity) _), sub_zero]
  unfold euclideanHeatKernel
  rw [← hc]
  have he : Real.exp (-(‖x‖ ^ 2) / 16) ≤ Real.exp (-(euclideanSq x) / (4 * (4 * d))) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := euclideanSq_le_card_mul_norm_sq x
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  calc |G x| * Real.exp (-(‖x‖ ^ 2) / 16)
      ≤ |G x| * Real.exp (-(euclideanSq x) / (4 * (4 * d))) :=
        mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ = c⁻¹ * (|G x| * (c * Real.exp (-(euclideanSq x) / (4 * (4 * d))))) := by
        field_simp
    _ = _ := rfl

theorem GaussianFieldEstimate.ae_hasGaussianMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (hd : 1 ≤ d) {F : Ω → Vec d → ℝ} {C₁ C₂ ε : ℝ}
    (h : GaussianFieldEstimate P F C₁ C₂ ε) : ∀ᵐ a ∂P, HasGaussianMoment (F a) := by
  obtain ⟨F', hFm, hF, hFg, -, -⟩ := h
  filter_upwards [hFg] with a ha
  have hFa : AEStronglyMeasurable (F' a) volume :=
    (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hdpos : (0 : ℝ) < 4 * d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hi := integrable_mul_exp_of_euclideanHeatKernel hd hFa (ha (4 * d) hdpos 0)
  refine ⟨hFa.congr (hF a), hi.congr ?_⟩
  filter_upwards [hF a] with x hx
  rw [hx]

/-- **(4.126) from the Gaussian estimates** of the components of `∇φ_e(·/ε)` and of
`a(·/ε)(e + ∇φ_e(·/ε)) - ā e`. -/
theorem negativeSobolevCorrector_of_gaussian
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ j : Fin d,
            GaussianFieldEstimate P (fun a x => (S.corrector e).grad a (ε⁻¹ • x) j) C₁ C₂ ε ∧
            GaussianFieldEstimate P (fun a x => ((a (ε⁻¹ • x)).mulVec
              (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) j) C₁ C₂ ε) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_heatScale fun d hd Λ hΛ m hm => ?_
  obtain ⟨C₁, C₂, hC₁, hC₂, hP⟩ := h d hd Λ hΛ
  have hd1 : 1 ≤ d := by omega
  have hH : 0 < heatScaleCoefficient d (m - 1) := by
    have h1 := youngConstant_add_one_le (d := d) (n := m - 1) (Nat.zero_le _)
      (fun i : Fin 0 => i.elim0)
    have h2 := youngConstant_nonneg (countIndex (fun i : Fin 0 => (i.elim0 : Fin d)))
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK0 : 0 ≤ gaussSquareConstant d := Real.rpow_nonneg (mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (integral_nonneg fun u => (gaussWeight_pos u).le)) _
  refine ⟨heatScaleCoefficient d (m - 1) * ((C₁ + gaussSquareConstant d * C₂) *
    2 ^ ((d : ℝ) / 4)), by positivity, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨S, hS⟩ := hP P hPl
  refine ⟨S, fun e he ε hε hε2 j => ?_⟩
  obtain ⟨hG, hFl⟩ := hS e he ε hε hε2 j
  have hscale : ∀ {F : CoefficientField d Λ → Vec d → ℝ}, GaussianFieldEstimate P F C₁ C₂ ε →
      HeatScaleEstimate P (m - 1) F (heatScaleCoefficient d (m - 1) *
        ((C₁ + gaussSquareConstant d * C₂) * 2 ^ ((d : ℝ) / 4))) ε := fun {F} hF => by
    obtain ⟨F', hFm, hFF, hFg, ⟨R, hRo, hR⟩, hA⟩ := hF
    exact (heatScaleEstimate_of_gaussian hd1 (m - 1) hFm hε hC₁ hC₂ hFg hRo hR hA).congr hFF
  refine ⟨?_, hscale hG, hscale hFl⟩
  filter_upwards [hG.ae_hasGaussianMoment hd1, hFl.ae_hasGaussianMoment hd1] with a h1 h2
  exact ⟨h1, h2⟩

end QSH
