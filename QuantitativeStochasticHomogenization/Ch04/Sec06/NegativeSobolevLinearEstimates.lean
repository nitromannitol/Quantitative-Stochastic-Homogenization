import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevMeasurable
import QuantitativeStochasticHomogenization.Ch04.Sec03.LinearEstimateOptimal
import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedBoundsFromMeasurability

/-!
# Section 4.6: (4.126) from the commutator estimate, the linear estimate and the energy bound

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.126). For the homogenization data `S.linearize`, whose corrector in the direction `e` is
`∑ᵢ eᵢ φ_{eᵢ}`, the corrected field `e + ∇φ_e` is the field `G e` of the corrected coordinates
(`HomogenizationData.add_linearize_grad`). The three inputs of
`negativeSobolevCorrector_of_corrector_energy_bounds` then follow from estimates on the corrected
coordinates of `S`:

* (4.2) from the linear estimate `|∫ Φ_{z,r} G ξ - ξ| ≤ O_1(C (1 + |ξ|) r^{-d/2})`
  (`gradientAverages_linearize`);
* (4.3) from the linear estimate and the commutator estimate (4.34)
  `|∫ Φ_{z,r} a G eⱼ - ā ∫ Φ_{z,r} G eⱼ| ≤ O_1(C r^{-d/2})`, through
  `∫ Φ (a G e - ā e) = ∑ⱼ eⱼ (∫ Φ a G eⱼ - ā ∫ Φ G eⱼ) + ā (∫ Φ G e - e)`
  (`fluxAverages_linearize`);
* the Gaussian energy of `e + ∇φ_e(ε⁻¹ ·)` at the unit scale from the energy bound below the scale
  at the exponent `d/2`: the weight `e^{-‖x‖²/32}` is at most a multiple of the mask of radius
  `√(8d)`, the change of variables `x = ε y` turns it into the mask of radius `ε⁻¹ √(8d) ≥ 1`, and
  the energy bound gives `C (1 + X^d)`, whose square root is `O_1` by the power rule
  (`unitScaleEnergy_of_energyBound`).

Together they give the frozen statement (`negativeSobolevCorrector_of_linear_estimates`), with the
bounds of `ā` replaced by the measurability of the Dirichlet energies in
`negativeSobolevCorrector_of_linear_estimates_measurable`. Since the bounds `1 ≤ ā ≤ Λ` hold for all
homogenization data (`HomogenizationData.homogenizedMatrixBounds`), the frozen statement follows
from the three estimates alone (`negativeSobolevCorrector_of_commutator_linear_energy`), and from
(4.2), (4.3) and the Gaussian energy at the unit scale alone
(`negativeSobolevCorrector_of_corrector_energy_estimates`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The Gaussian weight and the change of scale -/

/-- `e^{-‖x‖²/32} ≤ (4π · 8d)^{d/2} Φ_{0,√(8d)}(x)`. -/
theorem gaussWeight_le_heatKernel (hd : 1 ≤ d) (x : Vec d) :
    gaussWeight x ≤ ((4 * Real.pi * (8 * d)) ^ (-(d : ℝ) / 2))⁻¹ *
      heatKernel 0 (Real.sqrt (8 * d)) x := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 0 < (8 * d : ℝ) := by positivity
  have hc := Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) ht)
    (-(d : ℝ) / 2)
  unfold gaussWeight heatKernel euclideanHeatKernel
  rw [sub_zero, Real.sq_sqrt ht.le, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (by positivity : 0 < 4 * (8 * d : ℝ))).2
  nlinarith [euclideanSq_le_card_mul_norm_sq x]

private theorem lintegral_ofReal_mul_le_of_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {S W K : E → ℝ} {B : ℝ} (hS : ∀ x, 0 ≤ S x) (hK : ∀ x, 0 ≤ K x) (hB : 0 ≤ B)
    (hWK : ∀ x, W x ≤ B * K x) (hI : Integrable (fun x => K x * S x) μ) :
    ∫⁻ x, ENNReal.ofReal (S x) * ENNReal.ofReal (W x) ∂μ ≤
      ENNReal.ofReal (B * ∫ x, K x * S x ∂μ) := by
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (B * (K x * S x)) ∂μ := by
         apply lintegral_mono
         intro x
         change ENNReal.ofReal (S x) * ENNReal.ofReal (W x) ≤ ENNReal.ofReal (B * (K x * S x))
         rw [← ENNReal.ofReal_mul (hS x)]
         apply ENNReal.ofReal_le_ofReal
         calc S x * W x ≤ S x * (B * K x) := mul_le_mul_of_nonneg_left (hWK x) (hS x)
              _ = _ := by ring
       _ = _ := by
         rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul B)
           (Eventually.of_forall (fun x => mul_nonneg hB (mul_nonneg (hK x) (hS x)))),
           integral_const_mul]

/-- **The Gaussian energy of a rescaled field**:
`∫ |F(ε⁻¹ x)|² e^{-‖x‖²/32} dx ≤ (4π · 8d)^{d/2} ∫ Φ_{0, ε⁻¹ √(8d)} |F|²`. -/
theorem vectorGaussianEnergy_rescaled_le (hd : 1 ≤ d) (F : Vec d → Vec d)
    {ε : ℝ} (hε : 0 < ε)
    (hi : Integrable (fun x => heatKernel 0 (ε⁻¹ * Real.sqrt (8 * d)) x * euclideanSq (F x))) :
    vectorGaussianEnergy (fun x => F (ε⁻¹ • x)) ≤
      ENNReal.ofReal (((4 * Real.pi * (8 * d)) ^ (-(d : ℝ) / 2))⁻¹ *
        ∫ x, heatKernel 0 (ε⁻¹ * Real.sqrt (8 * d)) x * euclideanSq (F x)) := by
  let ρ : ℝ := Real.sqrt (8 * d)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  let c : ℝ := ε⁻¹ ^ (-(d : ℝ))
  have hc : 0 < c := Real.rpow_pos_of_pos hεi _
  have hk (x : Vec d) : heatKernel 0 (ε⁻¹ * ρ) (ε⁻¹ • x) = c * heatKernel 0 ρ x := by
    simpa only [smul_zero, c] using (heatKernel_smul (0 : Vec d) x hεi hρ)
  have hi' : Integrable (fun x => heatKernel 0 ρ x * euclideanSq (F (ε⁻¹ • x))) := by
    have h := (hi.comp_smul (μ := volume) hεi.ne').const_mul c⁻¹
    apply h.congr (Eventually.of_forall fun x => ?_)
    change c⁻¹ * (heatKernel 0 (ε⁻¹ * ρ) (ε⁻¹ • x) * euclideanSq (F (ε⁻¹ • x))) = _
    rw [hk]
    field_simp
  have hres := integral_heatKernel_rescale (fun x => euclideanSq (F x)) (0 : Vec d) hε hρ
  simp only [smul_zero, smul_eq_mul] at hres
  have h := lintegral_ofReal_mul_le_of_le (μ := volume)
    (fun x => euclideanSq_nonneg (F (ε⁻¹ • x))) (heatKernel_nonneg (0 : Vec d) ρ)
    (by positivity) (gaussWeight_le_heatKernel hd) hi'
  rw [hres] at h
  exact h

/-- `X ≤ O_t(C)` with `X ≥ 0` gives `B X^t ≤ O_1(B C^t)`. -/
theorem OsBound.const_mul_rpow_self {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {t B C : ℝ} (h : OsBound P X t C)
    (hn : ∀ a, 0 ≤ X a) (ht : 0 < t) (hB : 0 < B) :
    OsBound P (fun a => B * X a ^ t) 1 (B * C ^ t) := by
  simpa only [div_self ht.ne'] using (h.rpow hn ht).const_mul hB

/-! ## The corrected field of the linearized data -/

section Linearize

variable {P : Measure (CoefficientField d Λ)}

/-- `e + ∇(∑ᵢ eᵢ φ_{eᵢ}) = G e`. -/
theorem HomogenizationData.add_linearize_grad (S : HomogenizationData P) (e : Vec d)
    (a : CoefficientField d Λ) (x : Vec d) :
    e + (S.linearize.corrector e).grad a x = correctedField S a e x := by
  rw [HomogenizationData.linearize_grad, correctedField]
  simp only [correctedCoordinate, smul_add, Finset.sum_add_distrib, sum_smul_unitVector_eq]

theorem HomogenizationData.linearize_grad_eq_sub (S : HomogenizationData P) (e : Vec d)
    (a : CoefficientField d Λ) (x : Vec d) :
    (S.linearize.corrector e).grad a x = correctedField S a e x - e := by
  rw [← S.add_linearize_grad]
  abel

/-- `G e = ∑ⱼ eⱼ G eⱼ`. -/
theorem correctedField_eq_sum_unitVector (S : HomogenizationData P) (a : CoefficientField d Λ)
    (e x : Vec d) :
    correctedField S a e x = ∑ j, e j • correctedField S a (unitVector j) x := by
  rw [correctedField]
  simp only [correctedField_unitVector, correctedCoordinate]

theorem measurable_euclideanSq : Measurable (euclideanSq (d := d)) := by
  unfold euclideanSq dot
  fun_prop

/-- The Gaussian average of the flux of a corrector, measurable through the jointly measurable
version of the coefficient field. -/
theorem measurable_euclideanNorm_integral_heatKernel_flux {e : Vec d} (φ : Corrector P e)
    (A : Mat d) (z : Vec d) (r : ℝ) :
    Measurable (fun a : CoefficientField d Λ => euclideanNorm (∫ y, heatKernel z r y •
      ((a y).mulVec (e + φ.grad a y) - A.mulVec e))) := by
  set Fl : CoefficientField d Λ → Vec d → Vec d := fun a y =>
    (coefficientVersion a y).mulVec (e + φ.grad a y) - A.mulVec e with hFldef
  have hFlm : Measurable (fun p : CoefficientField d Λ × Vec d => Fl p.1 p.2) := by
    have hmv : Continuous (fun q : Mat d × Vec d => q.1.mulVec q.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    refine Measurable.sub ?_ measurable_const
    exact hmv.measurable.comp (measurable_coefficientVersion.prodMk
      (measurable_const.add φ.measurable_grad))
  have hfun : (fun a : CoefficientField d Λ => euclideanNorm (∫ y, heatKernel z r y •
      ((a y).mulVec (e + φ.grad a y) - A.mulVec e))) =
        fun a => euclideanNorm (∫ y, heatKernel z r y • Fl a y) := by
    funext a
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_coefficientVersion_eq a] with y hy
    simp only [hFldef, hy]
  rw [hfun]
  have hf : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (y : Vec d) =>
      heatKernel z r y • Fl a y) :=
    (((measurable_heatKernel z r).comp measurable_snd).smul hFlm).stronglyMeasurable
  exact measurable_euclideanNorm.comp
    (hf.integral_prod_right (ν := (volume : Measure (Vec d)))).measurable

theorem euclideanSq_le_one_of_euclideanNorm_lt_one {e : Vec d} (he : euclideanNorm e < 1) :
    euclideanSq e ≤ 1 := by
  have h0 := euclideanSq_nonneg e
  have h1 := Real.sq_sqrt h0
  have h2 := Real.sqrt_nonneg (euclideanSq e)
  unfold euclideanNorm at he
  nlinarith

/-- `|A v| ≤ Λ |v|` for a symmetric matrix with `1 ≤ A ≤ Λ`. -/
theorem euclideanNorm_mulVec_le_mul_of_bounds {A : Mat d} (hΛ : 0 ≤ Λ) (hsymm : A.transpose = A)
    (hA : HomogenizedMatrixBounds A Λ) (v : Vec d) :
    euclideanNorm (A.mulVec v) ≤ Λ * euclideanNorm v := by
  have h := euclideanSq_mulVec_le_of_bounds hsymm hA v
  unfold euclideanNorm
  calc Real.sqrt (euclideanSq (A.mulVec v)) ≤ Real.sqrt (Λ ^ 2 * euclideanSq v) :=
        Real.sqrt_le_sqrt h
    _ = Λ * Real.sqrt (euclideanSq v) := by
        rw [Real.sqrt_mul (sq_nonneg Λ), Real.sqrt_sq hΛ]

/-! ## (4.2) from the linear estimate -/

/-- **(4.2) for `S.linearize`** from the linear estimate at the exponent `d/2`. -/
theorem gradientAverages_linearize (S : HomogenizationData P) (hint : AveragesIntegrable P S)
    {Cl : ℝ} (hCl : 0 ≤ Cl)
    (hlin : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
      OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ)) 1
        (Cl * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2))))
    {e : Vec d} (he : euclideanNorm e < 1) (z : Vec d) {r : ℝ} (hr : 1 ≤ r) :
    (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.linearize.corrector e).grad a y)) ∧
      OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.linearize.corrector e).grad a y))
        1 (2 * Cl * r ^ (-(d : ℝ) / 2)) := by
  have hr0 : 0 < r := by linarith
  have hconst : Integrable (fun y => heatKernel z r y • e) :=
    (integrable_heatKernel z hr0).smul_const _
  have hgood : ∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.linearize.corrector e).grad a y)
      ∧ (∫ y, heatKernel z r y • (S.linearize.corrector e).grad a y) =
        (∫ x, heatKernel z r x • correctedField S a e x) - e := by
    filter_upwards [hint z] with a ha
    have h1 := (ha r hr e).1
    simp only [S.linearize_grad_eq_sub, smul_sub]
    refine ⟨h1.sub hconst, ?_⟩
    rw [integral_sub h1 hconst, integral_smul_const, integral_heatKernel z hr0, one_smul]
  refine ⟨hgood.mono fun a ha => ha.1, ?_⟩
  refine ((hlin z r hr e).of_le_ae
    (measurable_euclideanNorm_integral_heatKernel_grad _ z r) ?_).mono_scale ?_
  · filter_upwards [hgood] with a ha
    rw [ha.2]
  · have hrp : 0 ≤ r ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg hr0.le _
    rw [neg_div]
    have h2 : 1 + euclideanNorm e ≤ 2 := by linarith
    calc Cl * (1 + euclideanNorm e) * r ^ (-((d : ℝ) / 2))
        ≤ Cl * 2 * r ^ (-((d : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCl) hrp
      _ = 2 * Cl * r ^ (-((d : ℝ) / 2)) := by ring

/-! ## (4.3) from the commutator estimate and the linear estimate -/

/-- `∫ Φ_{z,r} G e = ∑ⱼ eⱼ ∫ Φ_{z,r} G eⱼ` and `∫ Φ_{z,r} a G e = ∑ⱼ eⱼ ∫ Φ_{z,r} a G eⱼ` when the
averages of the corrected coordinates exist. -/
theorem averages_eq_sum_unitVector (S : HomogenizationData P) (a : CoefficientField d Λ)
    (z : Vec d) (r : ℝ)
    (hg : ∀ j : Fin d, Integrable (fun x => heatKernel z r x • correctedField S a (unitVector j) x))
    (hf : ∀ j : Fin d,
      Integrable (fun x => heatKernel z r x • (a x).mulVec (correctedField S a (unitVector j) x)))
    (e : Vec d) :
    gradientAverage S a z r e = ∑ j, e j • gradientAverage S a z r (unitVector j) ∧
      fluxAverage S a z r e = ∑ j, e j • fluxAverage S a z r (unitVector j) := by
  constructor
  · unfold gradientAverage
    have hfun : (fun x => heatKernel z r x • correctedField S a e x) = fun x =>
        ∑ j, e j • (heatKernel z r x • correctedField S a (unitVector j) x) := by
      funext x
      rw [correctedField_eq_sum_unitVector, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have hI : ∀ j ∈ Finset.univ, Integrable
        (fun x => e j • (heatKernel z r x • correctedField S a (unitVector j) x)) :=
      fun j _ => (hg j).smul (e j)
    rw [hfun]
    exact (integral_finsetSum _ hI).trans (Finset.sum_congr rfl fun j _ => integral_smul _ _)
  · unfold fluxAverage
    have hfun : (fun x => heatKernel z r x • (a x).mulVec (correctedField S a e x)) = fun x =>
        ∑ j, e j • (heatKernel z r x • (a x).mulVec (correctedField S a (unitVector j) x)) := by
      funext x
      rw [correctedField_eq_sum_unitVector, Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul]
      exact smul_comm _ _ _
    have hI : ∀ j ∈ Finset.univ, Integrable
        (fun x => e j • (heatKernel z r x • (a x).mulVec (correctedField S a (unitVector j) x))) :=
      fun j _ => (hf j).smul (e j)
    rw [hfun]
    exact (integral_finsetSum _ hI).trans (Finset.sum_congr rfl fun j _ => integral_smul _ _)

/-- **(4.3) for `S.linearize`** from the commutator estimate and the linear estimate at the
exponent `d/2`. -/
theorem fluxAverages_linearize (hd : 1 ≤ d) (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (hint : AveragesIntegrable P S)
    {Cc Cl : ℝ} (hCl : 0 ≤ Cl)
    (hcom : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
      OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
        S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) 1
          (Cc * r ^ (-((d : ℝ) / 2))))
    (hlin : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
      OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ)) 1
        (Cl * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2))))
    {e : Vec d} (he : euclideanNorm e < 1) (z : Vec d) {r : ℝ} (hr : 1 ≤ r) :
    (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y •
      ((a y).mulVec (e + (S.linearize.corrector e).grad a y) - S.homogenized.mulVec e))) ∧
      OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y •
        ((a y).mulVec (e + (S.linearize.corrector e).grad a y) - S.homogenized.mulVec e))) 1
          ((d * Cc + 2 * Λ * Cl) * r ^ (-(d : ℝ) / 2)) := by
  have hr0 : 0 < r := by linarith
  set A := S.homogenized with hAdef
  have hconst : Integrable (fun y => heatKernel z r y • A.mulVec e) :=
    (integrable_heatKernel z hr0).smul_const _
  set Y : CoefficientField d Λ → ℝ := fun a =>
    (∑ j, euclideanNorm (fluxAverage S a z r (unitVector j) -
      A.mulVec (gradientAverage S a z r (unitVector j)))) +
      Λ * euclideanNorm ((∫ x, heatKernel z r x • correctedField S a e x) - e) with hYdef
  have hgood : ∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y •
      ((a y).mulVec (e + (S.linearize.corrector e).grad a y) - A.mulVec e)) ∧
      euclideanNorm (∫ y, heatKernel z r y •
        ((a y).mulVec (e + (S.linearize.corrector e).grad a y) - A.mulVec e)) ≤ Y a := by
    filter_upwards [hint z] with a ha
    have h1 := (ha r hr e).2.1
    simp only [S.add_linearize_grad, smul_sub]
    refine ⟨h1.sub hconst, ?_⟩
    rw [integral_sub h1 hconst, integral_smul_const, integral_heatKernel z hr0, one_smul]
    obtain ⟨hgs, hfs⟩ := averages_eq_sum_unitVector S a z r (fun j => (ha r hr _).1)
      (fun j => (ha r hr _).2.1) e
    have hdec : (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a e x)) - A.mulVec e =
        (∑ j, e j • (fluxAverage S a z r (unitVector j) -
          A.mulVec (gradientAverage S a z r (unitVector j)))) +
          A.mulVec (gradientAverage S a z r e - e) := by
      change fluxAverage S a z r e - A.mulVec e = _
      rw [Matrix.mulVec_sub, hgs, hfs, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [hdec]
    refine (euclideanNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (euclideanNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [euclideanNorm_smul]
      have hej : |e j| ≤ 1 := (abs_apply_le_euclideanNorm e j).trans he.le
      exact (mul_le_mul_of_nonneg_right hej (euclideanNorm_nonneg _)).trans_eq (one_mul _)
    · exact euclideanNorm_mulVec_le_mul_of_bounds hΛ.le S.symmetric hA _
  refine ⟨hgood.mono fun a ha => ha.1, ?_⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hYo : OsBound P Y 1 ((∑ _j : Fin d, Cc * r ^ (-((d : ℝ) / 2))) +
      Λ * (Cl * (1 + euclideanNorm e) * r ^ (-((d : ℝ) / 2)))) :=
    osBound_add (osBound_finset_sum Finset.univ hne le_rfl fun j _ => hcom z r hr j)
      ((hlin z r hr e).const_mul hΛ) le_rfl
  refine (hYo.of_le_ae (measurable_euclideanNorm_integral_heatKernel_flux _ A z r)
    (hgood.mono fun a ha => ha.2)).mono_scale ?_
  have hrp : 0 ≤ r ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg hr0.le _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, neg_div]
  have h2 : 1 + euclideanNorm e ≤ 2 := by linarith
  have h3 : Λ * (Cl * (1 + euclideanNorm e)) ≤ Λ * (Cl * 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCl) hΛ.le
  nlinarith

/-! ## The Gaussian energy at the unit scale from the energy bound -/

/-- The constant `(2 C (4π · 8d)^{d/2})^{1/2}` of the Gaussian energy at the unit scale. -/
def unitScaleEnergyConstant (d : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt (2 * C * ((4 * Real.pi * (8 * d)) ^ (-(d : ℝ) / 2))⁻¹)

theorem unitScaleEnergyConstant_pos (hd : 1 ≤ d) {C : ℝ} (hC : 0 < C) :
    0 < unitScaleEnergyConstant d C := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact Real.sqrt_pos.mpr (mul_pos (by positivity)
    (inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)))

/-- **The Gaussian energy of `e + ∇φ_e(ε⁻¹ ·)` at the unit scale** for `S.linearize`, from the energy
bound below the scale at the exponent `d/2`: its square root is at most `B X^{d/2}` with `X` the
scale at the origin, which is `O_1(B C^{d/2})`. -/
theorem unitScaleEnergy_of_energyBound (hd : 1 ≤ d) (S : HomogenizationData P) {CN : ℝ}
    (hN : GaussianEnergyBound P S ((d : ℝ) / 2) CN) {e : Vec d} (he : euclideanNorm e < 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ R : CoefficientField d Λ → ℝ,
      OsBound P R 1 (unitScaleEnergyConstant d CN * CN ^ ((d : ℝ) / 2)) ∧
      ∀ᵐ a ∂P, vectorGaussianEnergy (fun x => e + (S.linearize.corrector e).grad a (ε⁻¹ • x)) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a) := by
  obtain ⟨X, -, hX1, hXo, hXe⟩ := hN
  set B := unitScaleEnergyConstant d CN with hBdef
  have hCN : 0 < CN := (hXo 0).scale_pos
  have hB : 0 < B := unitScaleEnergyConstant_pos hd hCN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨fun a => B * X a 0 ^ ((d : ℝ) / 2), ?_, ?_⟩
  · exact (hXo 0).const_mul_rpow_self (fun a => zero_le_one.trans (hX1 a 0)) (by positivity) hB
  filter_upwards [hXe 0] with a ha
  set ρ : ℝ := ε⁻¹ * Real.sqrt (8 * d) with hρdef
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr (by linarith)
  have hsq : 1 ≤ Real.sqrt (8 * d) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact Real.sqrt_le_sqrt (by linarith)
  have hρ : 1 ≤ ρ := one_le_mul_of_one_le_of_one_le hεi hsq
  obtain ⟨hint, hle⟩ := ha ρ hρ e
  have hF : (fun x => e + (S.linearize.corrector e).grad a (ε⁻¹ • x)) =
      fun x => correctedField S a e (ε⁻¹ • x) := by
    funext x
    exact S.add_linearize_grad e a _
  rw [hF]
  have hpt : ∀ x, heatKernel 0 ρ x * euclideanSq (correctedField S a e x) ≤
      heatKernel 0 ρ x * dot (correctedField S a e x) ((a x).mulVec (correctedField S a e x)) :=
    fun x => mul_le_mul_of_nonneg_left (a.elliptic x _).1 (heatKernel_nonneg 0 ρ x)
  have hGm : Measurable (fun x => correctedField S a e x) :=
    (measurable_correctedField S e).comp measurable_prodMk_left
  have hi : Integrable (fun x => heatKernel 0 ρ x * euclideanSq (correctedField S a e x)) := by
    refine hint.mono' ((measurable_heatKernel 0 ρ).mul
      (measurable_euclideanSq.comp hGm)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg _ _ _)
      (euclideanSq_nonneg _))]
    exact hpt x
  have h1 := vectorGaussianEnergy_rescaled_le hd (correctedField S a e) hε hi
  set c : ℝ := ((4 * Real.pi * (8 * d)) ^ (-(d : ℝ) / 2))⁻¹ with hcdef
  have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have hX : 1 ≤ X a 0 := hX1 a 0
  have hX0 : 0 ≤ X a 0 := zero_le_one.trans hX
  have h2 : ∫ x, heatKernel 0 ρ x * euclideanSq (correctedField S a e x) ≤
      CN * (1 + (X a 0 / ρ) ^ d) * euclideanSq e := (integral_mono hi hint hpt).trans hle
  have hXd : (X a 0 / ρ) ^ d ≤ X a 0 ^ d :=
    pow_le_pow_left₀ (div_nonneg hX0 (zero_le_one.trans hρ)) (div_le_self hX0 hρ) d
  have hXd1 : 1 ≤ X a 0 ^ d := one_le_pow₀ hX
  have he1 := euclideanSq_le_one_of_euclideanNorm_lt_one he
  have he0 := euclideanSq_nonneg e
  have h3 : CN * (1 + (X a 0 / ρ) ^ d) * euclideanSq e ≤ 2 * CN * X a 0 ^ d := by
    have h4 : 0 ≤ CN * (1 + (X a 0 / ρ) ^ d) := by positivity
    calc CN * (1 + (X a 0 / ρ) ^ d) * euclideanSq e ≤ CN * (1 + (X a 0 / ρ) ^ d) * 1 :=
          mul_le_mul_of_nonneg_left he1 h4
      _ ≤ 2 * CN * X a 0 ^ d := by nlinarith
  have hB2 : B ^ 2 = 2 * CN * c := Real.sq_sqrt (by positivity)
  have h5 : vectorGaussianEnergy (fun x => correctedField S a e (ε⁻¹ • x)) ≤
      ENNReal.ofReal (B ^ 2 * X a 0 ^ d) := by
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hB2]
    calc c * ∫ x, heatKernel 0 ρ x * euclideanSq (correctedField S a e x)
        ≤ c * (2 * CN * X a 0 ^ d) := mul_le_mul_of_nonneg_left (h2.trans h3) hc.le
      _ = 2 * CN * c * X a 0 ^ d := by ring
  calc vectorGaussianEnergy (fun x => correctedField S a e (ε⁻¹ • x)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (B ^ 2 * X a 0 ^ d) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h5 (by norm_num)
    _ = ENNReal.ofReal ((B ^ 2 * X a 0 ^ d) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal (B * X a 0 ^ ((d : ℝ) / 2)) := by
        congr 1
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hB.le, ← Real.rpow_natCast, ← Real.rpow_mul hX0]
        congr 2
        ring

end Linearize

/-! ## The frozen statement -/

/-- **(4.126) from the commutator estimate (4.34), the linear estimate and the energy bound below
the scale**, at the stochastic exponent `1` and the spatial exponent `d/2`, with the bounds
`1 ≤ ā ≤ Λ` and with constants depending only on `d` and `Λ`. -/
theorem negativeSobolevCorrector_of_linear_estimates
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Cc Cl CN : ℝ, 0 < Cc ∧ 0 < Cl ∧ 0 < CN ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, HomogenizedMatrixBounds S.homogenized Λ ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
            OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
              S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) 1
                (Cc * r ^ (-((d : ℝ) / 2)))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
            OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) -
              ξ)) 1 (Cl * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2)))) ∧
          GaussianEnergyBound P S ((d : ℝ) / 2) CN) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_corrector_energy_bounds fun d hd Λ hΛ => ?_
  obtain ⟨Cc, Cl, CN, hCc, hCl, hCN, hP⟩ := h d hd Λ hΛ
  have hd1 : 1 ≤ d := by omega
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨d * Cc + 2 * Λ * Cl, unitScaleEnergyConstant d CN * CN ^ ((d : ℝ) / 2),
    by positivity, mul_pos (unitScaleEnergyConstant_pos hd1 hCN) (by positivity), fun P hPl => ?_⟩
  obtain ⟨S, hA, hcom, hlin, hN⟩ := hP P hPl
  have hint := averagesIntegrable_of_energyBound S hΛ0.le hN
  refine ⟨S.linearize, hA, fun e he => ⟨fun z r hr => ?_, fun z r hr => ?_, fun ε hε hε2 => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := gradientAverages_linearize S hint hCl.le hlin he z hr
    refine ⟨h1, h2.mono_scale ?_⟩
    have hrp : 0 ≤ r ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have : 2 * Cl ≤ d * Cc + 2 * Λ * Cl := by
      have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      nlinarith
    exact mul_le_mul_of_nonneg_right this hrp
  · exact fluxAverages_linearize hd1 S hΛ0 hA hint hCl.le hcom hlin he z hr
  · exact unitScaleEnergy_of_energyBound hd1 S hN he hε hε2

/-- **(4.126) from the commutator estimate (4.34), the linear estimate and the energy bound below
the scale**, with the bounds of `ā` replaced by the measurability of the Dirichlet energies on the
triadic cubes. -/
theorem negativeSobolevCorrector_of_linear_estimates_measurable
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Cc Cl CN : ℝ, 0 < Cc ∧ 0 < Cl ∧ 0 < CN ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        (∀ (n : ℕ) (ξ : Vec d), AEStronglyMeasurable
          (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) ξ) P) ∧
        ∃ S : HomogenizationData P,
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
            OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
              S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) 1
                (Cc * r ^ (-((d : ℝ) / 2)))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
            OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) -
              ξ)) 1 (Cl * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2)))) ∧
          GaussianEnergyBound P S ((d : ℝ) / 2) CN) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_linear_estimates fun d hd Λ hΛ => ?_
  obtain ⟨Cc, Cl, CN, hCc, hCl, hCN, hP⟩ := h d hd Λ hΛ
  refine ⟨Cc, Cl, CN, hCc, hCl, hCN, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨hmeas, S, hS⟩ := hP P hPl
  exact ⟨S, homogenizedMatrixBounds_of_aestronglyMeasurable S (by linarith) hmeas, hS⟩

/-- **(4.126) from (4.2), (4.3) and the Gaussian energy estimate of the corrected field**
`e + ∇φ_e(·/ε)` at the unit scale. -/
theorem negativeSobolevCorrector_of_corrector_energy_estimates
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C C₁ : ℝ, 0 < C ∧ 0 < C₁ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P, ∀ e : Vec d, euclideanNorm e < 1 →
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • (S.corrector e).grad a y)) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y • (S.corrector e).grad a y))
              1 (C * r ^ (-(d : ℝ) / 2))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r →
            (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y •
              ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e))) ∧
            OsBound P (fun a => euclideanNorm (∫ y, heatKernel z r y •
              ((a y).mulVec (e + (S.corrector e).grad a y) - S.homogenized.mulVec e))) 1
                (C * r ^ (-(d : ℝ) / 2))) ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ R : CoefficientField d Λ → ℝ, OsBound P R 1 C₁ ∧
            ∀ᵐ a ∂P, vectorGaussianEnergy (fun x => e + (S.corrector e).grad a (ε⁻¹ • x)) ^
              (1 / 2 : ℝ) ≤ ENNReal.ofReal (R a)) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_corrector_energy_bounds fun d hd Λ hΛ => ?_
  obtain ⟨C, C₁, hC, hC₁, hP⟩ := h d hd Λ hΛ
  refine ⟨C, C₁, hC, hC₁, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨S, hS⟩ := hP P hPl
  exact ⟨S, S.homogenizedMatrixBounds (by linarith), hS⟩

/-- **(4.126) from the commutator estimate (4.34), the linear estimate and the energy bound below
the scale**, at the stochastic exponent `1` and the spatial exponent `d/2`, with constants depending
only on `d` and `Λ`. -/
theorem negativeSobolevCorrector_of_commutator_linear_energy
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ Cc Cl CN : ℝ, 0 < Cc ∧ 0 < Cl ∧ 0 < CN ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
        ∃ S : HomogenizationData P,
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
            OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
              S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) 1
                (Cc * r ^ (-((d : ℝ) / 2)))) ∧
          (∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
            OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) -
              ξ)) 1 (Cl * (1 + euclideanNorm ξ) * r ^ (-((d : ℝ) / 2)))) ∧
          GaussianEnergyBound P S ((d : ℝ) / 2) CN) :
    QSH.Frozen.negativeSobolevCorrector := by
  refine negativeSobolevCorrector_of_linear_estimates fun d hd Λ hΛ => ?_
  obtain ⟨Cc, Cl, CN, hCc, hCl, hCN, hP⟩ := h d hd Λ hΛ
  refine ⟨Cc, Cl, CN, hCc, hCl, hCN, fun P hPl => ?_⟩
  have := hPl.1
  obtain ⟨S, hS⟩ := hP P hPl
  exact ⟨S, S.homogenizedMatrixBounds (by linarith), hS⟩

end QSH
