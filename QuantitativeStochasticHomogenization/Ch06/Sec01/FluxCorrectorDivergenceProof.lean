import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrectorDivergence
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatFormulaDivergence
import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorSublinear
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakCongruence

/-!
# Proof of the divergence identity of the flux corrector

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 6.1, (6.6): `fluxCorrectorDivergenceStatement`. The centered flux `a(e + ∇φ_e) - E[∫_□ a(e + ∇φ_e)]`
is divergence free and satisfies the hypotheses of the heat formula (6.7), and its deviation from
the constant `ā e - E[∫_□ a(e + ∇φ_e)]` has the scale pairing bounds of the high-contrast
homogenization theorem; so the deterministic identity
`hasWeakDivergence_row_of_isHeatSelectedFluxGradient` applies almost surely, with `D = ā e`
for the homogenized matrix `ā` of the high-contrast homogenization theorem.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Weak divergences only depend on the almost everywhere classes of the field and the
divergence. -/
theorem HasWeakDivergence.congr_ae {F F' : Vec d → Vec d} {h h' : Vec d → ℝ}
    (H : HasWeakDivergence Set.univ F h) (hF : ∀ᵐ x ∂(volume : Measure (Vec d)), F x = F' x)
    (hh : h =ᵐ[volume] h') : HasWeakDivergence Set.univ F' h' := by
  refine ⟨fun k => locallyIntegrableOn_congr_ae isOpen_univ (H.1 k) ?_,
    locallyIntegrableOn_congr_ae isOpen_univ H.2.1 (by rwa [Measure.restrict_univ]), ?_⟩
  · rw [Measure.restrict_univ]
    filter_upwards [hF] with x hx
    rw [hx]
  · intro ψ hψ
    have h1 := H.2.2 ψ hψ
    have e1 : ∫ x in Set.univ, dot (F x) (gradient ψ x) = ∫ x in Set.univ, dot (F' x) (gradient ψ x) := by
      rw [Measure.restrict_univ]
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hx
      rw [hx]
    have e2 : ∫ x in Set.univ, h x * ψ x = ∫ x in Set.univ, h' x * ψ x := by
      rw [Measure.restrict_univ]
      refine integral_congr_ae ?_
      filter_upwards [hh] with x hx
      rw [hx]
    rw [← e1, ← e2]
    exact h1

/-- A constant field has zero weak divergence. -/
theorem hasWeakDivergence_const (c : Vec d) :
    HasWeakDivergence Set.univ (fun _ => c) (fun _ => 0) := by
  refine ⟨fun k => locallyIntegrableOn_const _, locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hdint : ∀ k, Integrable (coordinateDerivative k ψ) := fun k =>
    (isSpatialTest_coordinateDerivative hψ k).1.continuous.integrable_of_hasCompactSupport
      (isSpatialTest_coordinateDerivative hψ k).2.1
  have hψint : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hzero : ∀ k, ∫ x, coordinateDerivative k ψ x = 0 := by
    intro k
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Vec d))) (f := fun _ : Vec d => (1 : ℝ)) (g := ψ)
      (v := unitVector k) (by simp) (by simp only [one_mul]; exact hdint k)
      (by simp only [one_mul]; exact hψint) (fun x _ => differentiableAt_const _)
      (fun x _ => hψd x)
    simpa [coordinateDerivative] using h
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero]
  unfold dot gradient
  rw [integral_finsetSum _ fun k _ => (hdint k).const_mul (c k)]
  exact Finset.sum_eq_zero fun k _ => by rw [integral_const_mul, hzero k, mul_zero]

/-- Gaussian moments are stable under subtracting a constant. -/
theorem HasGaussianMoments.sub_const {f : Vec d → ℝ} (hf : HasGaussianMoments f)
    (hfm : Measurable f) (c : ℝ) : HasGaussianMoments fun y => f y - c := by
  intro s hs ρ
  obtain ⟨B, hB⟩ := hf s hs ρ
  refine ⟨B + |c|, fun x hx => ⟨?_, ?_⟩⟩
  · refine ((hB x hx).1.add ((integrable_euclideanHeatKernel_sub hs x).mul_const |c|)).mono'
      ((((measurable_euclideanHeatKernel_joint (d := d)).comp (measurable_const.prodMk
        (measurable_const.sub measurable_id))).mul (hfm.sub measurable_const).abs).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    have hk := euclideanHeatKernel_nonneg hs.le (x - y)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, abs_abs]
    calc euclideanHeatKernel s (x - y) * |f y - c|
        ≤ euclideanHeatKernel s (x - y) * (|f y| + |c|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) hk
      _ = _ := by simp only [Pi.add_apply]; ring
  · have hint1 := (hB x hx).1
    have hint2 := (integrable_euclideanHeatKernel_sub hs x).mul_const |c|
    calc ∫ y, euclideanHeatKernel s (x - y) * |f y - c|
        ≤ ∫ y, (euclideanHeatKernel s (x - y) * |f y| + euclideanHeatKernel s (x - y) * |c|) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg
            (euclideanHeatKernel_nonneg hs.le _) (abs_nonneg _)) (hint1.add hint2)
            (Eventually.of_forall fun y => ?_)
          have hk := euclideanHeatKernel_nonneg hs.le (x - y)
          calc euclideanHeatKernel s (x - y) * |f y - c|
              ≤ euclideanHeatKernel s (x - y) * (|f y| + |c|) :=
                mul_le_mul_of_nonneg_left (abs_sub _ _) hk
            _ = _ := by ring
      _ = (∫ y, euclideanHeatKernel s (x - y) * |f y|) + |c| := by
          rw [integral_add hint1 hint2, integral_mul_const, integral_euclideanHeatKernel_sub hs x,
            one_mul]
      _ ≤ B + |c| := by linarith [(hB x hx).2]

/-- **Lemma 6.1, (6.6).** -/
theorem fluxCorrectorDivergence : fluxCorrectorDivergenceStatement := by
  intro d hd Λ hΛ P hP e he φ S
  have hK1 : 1 ≤ Λ := hΛ.le
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  obtain ⟨pk⟩ := hpk Λ hK1 P hP
  obtain ⟨Ap, Cab, hAp, -, hpair⟩ := exists_uniform_flux_pairing d hd Λ hK1 hκ hC₀.le
  refine ⟨fun k => (_root_.Homogenization.matVecMul pk.abar e) k, ?_⟩
  filter_upwards [hpair P pk hP e he φ, ae_heatFormulaHypotheses_representativeFlux hd hΛ hP he φ,
    S.heat_selected, S.weak_gradient, φ.harmonic] with a hpa hg hS hwS hharm
  intro j
  set g := representativeFlux φ a with hgdef
  set c : Vec d := fun k => (_root_.Homogenization.matVecMul pk.abar e) k - meanFlux φ k with hc
  have hrep := coefficientRepresentative_ae_eq a
  -- divergence free
  have hdiv : HasWeakDivergence Set.univ g (fun _ => 0) := by
    have h1 := hasWeakDivergence_add hharm (hasWeakDivergence_const (-meanFlux φ))
    refine h1.congr_ae ?_ (Eventually.of_forall fun x => by simp)
    filter_upwards [hrep] with x hx
    simp only [hgdef, representativeFlux, hx, sub_eq_add_neg]
  have hGsel : IsHeatSelectedFluxGradient g (S.grad a) :=
    isHeatSelectedFluxGradient_congr_ae (representativeFlux_ae_eq φ a).symm hS
  have hX0 : 0 < 2 * pk.X (toHighContrast hK1 a) := by
    have := pk.one_le_X (toHighContrast hK1 a)
    linarith
  have hfun : ∀ k, (fun y => g y k - c k) = fun y =>
      ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k -
        (_root_.Homogenization.matVecMul pk.abar e) k := by
    intro k
    funext y
    simp only [hgdef, representativeFlux, hc, Pi.sub_apply]
    ring
  have hpairk : ∀ k, HasScalePairingBound (fun y => g y k - c k)
      (2 * pk.X (toHighContrast hK1 a)) Ap κ := by
    intro k
    rw [hfun k]
    exact hpa.2.2 k
  have hmomc : ∀ k, HasGaussianMoments fun y => g y k - c k := fun k =>
    (hg.moments k).sub_const (hg.measurable k) (c k)
  have hdivj := hasWeakDivergence_row_of_isHeatSelectedFluxGradient hg hdiv hGsel hwS hpairk hX0
    hAp hκ hmomc j
  refine hdivj.congr_ae (Eventually.of_forall fun x => rfl) ?_
  filter_upwards [hrep] with x hx
  simp only [hgdef, hc, representativeFlux, Pi.sub_apply, hx]
  ring

end QSH
