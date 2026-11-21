import QuantitativeStochasticHomogenization.AppD.HeatKernelDerivatives
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses

/-!
# Appendix D: heat smoothing of test functions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D (Sobolev norms and heat flow): the heat smoothing `Φ(t) ∗ ψ` of a smooth compactly
supported function commutes with the iterated coordinate derivatives `∂^β` of the normalized
Sobolev norms (`multiIndexDerivative_heatSmooth`).
-/

open MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The heat smoothing `Φ(t) ∗ ψ`. -/
def heatSmooth (t : ℝ) (ψ : Vec d → ℝ) : Vec d → ℝ :=
  euclideanHeatKernel t ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ

theorem contDiff_coordinateDerivative {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin d) :
    ContDiff ℝ ∞ (coordinateDerivative j ψ) :=
  (hψ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem hasCompactSupport_coordinateDerivative {ψ : Vec d → ℝ} (hcψ : HasCompactSupport ψ)
    (j : Fin d) : HasCompactSupport (coordinateDerivative j ψ) :=
  hcψ.fderiv_apply (𝕜 := ℝ) (unitVector j)

theorem coordinateDerivative_heatSmooth {t : ℝ} (ht : 0 < t) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (j : Fin d) :
    coordinateDerivative j (heatSmooth t ψ) = heatSmooth t (coordinateDerivative j ψ) := by
  funext x
  have hf : LocallyIntegrable (euclideanHeatKernel (d := d) t) volume :=
    (integrable_euclideanHeatKernel ht).locallyIntegrable
  have h1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  unfold coordinateDerivative heatSmooth
  rw [(hcψ.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf h1 x).fderiv,
    convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf (hcψ.fderiv (𝕜 := ℝ))
      (h1.continuous_fderiv one_ne_zero) x
      (unitVector j)]

theorem foldr_coordinateDerivative_smooth {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (l : List (Fin d)) :
    ContDiff ℝ ∞ (l.foldr coordinateDerivative ψ) ∧
      HasCompactSupport (l.foldr coordinateDerivative ψ) := by
  induction l with
  | nil => exact ⟨hψ, hcψ⟩
  | cons j l ih =>
    rw [List.foldr_cons]
    exact ⟨contDiff_coordinateDerivative ih.1 j, hasCompactSupport_coordinateDerivative ih.2 j⟩

theorem foldr_coordinateDerivative_heatSmooth {t : ℝ} (ht : 0 < t) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (l : List (Fin d)) :
    l.foldr coordinateDerivative (heatSmooth t ψ) =
      heatSmooth t (l.foldr coordinateDerivative ψ) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    have h := foldr_coordinateDerivative_smooth hψ hcψ l
    exact coordinateDerivative_heatSmooth ht h.1 h.2 j

/-- **`∂^β (Φ(t) ∗ ψ) = Φ(t) ∗ ∂^β ψ`** for a smooth compactly supported `ψ`. -/
theorem multiIndexDerivative_heatSmooth {m : ℕ} {t : ℝ} (ht : 0 < t) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (β : Fin d → Fin (m + 1)) :
    multiIndexDerivative β (heatSmooth t ψ) = heatSmooth t (multiIndexDerivative β ψ) :=
  foldr_coordinateDerivative_heatSmooth ht hψ hcψ _

theorem multiIndexDerivative_smooth {m : ℕ} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (β : Fin d → Fin (m + 1)) :
    ContDiff ℝ ∞ (multiIndexDerivative β ψ) ∧ HasCompactSupport (multiIndexDerivative β ψ) :=
  foldr_coordinateDerivative_smooth hψ hcψ _

/-! ## Moving the derivatives onto the kernel -/

theorem integrable_mul_comp_sub_of_compact {K : Vec d → ℝ} (hK : Continuous K) {χ : Vec d → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (x : Vec d) :
    Integrable (fun s => K s * χ (x - s)) := by
  have hc : HasCompactSupport (fun s => χ (x - s)) :=
    hcχ.comp_homeomorph (Homeomorph.subLeft x)
  exact hK.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    (hχ.comp (continuous_const.sub continuous_id)) hc

/-- **One derivative moves onto the kernel**: `K ∗ ∂ⱼχ = ∂ⱼK ∗ χ` for a `C¹` kernel `K` and a smooth
compactly supported `χ`. -/
theorem convolution_coordinateDerivative {K : Vec d → ℝ} (hK : ContDiff ℝ 1 K) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (j : Fin d) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] coordinateDerivative j χ) =
      (coordinateDerivative j K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) := by
  funext x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  set g : Vec d → ℝ := fun s => χ (x - s) with hg
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hgd : ∀ s, HasFDerivAt g
      ((fderiv ℝ χ (x - s)).comp (-(ContinuousLinearMap.id ℝ (Vec d)))) s := fun s => by
    have h1 := (hχ1.differentiable one_ne_zero (x - s)).hasFDerivAt
    have h2 : HasFDerivAt (fun s : Vec d => x - s) (-(ContinuousLinearMap.id ℝ (Vec d))) s :=
      (hasFDerivAt_id s).const_sub x
    exact h1.comp s h2
  have hfg : ∀ s, fderiv ℝ g s (unitVector j) = -coordinateDerivative j χ (x - s) := fun s => by
    rw [(hgd s).fderiv, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
    rfl
  have hKc : Continuous K := hK.continuous
  have hdK : Continuous (coordinateDerivative j K) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdχ : Continuous (coordinateDerivative j χ) :=
    (hχ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := K) (g := g)
    (v := unitVector j)
    (integrable_mul_comp_sub_of_compact hdK hχ.continuous hcχ x)
    (by
      simp only [hfg]
      have := integrable_mul_comp_sub_of_compact hKc hdχ
        (hasCompactSupport_coordinateDerivative hcχ j) x
      simpa [mul_neg] using this.neg)
    (integrable_mul_comp_sub_of_compact hKc hχ.continuous hcχ x)
    (fun s _ => (hK.differentiable one_ne_zero) s)
    (fun s _ => (hgd s).differentiableAt)
  simp only [hfg, mul_neg, integral_neg] at hibp
  have := neg_inj.mp hibp
  exact this

theorem foldr_coordinateDerivative_contDiff {K : Vec d → ℝ} (hK : ContDiff ℝ ∞ K)
    (l : List (Fin d)) : ContDiff ℝ ∞ (l.foldr coordinateDerivative K) := by
  induction l with
  | nil => exact hK
  | cons j l ih => exact contDiff_coordinateDerivative ih j

/-- **All the derivatives move onto the kernel**: `K ∗ ∂_{j₁} ⋯ ∂_{jₙ} χ = ∂_{jₙ} ⋯ ∂_{j₁} K ∗ χ`. -/
theorem convolution_foldr_coordinateDerivative {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (l : List (Fin d)) {K : Vec d → ℝ} (hK : ContDiff ℝ ∞ K) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] l.foldr coordinateDerivative χ) =
      ((l.reverse.foldr coordinateDerivative K) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) := by
  induction l generalizing K with
  | nil => rfl
  | cons j l ih =>
    have hs := foldr_coordinateDerivative_smooth hχ hcχ l
    rw [List.foldr_cons, convolution_coordinateDerivative (hK.of_le (by simp)) hs.1 hs.2 j,
      ih (contDiff_coordinateDerivative hK j), List.reverse_cons, List.foldr_append]
    rfl

end QSH
