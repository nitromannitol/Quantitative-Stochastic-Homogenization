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

end QSH
