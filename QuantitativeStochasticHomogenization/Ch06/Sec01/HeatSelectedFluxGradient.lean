import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch06.Sec01.GaussianHeatGradientDensity
import QuantitativeStochasticHomogenization.Ch03.Sec04.FrobeniusNorm

/-!
# The heat-selected flux gradient

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/External/AKMCorrectorOscillation.lean`.

The predicate `IsHeatSelectedFluxGradient g G`: `G` is the gradient of the flux corrector of the field `g` selected by the heat formula (6.7) of Lemma 6.1, as the local `L²` limit of the truncations of the time integral.
-/

open MeasureTheory

open scoped Topology

noncomputable section

namespace QSH

/-- The local L² interpretation of the iterated positive-time integral
(6.7). Space is integrated first; the two time endpoints vary independently.
The integrability clauses ensure that both integrals are genuine integrals. -/
def IsHeatSelectedFluxGradient {d : ℕ} (g : Vec d → Vec d)
    (G : Fin d → Fin d → Vec d → Vec d) : Prop :=
  ∀ j k ℓ : Fin d, ∀ R : ℕ,
    let μ : Measure (Vec d) := volume.restrict (ball 0 (R + 1))
    (∀ m n : ℕ, ∀ᵐ x ∂μ,
      (∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
        Integrable (fun y =>
          heatGradientDensity g t j k ℓ x y)
          volume) ∧
      Integrable (fun t =>
        heatGradientSpaceIntegral g t j k ℓ x)
        (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)))) ∧
    (∀ m n : ℕ, MemLp
      (fun x => iteratedHeatGradientTruncation
        g m n j k ℓ x) 2 μ) ∧
    MemLp (fun x => G j k x ℓ) 2 μ ∧
    Filter.Tendsto (fun mn : ℕ × ℕ => eLpNorm
      (fun x => iteratedHeatGradientTruncation
        g mn.1 mn.2 j k ℓ x - G j k x ℓ) 2 μ) Filter.atTop (nhds 0)

end QSH
