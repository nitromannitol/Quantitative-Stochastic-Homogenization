import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch06.Sec01.GaussianHeatGradientDensity
import QuantitativeStochasticHomogenization.Ch03.Sec04.FrobeniusNorm
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# AKM scalar and flux corrector oscillation estimates

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/External/AKMCorrectorOscillation.lean`.

Proposed, unfrozen literature propositions from Armstrong--Kuusi--Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity* (2019),
the book. Application: the application.

All laws below use AKM's coefficient carrier and test-integral sigma algebra,
normalized ellipticity, lattice stationarity and unit range. No canonical
corrector identification, spatial rescaling, pointwise regularity, or passage
to spatial Lᵐ estimates is assumed. These remain internal proof obligations.
The norms with an overbar in AKM are normalized spatial L² norms.

The scalar stationary estimate is (4.5), printed p. 124 (PDF page 159).
The two-dimensional estimates are (4.6)--(4.7), on that same page, and
Proposition 4.27, (4.147), printed p. 181 (PDF page 216).
The flux gradient estimate is Lemma 6.1, (6.8), printed p. 246 (PDF page 281).
Its gradient is selected by (6.7) on that page. The stationary flux estimate
is Proposition 6.2, (6.14), printed p. 250 (PDF page 285); the difference of
heat averages is (6.16), on the same page. In particular, (6.14) is a bound
on the **square** of the normalized L² norm. No signed Poisson or divergence
identity is imported from this source.
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
