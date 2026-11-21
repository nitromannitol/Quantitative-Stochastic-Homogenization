import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors
import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatSelectedFluxGradient

/-!
# Flux Corrector

Moved from einstein-relation-lean c97689e `EinsteinFull/External/Source/AKMSourceFluxCorrector.lean`.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- The mean cell flux `E[∫_□ a(e + ∇φ)]`. This total integral imposes no
integrability premise on the corrector. Its integrability and identification
with the homogenized flux must be derived separately. -/
def meanFlux {d : ℕ} {K : ℝ} {P : Measure (CoefficientField d K)} {e : Vec d}
    (φ : Corrector P e) : Vec d :=
  ∫ a, ∫ x in unitCell d, (a x).mulVec (e + φ.grad a x) ∂volume ∂P

/-- The flux in (6.7). The spatial Gaussian Hessian annihilates the
constant centering vector. No cell integrability or expected-flux equality
is a hypothesis of this definition or of the flux corrector below. -/
def centeredFlux {d : ℕ} {K : ℝ} {P : Measure (CoefficientField d K)}
    {e : Vec d} (φ : Corrector P e) (a : CoefficientField d K) (x : Vec d) : Vec d :=
  (a x).mulVec (e + φ.grad a x) - meanFlux φ

/-- The flux potential selected up to constants by AKM (6.7), printed
p.246. It consists of the heat selection, the weak gradient and the local Sobolev
regularity; it assumes no quantitative
bound or derived annealed cell-flux integrability. -/
structure FluxCorrector {d : ℕ} {K : ℝ} {P : Measure (CoefficientField d K)}
    {e : Vec d} (φ : Corrector P e) where
  /-- The spatial matrix-valued flux potential, defined up to constants. -/
  potential : CoefficientField d K → Vec d → Mat d
  /-- The weak spatial gradient of each matrix entry. -/
  grad : CoefficientField d K → Fin d → Fin d → Vec d → Vec d
  measurable_potential : Measurable
    (fun p : CoefficientField d K × Vec d => potential p.1 p.2)
  measurable_grad : ∀ j k, Measurable
    (fun p : CoefficientField d K × Vec d => grad p.1 j k p.2)
  weak_gradient : ∀ᵐ a ∂P, ∀ j k,
    HasWeakGradient Set.univ (fun x => potential a x j k) (grad a j k)
  locally_square_integrable : ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R → ∀ j k,
    MemLp (fun x => potential a x j k) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (grad a j k) 2 (volume.restrict (ball 0 R))
  heat_selected : ∀ᵐ a ∂P, IsHeatSelectedFluxGradient (centeredFlux φ a) (grad a)

end QSH
