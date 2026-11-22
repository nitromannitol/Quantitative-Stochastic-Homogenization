import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel
import QuantitativeStochasticHomogenization.Ch03.Sec04.HeatConvolutionMeasurability
import QuantitativeStochasticHomogenization.Ch03.Sec04.HeatTransferIdentity

/-!
# Continuity of the coordinate Laplacian

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/HeatTransferBands.lean`.

The coordinate Laplacian `∑ᵢ ∂ᵢ² K` of a `C²` function is continuous.
-/

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- A compactly supported `C²` kernel has a continuous coordinate Laplacian. -/
theorem continuous_coordLaplacian {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) :
    Continuous (coordLaplacianFderiv K) := by
  exact continuous_finsetSum _ fun i _ =>
    continuous_fderiv_dir (contDiff_one_fderiv_dir hK (unitVector i)) (unitVector i)

end QSH
