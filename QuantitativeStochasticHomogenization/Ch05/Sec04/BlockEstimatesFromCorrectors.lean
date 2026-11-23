import QuantitativeStochasticHomogenization.Ch05.Sec04.LocalizedAdditivityProof
import QuantitativeStochasticHomogenization.Ch03.Sec04.CorrectorMeasurability

/-!
# Lemma 5.29 from Theorem 4.6 (i)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 5.29 (i)-(iii). The three block estimates follow from Theorem 4.6 (i) with constants
uniform over the laws (`UniformAdditivityJ1`) and the existence of homogenization data for every
law, which is `homogenizationDataExists`.
-/

open MeasureTheory

namespace QSH

/-- **Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`) from Theorem 4.6 (i) with constants uniform over
the laws. -/
theorem blockCLT_of_uniformAdditivity (hU : UniformAdditivityJ1) : QSH.Frozen.blockCLT :=
  blockCLT_of_uniformAdditivityJ1 hU homogenizationDataExists

/-- **Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`) from Theorem 4.6 (i) with constants uniform
over the laws. -/
theorem blockBoundary_of_uniformAdditivity (hU : UniformAdditivityJ1) :
    QSH.Frozen.blockBoundary :=
  blockBoundary_of_uniformAdditivityJ1 hU homogenizationDataExists

/-- **Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`) from Theorem 4.6 (i) with constants uniform
over the laws. -/
theorem blockChange_of_uniformAdditivity (hU : UniformAdditivityJ1) : QSH.Frozen.blockChange :=
  blockChange_of_uniformAdditivityJ1 hU homogenizationDataExists

end QSH
