import QuantitativeStochasticHomogenization.Ch05.Sec04.LocalizedAdditivityProof
import QuantitativeStochasticHomogenization.Ch03.Sec04.HomogenizationDataExistence

/-!
# Lemma 5.29 from Theorem 4.6 (i) and the measurability of the correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 5.29 (i)-(iii). The three block estimates follow from Theorem 4.6 (i) with constants
uniform over the laws (`UniformAdditivityJ1`) and the existence of homogenization data for every
law, which is `homogenizationDataExists_of_measurable` given the joint measurability of the
corrector gradients (`HighContrastCorrectorMeasurable`).
-/

open MeasureTheory

namespace QSH

/-- **Lemma 5.29 (i)** (`QSH.Frozen.blockCLT`) from Theorem 4.6 (i) with constants uniform over
the laws and the joint measurability of the corrector gradients. -/
theorem blockCLT_of_uniformAdditivityJ1_of_measurable (hU : UniformAdditivityJ1)
    (hM : HighContrastCorrectorMeasurable) : QSH.Frozen.blockCLT :=
  blockCLT_of_uniformAdditivityJ1 hU (homogenizationDataExists_of_measurable hM)

/-- **Lemma 5.29 (ii)** (`QSH.Frozen.blockBoundary`) from Theorem 4.6 (i) with constants uniform
over the laws and the joint measurability of the corrector gradients. -/
theorem blockBoundary_of_uniformAdditivityJ1_of_measurable (hU : UniformAdditivityJ1)
    (hM : HighContrastCorrectorMeasurable) : QSH.Frozen.blockBoundary :=
  blockBoundary_of_uniformAdditivityJ1 hU (homogenizationDataExists_of_measurable hM)

/-- **Lemma 5.29 (iii)** (`QSH.Frozen.blockChange`) from Theorem 4.6 (i) with constants uniform
over the laws and the joint measurability of the corrector gradients. -/
theorem blockChange_of_uniformAdditivityJ1_of_measurable (hU : UniformAdditivityJ1)
    (hM : HighContrastCorrectorMeasurable) : QSH.Frozen.blockChange :=
  blockChange_of_uniformAdditivityJ1 hU (homogenizationDataExists_of_measurable hM)

end QSH
