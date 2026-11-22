import QuantitativeStochasticHomogenization.Ch04.Sec01.HomogenizedBounds
import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyMeasurability

/-!
# The bounds `1 ≤ ā ≤ Λ` of the homogenized matrix

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Definition 1.2 and (1.22). The Dirichlet energies on the triadic cubes are measurable
(`measurable_dirichletEnergy`), hence almost surely strongly measurable for every law
(`aestronglyMeasurable_dirichletEnergy_triadicCube`), and the bounds `1 ≤ ā ≤ Λ` hold for the
homogenized matrix of any homogenization data of a probability measure
(`HomogenizationData.homogenizedMatrixBounds`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **The Dirichlet energies on the triadic cubes are almost surely strongly measurable** for every
law. -/
theorem aestronglyMeasurable_dirichletEnergy_triadicCube (hΛ : 0 ≤ Λ)
    (P : Measure (CoefficientField d Λ)) (n : ℕ) (e : Vec d) :
    AEStronglyMeasurable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) e)
      P :=
  (measurable_dirichletEnergy (volume_triadicCube_ne_top d n) hΛ e).aestronglyMeasurable

/-- **`1 ≤ ā ≤ Λ`** for the homogenized matrix of homogenization data of a probability measure. -/
theorem HomogenizationData.homogenizedMatrixBounds {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (S : HomogenizationData P) (hΛ : 0 ≤ Λ) :
    HomogenizedMatrixBounds S.homogenized Λ :=
  homogenizedMatrixBounds_of_aestronglyMeasurable S hΛ fun n e =>
    aestronglyMeasurable_dirichletEnergy_triadicCube hΛ P n e

end QSH
