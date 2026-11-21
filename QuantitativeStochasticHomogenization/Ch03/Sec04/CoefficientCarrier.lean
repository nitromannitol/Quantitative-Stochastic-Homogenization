import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MeasurableRepresentative
import Homogenization.Probability.RegCoeffField.Sigma

/-!
# Coefficient carriers for homogenization

Moved from einstein-relation-lean c97689e `EinsteinFull/Homogenization/CoefficientCarrier.lean`.

The locally integrable coefficient fields of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.6)–(0.11),
admit Borel representatives. The representatives preserve the smooth integral
observations defining the local coefficient sigma algebras.
-/

open MeasureTheory

namespace QSH

attribute [local irreducible] coefficientRepresentative

/-- A Borel representative of a source coefficient as a regular coefficient field. -/
noncomputable def regularCoefficient {d : ℕ} {K : ℝ} (a : CoefficientField d K) :
    _root_.Homogenization.RegCoeffField d where
  toFun := coefficientRepresentative a
  entry_measurable := by
    intro i j
    have h : Measurable (fun x : Vec d => (a, x)) :=
      (measurable_const : Measurable (fun _ : Vec d => a)).prodMk measurable_id
    have hm := measurable_coefficientRepresentative (d := d) (K := K)
    change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _ at hm
    rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq] at hm
    have he := (measurable_pi_iff.mp (measurable_pi_iff.mp hm i)) j
    exact he.comp h
  entry_locInt := by
    intro i j
    apply (a.locally_integrable i j).congr
    have h := (coefficientRepresentative_ae_eq a).symm
    filter_upwards [h] with x hx
    exact congrFun (congrFun hx i) j

/-- The representative and original coefficient agree almost everywhere. -/
theorem regularCoefficient_ae_eq {d : ℕ} {K : ℝ} (a : CoefficientField d K) :
    (regularCoefficient a).toFun =ᵐ[volume] a.field :=
  coefficientRepresentative_ae_eq a

end QSH
