import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MeasurableRepresentative
import Homogenization.Probability.RegCoeffField.Sigma

/-!
# Borel representatives of coefficient fields

Moved from einstein-relation-lean c97689e `EinsteinFull/Homogenization/CoefficientCarrier.lean`.

The locally integrable coefficient fields of (0.6)–(0.11) admit Borel representatives. The representatives preserve the test integrals (0.7) defining the local σ-algebras and agree with the field almost everywhere.
-/

open MeasureTheory

namespace QSH

attribute [local irreducible] coefficientRepresentative

/-- A Borel representative of a coefficient field as a regular coefficient field. -/
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
