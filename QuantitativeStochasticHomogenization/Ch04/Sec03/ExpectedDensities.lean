import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedPeriodicAverages
import QuantitativeStochasticHomogenization.Ch04.Sec03.HomogenizedBoundsFromAverages
import QuantitativeStochasticHomogenization.Front.Assumptions.MeasurableVersion

/-!
# The stationary densities of the corrected fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10.

The flux and energy densities of the corrected field `G ξ = ∑ ξᵢ (eᵢ + ∇φ_{eᵢ})`, formed with the
jointly measurable version `coefficientVersion` of the coefficients (`fluxDensity`,
`energyDensity`), are jointly measurable, agree for every coefficient field with the densities
formed with `a(x)` for almost every `x`, and are stationary: almost surely
`G ξ(a, x + n) = G ξ(T_n a, x)` for almost every `x`, and the same for the two densities.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ} {P : Measure (CoefficientField d Λ)}

/-- The flux density `a(x) G ξ(x)`, with the jointly measurable version of the coefficients. -/
def fluxDensity (S : HomogenizationData P) (ξ : Vec d) (a : CoefficientField d Λ) (x : Vec d) :
    Vec d :=
  (coefficientVersion a x).mulVec (correctedField S a ξ x)

/-- The energy density `G ξ(x) · a(x) G ξ(x)`, with the jointly measurable version of the
coefficients. -/
def energyDensity (S : HomogenizationData P) (ξ : Vec d) (a : CoefficientField d Λ) (x : Vec d) :
    ℝ :=
  dot (correctedField S a ξ x) (fluxDensity S ξ a x)

theorem measurable_mulVec_coefficientVersion {G : CoefficientField d Λ × Vec d → Vec d}
    (hG : Measurable G) :
    Measurable fun p : CoefficientField d Λ × Vec d => (coefficientVersion p.1 p.2).mulVec (G p) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct, coefficientVersion, Matrix.of_apply]
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_coefficientVersionEntry i j).mul ((measurable_pi_apply j).comp hG)

theorem measurable_fluxDensity (S : HomogenizationData P) (ξ : Vec d) :
    Measurable fun p : CoefficientField d Λ × Vec d => fluxDensity S ξ p.1 p.2 :=
  measurable_mulVec_coefficientVersion (measurable_correctedField S ξ)

theorem measurable_energyDensity (S : HomogenizationData P) (ξ : Vec d) :
    Measurable fun p : CoefficientField d Λ × Vec d => energyDensity S ξ p.1 p.2 := by
  unfold energyDensity dot
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp (measurable_correctedField S ξ)).mul
      ((measurable_pi_apply i).comp (measurable_fluxDensity S ξ))

theorem ae_fluxDensity_eq (S : HomogenizationData P) (ξ : Vec d) (a : CoefficientField d Λ) :
    ∀ᵐ x, fluxDensity S ξ a x = (a x).mulVec (correctedField S a ξ x) := by
  filter_upwards [ae_coefficientVersion_eq a] with x hx
  rw [fluxDensity, hx]

theorem ae_energyDensity_eq (S : HomogenizationData P) (ξ : Vec d) (a : CoefficientField d Λ) :
    ∀ᵐ x, energyDensity S ξ a x =
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
  filter_upwards [ae_fluxDensity_eq S ξ a] with x hx
  rw [energyDensity, hx]

theorem integral_heatKernel_smul_fluxDensity (S : HomogenizationData P) (ξ : Vec d)
    (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) :
    ∫ x, heatKernel z r x • fluxDensity S ξ a x =
      ∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x) :=
  integral_congr_ae (by filter_upwards [ae_fluxDensity_eq S ξ a] with x hx; rw [hx])

theorem integral_heatKernel_smul_energyDensity (S : HomogenizationData P) (ξ : Vec d)
    (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) :
    ∫ x, heatKernel z r x • energyDensity S ξ a x =
      ∫ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) :=
  integral_congr_ae (by filter_upwards [ae_energyDensity_eq S ξ a] with x hx; rw [hx, smul_eq_mul])

/-! ## Stationarity -/

theorem ae_correctedField_add_latticeShift (S : HomogenizationData P) (ξ : Vec d)
    (n : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ᵐ x, correctedField S a ξ (x + latticeShift n) =
      correctedField S (translate (latticeShift n) a) ξ x := by
  have h : ∀ᵐ a ∂P, ∀ i : Fin d, ∀ᵐ x,
      (S.corrector (unitVector i)).grad a (x + latticeShift n) =
        (S.corrector (unitVector i)).grad (translate (latticeShift n) a) x :=
    ae_all_iff.mpr fun i => (S.corrector (unitVector i)).stationary n
  filter_upwards [h] with a ha
  filter_upwards [ae_all_iff.mpr ha] with x hx
  unfold correctedField correctedCoordinate
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

theorem ae_coefficientVersion_add (a : CoefficientField d Λ) (y : Vec d) :
    ∀ᵐ x, coefficientVersion a (x + y) = coefficientVersion (translate y a) x := by
  have h1 : ∀ᵐ x, coefficientVersion a (x + y) = a.field (x + y) :=
    (measurePreserving_add_right (volume : Measure (Vec d)) y).quasiMeasurePreserving.ae
      (ae_coefficientVersion_eq a)
  filter_upwards [h1, ae_coefficientVersion_eq (translate y a)] with x hx1 hx2
  rw [hx1, hx2]
  change a.field (x + y) = a.field (y + x)
  rw [add_comm]

theorem ae_fluxDensity_add_latticeShift (S : HomogenizationData P) (ξ : Vec d)
    (n : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ᵐ x, fluxDensity S ξ a (x + latticeShift n) =
      fluxDensity S ξ (translate (latticeShift n) a) x := by
  filter_upwards [ae_correctedField_add_latticeShift S ξ n] with a ha
  filter_upwards [ha, ae_coefficientVersion_add a (latticeShift n)] with x hx1 hx2
  rw [fluxDensity, fluxDensity, hx1, hx2]

theorem ae_energyDensity_add_latticeShift (S : HomogenizationData P) (ξ : Vec d)
    (n : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ᵐ x, energyDensity S ξ a (x + latticeShift n) =
      energyDensity S ξ (translate (latticeShift n) a) x := by
  filter_upwards [ae_correctedField_add_latticeShift S ξ n,
    ae_fluxDensity_add_latticeShift S ξ n] with a ha hb
  filter_upwards [ha, hb] with x hx1 hx2
  rw [energyDensity, energyDensity, hx1, hx2]

end QSH
