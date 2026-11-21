import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct

/-!
# Compact localization of spatial weak equations

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Correctors/SpatialWeakLocalization.lean`.

Source: the application–928`. The conditioned equations are valid
on a ball depending on the conditioning center. A smooth weight supported
strictly inside that ball extends the weighted equation to the whole
space. No weak equation for an unweighted field outside its domain is
assumed.
-/

open MeasureTheory

namespace QSH

/-- A derivative of a spatial test is another test on the same domain.
Source: the application–928`. -/
theorem isSpatialTest_coordinateDerivative {d : ℕ} {U : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (j : Fin d) :
    IsSpatialTest U (coordinateDerivative j ψ) := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const,
    hψ.2.1.fderiv_apply ℝ (unitVector j), ?_⟩
  apply Set.Subset.trans ?_ hψ.2.2
  apply closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra hxs
  have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs
  exact hx (by simp only [coordinateDerivative, hz, ContinuousLinearMap.zero_apply])

private theorem setIntegral_mul_test {d : ℕ} {U : Set (Vec d)}
    (f : Vec d → ℝ) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    (∫ x in U, f x * ψ x) = ∫ x, f x * ψ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : ψ x = 0 := by
    by_contra hzero
    exact hx (hψ.2.2 (subset_tsupport ψ hzero))
  rw [hz, mul_zero]

private theorem setIntegral_mul_test_derivative {d : ℕ} {U : Set (Vec d)}
    (f : Vec d → ℝ) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (j : Fin d) :
    (∫ x in U, f x * coordinateDerivative j ψ x) =
      ∫ x, f x * coordinateDerivative j ψ x :=
  setIntegral_mul_test f (isSpatialTest_coordinateDerivative hψ j)

/-- Restriction to a smaller spatial domain preserves a weak partial
derivative. Source: the application–928`. -/
theorem hasWeakPartialDerivative_mono {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {j : Fin d} {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U j f g) :
    HasWeakPartialDerivative V j f g := by
  refine ⟨h.1.mono_set hVU, h.2.1.mono_set hVU, ?_⟩
  intro ψ hψ
  have hψU : IsSpatialTest U ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hVU⟩
  have heq := h.2.2 ψ hψU
  rw [setIntegral_mul_test_derivative f hψU j, setIntegral_mul_test g hψU] at heq
  rwa [setIntegral_mul_test_derivative f hψ j, setIntegral_mul_test g hψ]

/-- Restriction of a weak gradient. Source: the application–928`. -/
theorem hasWeakGradient_mono {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {f : Vec d → ℝ} {G : Vec d → Vec d} (h : HasWeakGradient U f G) :
    HasWeakGradient V f G := fun j => hasWeakPartialDerivative_mono hVU (h j)

end QSH
