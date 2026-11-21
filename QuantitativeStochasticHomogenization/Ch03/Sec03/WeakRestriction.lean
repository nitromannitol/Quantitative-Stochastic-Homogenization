import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization

/-!
# Restriction of weak derivatives to subsets

A weak gradient or weak divergence on the whole space is one on every subset: a test supported
in `U` is a test on the whole space, and the integrands vanish outside its support.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

theorem setIntegral_eq_integral_of_tsupport_subset {U : Set (Vec d)} {ψ : Vec d → ℝ}
    (hψ : tsupport ψ ⊆ U) (f : Vec d → ℝ) :
    ∫ x in U, f x * ψ x = ∫ x, f x * ψ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  have : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hψ h)
  rw [this, mul_zero]

theorem HasWeakGradient.mono_univ {U : Set (Vec d)} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ f g) : HasWeakGradient U f g := by
  intro i
  refine ⟨(h i).1.mono_set (Set.subset_univ _), (h i).2.1.mono_set (Set.subset_univ _),
    fun ψ hψ => ?_⟩
  have htest : IsSpatialTest Set.univ ψ := ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
  have h1 := (h i).2.2 ψ htest
  simp only [Measure.restrict_univ] at h1
  have hdψ := (isSpatialTest_coordinateDerivative hψ i).2.2
  rw [setIntegral_eq_integral_of_tsupport_subset hdψ, setIntegral_eq_integral_of_tsupport_subset hψ.2.2]
  exact h1

end QSH
