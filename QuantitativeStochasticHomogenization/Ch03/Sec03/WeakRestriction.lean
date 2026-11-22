import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakLocalization
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct

/-!
# Restriction of weak derivatives to subsets

A weak gradient or weak divergence on the whole space is one on every subset: a test supported
in `U` is a test on the whole space, and the integrands vanish outside its support.
-/

open MeasureTheory Filter

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

/-- **Uniqueness of weak divergences on open sets.** -/
theorem HasWeakDivergence.ae_eq {U : Set (Vec d)} (hU : IsOpen U) {F : Vec d → Vec d}
    {h₁ h₂ : Vec d → ℝ} (H₁ : HasWeakDivergence U F h₁) (H₂ : HasWeakDivergence U F h₂) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ U → h₁ x = h₂ x := by
  have hloc : LocallyIntegrableOn (fun x => h₁ x - h₂ x) U volume := H₁.2.1.sub H₂.2.1
  have h0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψc hψU => by
    have htest : IsSpatialTest U ψ := ⟨hψ, hψc, hψU⟩
    have e1 := H₁.2.2 ψ htest
    have e2 := H₂.2.2 ψ htest
    have i1 : IntegrableOn (fun x => h₁ x * ψ x) U := integrableOn_mul_spatialTest H₁.2.1 htest
    have i2 : IntegrableOn (fun x => h₂ x * ψ x) U := integrableOn_mul_spatialTest H₂.2.1 htest
    have hsplit : ∫ x in U, h₁ x * ψ x = ∫ x in U, h₂ x * ψ x := by linarith
    have e0 : ∫ x, ψ x • (h₁ x - h₂ x) = ∫ x in U, (h₁ x - h₂ x) * ψ x := by
      rw [setIntegral_eq_integral_of_tsupport_subset hψU]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    have e : ∫ x in U, (h₁ x - h₂ x) * ψ x = (∫ x in U, h₁ x * ψ x) - ∫ x in U, h₂ x * ψ x := by
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [e0, e, hsplit, sub_self]
  filter_upwards [h0] with x hx hxU
  linarith [hx hxU]

end QSH
