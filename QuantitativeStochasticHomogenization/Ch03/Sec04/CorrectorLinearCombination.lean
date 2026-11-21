import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors

/-!
# Linear combinations of first-order correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4, Definitions 3.14–3.15: if `φᵢ` are correctors in the directions `uᵢ`, then
`∑ᵢ cᵢ φᵢ` is a corrector in the direction `∑ᵢ cᵢ uᵢ` (`Corrector.linearCombination`). In
particular homogenization data can be replaced by data whose correctors are the combinations of
the correctors in the coordinate directions (`HomogenizationData.linearize`), with the same
homogenized matrix.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Weak derivatives of finite linear combinations -/

theorem isSpatialTest_continuous_coordinateDerivative {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) (j : Fin d) : Continuous (coordinateDerivative j φ) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem isSpatialTest_hasCompactSupport_coordinateDerivative {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) (j : Fin d) : HasCompactSupport (coordinateDerivative j φ) :=
  hφ.2.1.fderiv_apply (𝕜 := ℝ) (unitVector j)

theorem integrable_mul_coordinateDerivative {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest Set.univ φ) (j : Fin d) :
    Integrable (fun x => f x * coordinateDerivative j φ x) :=
  hf.integrable_smul_right_of_hasCompactSupport
    (isSpatialTest_continuous_coordinateDerivative hφ j)
    (isSpatialTest_hasCompactSupport_coordinateDerivative hφ j)

theorem integrable_mul_test {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) : Integrable (fun x => f x * φ x) :=
  hf.integrable_smul_right_of_hasCompactSupport hφ.1.continuous hφ.2.1

theorem HasWeakPartialDerivative.finsetSum {ι : Type*} (s : Finset ι) {j : Fin d}
    {f g : ι → Vec d → ℝ} (c : ι → ℝ)
    (h : ∀ i ∈ s, HasWeakPartialDerivative Set.univ j (f i) (g i)) :
    HasWeakPartialDerivative Set.univ j (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * g i x) := by
  have hf : ∀ i ∈ s, LocallyIntegrable (f i) volume := fun i hi =>
    locallyIntegrableOn_univ.mp (h i hi).1
  have hg : ∀ i ∈ s, LocallyIntegrable (g i) volume := fun i hi =>
    locallyIntegrableOn_univ.mp (h i hi).2.1
  refine ⟨locallyIntegrableOn_univ.mpr (locallyIntegrable_finsetSum s fun i hi =>
      (hf i hi).smul (c i)), locallyIntegrableOn_univ.mpr (locallyIntegrable_finsetSum s
      fun i hi => (hg i hi).smul (c i)), fun φ hφ => ?_⟩
  have h1 := fun i hi => (h i hi).2.2 φ hφ
  simp only [Measure.restrict_univ] at h1 ⊢
  have hint1 : ∀ i ∈ s, Integrable (fun x => c i * (f i x * coordinateDerivative j φ x)) :=
    fun i hi => (integrable_mul_coordinateDerivative (hf i hi) hφ j).const_mul (c i)
  have hint2 : ∀ i ∈ s, Integrable (fun x => c i * (g i x * φ x)) :=
    fun i hi => (integrable_mul_test (hg i hi) hφ).const_mul (c i)
  calc (∫ x, (∑ i ∈ s, c i * f i x) * coordinateDerivative j φ x)
      = ∫ x, ∑ i ∈ s, c i * (f i x * coordinateDerivative j φ x) := by
        congr 1; funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ s, c i * ∫ x, f i x * coordinateDerivative j φ x := by
        rw [integral_finsetSum s hint1]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i ∈ s, c i * -(∫ x, g i x * φ x) :=
        Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
    _ = -(∫ x, (∑ i ∈ s, c i * g i x) * φ x) := by
        rw [show (fun x => (∑ i ∈ s, c i * g i x) * φ x) =
            fun x => ∑ i ∈ s, c i * (g i x * φ x) by
          funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
          integral_finsetSum s hint2, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring

theorem HasWeakGradient.finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ}
    {g : ι → Vec d → Vec d} (c : ι → ℝ) (h : ∀ i ∈ s, HasWeakGradient Set.univ (f i) (g i)) :
    HasWeakGradient Set.univ (fun x => ∑ i ∈ s, c i * f i x) (fun x => ∑ i ∈ s, c i • g i x) :=
  fun j => by
    have := HasWeakPartialDerivative.finsetSum s (j := j) (f := f) (g := fun i x => g i x j) c
      fun i hi => h i hi j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

theorem integrable_dot_gradient {F : Vec d → Vec d}
    (hF : ∀ k : Fin d, LocallyIntegrable (fun x => F x k) volume) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) : Integrable (fun x => dot (F x) (gradient φ x)) := by
  unfold dot
  exact integrable_finsetSum _ fun k _ => integrable_mul_coordinateDerivative (hF k) hφ k

theorem HasWeakDivergence.finsetSum_zero {ι : Type*} (s : Finset ι) {F : ι → Vec d → Vec d}
    (c : ι → ℝ) (h : ∀ i ∈ s, HasWeakDivergence Set.univ (F i) (fun _ => 0)) :
    HasWeakDivergence Set.univ (fun x => ∑ i ∈ s, c i • F i x) (fun _ => 0) := by
  have hF : ∀ i ∈ s, ∀ k : Fin d, LocallyIntegrable (fun x => F i x k) volume := fun i hi k =>
    locallyIntegrableOn_univ.mp ((h i hi).1 k)
  refine ⟨fun k => ?_, locallyIntegrableOn_zero, fun φ hφ => ?_⟩
  · refine locallyIntegrableOn_univ.mpr ?_
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      locallyIntegrable_finsetSum s fun i hi => (hF i hi k).smul (c i)
  · have h1 := fun i hi => (h i hi).2.2 φ hφ
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h1 ⊢
    have hint : ∀ i ∈ s, Integrable (fun x => c i * dot (F i x) (gradient φ x)) := fun i hi =>
      (integrable_dot_gradient (hF i hi) hφ).const_mul (c i)
    calc (∫ x, dot (∑ i ∈ s, c i • F i x) (gradient φ x))
        = ∫ x, ∑ i ∈ s, c i * dot (F i x) (gradient φ x) := by
          congr 1; funext x
          simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ i ∈ s, c i * ∫ x, dot (F i x) (gradient φ x) := by
          rw [integral_finsetSum s hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ = 0 := Finset.sum_eq_zero fun i hi => by rw [h1 i hi, mul_zero]

end QSH
