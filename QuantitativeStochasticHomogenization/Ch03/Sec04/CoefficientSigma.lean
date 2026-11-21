import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Ch03.Sec04.MatrixBorel

/-!
# Coefficient Sigma

Moved from einstein-relation-lean c97689e `vendor/EinsteinRelation/EinsteinRelation/Environment/AKMTestIntegralSupport.lean`.
-/

open MeasureTheory

namespace QSH

theorem euclideanSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanSq (c • x) = c ^ 2 * euclideanSq x := by
  change (∑ i, (c * x i) * (c * x i)) = c ^ 2 * ∑ i, x i * x i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem euclideanNorm_smul {d : ℕ} (c : ℝ) (hc : 0 ≤ c) (x : Vec d) :
    euclideanNorm (c • x) = c * euclideanNorm x := by
  unfold euclideanNorm
  rw [euclideanSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

theorem integrable_testIntegrand {d : ℕ} {K : ℝ} (A : CoefficientField d K)
    (u : SmoothCompactTest d) (i j : Fin d) :
    Integrable (fun x => u x * A.field x i j) volume := by
  simpa [smul_eq_mul] using
    (A.locally_integrable i j).integrable_smul_left_of_hasCompactSupport
      u.smooth.continuous u.compact

/-- the book's full coefficient sigma algebra, defined by the test-integral observables. -/
@[instance_reducible]
noncomputable def coefficientSigma {d : ℕ} {K : ℝ} : MeasurableSpace (CoefficientField d K) :=
  ⨆ u : SmoothCompactTest d, ⨆ i : Fin d, ⨆ j : Fin d,
    MeasurableSpace.comap (fun A : CoefficientField d K => testIntegral A u i j) inferInstance

def translateDomain {d : ℕ} (y : Vec d) : Vec d ≃ₜ Vec d where
  toFun := fun x => y + x
  invFun := fun x => -y + x
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  continuous_toFun := continuous_const.add continuous_id
  continuous_invFun := continuous_const.add continuous_id

theorem locallyIntegrable_translate {d : ℕ} (y : Vec d) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun x => f (y + x)) volume := by
  let e := translateDomain y
  have hmp : MeasurePreserving e volume volume := by
    simpa [e, translateDomain] using measurePreserving_add_left (volume : Measure (Vec d)) y
  have hmap : Measure.map e volume = volume := hmp.map_eq
  have hf' : LocallyIntegrable f (Measure.map e volume) := by rw [hmap]; exact hf
  exact (locallyIntegrable_map_homeomorph e).1 hf'

def translateTest {d : ℕ} (y : Vec d) (u : SmoothCompactTest d) : SmoothCompactTest d := by
  let e := translateDomain y
  refine ⟨fun x => u (e.symm x), ?_, ?_⟩
  · exact u.smooth.comp (contDiff_const.add contDiff_id)
  · rw [HasCompactSupport, tsupport]
    have hsupp : Function.support (fun x => u (e.symm x)) = e '' Function.support u := by
      ext x
      constructor
      · intro hx
        exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [hsupp, ← e.image_closure]
    exact u.compact.image e.continuous

theorem testIntegral_translate {d : ℕ} {K : ℝ} (y : Vec d)
    (A : CoefficientField d K) (u : SmoothCompactTest d) (i j : Fin d) :
    testIntegral (translate y A) u i j =
      testIntegral A (translateTest y u) i j := by
  let e := translateDomain y
  have hmp : MeasurePreserving e volume volume := by
    simpa [e, translateDomain] using measurePreserving_add_left (volume : Measure (Vec d)) y
  have h := hmp.integral_comp e.measurableEmbedding
    (fun x => u (e.symm x) * A.field x i j)
  simpa [testIntegral, translate, translateTest, e, translateDomain,
    add_assoc] using h

theorem measurable_translateCoefficient {d : ℕ} {K : ℝ} (y : Vec d) :
    Measurable (translate (d := d) (Λ := K) y) := by
  rw [measurable_iff_comap_le]
  change (coefficientSigma (d := d) (K := K)).comap
    (translate y) ≤ coefficientSigma (d := d) (K := K)
  unfold coefficientSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro u
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro i
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro j
  have hcomp : (fun A : CoefficientField d K =>
      testIntegral (translate y A) u i j) =
      (fun A => testIntegral A (translateTest y u) i j) := by
    funext A
    exact testIntegral_translate y A u i j
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
    (fun A : CoefficientField d K => testIntegral (translate y A) u i j)
    inferInstance ≤ _
  rw [hcomp]
  exact le_iSup_of_le (translateTest y u)
    (le_iSup_of_le i (le_iSup_of_le j le_rfl))

def HasUnitRangeOfDependence {d : ℕ} {K : ℝ} (P : Measure (CoefficientField d K)) : Prop :=
  ∀ U W : Set (Vec d), MeasurableSet U → MeasurableSet W →
    (∃ s : ℝ, 1 < s ∧ ∀ x ∈ U, ∀ y ∈ W, s ≤ euclideanNorm (x - y)) →
    ProbabilityTheory.Indep (localSigma U) (localSigma W) P

/-- The exact random-variable convention (0.41)--(0.42) of the cited book. -/
theorem measurable_testIntegral {d : ℕ} {K : ℝ} (u : SmoothCompactTest d)
    (i j : Fin d) : Measurable (fun A : CoefficientField d K => testIntegral A u i j) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le u (le_iSup_of_le i (le_iSup_of_le j le_rfl))

end QSH
