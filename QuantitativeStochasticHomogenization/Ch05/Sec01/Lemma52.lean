import Mathlib.Probability.CramerWold
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Lemma 5.2: the Cramér–Wold lemma

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.1, Lemma 5.2, for random variables with values in `ℝ^d = Vec d`, on possibly different
probability spaces:

1. if `λ·Xₙ → λ·X` in law for every `λ ∈ ℝ^d`, then `Xₙ → X` in law
   (`lemma_5_2_tendstoInDistribution`);
2. if `λ·X₁` and `λ·X` have the same law for every `λ ∈ ℝ^d`, then `X₁` and `X` have the same
   law (`lemma_5_2_map_eq`).

The book refers to the Fourier transform; the proofs go through `EuclideanSpace ℝ (Fin d)`, where
`⟪x, t⟫ = t·x`, with Lévy's continuity theorem (`TendstoInDistribution.of_tendsto_charFun`) and the
uniqueness of the characteristic function (`Measure.ext_of_charFun`), as in Mathlib's Cramér–Wold
theorem `tendstoInDistribution_iff_tendstoInDistribution_inner` (stated there on one probability
space).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `⟪x, t⟫ = t·x` under `Vec d ≃ EuclideanSpace ℝ (Fin d)`. -/
theorem inner_euclideanSpace_equiv_symm (x t : Vec d) :
    inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) ((EuclideanSpace.equiv (Fin d) ℝ).symm t) =
      dot t x := by
  simp [PiLp.inner_apply, dot, mul_comm]

theorem inner_euclideanSpace_equiv_symm_left (x : Vec d) (t : EuclideanSpace ℝ (Fin d)) :
    inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) t =
      dot (EuclideanSpace.equiv (Fin d) ℝ t) x := by
  have h := inner_euclideanSpace_equiv_symm x (EuclideanSpace.equiv (Fin d) ℝ t)
  rwa [ContinuousLinearEquiv.symm_apply_apply] at h

/-- **Lemma 5.2 (1), the Cramér–Wold lemma**: if `λ·Xₙ → λ·X` in law for every `λ ∈ ℝ^d`, then
`Xₙ → X` in law. -/
theorem lemma_5_2_tendstoInDistribution {Ω : ℕ → Type*} {m : (n : ℕ) → MeasurableSpace (Ω n)}
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {Ω' : Type*}
    {m' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : (n : ℕ) → Ω n → Vec d} {X' : Ω' → Vec d}
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hX' : AEMeasurable X' P')
    (h : ∀ l : Vec d, TendstoInDistribution (fun n ω => dot l (X n ω)) atTop
      (fun ω => dot l (X' ω)) P P') :
    TendstoInDistribution X atTop X' P P' := by
  have hY : ∀ n, AEMeasurable (fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X n ω)) (P n) :=
    fun n => (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp_aemeasurable (hX n)
  have hY' : AEMeasurable (fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X' ω)) P' :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp_aemeasurable hX'
  have hconv : TendstoInDistribution (fun n ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X n ω))
      atTop (fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X' ω)) P P' := by
    refine TendstoInDistribution.of_tendsto_charFun hY hY' fun t => ?_
    have e1 : ∀ n, charFun ((P n).map fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X n ω)) t =
        charFun ((P n).map fun ω => dot (EuclideanSpace.equiv (Fin d) ℝ t) (X n ω)) 1 :=
      fun n => by
        rw [charFun_map_eq_charFun_map_inner_one (hY n)]
        simp only [inner_euclideanSpace_equiv_symm_left]
    have e2 : charFun (P'.map fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X' ω)) t =
        charFun (P'.map fun ω => dot (EuclideanSpace.equiv (Fin d) ℝ t) (X' ω)) 1 := by
      rw [charFun_map_eq_charFun_map_inner_one hY']
      simp only [inner_euclideanSpace_equiv_symm_left]
    simp only [e1, e2]
    exact (h (EuclideanSpace.equiv (Fin d) ℝ t)).tendsto_charFun 1
  have h2 := hconv.continuous_comp (EuclideanSpace.equiv (Fin d) ℝ).continuous
  have hXe : (fun n => (EuclideanSpace.equiv (Fin d) ℝ) ∘
      fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X n ω)) = X := by
    funext n ω
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hXe' : ((EuclideanSpace.equiv (Fin d) ℝ) ∘
      fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X' ω)) = X' := by
    funext ω
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hXe, hXe'] at h2
  exact h2

/-- **Lemma 5.2 (2)**: if `λ·X₁` and `λ·X` have the same law for every `λ ∈ ℝ^d`, then `X₁` and
`X` have the same law. -/
theorem lemma_5_2_map_eq {Ω₁ Ω : Type*} {m₁ : MeasurableSpace Ω₁} {m : MeasurableSpace Ω}
    {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁] {P : Measure Ω} [IsProbabilityMeasure P]
    {X₁ : Ω₁ → Vec d} {X : Ω → Vec d} (hX₁ : AEMeasurable X₁ P₁) (hX : AEMeasurable X P)
    (h : ∀ l : Vec d, P₁.map (fun ω => dot l (X₁ ω)) = P.map (fun ω => dot l (X ω))) :
    P₁.map X₁ = P.map X := by
  have hY₁ : AEMeasurable (fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X₁ ω)) P₁ :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp_aemeasurable hX₁
  have hY : AEMeasurable (fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X ω)) P :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp_aemeasurable hX
  have hchar : charFun (P₁.map fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X₁ ω)) =
      charFun (P.map fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X ω)) := by
    funext t
    rw [charFun_map_eq_charFun_map_inner_one hY₁, charFun_map_eq_charFun_map_inner_one hY]
    simp only [inner_euclideanSpace_equiv_symm_left]
    rw [h]
  have hmap := Measure.ext_of_charFun hchar
  have h1 : P₁.map X₁ = (P₁.map fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X₁ ω)).map
      (EuclideanSpace.equiv (Fin d) ℝ) := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (EuclideanSpace.equiv (Fin d) ℝ).continuous.aemeasurable hY₁]
    congr 1
  have h2 : P.map X = (P.map fun ω => (EuclideanSpace.equiv (Fin d) ℝ).symm (X ω)).map
      (EuclideanSpace.equiv (Fin d) ℝ) := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (EuclideanSpace.equiv (Fin d) ℝ).continuous.aemeasurable hY]
    congr 1
  rw [h1, h2, hmap]

end QSH
