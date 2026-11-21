import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipsoidCutoff
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientEllipticity
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientCarrier
import EllipticRegularity.Energy.CoefficientEnergyCaccioppoli
import Homogenization.Probability.RegCoeffField.EllipticSet
import HCPoly.Setup.CoefficientSpace

/-!
# Weak solutions of the elliptic regularity library from coefficient fields

A coefficient field `a` has a measurable representative which is `(1, Λ)`-elliptic at every
point and agrees with `a` almost everywhere. With it, a square-integrable function with
square-integrable weak gradient on an open set `U` whose flux `a ∇v` is weakly divergence free
is a weakly harmonic `H¹` function of the elliptic regularity library.
-/

open MeasureTheory Set Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The measurable `(1, Λ)`-elliptic representative of a coefficient field. -/
def ellipticFieldOf {Λ : ℝ} (a : CoefficientField d Λ) : Vec d → Mat d := fun x =>
  open Classical in
  if _root_.Homogenization.IsEllipticMatrix 1 Λ (coefficientRepresentative a x) then
    coefficientRepresentative a x else 1

theorem measurable_coefficientRepresentative_entry {Λ : ℝ} (a : CoefficientField d Λ)
    (i j : Fin d) : Measurable (fun x => coefficientRepresentative a x i j) :=
  (regularCoefficient a).entry_measurable i j

theorem measurableSet_isEllipticMatrix_representative {Λ : ℝ} (a : CoefficientField d Λ) :
    MeasurableSet {x | _root_.Homogenization.IsEllipticMatrix 1 Λ (coefficientRepresentative a x)} := by
  classical
  have hm : Measurable (fun x : Vec d => fun i j =>
      if x ∈ (Set.univ : Set (Vec d)) then coefficientRepresentative a x i j else 0) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact Measurable.ite MeasurableSet.univ (measurable_coefficientRepresentative_entry a i j)
      measurable_const
  have h := _root_.Homogenization.measurableSet_isEllipticMatrix_inter
    (a := coefficientRepresentative a) (Θ := Λ) MeasurableSet.univ (by convert hm)
  rwa [Set.univ_inter] at h

theorem measurable_ellipticFieldOf {Λ : ℝ} (a : CoefficientField d Λ) :
    Measurable (fun x i j => ellipticFieldOf a x i j) := by
  classical
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have heq : (fun x => ellipticFieldOf a x i j) = fun x =>
      if _root_.Homogenization.IsEllipticMatrix 1 Λ (coefficientRepresentative a x) then
        coefficientRepresentative a x i j else (1 : Mat d) i j := by
    funext x
    unfold ellipticFieldOf
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (measurableSet_isEllipticMatrix_representative a)
    (measurable_coefficientRepresentative_entry a i j) measurable_const

theorem isEllipticMatrix_ellipticFieldOf {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    (x : Vec d) : PDE.IsEllipticMatrix 1 Λ (ellipticFieldOf a x) := by
  unfold ellipticFieldOf
  split_ifs with h
  · exact h
  · exact _root_.Homogenization.HighContrast.isEllipticMatrix_one_le hΛ

theorem ellipticFieldOf_ae_eq {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ellipticFieldOf a x = a x := by
  filter_upwards [coefficientRepresentative_ae_eq a] with x hx
  have hell := coefficientField_isEllipticMatrix a hΛ le_rfl x
  unfold ellipticFieldOf
  rw [hx]
  simp [hell]

theorem isEllipticFieldOn_ellipticFieldOf {Λ : ℝ} (hΛ : 1 ≤ Λ) (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    PDE.IsEllipticFieldOn 1 Λ U (ellipticFieldOf a) := by
  classical
  refine ⟨?_, fun x _ => isEllipticMatrix_ellipticFieldOf hΛ a x⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite hU ((measurable_pi_iff.1 (measurable_pi_iff.1
    (measurable_ellipticFieldOf a) i) j)) measurable_const

/-- The `H¹` function of the weak data on an open set. -/
def toH1FunctionOn {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) : PDE.H1Function U where
  toFun := u
  grad := g
  memL2 := hu
  gradMemL2 := hg
  hasWeakGradient := fun i φ h1 h2 h3 => (hw i).2.2 φ ⟨h1, h2, h3⟩

theorem isWeakDivergenceFormHarmonicOn_toH1FunctionOn {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (a : CoefficientField d Λ) {U : Set (Vec d)} (hU : MeasurableSet U) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) (hw : HasWeakGradient U u g)
    (hdiv : HasWeakDivergence U (fun x => (a x).mulVec (g x)) (fun _ => 0)) :
    PDE.IsWeakDivergenceFormHarmonicOn (ellipticFieldOf a) U (toH1FunctionOn hu hg hw) := by
  intro φ
  have hdata : PDE.DivergenceFormL2DataOn (ellipticFieldOf a) U (toH1FunctionOn hu hg hw) 0 0 :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn (isEllipticFieldOn_ellipticFieldOf hΛ a hU)
      MemLp.zero (fun _ => MemLp.zero)
  refine ⟨hdata.testable φ, ?_⟩
  have htest : IsSpatialTest U φ.toFun := ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  have h := hdiv.2.2 φ.toFun htest
  simp only [zero_mul, integral_zero, neg_zero] at h
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  have e : ∫ x in U, PDE.vecDot (PDE.matVecMul (ellipticFieldOf a x)
      ((toH1FunctionOn hu hg hw).grad x)) (φ.grad x) =
      ∫ x in U, dot ((a x).mulVec (g x)) (gradient φ.toFun x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ellipticFieldOf_ae_eq hΛ a)] with x hx
    change dot ((ellipticFieldOf a x).mulVec (g x)) (gradient φ.toFun x) = _
    rw [hx]
  rw [e, h]
  simp [PDE.vecDot]

end QSH
