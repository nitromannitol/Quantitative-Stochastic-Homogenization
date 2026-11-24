import QuantitativeStochasticHomogenization.Ch02.Sec01.DualEnergy
import QuantitativeStochasticHomogenization.Ch01.Sec04.Lemma113
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientEllipticity
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann

/-!
# The maximizer of `μ*(U, q)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.1, the sentence after (2.1): the supremum (2.1) is attained. The book calls this routine;
it rests on the Poincaré inequality for `H¹(U)`. Here `U` is a bounded open convex nonempty set
and the maximizer is the Neumann maximizer of the coarse-graining library
(`Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory`, field
`neumann_meanZero_maximizer_exists`), whose `H¹` functions and Neumann functional agree with those
of (2.1) (`H1.toH1Function'`, `H1.ofH1Function`, `dualTrialEnergy_eq_symmetricNeumannEnergyValue`).

* `exists_isDualMaximizer`: a maximizer `(u, g)` of (2.1) exists; it lies in `A(U)`
  (`IsDualMaximizer.isAHarmonic`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- An `H¹(U)` function as an `H¹` function of the coarse-graining library. -/
def H1.toH1Function' {U : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H1 U u g) :
    _root_.Homogenization.H1Function U where
  toFun := u
  grad := g
  memL2 := hu.1
  gradMemL2 := fun i => hu.2.1.eval i
  hasWeakGradient := by
    intro i φ hφ hc hs
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      (hu.2.2 i).2.2 φ ⟨hφ, hc, hs⟩

/-- An `H¹` function of the coarse-graining library on a set of finite measure lies in `H¹(U)`. -/
theorem H1.ofH1Function {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (w : _root_.Homogenization.H1Function U) : H1 U w.toFun w.grad := by
  have := isFiniteMeasure_restrict.mpr hU
  have hg : MemLp w.grad 2 (volume.restrict U) := memLp_pi_iff.mpr w.gradMemL2
  exact ⟨w.memL2, hg, hasWeakGradient_of_hasWeakGradientOn' w.hasWeakGradient
    (IntegrableOn.locallyIntegrableOn (w.memL2.integrable one_le_two))
    fun i => IntegrableOn.locallyIntegrableOn ((w.gradMemL2 i).integrable one_le_two)⟩

theorem isBoundedDomain_of_isBounded {U : Set (Vec d)} (hU : Bornology.IsBounded U) :
    _root_.Homogenization.IsBoundedDomain U := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx i => ?_⟩
  have hx' : ‖x‖ ≤ R := by simpa using hR hx
  exact ((norm_le_pi_norm x i).trans hx').trans (le_max_left _ _)

/-- A bounded open convex nonempty set as a domain of the coarse-graining library. -/
def toCGDomain {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : Convex ℝ U) (hne : U.Nonempty) : _root_.Homogenization.Book.Ch02.Domain d :=
  ⟨U, ⟨hUo, isBoundedDomain_of_isBounded hUb, hUc⟩, hne⟩

/-- A coefficient field as a coefficient field of the coarse-graining library on a domain, with the
ellipticity constants `1` and `max Λ 1`. -/
def toCGCoeff (a : CoefficientField d Λ) (D : _root_.Homogenization.Book.Ch02.Domain d) :
    _root_.Homogenization.Book.Ch02.CoeffOn D where
  toCoeffField := a.field
  lam := 1
  Lam := max Λ 1
  lam_pos := one_pos
  lam_le_Lam := le_max_right _ _
  aeStronglyMeasurable := fun i j => by
    refine (a.locally_integrable i j).aestronglyMeasurable.restrict.congr ?_
    filter_upwards [ae_restrict_mem D.measurableSet] with x hx
    rw [_root_.Homogenization.restrictCoeffField_apply_of_mem hx]
  aeElliptic := Eventually.of_forall fun x =>
    coefficientField_isEllipticMatrix a (le_max_right _ _) (le_max_left _ _) x

theorem toCGCoeff_isSymmetric (a : CoefficientField d Λ)
    (D : _root_.Homogenization.Book.Ch02.Domain d) :
    _root_.Homogenization.Book.Ch02.CoeffOn.IsSymmetric (toCGCoeff a D) :=
  Eventually.of_forall fun x => a.symmetric x

/-- **The functional (2.1) is the Neumann functional of the coarse-graining library.** -/
theorem dualTrialEnergy_eq_symmetricNeumannEnergyValue (a : CoefficientField d Λ)
    (D : _root_.Homogenization.Book.Ch02.Domain d) (q : Vec d) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : H1 (D : Set (Vec d)) u g) :
    dualTrialEnergy a D q g =
      _root_.Homogenization.Book.Ch02.symmetricNeumannEnergyValue D (toCGCoeff a D) q
        hu.toH1Function' := by
  unfold _root_.Homogenization.Book.Ch02.symmetricNeumannEnergyValue
    _root_.Homogenization.Book.Ch02.average dualTrialEnergy
  rw [setAverage_eq, smul_eq_mul, measureReal_def]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change -(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) + dot q (g x) =
    dot q (g x) - (1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x))
  ring

/-- **Existence of the maximizer of (2.1)** for a bounded open convex nonempty set `U`. -/
theorem exists_isDualMaximizer (a : CoefficientField d Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) (q : Vec d) :
    ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), IsDualMaximizer a U q u g := by
  set D := toCGDomain hUo hUb hUc hne
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have key : ∀ {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : H1 U u g), dualTrialEnergy a U q g =
      _root_.Homogenization.Book.Ch02.symmetricNeumannEnergyValue D (toCGCoeff a D) q
        hu.toH1Function' := fun hu => dualTrialEnergy_eq_symmetricNeumannEnergyValue a D q hu
  obtain ⟨w, -, hw⟩ := (_root_.Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
    D (toCGCoeff a D) (toCGCoeff_isSymmetric a D)).neumann_meanZero_maximizer_exists q
  have hwU : H1 U w.toFun w.grad := H1.ofH1Function hU w
  refine ⟨w.toFun, w.grad, hwU, le_antisymm (dualTrialEnergy_le_dualEnergy a hU0 hU q hwU) ?_⟩
  refine csSup_le ⟨_, _, _, H1_zero U, rfl⟩ ?_
  rintro E ⟨u, g, hu, rfl⟩
  rw [key hu, key hwU]
  exact hw _

end QSH
