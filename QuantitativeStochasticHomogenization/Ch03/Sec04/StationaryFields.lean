import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors

/-!
# Section 3.4: stationary random fields and stationary random potential fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4, Definition 3.14 (`IsStationaryRandomField`) and Definition 3.15
(`IsStationaryPotentialField`), on the probability space of coefficient fields with the
translations `T_z a = a(z + ·)` (`translate`). The gradient of a first-order corrector is a
stationary random potential field (`Corrector.isStationaryPotentialField_grad`), as stated in
Lemma 3.16.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- **Definition 3.14 (Stationary random field)**: for a measurable space `S`, an `S`-valued
`ℤ^d`-stationary random field is a jointly measurable map `F`, written `F a x` for `F(x, a)`,
such that, for every `z ∈ ℤ^d`, `F(x + z, a) = F(x, T_z a)` for almost every `x ∈ ℝ^d` and
`P`-almost surely in `a`. -/
def IsStationaryRandomField {S : Type*} [MeasurableSpace S] (P : Measure (CoefficientField d Λ))
    (F : CoefficientField d Λ → Vec d → S) : Prop :=
  Measurable (fun p : CoefficientField d Λ × Vec d => F p.1 p.2) ∧
    ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F a (x + latticeShift z) = F (translate (latticeShift z) a) x

/-- **Definition 3.15 (Stationary random potential field)**: an `ℝ^d`-valued stationary random
field `F` such that, `P`-almost surely, `F(·, a)` is the gradient of a function in `H¹_loc(ℝ^d)`:
there is `u` with weak gradient `F(·, a)` on `ℝ^d`, `u` and `F(·, a)` being square integrable on
every ball. These fields form the collection `L²_pot`. -/
def IsStationaryPotentialField (P : Measure (CoefficientField d Λ))
    (F : CoefficientField d Λ → Vec d → Vec d) : Prop :=
  IsStationaryRandomField P F ∧ ∀ᵐ a ∂P, ∃ u : Vec d → ℝ, HasWeakGradient Set.univ u (F a) ∧
    ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
      MemLp (F a) 2 (volume.restrict (ball 0 R))

/-- **The gradient of a first-order corrector is a stationary random potential field**, the
membership `∇φ_e ∈ L²_pot` of Lemma 3.16. -/
theorem Corrector.isStationaryPotentialField_grad {P : Measure (CoefficientField d Λ)}
    {e : Vec d} (φ : Corrector P e) : IsStationaryPotentialField P φ.grad := by
  refine ⟨⟨φ.measurable_grad, φ.stationary⟩, ?_⟩
  filter_upwards [φ.weak_gradient, φ.locally_square_integrable] with a h1 h2
  exact ⟨φ.potential a, h1, h2⟩

end QSH
