import QuantitativeStochasticHomogenization.Ch10.Sec02.CoarseBridge

/-!
# The double-variable subadditive quantities of Section 10.2

Armstrong–Kuusi–Mourrat, Chapter 10, Section 10.2: the space `S(U)` of (10.19), the quantities
`μ(U, p, q)` of (10.15), `μ*(U, q*, p*)` of (10.16) and `J(U, X, X*)` of (10.20), for a field `a`
of the set `Ω` of (10.2).

The spaces `L²_pot(U)`, `L²_sol(U)`, `L²_pot,0(U)` and `L²_sol,0(U)` of (0.33)–(0.36) are those of
the coarse-graining library (`Homogenization.Book.Ch01.PotentialFieldOn`, `SolenoidalFieldOn`,
`PotentialZeroTraceFieldOn`, `SolenoidalZeroNormalTraceFieldOn`): `L²` fields which are a.e. the
gradient of an `H¹(U)` (resp. `H¹₀(U)`) function, and `L²` fields orthogonal to the gradients of
`H¹₀(U)` (resp. `H¹(U)`). Pairs `(S₁, S₂)` play the role of the elements `S` of
`L²_pot(U) × L²_sol(U)`, and `X = (p, q)`, `X* = (q*, p*)` the elements of `ℝ^{2d}`, so that
`X*·S = q*·S₁ + p*·S₂` as in (10.21). The bilinear form `S'·A S` is `representativePairing`.
-/

open MeasureTheory

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- `L²_pot(U)`, (0.33). -/
abbrev IsL2PotOn (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  _root_.Homogenization.Book.Ch01.PotentialFieldOn U f

/-- `L²_sol(U)`, (0.34). -/
abbrev IsL2SolOn (U : Set (Vec d)) (g : Vec d → Vec d) : Prop :=
  _root_.Homogenization.Book.Ch01.SolenoidalFieldOn U g

/-- `L²_pot,0(U)`, (0.35). -/
abbrev IsL2Pot0On (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  _root_.Homogenization.Book.Ch01.PotentialZeroTraceFieldOn U f

/-- `L²_sol,0(U)`, (0.36). -/
abbrev IsL2Sol0On (U : Set (Vec d)) (g : Vec d → Vec d) : Prop :=
  _root_.Homogenization.Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ)

/-- **The space `S(U)`**, (10.19): pairs `S = (S₁, S₂) ∈ L²_pot(U) × L²_sol(U)` with
`∫_U S'·A S = 0` for every `S' ∈ L²_pot,0(U) × L²_sol,0(U)`. -/
def IsResponseField (U : Set (Vec d)) (S₁ S₂ : Vec d → Vec d) : Prop :=
  IsL2PotOn U S₁ ∧ IsL2SolOn U S₂ ∧
    ∀ T₁ T₂ : Vec d → Vec d, IsL2Pot0On U T₁ → IsL2Sol0On U T₂ →
      ∫ x in U, representativePairing (a x) (T₁ x) (T₂ x) (S₁ x) (S₂ x) = 0

/-- **`μ(U, p, q)`**, (10.15): the infimum of `⨍_U A(∇v, h, ·)` over `∇v ∈ p + L²_pot,0(U)`
(that is, `v ∈ ℓ_p + H¹₀(U)`) and `h ∈ q + L²_sol,0(U)`. -/
noncomputable def doubleMu (U : Set (Vec d)) (p q : Vec d) : ℝ :=
  sInf {E : ℝ | ∃ V h : Vec d → Vec d, IsL2Pot0On U (fun x => V x - p) ∧
    IsL2Sol0On U (fun x => h x - q) ∧ E = ⨍ x in U, linearRepresentative (a x) (V x) (h x)}

/-- **`μ*(U, q*, p*)`**, (10.16): the supremum of `⨍_U (q*·∇u + p*·g - A(∇u, g, ·))` over
`∇u ∈ L²_pot(U)` and `g ∈ L²_sol(U)`. -/
noncomputable def doubleMuStar (U : Set (Vec d)) (qs ps : Vec d) : ℝ :=
  sSup {E : ℝ | ∃ V g : Vec d → Vec d, IsL2PotOn U V ∧ IsL2SolOn U g ∧
    E = ⨍ x in U, (dot qs (V x) + dot ps (g x) - linearRepresentative (a x) (V x) (g x))}

/-- The value `⨍_U (-½ S·AS - X·AS + X*·S)` of an element `S = (S₁, S₂)` in (10.20), for
`X = (p, q)` and `X* = (q*, p*)`. -/
noncomputable def responseValue (U : Set (Vec d)) (p q qs ps : Vec d) (S₁ S₂ : Vec d → Vec d) : ℝ :=
  ⨍ x in U, (-(1 / 2 : ℝ) * representativePairing (a x) (S₁ x) (S₂ x) (S₁ x) (S₂ x) -
    representativePairing (a x) p q (S₁ x) (S₂ x) + (dot qs (S₁ x) + dot ps (S₂ x)))

/-- **`J(U, X, X*)`**, (10.20), for `X = (p, q)` and `X* = (q*, p*)`: the supremum of the response
value over `S ∈ S(U)`. -/
noncomputable def doubleJ (U : Set (Vec d)) (p q qs ps : Vec d) : ℝ :=
  sSup {E : ℝ | ∃ S₁ S₂ : Vec d → Vec d, a.IsResponseField U S₁ S₂ ∧
    E = a.responseValue U p q qs ps S₁ S₂}

/-- A maximizer `S(·, U, X, X*)` of (10.20). -/
def IsResponseMaximizer (U : Set (Vec d)) (p q qs ps : Vec d) (S₁ S₂ : Vec d → Vec d) : Prop :=
  a.IsResponseField U S₁ S₂ ∧ ∀ T₁ T₂ : Vec d → Vec d, a.IsResponseField U T₁ T₂ →
    a.responseValue U p q qs ps T₁ T₂ ≤ a.responseValue U p q qs ps S₁ S₂

end GeneralCoefficientField

end QSH
