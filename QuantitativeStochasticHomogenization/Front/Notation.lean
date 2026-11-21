import Mathlib

/-!
# Notation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, the
chapter "Notation" before Chapter 1.

Defined here: coordinates of `ℝ^d`, the Euclidean scalar product and norm, Euclidean balls,
the lattice `ℤ^d`, the unit cell, triadic cubes (0.20) and cubes `□_R(z)` (0.27), weak
derivatives, normalized `L²` norms, and the normalized Sobolev norms `H^m` (0.26) and `H^{-m}`
(0.29).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QSH

/-! ## Notation of Chapter 0 -/

/-- Points of `ℝ^d` in coordinates. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The Euclidean scalar product. -/
def dot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean norm. -/
def euclideanSq {d : ℕ} (x : Vec d) : ℝ := dot x x

/-- The Euclidean norm `|x|`. -/
def euclideanNorm {d : ℕ} (x : Vec d) : ℝ := Real.sqrt (euclideanSq x)

/-- The coordinate unit vector `e_i`. -/
def unitVector {d : ℕ} (i : Fin d) : Vec d := Pi.single i 1

/-- The open Euclidean ball `B_r(x)`. -/
def ball {d : ℕ} (x : Vec d) (r : ℝ) : Set (Vec d) := {y | euclideanNorm (y - x) < r}

/-- The open Euclidean ball `B_R` centered at the origin. -/
def originBall (d : ℕ) (R : ℝ) : Set (Vec d) := {x | euclideanNorm x < R}

/-- Lattice points `ℤ^d`. -/
abbrev LatticeIndex (d : ℕ) := Fin d → ℤ

/-- The lattice point `z ∈ ℤ^d` as a point of `ℝ^d`. -/
def latticeShift {d : ℕ} (z : LatticeIndex d) : Vec d := fun i => (z i : ℝ)

/-- The centered unit cube `□_0 = [-1/2, 1/2)^d`. -/
def unitCell (d : ℕ) : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Ico (-1 / 2) (1 / 2))

/-- The triadic cube `□_n = (-3^n/2, 3^n/2)^d`, (0.20). -/
def triadicCube (d n : ℕ) : Set (Vec d) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-((3 : ℝ) ^ n) / 2) (((3 : ℝ) ^ n) / 2))

/-- The open cube `□_R(z)` of side `R` centered at `z`, (0.27). -/
def cube {d : ℕ} (z : Vec d) (R : ℝ) : Set (Vec d) := {x | ∀ i, |x i - z i| < R / 2}

/-! ## Weak derivatives -/

/-- The coordinate derivative `∂_i f`. -/
def coordinateDerivative {d : ℕ} (i : Fin d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  fderiv ℝ f x (unitVector i)

/-- The gradient `∇f`. -/
def gradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Vec d := fun i => coordinateDerivative i f x

/-- A smooth compactly supported test function in `U`. -/
def IsSpatialTest {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- A locally integrable weak coordinate derivative in `U`. -/
def HasWeakPartialDerivative {d : ℕ} (U : Set (Vec d)) (i : Fin d) (f g : Vec d → ℝ) : Prop :=
  LocallyIntegrableOn f U volume ∧ LocallyIntegrableOn g U volume ∧
  ∀ φ : Vec d → ℝ, IsSpatialTest U φ →
    (∫ x in U, f x * coordinateDerivative i φ x) = -(∫ x in U, g x * φ x)

/-- `g` is the weak gradient of `f` in `U`. -/
def HasWeakGradient {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivative U i f (fun x => g x i)

/-- `div F = h` weakly in `U`. -/
def HasWeakDivergence {d : ℕ} (U : Set (Vec d)) (F : Vec d → Vec d) (h : Vec d → ℝ) : Prop :=
  (∀ i : Fin d, LocallyIntegrableOn (fun x => F x i) U volume) ∧
  LocallyIntegrableOn h U volume ∧
  ∀ φ : Vec d → ℝ, IsSpatialTest U φ →
    (∫ x in U, dot (F x) (gradient φ x)) = -(∫ x in U, h x * φ x)

/-- The volume-normalized `L²(U)` norm of a scalar function. -/
def scalarRms {X : Type*} [MeasurableSpace X] (ν : Measure X) (U : Set X) (f : X → ℝ) : ℝ :=
  Real.sqrt (⨍ x in U, (f x) ^ 2 ∂ν)

/-- The volume-normalized `L²(U)` norm of a vector field. -/
def vectorRms {d : ℕ} {X : Type*} [MeasurableSpace X] (ν : Measure X) (U : Set X)
    (G : X → Vec d) : ℝ :=
  Real.sqrt (⨍ x in U, euclideanSq (G x) ∂ν)

/-! ## Negative Sobolev norms, (0.26), (0.29), Appendix B -/

/-- The iterated coordinate derivative `∂^β ψ`. -/
def multiIndexDerivative {d m : ℕ} (β : Fin d → Fin (m + 1)) (ψ : Vec d → ℝ) : Vec d → ℝ :=
  ((List.finRange d).flatMap fun j => List.replicate (β j).val j).foldr coordinateDerivative ψ

/-- The normalized `H^m(U)` norm, (0.26) and (B.1). -/
def integerSobolevTestNorm {d : ℕ} (m : ℕ) (U : Set (Vec d)) (ψ : Vec d → ℝ) : ℝ :=
  ∑ β : Fin d → Fin (m + 1),
    if (∑ j : Fin d, (β j).val) ≤ m then
      (volume U).toReal ^ ((((∑ j : Fin d, (β j).val : ℕ) : ℝ) - m) / d) *
        scalarRms volume U (multiIndexDerivative β ψ)
    else 0

/-- The normalized `H^{-m}(U)` norm, (0.29). -/
def negativeIntegerSobolevNorm {d : ℕ} (m : ℕ) (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧ integerSobolevTestNorm m U ψ ≤ 1},
    ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|

/-- The sum of the `H^{-m}(U)` norms of the components of a vector field. -/
def vectorNegativeIntegerSobolevNorm {d : ℕ} (m : ℕ) (U : Set (Vec d)) (F : Vec d → Vec d) :
    ℝ≥0∞ :=
  ∑ j : Fin d, negativeIntegerSobolevNorm m U (fun x => F x j)

end QSH
