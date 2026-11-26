import QuantitativeStochasticHomogenization.Front.Assumptions
import QuantitativeStochasticHomogenization.AppC.NegativeSobolevPairing
import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Parabolic cylinders, weak solutions and the norm of `L²(I; H⁻¹(U))`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 8.1: the cylinders `Q_r = I_r × B_r` with `I_r = (-r², 0]`, weak solutions of the
equation (8.6) `∂ₜu - ∇·(a∇u) = u*`, and the volume-normalized norm of `L²(I; H⁻¹(U))`.

Space-time points are written `(x, t) ∈ ℝ^d × ℝ`, space first, as in the parabolic part of the
elliptic regularity library. Its energy space `PDE.ParH1Function U I` is used for
`H¹_par(I × U)` of (8.2): a function of `L²(I; H¹(U))` given by its representative which is weakly
continuous in time (every function of `H¹_par(I × U)` has one, and the time derivative of a weak
solution is in `L²(I; H⁻¹(U))` by the equation). Test functions are the `C¹` functions with compact
support in `U × (I₋, I₊)`.

A right-hand side `u* ∈ L²(I; H⁻¹(U))` is written `u* = ∇·F` with `F ∈ L²(U × I; ℝ^d)`: on a
bounded `U` every element of `H⁻¹(U)` has this form (Riesz representation in `H¹₀(U)`). Its norm at
time `t` is the normalized `H⁻¹(U)` norm `negativeSobolevOneNorm 2 U 0 (F(·, t))` of (0.29).
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **The parabolic cylinder** `Q_r = I_r × B_r` with `I_r = (-r², 0]`, written `B_r × I_r`. -/
def parabolicCylinder (d : ℕ) (r : ℝ) : Set (Vec d × ℝ) :=
  ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) 0

/-- `∂ₜu = ∇·G` weakly in `I × U`: `∫ (-u ∂ₜφ + G · ∇φ) = 0` for every `C¹` test function `φ`
with compact support in `U × (I₋, I₊)`. -/
def IsParabolicFluxSolution (U : Set (Vec d)) (I : Set ℝ) (u : PDE.ParH1Function U I)
    (G : Vec d × ℝ → Vec d) : Prop :=
  ∀ φ : PDE.ParTestFunction U (interior I),
    IntegrableOn (fun z => -(u.toFun z * PDE.parTimeDeriv φ.toFun z) +
      dot (G z) (PDE.parSpaceGrad φ.toFun z)) (U ×ˢ I) ∧
    ∫ z in U ×ˢ I, (-(u.toFun z * PDE.parTimeDeriv φ.toFun z) +
      dot (G z) (PDE.parSpaceGrad φ.toFun z)) = 0

/-- **Weak solutions of (8.6)** `∂ₜu - ∇·(a∇u) = ∇·F` in `I × U`: the flux `a∇u + F` satisfies
`∂ₜu = ∇·(a∇u + F)` weakly. -/
def IsParabolicSolution {Λ : ℝ} (a : CoefficientField d Λ) (U : Set (Vec d)) (I : Set ℝ)
    (u : PDE.ParH1Function U I) (F : Vec d × ℝ → Vec d) : Prop :=
  IsParabolicFluxSolution U I u (fun z => (a z.1).mulVec (u.grad z) + F z)

/-- **The normalized norm of `L²(I; H⁻¹(U))`** of `u* = ∇·F`:
`‖u*‖_{L̲²(I; H̲⁻¹(U))} = (⨍_I ‖u*(t, ·)‖²_{H̲⁻¹(U)} dt)^{1/2}`, with values in `[0, ∞]`. -/
def timeNegativeSobolevNorm (I : Set ℝ) (U : Set (Vec d)) (F : Vec d × ℝ → Vec d) : ℝ≥0∞ :=
  ((volume I)⁻¹ * ∫⁻ t in I, negativeSobolevOneNorm 2 U (fun _ => 0) (fun x => F (x, t)) ^ 2) ^
    (1 / 2 : ℝ)

end QSH
