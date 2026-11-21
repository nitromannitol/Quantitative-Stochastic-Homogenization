import QuantitativeStochasticHomogenization.Ch03.Sec03HigherOrderRegularityAndLiouville
import QuantitativeStochasticHomogenization.Ch04.Opening

/-!
# Section 4.1: The Energy Quantity J₁ and Its Basic Properties

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 4 (Quantitative Description of First-Order Correctors), Section 4.1. Numbered results of
this section: Proposition 4.3; Lemma 4.4; Definitions 4.2, 4.5.

Defined here: `J₁(Ψ, p, q)` of (4.8) and its value at the masks `Φ_{z,r}`.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **`J₁(Ψ, p, q)`**, (4.8), a supremum over `A₁`. -/
def J1 {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d) : ℝ :=
  sSup {e : ℝ | ∃ w : HarmonicA1 a,
    e = ∫ x, mask x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))}

/-- `J₁(Φ_{z,r}, p, q)`. -/
def J1Heat {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  J1 a (heatKernel z r) p q

end QSH
