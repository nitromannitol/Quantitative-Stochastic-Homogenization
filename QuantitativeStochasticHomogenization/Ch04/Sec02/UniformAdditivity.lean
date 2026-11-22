import QuantitativeStochasticHomogenization.Ch04.Sec02AdditiveStructureOfJ1

/-!
# Theorem 4.6 (i) with constants uniform over the laws

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 4.6 (i): for every `s < 2` there is `C(s, d, Λ) < ∞` such that, for every `R > r ≥ 1`,
`z ∈ ℝᵈ` and `p, q ∈ B₁`,
`|J₁(Φ_{z,R}, p, q) - ∫ Φ_{z,√(R²-r²)}(x) J₁(Φ_{x,r}, p, q) dx| ≤ O_{s/2}(C r^{-d})`.
The constant depends only on `s`, `d` and `Λ`, so it is chosen before the law; this is the
statement `UniformAdditivityJ1`. The spatial average is the integral of an almost surely
integrable function, and the error is almost surely measurable (`AEOsBound`, Remark 5.17),
since `J₁(Φ_{z,r}, p, q)` is identified with its finite-dimensional form (4.12) only almost
surely.
-/

open MeasureTheory

namespace QSH

/-- **Theorem 4.6 (i) with constants uniform over the laws**: for every `s ∈ (0, 2)` there is
`C(s, d, Λ) > 0` such that, for every law satisfying the assumptions, `1 ≤ r < R`, `z` and `p, q`
in the open unit ball, `J₁(Φ_{z,R}, p, q)` is the `Φ_{z,√(R²-r²)}` average of
`x ↦ J₁(Φ_{x,r}, p, q)` up to `O_{s/2}(C r^{-d})`. -/
def UniformAdditivityJ1 : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ s : ℝ, 1 < Λ → 0 < s → s < 2 → ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
    ∀ (z : Vec d) (r R : ℝ), 1 ≤ r → r < R → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      (∀ᵐ a ∂P, Integrable
        (fun x => heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J1Heat a x r p q)) ∧
      AEOsBound P (fun a => |J1Heat a z R p q -
        ∫ x, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) x * J1Heat a x r p q|)
        (s / 2) (C * r ^ (-(d : ℝ)))

end QSH
