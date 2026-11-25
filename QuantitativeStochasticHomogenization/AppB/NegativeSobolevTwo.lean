import QuantitativeStochasticHomogenization.AppC.NegativeSobolevPairing

/-!
# The normalized `W^{-2,q}(U)` norm

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Definition B.4 and (0.29) for the order `2`, in the conventions of the order-one norm
`negativeSobolevOneNorm` of Appendix C.

* `sobolevTwoTestNorm p U ψ`: the normalized `W^{2,p}(U)` norm of (B.1),
  `|U|^{-2/d} ‖ψ‖_{L̲^p(U)} + |U|^{-1/d} ∑_i ‖∂_i ψ‖_{L̲^p(U)} + ∑_{i ≤ j} ‖∂_j ∂_i ψ‖_{L̲^p(U)}`; the
  pairs `i ≤ j` enumerate the multi-indices `β = e_i + e_j` of order two;
* `negativeSobolevTwoNorm q U f`: the normalized `W^{-2,q}(U)` norm
  `sup {|⨍_U f ψ| : ψ ∈ C_c^∞(U), ‖ψ‖_{W̲^{2,q'}(U)} ≤ 1}` with `q'` the Hölder conjugate of `q`
  (`ENNReal.conjExponent`, so that `q = 1` has `q' = ∞`), with values in `[0, ∞]`;
* `vectorNegativeSobolevOneNorm p U G`: the sum of the normalized `W^{-1,p}(U)` norms of the
  components of a vector field.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The normalized `W^{2,p}(U)` norm (B.1) of a test function. -/
def sobolevTwoTestNorm (p : ℝ≥0∞) (U : Set (Vec d)) (ψ : Vec d → ℝ) : ℝ :=
  (volume U).toReal ^ (-(2 : ℝ) / d) * (PDE.eLpMeanNormOn U p ψ).toReal +
    (volume U).toReal ^ (-(1 : ℝ) / d) *
      ∑ i : Fin d, (PDE.eLpMeanNormOn U p (coordinateDerivative i ψ)).toReal +
    ∑ i : Fin d, ∑ j ∈ Finset.Ici i,
      (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i ψ))).toReal

/-- **The normalized `W^{-2,q}(U)` norm**, Definition B.4 and (0.29), with `q'` the Hölder
conjugate of `q`. -/
def negativeSobolevTwoNorm (q : ℝ≥0∞) (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧ sobolevTwoTestNorm q.conjExponent U ψ ≤ 1},
    ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|

/-- The sum of the normalized `W^{-1,p}(U)` norms of the components of a vector field. -/
def vectorNegativeSobolevOneNorm (p : ℝ) (U : Set (Vec d)) (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ i : Fin d, negativeSobolevOneNorm p U (fun x => G x i) 0

theorem sobolevTwoTestNorm_nonneg (p : ℝ≥0∞) (U : Set (Vec d)) (ψ : Vec d → ℝ) :
    0 ≤ sobolevTwoTestNorm p U ψ := by
  unfold sobolevTwoTestNorm
  have h1 := ENNReal.toReal_nonneg (a := volume U)
  positivity

/-- A second derivative `‖∂_j ∂_i ψ‖_{L̲^p(U)}` with `i ≤ j` is bounded by the norm (B.1). -/
theorem toReal_eLpMeanNormOn_second_le (p : ℝ≥0∞) (U : Set (Vec d)) (ψ : Vec d → ℝ)
    {i j : Fin d} (hij : i ≤ j) :
    (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i ψ))).toReal ≤
      sobolevTwoTestNorm p U ψ := by
  unfold sobolevTwoTestNorm
  have h1 := ENNReal.toReal_nonneg (a := volume U)
  have hA : 0 ≤ (volume U).toReal ^ (-(2 : ℝ) / d) * (PDE.eLpMeanNormOn U p ψ).toReal +
      (volume U).toReal ^ (-(1 : ℝ) / d) *
        ∑ i : Fin d, (PDE.eLpMeanNormOn U p (coordinateDerivative i ψ)).toReal := by positivity
  have hB : (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i ψ))).toReal ≤
      ∑ i : Fin d, ∑ j ∈ Finset.Ici i,
        (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i ψ))).toReal := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.Ici i,
        (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i ψ))).toReal)
      (fun k _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j =>
        (PDE.eLpMeanNormOn U p (coordinateDerivative j (coordinateDerivative i ψ))).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_Ici.2 hij)
  linarith

/-- The defining bound of the normalized `W^{-2,q}(U)` norm on the unit ball of `W^{2,q'}`. -/
theorem ofReal_abs_setAverage_le_negativeSobolevTwoNorm {q : ℝ≥0∞} {U : Set (Vec d)}
    {f ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (hψ1 : sobolevTwoTestNorm q.conjExponent U ψ ≤ 1) :
    ENNReal.ofReal |⨍ x in U, f x * ψ x ∂volume| ≤ negativeSobolevTwoNorm q U f :=
  le_iSup (fun ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧
      sobolevTwoTestNorm q.conjExponent U ψ ≤ 1} =>
    ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|) ⟨ψ, hψ, hψ1⟩

/-- A bound of the pairings with the unit ball of `W^{2,q'}(U)` bounds the `W^{-2,q}(U)` norm. -/
theorem negativeSobolevTwoNorm_le {q : ℝ≥0∞} {U : Set (Vec d)} {f : Vec d → ℝ} {B : ℝ≥0∞}
    (h : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ → sobolevTwoTestNorm q.conjExponent U ψ ≤ 1 →
      ENNReal.ofReal |⨍ x in U, f x * ψ x ∂volume| ≤ B) :
    negativeSobolevTwoNorm q U f ≤ B :=
  iSup_le fun ψ => h ψ.1 ψ.2.1 ψ.2.2

end QSH
