import QuantitativeStochasticHomogenization.Ch04.Sec03.ComponentFluctuation

/-!
# Jensen's inequality for heat kernel averages

`|∫ Φ_{y,r} v|² ≤ ∫ Φ_{y,r} |v|²` for a vector field `v` with `Φ_{y,r} v` and `Φ_{y,r} |v|²`
integrable (`euclideanSq_integral_heatKernel_le`). Consequently the averaged gradient and flux of
the corrected fields are bounded by their averaged energy (`euclideanSq_gradientAverage_le`,
`euclideanSq_fluxAverage_le`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem heatKernel_aestronglyMeasurable (y : Vec d) (r : ℝ) :
    AEStronglyMeasurable (fun x => heatKernel y r x) volume :=
  ((continuous_heatKernel_uncurry r).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/-- **Jensen's inequality for a scalar heat kernel average**: `(∫ Φ f)² ≤ ∫ Φ f²`. -/
theorem sq_integral_heatKernel_le (y : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Integrable fun x => heatKernel y r x * f x)
    (hf2 : Integrable fun x => heatKernel y r x * f x ^ 2) :
    (∫ x, heatKernel y r x * f x) ^ 2 ≤ ∫ x, heatKernel y r x * f x ^ 2 := by
  set m := ∫ x, heatKernel y r x * f x with hm
  have hΦ := integrable_heatKernel y hr
  have hmass := integral_heatKernel y hr
  have hsq : Integrable fun x => heatKernel y r x * (f x - m) ^ 2 := by
    have : (fun x => heatKernel y r x * (f x - m) ^ 2) = fun x =>
        heatKernel y r x * f x ^ 2 - 2 * m * (heatKernel y r x * f x) + m ^ 2 * heatKernel y r x := by
      funext x; ring
    rw [this]
    exact (hf2.sub (hf.const_mul _)).add (hΦ.const_mul _)
  have h0 : 0 ≤ ∫ x, heatKernel y r x * (f x - m) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (heatKernel_nonneg _ _ _) (sq_nonneg _)
  have hexp : ∫ x, heatKernel y r x * (f x - m) ^ 2 = (∫ x, heatKernel y r x * f x ^ 2) - m ^ 2 := by
    have : (fun x => heatKernel y r x * (f x - m) ^ 2) = fun x =>
        heatKernel y r x * f x ^ 2 - 2 * m * (heatKernel y r x * f x) + m ^ 2 * heatKernel y r x := by
      funext x; ring
    have i1 : Integrable fun x => heatKernel y r x * f x ^ 2 - 2 * m * (heatKernel y r x * f x) :=
      hf2.sub (hf.const_mul _)
    rw [this, integral_add i1 (hΦ.const_mul _), integral_sub hf2 (hf.const_mul _),
      integral_const_mul, integral_const_mul, hmass, ← hm]
    ring
  linarith

/-- **Jensen's inequality for a vector heat kernel average**: `|∫ Φ v|² ≤ ∫ Φ |v|²`. -/
theorem euclideanSq_integral_heatKernel_le (y : Vec d) {r : ℝ} (hr : 0 < r) {v : Vec d → Vec d}
    (hv : Integrable fun x => heatKernel y r x • v x)
    (hv2 : Integrable fun x => heatKernel y r x * euclideanSq (v x)) :
    euclideanSq (∫ x, heatKernel y r x • v x) ≤ ∫ x, heatKernel y r x * euclideanSq (v x) := by
  have hΦpos := heatKernel_pos y hr
  -- measurability of the components
  have hvm : ∀ i, AEStronglyMeasurable (fun x => v x i) volume := by
    intro i
    have h1 : AEStronglyMeasurable (fun x => heatKernel y r x * v x i) volume :=
      (Integrable.eval hv i).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x => (heatKernel y r x)⁻¹) volume :=
      (((continuous_heatKernel_uncurry r).comp (continuous_const.prodMk continuous_id)).inv₀
        fun x => (hΦpos x).ne').aestronglyMeasurable
    refine (h1.mul h2).congr (Filter.Eventually.of_forall fun x => ?_)
    have := (hΦpos x).ne'
    simp only [Pi.mul_apply]
    field_simp
  have hcomp : ∀ i, Integrable fun x => heatKernel y r x * v x i ^ 2 := by
    intro i
    refine hv2.mono' ((heatKernel_aestronglyMeasurable y r).mul ((hvm i).pow 2))
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 := heatKernel_nonneg y r x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ h0
    simp only [euclideanSq, dot]
    rw [sq]
    exact Finset.single_le_sum (f := fun l => v x l * v x l) (fun l _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hcompi : ∀ i, Integrable fun x => heatKernel y r x * v x i := fun i =>
    Integrable.eval hv i
  calc euclideanSq (∫ x, heatKernel y r x • v x)
      = ∑ i, (∫ x, heatKernel y r x * v x i) ^ 2 := by
        simp only [euclideanSq, dot, ← sq]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eval_integral (Integrable.eval hv)]
        rfl
    _ ≤ ∑ i, ∫ x, heatKernel y r x * v x i ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_integral_heatKernel_le y hr (hcompi i) (hcomp i)
    _ = ∫ x, heatKernel y r x * euclideanSq (v x) := by
        rw [← integral_finsetSum _ fun i _ => hcomp i]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [euclideanSq, dot, ← sq, Finset.mul_sum]

end QSH
