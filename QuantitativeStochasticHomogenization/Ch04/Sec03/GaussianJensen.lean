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

/-- The components of `v` are measurable when `Φ_{y,r} v` is integrable. -/
theorem aestronglyMeasurable_apply_of_heatKernel_smul (y : Vec d) {r : ℝ} (hr : 0 < r)
    {v : Vec d → Vec d} (hv : Integrable fun x => heatKernel y r x • v x) (i : Fin d) :
    AEStronglyMeasurable (fun x => v x i) volume := by
  have hΦpos := heatKernel_pos y hr
  have h1 : AEStronglyMeasurable (fun x => heatKernel y r x * v x i) volume :=
    (Integrable.eval hv i).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun x => (heatKernel y r x)⁻¹) volume :=
    (((continuous_heatKernel_uncurry r).comp (continuous_const.prodMk continuous_id)).inv₀
      fun x => (hΦpos x).ne').aestronglyMeasurable
  refine (h1.mul h2).congr (Filter.Eventually.of_forall fun x => ?_)
  have := (hΦpos x).ne'
  simp only [Pi.mul_apply]
  field_simp

/-- **The averaged gradient and flux are bounded by the averaged energy**:
`|∫ Φ v|² ≤ ∫ Φ v·av` and `|∫ Φ av|² ≤ Λ² ∫ Φ v·av` for a coefficient field `a` with `Λ ≥ 0`. -/
theorem euclideanSq_averages_le_energy (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (y : Vec d)
    {r : ℝ} (hr : 0 < r) {v : Vec d → Vec d} (hv : Integrable fun x => heatKernel y r x • v x)
    (hav : Integrable fun x => heatKernel y r x • (a x).mulVec (v x))
    (hE : Integrable fun x => heatKernel y r x * dot (v x) ((a x).mulVec (v x))) :
    euclideanSq (∫ x, heatKernel y r x • v x) ≤
        ∫ x, heatKernel y r x * dot (v x) ((a x).mulVec (v x)) ∧
      euclideanSq (∫ x, heatKernel y r x • (a x).mulVec (v x)) ≤
        Λ ^ 2 * ∫ x, heatKernel y r x * dot (v x) ((a x).mulVec (v x)) := by
  have hvm : AEStronglyMeasurable v volume :=
    (aemeasurable_pi_iff.mpr fun i =>
      (aestronglyMeasurable_apply_of_heatKernel_smul y hr hv i).aemeasurable).aestronglyMeasurable
  have havm : AEStronglyMeasurable (fun x => (a x).mulVec (v x)) volume :=
    (aemeasurable_pi_iff.mpr fun i =>
      (aestronglyMeasurable_apply_of_heatKernel_smul y hr hav i).aemeasurable).aestronglyMeasurable
  have hsqm : ∀ {w : Vec d → Vec d}, AEStronglyMeasurable w volume →
      AEStronglyMeasurable (fun x => heatKernel y r x * euclideanSq (w x)) volume := by
    intro w hw
    have hc : ∀ i, AEStronglyMeasurable (fun x => w x i) volume := fun i =>
      (continuous_apply i).comp_aestronglyMeasurable hw
    simp only [euclideanSq, dot]
    exact (heatKernel_aestronglyMeasurable y r).mul (Finset.aestronglyMeasurable_fun_sum _
      fun i _ => (hc i).mul (hc i))
  have hptv : ∀ x, euclideanSq (v x) ≤ dot (v x) ((a x).mulVec (v x)) := fun x =>
    (a.elliptic x (v x)).1
  have hpta : ∀ x, euclideanSq ((a x).mulVec (v x)) ≤ Λ ^ 2 * dot (v x) ((a x).mulVec (v x)) := by
    intro x
    have hop := euclideanNorm_mulVec_le_of_abs_dot_le (a.symmetric x) hΛ (fun u => by
      rw [abs_of_nonneg ((euclideanSq_nonneg u).trans (a.elliptic x u).1)]
      exact (a.elliptic x u).2) (v x)
    have h0 := euclideanNorm_nonneg ((a x).mulVec (v x))
    have h1 := pow_le_pow_left₀ h0 hop 2
    rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq] at h1
    nlinarith [hptv x, mul_le_mul_of_nonneg_left (hptv x) (sq_nonneg Λ)]
  have hv2 : Integrable fun x => heatKernel y r x * euclideanSq (v x) :=
    hE.mono' (hsqm hvm) (Filter.Eventually.of_forall fun x => by
      have h0 := heatKernel_nonneg y r x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (euclideanSq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hptv x) h0)
  have hav2 : Integrable fun x => heatKernel y r x * euclideanSq ((a x).mulVec (v x)) :=
    (hE.const_mul (Λ ^ 2)).mono' (hsqm havm) (Filter.Eventually.of_forall fun x => by
      have h0 := heatKernel_nonneg y r x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (euclideanSq_nonneg _))]
      have := mul_le_mul_of_nonneg_left (hpta x) h0
      linarith)
  refine ⟨(euclideanSq_integral_heatKernel_le y hr hv hv2).trans
    (integral_mono hv2 hE fun x => mul_le_mul_of_nonneg_left (hptv x) (heatKernel_nonneg y r x)), ?_⟩
  refine (euclideanSq_integral_heatKernel_le y hr hav hav2).trans ?_
  rw [← integral_const_mul]
  exact integral_mono hav2 (hE.const_mul _) fun x => by
    have h0 := heatKernel_nonneg y r x
    have := mul_le_mul_of_nonneg_left (hpta x) h0
    simp only
    linarith

end QSH
