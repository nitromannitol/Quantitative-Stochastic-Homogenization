import QuantitativeStochasticHomogenization.Ch04.Sec03.EnergyFromRate

/-!
# The bounds on `ā` from the expectations of the averages

Jensen's inequality, first for the heat kernel average and then for the expectation, gives
`|E ∫ Φ_{0,r} G ξ|² ≤ E ∫ Φ_{0,r} G ξ·aG ξ` and `|E ∫ Φ_{0,r} aG ξ|² ≤ Λ E ∫ Φ_{0,r} G ξ·aG ξ`,
the latter by `|av|² ≤ Λ v·av` (`euclideanSq_coefficient_mulVec_le`). Letting `r → ∞` in the
expectations (1) of the averages gives `|ξ|² ≤ ξ·āξ` and `|āξ|² ≤ Λ ξ·āξ`, hence `I ≤ ā ≤ Λ I`
(`homogenizedMatrixBounds_of_expectedAverages`). Consequently (5.58) holds without the
measurability of the Dirichlet energies (`estimate558_of_heatBound_and_rate`).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- Every matrix satisfies `ξ·Mξ ≤ K |ξ|²` for some `K`. -/
theorem exists_dot_mulVec_le (M : Mat d) :
    ∃ K : ℝ, ∀ ξ : Vec d, dot ξ (M.mulVec ξ) ≤ K * euclideanSq ξ := by
  refine ⟨∑ i, ∑ j, |M i j|, fun ξ => ?_⟩
  have hb : ∀ i j, ξ i * (M i j * ξ j) ≤ |M i j| * euclideanSq ξ := by
    intro i j
    have h1 := abs_apply_le_euclideanNorm ξ i
    have h2 := abs_apply_le_euclideanNorm ξ j
    have h3 : |ξ i| * |ξ j| ≤ euclideanSq ξ := by
      rw [← euclideanNorm_sq]
      nlinarith [abs_nonneg (ξ i), abs_nonneg (ξ j), euclideanNorm_nonneg ξ]
    calc ξ i * (M i j * ξ j) ≤ |ξ i * (M i j * ξ j)| := le_abs_self _
      _ = |M i j| * (|ξ i| * |ξ j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ |M i j| * euclideanSq ξ := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  calc dot ξ (M.mulVec ξ) = ∑ i, ∑ j, ξ i * (M i j * ξ j) := by
        simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |M i j| * euclideanSq ξ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = (∑ i, ∑ j, |M i j|) * euclideanSq ξ := by simp only [Finset.sum_mul]

/-- `|a v|² ≤ Λ v·av` for a coefficient field. -/
theorem euclideanSq_coefficient_mulVec_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (x v : Vec d) :
    euclideanSq ((a x).mulVec v) ≤ Λ * dot v ((a x).mulVec v) := by
  have hcs := dot_mulVec_sq_le (a.symmetric x) (fun ξ => (a.elliptic x ξ).1) ((a x).mulVec v) v
  have h2 := (a.elliptic x ((a x).mulVec v)).2
  have hv0 : 0 ≤ dot v ((a x).mulVec v) := (euclideanSq_nonneg v).trans (a.elliptic x v).1
  have he : dot ((a x).mulVec v) ((a x).mulVec v) = euclideanSq ((a x).mulVec v) := rfl
  rw [he] at hcs
  by_cases hs : euclideanSq ((a x).mulVec v) = 0
  · rw [hs]; exact mul_nonneg hΛ hv0
  · have hs' : 0 < euclideanSq ((a x).mulVec v) :=
      lt_of_le_of_ne (euclideanSq_nonneg _) (Ne.symm hs)
    have h3 : euclideanSq ((a x).mulVec v) ^ 2 ≤
        Λ * euclideanSq ((a x).mulVec v) * dot v ((a x).mulVec v) :=
      hcs.trans (mul_le_mul_of_nonneg_right h2 hv0)
    have h4 : euclideanSq ((a x).mulVec v) * euclideanSq ((a x).mulVec v) ≤
        euclideanSq ((a x).mulVec v) * (Λ * dot v ((a x).mulVec v)) := by nlinarith
    exact le_of_mul_le_mul_left h4 hs'

/-- **The averaged flux is bounded by the averaged energy**: `|∫ Φ av|² ≤ Λ ∫ Φ v·av`. -/
theorem euclideanSq_fluxAverage_le_energy (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (y : Vec d)
    {r : ℝ} (hr : 0 < r) {v : Vec d → Vec d}
    (hav : Integrable fun x => heatKernel y r x • (a x).mulVec (v x))
    (hE : Integrable fun x => heatKernel y r x * dot (v x) ((a x).mulVec (v x))) :
    euclideanSq (∫ x, heatKernel y r x • (a x).mulVec (v x)) ≤
      Λ * ∫ x, heatKernel y r x * dot (v x) ((a x).mulVec (v x)) := by
  have havm : AEStronglyMeasurable (fun x => (a x).mulVec (v x)) volume :=
    (aemeasurable_pi_iff.mpr fun i =>
      (aestronglyMeasurable_apply_of_heatKernel_smul y hr hav i).aemeasurable).aestronglyMeasurable
  have hc : ∀ i, AEStronglyMeasurable (fun x => (a x).mulVec (v x) i) volume := fun i =>
    (continuous_apply i).comp_aestronglyMeasurable havm
  have hsqm : AEStronglyMeasurable
      (fun x => heatKernel y r x * euclideanSq ((a x).mulVec (v x))) volume := by
    simp only [euclideanSq, dot]
    exact (heatKernel_aestronglyMeasurable y r).mul (Finset.aestronglyMeasurable_fun_sum _
      fun i _ => (hc i).mul (hc i))
  have hpt : ∀ x, heatKernel y r x * euclideanSq ((a x).mulVec (v x)) ≤
      Λ * (heatKernel y r x * dot (v x) ((a x).mulVec (v x))) := fun x => by
    have h0 := heatKernel_nonneg y r x
    have := mul_le_mul_of_nonneg_left (euclideanSq_coefficient_mulVec_le a hΛ x (v x)) h0
    linarith
  have hav2 : Integrable fun x => heatKernel y r x * euclideanSq ((a x).mulVec (v x)) :=
    (hE.const_mul Λ).mono' hsqm (Eventually.of_forall fun x => by
      have h0 := heatKernel_nonneg y r x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (euclideanSq_nonneg _))]
      exact hpt x)
  refine (euclideanSq_integral_heatKernel_le y hr hav hav2).trans ?_
  rw [← integral_const_mul]
  exact integral_mono hav2 (hE.const_mul Λ) hpt

/-- Jensen's inequality for the expectation of a square. -/
theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Integrable f P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  set m := ∫ ω, f ω ∂P with hm
  have hexp : (fun ω => (f ω - m) ^ 2) = fun ω => f ω ^ 2 - 2 * m * f ω + m ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => f ω ^ 2 - 2 * m * f ω) P := hf2.sub (hf.const_mul _)
  have h0 : 0 ≤ ∫ ω, (f ω - m) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hc : ∫ _ω, m ^ 2 ∂P = m ^ 2 := by simp
  rw [hexp, integral_add i1 (integrable_const _), integral_sub hf2 (hf.const_mul _),
    integral_const_mul, hc, ← hm] at h0
  nlinarith

/-- Jensen's inequality for the expectation of a random vector: `|E V|² ≤ E |V|²`. -/
theorem euclideanSq_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → Vec d} (hV : Integrable V P)
    (hV2 : Integrable (fun ω => euclideanSq (V ω)) P) :
    euclideanSq (∫ ω, V ω ∂P) ≤ ∫ ω, euclideanSq (V ω) ∂P := by
  have hc : ∀ k, Integrable (fun ω => V ω k) P := Integrable.eval hV
  have hc2 : ∀ k, Integrable (fun ω => V ω k ^ 2) P := fun k =>
    hV2.mono' ((hc k).aestronglyMeasurable.pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← euclideanNorm_sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_le_euclideanNorm (V ω) k) 2)
  have hsum : euclideanSq (∫ ω, V ω ∂P) = ∑ k, (∫ ω, V ω k ∂P) ^ 2 := by
    simp only [euclideanSq, dot]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_integral hc k, sq]
  have hsum2 : ∫ ω, euclideanSq (V ω) ∂P = ∑ k, ∫ ω, V ω k ^ 2 ∂P := by
    simp only [euclideanSq, dot]
    rw [integral_finsetSum]
    · simp only [sq]
    · intro k _
      simpa only [sq] using hc2 k
  rw [hsum, hsum2]
  exact Finset.sum_le_sum fun k _ => sq_integral_le_integral_sq (hc k) (hc2 k)

end QSH
