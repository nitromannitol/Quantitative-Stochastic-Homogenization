import QuantitativeStochasticHomogenization.Ch04.Sec01.BaseExponent

/-!
# The bounds (3.101)–(3.103) from the coordinate directions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Proposition 3.21: the corrected field `G ξ = ∑ ξᵢ Gᵢ` is linear in `ξ`, so the bounds
(3.101)–(3.103) at the mask `Φ_{x₀,r}` follow from the Gaussian averages of the components of the
`d` coordinate fields `Gᵢ`, of their fluxes `a Gᵢ`, and of the energies `Gₗ · a Gᵢ`
(`gaussianAverageBounds_of_basis`), with the error multiplied by `d²`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem sum_abs_le_mul_euclideanNorm (ξ : Vec d) : ∑ i, |ξ i| ≤ d * euclideanNorm ξ := by
  calc ∑ i, |ξ i| ≤ ∑ _i : Fin d, euclideanNorm ξ :=
        Finset.sum_le_sum fun i _ => abs_apply_le_euclideanNorm ξ i
    _ = d * euclideanNorm ξ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sqrt_natCast_le (d : ℕ) : Real.sqrt d ≤ d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast h
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith

theorem euclideanNorm_le_of_abs_le {v : Vec d} {B : ℝ} (hB : 0 ≤ B) (h : ∀ k, |v k| ≤ B) :
    euclideanNorm v ≤ d * B := by
  have h1 : euclideanNorm v ≤ Real.sqrt (d * B ^ 2) := by
    unfold euclideanNorm euclideanSq dot
    refine Real.sqrt_le_sqrt ?_
    calc ∑ k, v k * v k ≤ ∑ _k : Fin d, B ^ 2 := Finset.sum_le_sum fun k _ => by
          have := h k
          nlinarith [abs_nonneg (v k), sq_abs (v k)]
      _ = d * B ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hB] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (sqrt_natCast_le d) hB)

theorem dot_sum_smul_left (ξ : Vec d) (G : Fin d → Vec d) (w : Vec d) :
    dot (∑ l, ξ l • G l) w = ∑ l, ξ l * dot (G l) w := by
  unfold dot
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem dot_sum_smul_right (v : Vec d) (ξ : Vec d) (q : Fin d → Vec d) :
    dot v (∑ i, ξ i • q i) = ∑ i, ξ i * dot v (q i) := by
  unfold dot
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The bounds on the coordinate fields** `Gᵢ` at the mask `Φ_{x₀,r}`: their averages, the
averages of their fluxes and of their mutual energies are within `ε` of `eᵢ`, `A eᵢ` and
`eₗ · A eᵢ`. -/
def GaussianBasisBounds (a : CoefficientField d Λ) (A : Mat d) (G : Fin d → Vec d → Vec d)
    (x₀ : Vec d) (r ε : ℝ) : Prop :=
  (∀ i k, Integrable fun x => heatKernel x₀ r x * G i x k) ∧
  (∀ i k, Integrable fun x => heatKernel x₀ r x * ((a x).mulVec (G i x)) k) ∧
  (∀ l i, Integrable fun x => heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x))) ∧
  (∀ i k, |(∫ x, heatKernel x₀ r x * G i x k) - unitVector i k| ≤ ε) ∧
  (∀ i k, |(∫ x, heatKernel x₀ r x * ((a x).mulVec (G i x)) k) - A k i| ≤ ε) ∧
  (∀ l i, |(∫ x, heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x))) - A l i| ≤ ε)

theorem GaussianBasisBounds.mono {a : CoefficientField d Λ} {A : Mat d}
    {G : Fin d → Vec d → Vec d} {x₀ : Vec d} {r ε ε' : ℝ} (h : GaussianBasisBounds a A G x₀ r ε)
    (hε : ε ≤ ε') : GaussianBasisBounds a A G x₀ r ε' :=
  ⟨h.1, h.2.1, h.2.2.1, fun i k => (h.2.2.2.1 i k).trans hε,
    fun i k => (h.2.2.2.2.1 i k).trans hε, fun l i => (h.2.2.2.2.2 l i).trans hε⟩

/-- **The bounds (3.101)–(3.103) from the coordinate fields.** -/
theorem gaussianAverageBounds_of_basis {a : CoefficientField d Λ} {A : Mat d}
    {G : Fin d → Vec d → Vec d} {x₀ : Vec d} {r ε : ℝ} (hε : 0 ≤ ε)
    (hB : GaussianBasisBounds a A G x₀ r ε) :
    GaussianAverageBounds a A (fun ξ x => ∑ i, ξ i • G i x) x₀ r ((d : ℝ) ^ 2 * ε) := by
  obtain ⟨hGi, hqi, hEi, hG, hq, hE⟩ := hB
  intro ξ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hξ : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _
  have hsum := sum_abs_le_mul_euclideanNorm ξ
  -- the components
  have hGk : ∀ k, (fun x => heatKernel x₀ r x * (∑ i, ξ i • G i x) k) =
      fun x => ∑ i, ξ i * (heatKernel x₀ r x * G i x k) := by
    intro k
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmv : ∀ x, (a x).mulVec (∑ i, ξ i • G i x) = ∑ i, ξ i • (a x).mulVec (G i x) := by
    intro x
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_smul _ _ _
  have hqk : ∀ k, (fun x => heatKernel x₀ r x * ((a x).mulVec (∑ i, ξ i • G i x)) k) =
      fun x => ∑ i, ξ i * (heatKernel x₀ r x * ((a x).mulVec (G i x)) k) := by
    intro k
    funext x
    rw [hmv x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hEk : (fun x => heatKernel x₀ r x *
      dot (∑ i, ξ i • G i x) ((a x).mulVec (∑ i, ξ i • G i x))) =
      fun x => ∑ l, ∑ i, ξ l * ξ i *
        (heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x))) := by
    funext x
    rw [hmv x, dot_sum_smul_left]
    simp_rw [dot_sum_smul_right]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hIG : ∀ k, Integrable fun x => heatKernel x₀ r x * (∑ i, ξ i • G i x) k := by
    intro k
    rw [hGk k]
    exact integrable_finsetSum _ fun i _ => (hGi i k).const_mul _
  have hIq : ∀ k, Integrable fun x => heatKernel x₀ r x * ((a x).mulVec (∑ i, ξ i • G i x)) k := by
    intro k
    rw [hqk k]
    exact integrable_finsetSum _ fun i _ => (hqi i k).const_mul _
  have hIE : Integrable fun x => heatKernel x₀ r x *
      dot (∑ i, ξ i • G i x) ((a x).mulVec (∑ i, ξ i • G i x)) := by
    rw [hEk]
    exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ =>
      (hEi l i).const_mul _
  have hIG' : ∀ k, Integrable fun x => (heatKernel x₀ r x • ∑ i, ξ i • G i x) k := hIG
  have hIq' : ∀ k, Integrable fun x =>
      (heatKernel x₀ r x • (a x).mulVec (∑ i, ξ i • G i x)) k := hIq
  refine ⟨integrable_pi_iff.mpr hIG', integrable_pi_iff.mpr hIq', hIE, ?_, ?_, ?_⟩
  · -- (3.101)
    refine euclideanNorm_le_of_abs_le (B := d * euclideanNorm ξ * ε) (by positivity)
      (fun k => ?_) |>.trans (le_of_eq (by ring))
    rw [Pi.sub_apply, eval_integral hIG' k]
    have h1 : ∫ x, (heatKernel x₀ r x • ∑ i, ξ i • G i x) k =
        ∑ i, ξ i * ∫ x, heatKernel x₀ r x * G i x k := by
      show ∫ x, heatKernel x₀ r x * (∑ i, ξ i • G i x) k = _
      rw [hGk k, integral_finsetSum _ fun i _ => (hGi i k).const_mul _]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    have h2 : ξ k = ∑ i, ξ i * unitVector i k := by
      rw [Finset.sum_eq_single k]
      · simp [unitVector]
      · intro b _ hb
        simp [unitVector, Ne.symm hb]
      · simp
    rw [h1, h2, ← Finset.sum_sub_distrib]
    calc |∑ i, ((ξ i * ∫ x, heatKernel x₀ r x * G i x k) - ξ i * unitVector i k)|
        ≤ ∑ i, |ξ i| * ε := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (hG i k) (abs_nonneg _)
      _ = (∑ i, |ξ i|) * ε := by rw [Finset.sum_mul]
      _ ≤ d * euclideanNorm ξ * ε := mul_le_mul_of_nonneg_right hsum hε
  · -- (3.102)
    refine euclideanNorm_le_of_abs_le (B := d * euclideanNorm ξ * ε) (by positivity)
      (fun k => ?_) |>.trans (le_of_eq (by ring))
    rw [Pi.sub_apply, eval_integral hIq' k]
    have h1 : ∫ x, (heatKernel x₀ r x • (a x).mulVec (∑ i, ξ i • G i x)) k =
        ∑ i, ξ i * ∫ x, heatKernel x₀ r x * ((a x).mulVec (G i x)) k := by
      show ∫ x, heatKernel x₀ r x * ((a x).mulVec (∑ i, ξ i • G i x)) k = _
      rw [hqk k, integral_finsetSum _ fun i _ => (hqi i k).const_mul _]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    have h2 : A.mulVec ξ k = ∑ i, ξ i * A k i := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1, h2, ← Finset.sum_sub_distrib]
    calc |∑ i, ((ξ i * ∫ x, heatKernel x₀ r x * ((a x).mulVec (G i x)) k) - ξ i * A k i)|
        ≤ ∑ i, |ξ i| * ε := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (hq i k) (abs_nonneg _)
      _ = (∑ i, |ξ i|) * ε := by rw [Finset.sum_mul]
      _ ≤ d * euclideanNorm ξ * ε := mul_le_mul_of_nonneg_right hsum hε
  · -- (3.103)
    have h1 : ∫ x, heatKernel x₀ r x * dot (∑ i, ξ i • G i x) ((a x).mulVec (∑ i, ξ i • G i x)) =
        ∑ l, ∑ i, ξ l * ξ i * ∫ x, heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x)) := by
      rw [hEk, integral_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ =>
        (hEi l i).const_mul _]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_finsetSum _ fun i _ => (hEi l i).const_mul _]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    have h2 : dot ξ (A.mulVec ξ) = ∑ l, ∑ i, ξ l * ξ i * A l i := by
      simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, h2]
    have h3 : (∑ l, ∑ i, ξ l * ξ i * ∫ x, heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x))) -
        ∑ l, ∑ i, ξ l * ξ i * A l i = ∑ l, ∑ i, ξ l * ξ i *
          ((∫ x, heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x))) - A l i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h3]
    calc |∑ l, ∑ i, ξ l * ξ i * ((∫ x, heatKernel x₀ r x * dot (G l x) ((a x).mulVec (G i x))) -
          A l i)|
        ≤ ∑ l, ∑ i, |ξ l| * |ξ i| * ε := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hE l i) (by positivity)
      _ = (∑ i, |ξ i|) ^ 2 * ε := by
          rw [sq, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ (d * euclideanNorm ξ) ^ 2 * ε :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ =>
            abs_nonneg _) hsum 2) hε
      _ ≤ 2 * ((d : ℝ) ^ 2 * ε) * euclideanNorm ξ ^ 2 := by
          have : 0 ≤ (d : ℝ) ^ 2 * ε * euclideanNorm ξ ^ 2 := by positivity
          nlinarith

end QSH
