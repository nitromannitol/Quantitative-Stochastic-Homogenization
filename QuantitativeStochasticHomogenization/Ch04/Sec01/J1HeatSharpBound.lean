import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatBounds
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1Quadratic
import QuantitativeStochasticHomogenization.Ch03.Sec04.EuclideanSqNonneg

/-!
# The sharp deterministic upper bound for J₁

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
(4.8) in the form `J₁(Φ_{z,r}, p, q) ≤ ½ (√Λ |p| + |q|)²`. For every gradient `g`, with
`N² = g · a g`, Cauchy–Schwarz for the form of `a(x)` and `|g|² ≤ g · a g` give
`-½ g · a g - p · a g + q · g ≤ -½ N² + (√Λ |p| + |q|) N ≤ ½ (√Λ |p| + |q|)²`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- Cauchy–Schwarz for the Euclidean dot product. -/
theorem dot_sq_le_euclideanSq_mul (u v : Vec d) :
    dot u v ^ 2 ≤ euclideanSq u * euclideanSq v := by
  have hpos : ∀ t : ℝ, 0 ≤ euclideanSq v * (t * t) + 2 * dot u v * t + euclideanSq u := by
    intro t
    have h := euclideanSq_nonneg (u + t • v)
    have hexp : euclideanSq (u + t • v) =
        euclideanSq v * (t * t) + 2 * dot u v * t + euclideanSq u := by
      change dotProduct (u + t • v) (u + t • v) =
        dotProduct v v * (t * t) + 2 * dotProduct u v * t + dotProduct u u
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm v u]
      ring
    linarith
  have h := discrim_le_zero hpos
  unfold discrim at h
  nlinarith [h]

/-- Cauchy–Schwarz for the bilinear form of a coefficient field. -/
theorem dot_mulVec_sq_le {Λ : ℝ} (a : CoefficientField d Λ) (x u v : Vec d) :
    dot u ((a x).mulVec v) ^ 2 ≤ dot u ((a x).mulVec u) * dot v ((a x).mulVec v) := by
  have hpos : ∀ t : ℝ, 0 ≤ dot v ((a x).mulVec v) * (t * t) +
      2 * dot u ((a x).mulVec v) * t + dot u ((a x).mulVec u) := by
    intro t
    have h := (euclideanSq_nonneg (u + t • v)).trans (a.elliptic x (u + t • v)).1
    have hsym := dot_mulVec_comm_of_coefficientField a x v u
    have hexp : dot (u + t • v) ((a x).mulVec (u + t • v)) = dot u ((a x).mulVec u) +
        t * dot u ((a x).mulVec v) + t * dot v ((a x).mulVec u) +
          t * t * dot v ((a x).mulVec v) := by
      change dotProduct _ _ = dotProduct _ _ + t * dotProduct _ _ + t * dotProduct _ _ +
        t * t * dotProduct _ _
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [hexp, hsym] at h
    linarith
  have h := discrim_le_zero hpos
  unfold discrim at h
  nlinarith [h]

/-- The pointwise bound on the integrand of `J₁`. -/
theorem J1_integrand_le_half_sq {Λ : ℝ} (a : CoefficientField d Λ) (x p q g : Vec d) :
    -(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g) + dot q g ≤
      1 / 2 * (Real.sqrt Λ * euclideanNorm p + euclideanNorm q) ^ 2 := by
  have hE : 0 ≤ dot g ((a x).mulVec g) := (euclideanSq_nonneg g).trans (a.elliptic x g).1
  set N := Real.sqrt (dot g ((a x).mulVec g)) with hNdef
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hNsq : N ^ 2 = dot g ((a x).mulVec g) := Real.sq_sqrt hE
  have h1 : |dot p ((a x).mulVec g)| ≤ Real.sqrt Λ * euclideanNorm p * N := by
    have hpp0 : 0 ≤ dot p ((a x).mulVec p) := (euclideanSq_nonneg p).trans (a.elliptic x p).1
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (dot p ((a x).mulVec g) ^ 2)
        ≤ Real.sqrt (dot p ((a x).mulVec p) * dot g ((a x).mulVec g)) :=
          Real.sqrt_le_sqrt (dot_mulVec_sq_le a x p g)
      _ = Real.sqrt (dot p ((a x).mulVec p)) * N := Real.sqrt_mul hpp0 _
      _ ≤ Real.sqrt Λ * euclideanNorm p * N := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact (Real.sqrt_le_sqrt (a.elliptic x p).2).trans_eq
            (Real.sqrt_mul' Λ (euclideanSq_nonneg p))
  have h2 : |dot q g| ≤ euclideanNorm q * N := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (dot q g ^ 2) ≤ Real.sqrt (euclideanSq q * euclideanSq g) :=
          Real.sqrt_le_sqrt (dot_sq_le_euclideanSq_mul q g)
      _ = euclideanNorm q * euclideanNorm g := Real.sqrt_mul (euclideanSq_nonneg q) _
      _ ≤ euclideanNorm q * N :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (a.elliptic x g).1) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (N - (Real.sqrt Λ * euclideanNorm p + euclideanNorm q)), h1, h2, hNsq,
    neg_le_abs (dot p ((a x).mulVec g)), le_abs_self (dot q g)]

/-- `J₁(Ψ, p, q) ≤ (∫ Ψ) · ½ (√Λ |p| + |q|)²` for nonnegative integrable masks `Ψ`. -/
theorem J1_le_mul_half_sq {Λ : ℝ} (a : CoefficientField d Λ) {mask : Vec d → ℝ}
    (hm : Integrable mask) (hpos : ∀ x, 0 ≤ mask x) (p q : Vec d) :
    J1 a mask p q ≤
      (∫ x, mask x) * (1 / 2 * (Real.sqrt Λ * euclideanNorm p + euclideanNorm q) ^ 2) := by
  have hB : 0 ≤ 1 / 2 * (Real.sqrt Λ * euclideanNorm p + euclideanNorm q) ^ 2 := by positivity
  rw [← integral_mul_const]
  unfold J1
  refine Real.sSup_le ?_ (integral_nonneg fun x => mul_nonneg (hpos x) hB)
  rintro e ⟨w, rfl⟩
  by_cases hi : Integrable (fun x => mask x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))
  · exact integral_mono hi (hm.mul_const _) fun x =>
      mul_le_mul_of_nonneg_left (J1_integrand_le_half_sq a x p q (w.grad x)) (hpos x)
  · rw [integral_undef hi]
    exact integral_nonneg fun x => mul_nonneg (hpos x) hB

/-- **(4.8), sharp form.** `J₁(Φ_{z,r}, p, q) ≤ ½ (√Λ |p| + |q|)²`. -/
theorem J1Heat_le_half_sq {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (p q : Vec d) :
    J1Heat a z r p q ≤ 1 / 2 * (Real.sqrt Λ * euclideanNorm p + euclideanNorm q) ^ 2 := by
  have hi : Integrable (heatKernel (d := d) z r) :=
    (integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hn : ∀ x, 0 ≤ heatKernel z r x := fun x =>
    euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hmass : ∫ x, heatKernel (d := d) z r x = 1 := by
    unfold heatKernel
    rw [integral_sub_right_eq_self, integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  simpa only [J1Heat, hmass, one_mul] using J1_le_mul_half_sq a hi hn p q

end QSH
