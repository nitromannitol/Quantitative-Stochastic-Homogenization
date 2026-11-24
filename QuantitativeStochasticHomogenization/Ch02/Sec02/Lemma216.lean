import QuantitativeStochasticHomogenization.Ch02.Sec02.CubeCaccioppoli

/-!
# Lemma 2.16: the rate of `E[J(□_n, p, ā_n p)]` in terms of the additivity defects

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Lemma 2.16, (2.54): there are `κ(d) > 0` and `C(d, Λ) < ∞` such that for every law
satisfying (0.10)–(0.11), `n ∈ ℕ` and `p ∈ B₁`,
`E[J(□_n, p, ā_n p)] ≤ C (3^{-κn} + Σ_{m=0}^n 3^{-κ(n-m)} τ_m)` (`lemma_2_16`).

The proof is the book's: Lemma 2.15 with `q = ā_n p` (for which `ā_n⁻¹ q - p = 0`), the Caccioppoli
inequality on `□_n ⊆ □_{n+1}` (`caccioppoli_triadicCube`), and (2.55),
`E[J(□_n, p, q)] ≤ C E ⨍_{□_n} |∇v(·, □_{n+1}, p, q)|² + C τ_n`, from
`J(□_n) = ⨍_{□_n} ½ ∇w·a∇w + ⨍_{□_n} ½ (∇v - ∇w)·a(∇v + ∇w)`, `v = v(·, □_n)`, `w = v(·, □_{n+1})`,
with Young's inequality pointwise in place of the book's Hölder inequality in expectation, and
Lemma 2.12 on the `3^d` subcubes of `□_{n+1}` for `∇v - ∇w`. Since `|ā_n p| ≤ Λ`, Lemma 2.15 and the
definition of `τ_n` (over `B₁ × B₁`) are used at `(p/Λ, q/Λ)` and scaled: `J` and `v` are
homogeneous of degrees two and one in `(p, q)`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Homogeneity -/

theorem dualityDefect_smul_smul [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) (t : ℝ)
    (p q : Vec d) :
    dualityDefect a U (t • p) (t • q) = t ^ 2 * dualityDefect a U p q := by
  rw [dualityDefect_eq_coarseMatrix a hUo hUb hUc hne, dualityDefect_eq_coarseMatrix a hUo hUb hUc hne]
  simp only [dot_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem IsDefectMaximizer.const_mul [NeZero d] {a : CoefficientField d Λ} {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    {p q : Vec d} {v : Vec d → ℝ} {g : Vec d → Vec d} (h : IsDefectMaximizer a U p q v g) (t : ℝ) :
    IsDefectMaximizer a U (t • p) (t • q) (fun x => t * v x) (fun x => t • g x) := by
  have h2 := h.linearCombination hUo hUb hUc hne h t 0
  simp only [zero_smul, add_zero, zero_mul] at h2
  exact h2

theorem centeredMeanSq_const_mul (U : Set (Vec d)) (f : Vec d → ℝ) (t : ℝ) :
    centeredMeanSq U (fun x => t * f x) = t ^ 2 * centeredMeanSq U f := by
  unfold centeredMeanSq
  have e : ∀ x, (t * f x - ⨍ y in U, t * f y) ^ 2 = t ^ 2 * (f x - ⨍ y in U, f y) ^ 2 := fun x => by
    rw [show (⨍ y in U, t * f y) = t * ⨍ y in U, f y by
      rw [setAverage_eq, setAverage_eq, integral_const_mul, smul_eq_mul, smul_eq_mul]; ring]
    ring
  simp only [e]
  rw [setAverage_eq (f := fun x => t ^ 2 * (f x - ⨍ y in U, f y) ^ 2),
    setAverage_eq (f := fun x => (f x - ⨍ y in U, f y) ^ 2), integral_const_mul, smul_eq_mul,
    smul_eq_mul]
  ring

theorem euclideanSq_lt_one_of_mem_originBall {p : Vec d} (hp : p ∈ originBall d 1) :
    euclideanSq p < 1 := by
  have h : euclideanNorm p < 1 := hp
  have h0 : 0 ≤ euclideanNorm p := Real.sqrt_nonneg _
  rw [← euclideanNorm_sq]
  nlinarith

theorem mem_originBall_of_euclideanSq_lt_one {p : Vec d} (hp : euclideanSq p < 1) :
    p ∈ originBall d 1 := by
  show Real.sqrt (euclideanSq p) < 1
  rw [Real.sqrt_lt' one_pos]
  linarith

/-! ## The centre subcube -/

theorem triadicSubcube_one (n : ℕ) : triadicSubcube (d := d) n (fun _ => 1) = triadicCube d n := by
  ext x
  show x - latticeShift (subcubeOffset (d := d) n (fun _ => 1)) ∈ triadicCube d n ↔ x ∈ triadicCube d n
  have e : latticeShift (subcubeOffset (d := d) n (fun _ => 1)) = 0 := by
    funext i
    simp [latticeShift, subcubeOffset]
  rw [e, sub_zero]

/-! ## (2.55), pointwise -/

theorem dot_le_young (u w : Vec d) {t : ℝ} (ht : 0 < t) :
    dot u w ≤ 1 / (2 * t) * euclideanSq u + t / 2 * euclideanSq w := by
  have h := euclideanSq_nonneg (u - t • w)
  have e : euclideanSq (u - t • w) = euclideanSq u - 2 * t * dot u w + t ^ 2 * euclideanSq w := by
    simp only [euclideanSq, dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  have h2 : 2 * t * dot u w ≤ euclideanSq u + t ^ 2 * euclideanSq w := by linarith
  have h3 : dot u w ≤ (euclideanSq u + t ^ 2 * euclideanSq w) / (2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc dot u w ≤ (euclideanSq u + t ^ 2 * euclideanSq w) / (2 * t) := h3
    _ = 1 / (2 * t) * euclideanSq u + t / 2 * euclideanSq w := by field_simp

/-- The pointwise splitting `½ g·ag ≤ (Λ + ½)·... `: for `t = 1/(2Λ²)`,
`½ g·ag ≤ ½ Λ |h|² + Λ² |g - h|² + ¼ (|g|² + |h|²)`. -/
theorem half_dot_le_split (a : CoefficientField d Λ) (hΛ : 1 ≤ Λ) (x : Vec d) (g h : Vec d) :
    (1 / 2 : ℝ) * dot g ((a x).mulVec g) ≤
      (1 / 2 : ℝ) * Λ * euclideanSq h + Λ ^ 2 * euclideanSq (g - h) +
        (1 / 4 : ℝ) * (euclideanSq g + euclideanSq h) := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hs := dot_mulVec_comm_of_symm (a.symmetric x) g h
  have hsplit : (1 / 2 : ℝ) * dot g ((a x).mulVec g) = (1 / 2 : ℝ) * dot h ((a x).mulVec h) +
      (1 / 2 : ℝ) * dot (g - h) ((a x).mulVec (g + h)) := by
    simp only [dot_eq_dotProduct, Matrix.mulVec_add, dotProduct_add, sub_dotProduct] at hs ⊢
    change g ⬝ᵥ (a x).mulVec h = h ⬝ᵥ (a x).mulVec g at hs
    linarith
  have hh : dot h ((a x).mulVec h) ≤ Λ * euclideanSq h := (a.elliptic x h).2
  have ht : (0 : ℝ) < 1 / (2 * Λ ^ 2) := by positivity
  have hy := dot_le_young (g - h) ((a x).mulVec (g + h)) ht
  have ha := euclideanSq_coefficient_mulVec_le_sq a x (g + h)
  have hgh : euclideanSq (g + h) ≤ 2 * euclideanSq g + 2 * euclideanSq h := by
    simp only [euclideanSq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (g i - h i)]
  have e1 : 1 / (2 * (1 / (2 * Λ ^ 2))) = Λ ^ 2 := by field_simp
  have e2 : (1 / (2 * Λ ^ 2)) / 2 * (Λ ^ 2 * euclideanSq (g + h)) = (1 / 4 : ℝ) * euclideanSq (g + h) := by
    field_simp
    ring
  rw [e1] at hy
  have hy2 : (1 / (2 * Λ ^ 2)) / 2 * euclideanSq ((a x).mulVec (g + h)) ≤
      (1 / (2 * Λ ^ 2)) / 2 * (Λ ^ 2 * euclideanSq (g + h)) :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  rw [e2] at hy2
  have hgh' : (1 / 4 : ℝ) * euclideanSq (g + h) ≤ (1 / 2 : ℝ) * (euclideanSq g + euclideanSq h) := by
    linarith
  rw [hsplit]
  have := mul_nonneg (sq_nonneg Λ) (euclideanSq_nonneg (g - h))
  linarith

end QSH
