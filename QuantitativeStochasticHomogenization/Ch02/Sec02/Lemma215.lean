import QuantitativeStochasticHomogenization.Ch02.Sec02.SubcubeDeviation
import QuantitativeStochasticHomogenization.Ch01.Sec04.Corollary114

/-!
# Lemma 2.15: the flatness of the maximizer of `J(□_{n+1}, p, q)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Lemma 2.15, (2.47): there are `κ(d) > 0` and `C(d, Λ) < ∞` such that for every law
satisfying (0.10)–(0.11), `n ∈ ℕ` and `p, q ∈ B₁`,
`E ⨍_{□_{n+1}} |v(x, □_{n+1}, p, q) - (ā_n⁻¹ q - p)·x|² dx ≤ C 3^{2n} (3^{-κn} + Σ_{m=0}^n 3^{-κ(n-m)} τ_m)`
(`lemma_2_15`), with `v` centered by subtracting the mean of `v - ℓ`, `ℓ(x) = (ā_n⁻¹ q - p)·x`, which
the book leaves implicit (the maximizer is defined up to a constant), and for every choice of the
maximizers; the expectation is of an integrable variable
(`measurable_centeredMeanSq_defectMaximizer`).

The proof is the book's. Step 1: Corollary 1.14 for `v - ℓ` on `□_{n+1}`, the bound (2.49) of the
first term by `J`, and Hölder's inequality for the sum over the scales. Step 2: at each scale `k ≤ n`
the subcube deviations are bounded (`sum_euclideanSq_vectorAverage_sub_le`) by
`2 (E J(□_k) - E J(□_{n+1})) + var[M_k] + |ā_k⁻¹ q - ā_n⁻¹ q|²`, with Lemma 2.13 and (2.44).
Corollary 1.14 also has the scale `n + 1` (the average over `□_{n+1}`), bounded through
`var[M_{n+1}] ≤ 2 var[M_n] + 4 τ_n` and (2.44). Step 3: the sums over the scales, with
`κ = min(κ₂.₁₃, ½)`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Sums over the scales -/

theorem geom_sum_le_of_one_lt {x : ℝ} (hx : 1 < x) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), x ^ k ≤ x / (x - 1) * x ^ n := by
  rw [geom_sum_eq hx.ne' (n + 1)]
  have hx1 : 0 < x - 1 := by linarith
  rw [div_le_iff₀ hx1, pow_succ]
  field_simp
  nlinarith [pow_pos (zero_lt_one.trans hx) n]

theorem pow_mul_sum_le_sum {θ : ℝ} (hθ0 : 0 ≤ θ) {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j) {k n : ℕ}
    (hkn : k ≤ n) :
    θ ^ (n - k) * ∑ j ∈ Finset.range (k + 1), θ ^ (k - j) * τ j ≤
      ∑ j ∈ Finset.range (n + 1), θ ^ (n - j) * τ j := by
  rw [Finset.mul_sum]
  have e : ∀ j ∈ Finset.range (k + 1), θ ^ (n - k) * (θ ^ (k - j) * τ j) = θ ^ (n - j) * τ j :=
    fun j hj => by
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [← mul_assoc, ← pow_add, show n - k + (k - j) = n - j by omega]
  rw [Finset.sum_congr rfl e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    fun j _ _ => mul_nonneg (pow_nonneg hθ0 _) (hτ j)

theorem pow_mul_sum_Ico_le_sum {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {τ : ℕ → ℝ}
    (hτ : ∀ j, 0 ≤ τ j) {k n : ℕ} :
    θ ^ (n - k) * ∑ j ∈ Finset.Ico k (n + 1), τ j ≤
      ∑ j ∈ Finset.range (n + 1), θ ^ (n - j) * τ j := by
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun j hj => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (Nat.zero_le k) |>.trans
      (by rw [Finset.range_eq_Ico]))
      fun j _ _ => mul_nonneg (pow_nonneg hθ0 _) (hτ j))
  have hj' := Finset.mem_Ico.mp hj
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0 hθ1 (by omega)) (hτ j)

/-! ## Step 1: the multiscale Poincaré inequality -/

/-- `|ā_U⁻¹ q - p|² ≤ 4` for `p, q ∈ B₁`. -/
theorem euclideanSq_expectedDualInvMatrix_mulVec_sub_le [NeZero d]
    {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P] (hΛ : 1 ≤ Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    {p q : Vec d} (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) :
    euclideanSq ((expectedDualInvMatrix P U).mulVec q - p) ≤ 4 := by
  have hb := expectedDualInvMatrix_bounds P hUo hUb hUc hne hΛ
  have hΛ0 : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hA := euclideanSq_mulVec_le_of_dot_le (expectedDualInvMatrix_transpose P hUo hUb hUc hne)
    (fun v => (mul_nonneg hΛ0.le (euclideanSq_nonneg v)).trans (hb v).1)
    (fun v => by rw [one_mul]; exact (hb v).2) q
  have hp1 := euclideanSq_le_one_of_mem_originBall hp
  have hq1 := euclideanSq_le_one_of_mem_originBall hq
  have h := euclideanSq_sub_le_two ((expectedDualInvMatrix P U).mulVec q) p
  nlinarith

/-- The weighted sum `3^{-d(n+1-k)} Σ_z |(G)_{z + □_k}|²` of Corollary 1.14 at the scale `k`. -/
def scaleDeviation (n k : ℕ) (G : Vec d → Vec d) : ℝ :=
  1 / ((3 : ℝ) ^ (n + 1 - k)) ^ d * ∑ z : Fin d → Fin (3 ^ (n + 1 - k)),
    euclideanSq (vectorAverage (partitionCube k (n + 1 - k) z) G)

theorem scaleDeviation_nonneg (n k : ℕ) (G : Vec d → Vec d) : 0 ≤ scaleDeviation n k G := by
  unfold scaleDeviation
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => euclideanSq_nonneg _)

theorem sq_sum_three_pow_sqrt_le (n : ℕ) (Y : ℕ → ℝ) (hY : ∀ k, 0 ≤ Y k) :
    (∑ k ∈ Finset.range (n + 2), (3 : ℝ) ^ k * Real.sqrt (Y k)) ^ 2 ≤
      (3 : ℝ) ^ (n + 2) / 2 * ∑ k ∈ Finset.range (n + 2), (3 : ℝ) ^ k * Y k := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 2))
    (fun k => Real.sqrt ((3 : ℝ) ^ k)) (fun k => Real.sqrt ((3 : ℝ) ^ k) * Real.sqrt (Y k))
  have e1 : ∀ k, Real.sqrt ((3 : ℝ) ^ k) * (Real.sqrt ((3 : ℝ) ^ k) * Real.sqrt (Y k)) =
      (3 : ℝ) ^ k * Real.sqrt (Y k) := fun k => by
    rw [← mul_assoc, Real.mul_self_sqrt (by positivity)]
  have e2 : ∀ k, Real.sqrt ((3 : ℝ) ^ k) ^ 2 = (3 : ℝ) ^ k := fun k => Real.sq_sqrt (by positivity)
  have e3 : ∀ k, (Real.sqrt ((3 : ℝ) ^ k) * Real.sqrt (Y k)) ^ 2 = (3 : ℝ) ^ k * Y k := fun k => by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (hY k)]
  simp only [e1, e2, e3] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ =>
    mul_nonneg (by positivity) (hY k)))
  rw [geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1)]
  have : (0 : ℝ) ≤ 1 := zero_le_one
  linarith

/-- **Step 1 of Lemma 2.15, pointwise**: for the maximizer `v` of `J(□_{n+1}, p, q)` with gradient
`g` and `|c|² ≤ 4`, `⨍ |v - ℓ_c - (v - ℓ_c)|² ≤ 2C²(4 J + 8) + C² 3^{n+2} Σ_{k=0}^{n+1} 3^k Y_k`
with the scale deviations `Y_k` of `g - c`. -/
theorem centeredMeanSq_le_scaleDeviation [NeZero d] {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (h114 : ∀ (m : ℕ) (u : Vec d → ℝ) (g : Vec d → Vec d), H1 (triadicCube d m) u g →
      scalarRms volume (triadicCube d m) (fun x => u x - ⨍ y in triadicCube d m, u y) ≤
        C₁ * vectorRms volume (triadicCube d m) g +
          C₁ * ∑ n ∈ Finset.range (m + 1), (3 : ℝ) ^ n *
            √(1 / ((3 : ℝ) ^ (m - n)) ^ d * ∑ k : Fin d → Fin (3 ^ (m - n)),
              euclideanSq (vectorAverage (partitionCube n (m - n) k) g)))
    (a : CoefficientField d Λ) (n : ℕ) (p q c : Vec d) (hc : euclideanSq c ≤ 4) {v : Vec d → ℝ}
    {g : Vec d → Vec d} (hv : IsDefectMaximizer a (triadicCube d (n + 1)) p q v g) :
    centeredMeanSq (triadicCube d (n + 1)) (fun x => v x - dot c x) ≤
      2 * C₁ ^ 2 * (4 * dualityDefect a (triadicCube d (n + 1)) p q + 8) +
        C₁ ^ 2 * (3 : ℝ) ^ (n + 2) * ∑ k ∈ Finset.range (n + 2),
          (3 : ℝ) ^ k * scaleDeviation n k (fun x => g x - c) := by
  set U := triadicCube d (n + 1) with hUdef
  have hUb := isBounded_triadicCube (d := d) (n + 1)
  have hU : volume U ≠ ⊤ := volume_triadicCube_ne_top d (n + 1)
  have hU0 : volume U ≠ 0 := volume_triadicCube_ne_zero d (n + 1)
  have := isFiniteMeasure_restrict.mpr hU
  have hu : H1 U (fun x => v x - dot c x) (fun x => g x - c) := hv.1.1.sub (H1.linear hUb c)
  have h := h114 (n + 1) _ _ hu
  -- the gradient term
  have hgL : MemLp g 2 (volume.restrict U) := hv.1.1.2.1
  have hJ := hv.dualityDefect_eq hUb hU0
  have hg2 := setAverage_euclideanSq_le_two_mul a hU hgL
  have hvr : vectorRms volume U (fun x => g x - c) ^ 2 ≤
      4 * dualityDefect a U p q + 8 := by
    unfold vectorRms
    rw [Real.sq_sqrt (by
      rw [setAverage_eq, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
        (integral_nonneg fun _ => euclideanSq_nonneg _))]
    have hi1 : Integrable (fun x => euclideanSq (g x - c)) (volume.restrict U) :=
      integrable_euclideanSq_of_memLp (hgL.sub (memLp_const c))
    have hi2 : Integrable (fun x => 2 * euclideanSq (g x) + 2 * euclideanSq c) (volume.restrict U) :=
      ((integrable_euclideanSq_of_memLp hgL).const_mul 2).add (integrable_const _)
    have hmono : ⨍ x in U, euclideanSq (g x - c) ≤ ⨍ x in U, (2 * euclideanSq (g x) + 2 * euclideanSq c) := by
      rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (integral_mono hi1 hi2 fun x =>
        euclideanSq_sub_le_two (g x) c) (inv_nonneg.mpr measureReal_nonneg)
    have hsplit : ⨍ x in U, (2 * euclideanSq (g x) + 2 * euclideanSq c) =
        2 * (⨍ x in U, euclideanSq (g x)) + 2 * euclideanSq c := by
      have hV : volume.real U ≠ 0 := (ENNReal.toReal_pos hU0 hU).ne'
      rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
        integral_add ((integrable_euclideanSq_of_memLp hgL).const_mul 2) (integrable_const _),
        integral_const_mul, integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
      field_simp
    rw [hsplit] at hmono
    rw [← hJ] at hg2
    linarith
  -- squaring Corollary 1.14
  set S := ∑ k ∈ Finset.range (n + 2), (3 : ℝ) ^ k * Real.sqrt (scaleDeviation n k (fun x => g x - c))
    with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hS2 := sq_sum_three_pow_sqrt_le n (fun k => scaleDeviation n k (fun x => g x - c))
    fun k => scaleDeviation_nonneg n k _
  have hA0 : 0 ≤ vectorRms volume U (fun x => g x - c) := Real.sqrt_nonneg _
  have hcor : scalarRms volume U (fun x => (v x - dot c x) - ⨍ y in U, (v y - dot c y)) ≤
      C₁ * vectorRms volume U (fun x => g x - c) + C₁ * S := by
    refine h.trans (le_of_eq ?_)
    rw [hSdef]
    congr 2
  rw [centeredMeanSq_eq_sq_scalarRms]
  have hsq := pow_le_pow_left₀ (scalarRms_nonneg U _) hcor 2
  have hJ0 : 0 ≤ dualityDefect a U p q := by
    rw [hJ, setAverage_eq, smul_eq_mul]
    refine mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun x => ?_)
    have := (a.elliptic x (g x)).1
    have := euclideanSq_nonneg (g x)
    show 0 ≤ (1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x))
    linarith
  have hC2 : 0 ≤ C₁ ^ 2 := sq_nonneg C₁
  nlinarith [sq_nonneg (C₁ * vectorRms volume U (fun x => g x - c) - C₁ * S),
    mul_le_mul_of_nonneg_left hvr hC2, mul_le_mul_of_nonneg_left hS2 hC2]

end QSH
