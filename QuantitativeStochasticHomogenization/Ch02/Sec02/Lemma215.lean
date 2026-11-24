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
theorem centeredMeanSq_le_scaleDeviation [NeZero d] {C₁ : ℝ}
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

/-! ## Step 2: the expectations at each scale -/

/-- The measurable majorant `3 (2 (3^{-dr} Σ_z J(z + □_k) - J(□_{n+1})) + 3^{-dr} Σ_z |M(z + □_k) - c'|²
+ |c' - c|²)`, `r = n + 1 - k`, of the scale deviation `Y_k`. -/
def scaleMajorant (n k : ℕ) (p q c c' : Vec d) (a : CoefficientField d Λ) : ℝ :=
  3 * (2 * (∑ z : Fin d → Fin (3 ^ (n + 1 - k)), 1 / ((3 : ℝ) ^ (n + 1 - k)) ^ d *
      dualityDefect a (partitionCube k (n + 1 - k) z) p q - dualityDefect a (triadicCube d (n + 1)) p q) +
    ∑ z : Fin d → Fin (3 ^ (n + 1 - k)), 1 / ((3 : ℝ) ^ (n + 1 - k)) ^ d *
      euclideanSq (meanGradient a (partitionCube k (n + 1 - k) z) p q - c') +
    euclideanSq (c' - c))

theorem scaleDeviation_le_scaleMajorant [NeZero d] (a : CoefficientField d Λ) {n k : ℕ}
    (hk : k ≤ n + 1) (p q c c' : Vec d) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : IsDefectMaximizer a (triadicCube d (n + 1)) p q v g) :
    scaleDeviation n k (fun x => g x - c) ≤ scaleMajorant n k p q c c' a := by
  have e : k + (n + 1 - k) = n + 1 := by omega
  have hv' : IsDefectMaximizer a (triadicCube d (k + (n + 1 - k))) p q v g := by rw [e]; exact hv
  have h := sum_euclideanSq_vectorAverage_sub_le a k (n + 1 - k) p q c c' hv'
  rw [e] at h
  exact h

theorem integrable_euclideanSq_sub_of_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → Vec d} (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) (m : Vec d) :
    Integrable (fun ω => euclideanSq (X ω - m)) P := by
  simp only [euclideanSq, dot, Pi.sub_apply]
  exact integrable_finsetSum _ fun i _ =>
    ((hX i).sub (memLp_const (m i))).integrable_mul ((hX i).sub (memLp_const (m i)))

/-- **The expectation of the majorant**: for `p, q ∈ B₁` and `c' = ā_k⁻¹ q - p`,
`E[Z_k] ≤ 3 (2 Σ_{j=k}^{n} τ_j + var[M_k] + |c' - c|²)`. -/
theorem integral_scaleMajorant_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 1 ≤ Λ) {n k : ℕ} (hk : k ≤ n + 1) {p q : Vec d}
    (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) (c : Vec d) :
    Integrable (scaleMajorant n k p q c ((expectedDualInvMatrix P (triadicCube d k)).mulVec q - p)) P ∧
      ∫ a, scaleMajorant n k p q c ((expectedDualInvMatrix P (triadicCube d k)).mulVec q - p) a ∂P ≤
        3 * (2 * ∑ j ∈ Finset.Ico k (n + 1), additivityDefect P j +
          vecVariance P (fun a => meanGradient a (triadicCube d k) p q) +
          euclideanSq ((expectedDualInvMatrix P (triadicCube d k)).mulVec q - p - c)) := by
  have : IsProbabilityMeasure P := hP.1
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  set r := n + 1 - k with hr
  have e : k + r = n + 1 := by omega
  set w : ℝ := 1 / ((3 : ℝ) ^ r) ^ d with hw
  set c' := (expectedDualInvMatrix P (triadicCube d k)).mulVec q - p with hc'
  have hJQ : ∀ z : Fin d → Fin (3 ^ r), Integrable (fun a => dualityDefect a (partitionCube k r z) p q) P :=
    fun z => integrable_dualityDefect hΛ0 (isOpen_partitionCube k r z) (isBounded_partitionCube k r z)
      (convex_partitionCube k r z) (partitionCube_nonempty k r z) hp hq
  have hJU : Integrable (fun a => dualityDefect a (triadicCube d (n + 1)) p q) P :=
    integrable_dualityDefect hΛ0 (isOpen_triadicCube' (n + 1)) (isBounded_triadicCube (n + 1))
      (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1)) hp hq
  have hMQ : ∀ (z : Fin d → Fin (3 ^ r)) (i : Fin d),
      MemLp (fun a => meanGradient a (partitionCube k r z) p q i) 2 P := fun z i =>
    memLp_meanGradient_apply hΛ0 (isOpen_partitionCube k r z) (isBounded_partitionCube k r z)
      (convex_partitionCube k r z) (partitionCube_nonempty k r z) hp hq i
  have hE : ∀ z : Fin d → Fin (3 ^ r), Integrable (fun a =>
      euclideanSq (meanGradient a (partitionCube k r z) p q - c')) P := fun z =>
    integrable_euclideanSq_sub_of_memLp (hMQ z) c'
  have hS1 : Integrable (fun a => ∑ z : Fin d → Fin (3 ^ r), w * dualityDefect a (partitionCube k r z) p q) P :=
    integrable_finsetSum _ fun z _ => (hJQ z).const_mul _
  have hS2 : Integrable (fun a => ∑ z : Fin d → Fin (3 ^ r), w *
      euclideanSq (meanGradient a (partitionCube k r z) p q - c')) P :=
    integrable_finsetSum _ fun z _ => (hE z).const_mul _
  have hA : Integrable (fun a => 2 * (∑ z : Fin d → Fin (3 ^ r), w *
      dualityDefect a (partitionCube k r z) p q - dualityDefect a (triadicCube d (n + 1)) p q)) P :=
    (hS1.sub hJU).const_mul 2
  have hAB : Integrable (fun a => 2 * (∑ z : Fin d → Fin (3 ^ r), w *
      dualityDefect a (partitionCube k r z) p q - dualityDefect a (triadicCube d (n + 1)) p q) +
      ∑ z : Fin d → Fin (3 ^ r), w * euclideanSq (meanGradient a (partitionCube k r z) p q - c')) P :=
    hA.add hS2
  have hint : Integrable (scaleMajorant n k p q c c') P := (hAB.add (integrable_const _)).const_mul 3
  refine ⟨hint, ?_⟩
  -- the three expectations
  have hcard : w * (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) = 1 := by
    rw [hw]; exact partition_weight_mul_card r
  have hJ : ∫ a, ∑ z : Fin d → Fin (3 ^ r), w * dualityDefect a (partitionCube k r z) p q ∂P =
      ∫ a, dualityDefect a (triadicCube d k) p q ∂P := by
    rw [integral_finsetSum _ fun z _ => (hJQ z).const_mul _]
    simp only [integral_const_mul, integral_dualityDefect_partitionCube hP hΛ0 k r _ p q]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      mul_comm (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) w, hcard, one_mul]
  have hvar : ∀ z : Fin d → Fin (3 ^ r),
      ∫ a, euclideanSq (meanGradient a (partitionCube k r z) p q - c') ∂P =
        vecVariance P (fun a => meanGradient a (triadicCube d k) p q) := fun z => by
    have hmean : ∀ i, ∫ a, meanGradient a (partitionCube k r z) p q i ∂P = c' i := fun i => by
      rw [integral_meanGradient_partitionCube hP hΛ0 k r z p q i, integral_meanGradient_apply hΛ
        (isOpen_triadicCube' k) (isBounded_triadicCube k) (convex_triadicCube k)
        (triadicCube_nonempty k)]
    have e1 : ∫ a, euclideanSq (meanGradient a (partitionCube k r z) p q - c') ∂P =
        vecVariance P (fun a => meanGradient a (partitionCube k r z) p q) := by
      unfold vecVariance
      simp only [hmean]
      simp only [euclideanSq, dot, Pi.sub_apply, ← sq]
      exact integral_finsetSum _ fun i _ => ((hMQ z i).sub (memLp_const (c' i))).integrable_sq
    rw [e1]
    have e2 : (fun a : CoefficientField d Λ => meanGradient a (partitionCube k r z) p q) = fun a =>
        meanGradient (translate (latticeShift (partitionCenter k r z)) a) (triadicCube d k) p q :=
      funext fun a => meanGradient_partitionCube a k r z p q
    rw [e2]
    exact vecVariance_comp_translate hP _ fun i => measurable_meanGradient_apply
      (volume_triadicCube_ne_zero d k) (volume_triadicCube_ne_top d k) hΛ0 p q i
  have hM : ∫ a, ∑ z : Fin d → Fin (3 ^ r), w *
      euclideanSq (meanGradient a (partitionCube k r z) p q - c') ∂P =
      vecVariance P (fun a => meanGradient a (triadicCube d k) p q) := by
    rw [integral_finsetSum _ fun z _ => (hE z).const_mul _]
    simp only [integral_const_mul, hvar]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      mul_comm (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) w, hcard, one_mul]
  have htel := integral_dualityDefect_sub_le_sum (P := P) hΛ0 hp hq k r
  rw [e] at htel
  have hcalc : ∫ a, scaleMajorant n k p q c c' a ∂P = 3 * (2 * (∫ a, dualityDefect a (triadicCube d k) p q ∂P -
      ∫ a, dualityDefect a (triadicCube d (n + 1)) p q ∂P) +
      vecVariance P (fun a => meanGradient a (triadicCube d k) p q) + euclideanSq (c' - c)) := by
    unfold scaleMajorant
    rw [integral_const_mul, integral_add hAB (integrable_const _), integral_add hA hS2,
      integral_const_mul, integral_sub hS1 hJU, hJ, hM, integral_const, probReal_univ, one_smul]
  rw [hcalc]
  have hτ0 : 0 ≤ ∑ j ∈ Finset.Ico k (n + 1), additivityDefect P j :=
    Finset.sum_nonneg fun j _ => additivityDefect_nonneg hΛ0 j
  linarith

/-! ## Lemma 2.15 -/

/-- **Lemma 2.15**, (2.47): there is `κ(d) > 0` such that for every `Λ` there is `C(d, Λ) < ∞` with,
for every law satisfying (0.10)–(0.11), every `n ∈ ℕ`, every `p, q ∈ B₁` and every choice of the
maximizers `v(·, □_{n+1}, p, q)` of (2.9), with `ℓ(x) = (ā_n⁻¹ q - p)·x`, the centered mean square
`⨍_{□_{n+1}} |v - ℓ - (v - ℓ)_{□_{n+1}}|²` (`centeredMeanSq`) is integrable and
`E ⨍_{□_{n+1}} |v - ℓ - (v - ℓ)_{□_{n+1}}|² ≤ C 3^{2n} (3^{-κn} + Σ_{m=0}^n 3^{-κ(n-m)} τ_m)`. -/
theorem lemma_2_15 [NeZero d] :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Λ : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (n : ℕ), ∀ p ∈ originBall d 1, ∀ q ∈ originBall d 1,
      ∀ (v : CoefficientField d Λ → Vec d → ℝ) (g : CoefficientField d Λ → Vec d → Vec d),
        (∀ a, IsDefectMaximizer a (triadicCube d (n + 1)) p q (v a) (g a)) →
        Integrable (fun a => centeredMeanSq (triadicCube d (n + 1)) fun x =>
          v a x - dot ((averagedDualMatrix P (triadicCube d n))⁻¹.mulVec q - p) x) P ∧
        ∫ a, centeredMeanSq (triadicCube d (n + 1)) (fun x =>
            v a x - dot ((averagedDualMatrix P (triadicCube d n))⁻¹.mulVec q - p) x) ∂P ≤
          C * (3 : ℝ) ^ (2 * n) * ((3 : ℝ) ^ (-(κ * n)) + ∑ m ∈ Finset.range (n + 1),
            (3 : ℝ) ^ (-(κ * ((n : ℝ) - m))) * additivityDefect P m) := by
  obtain ⟨κ₀, C₀, hκ₀, hC₀, h213⟩ := exists_vecVariance_meanGradient_le (d := d)
  obtain ⟨C₁, hC₁, h114⟩ := corollary_1_14 (d := d)
  set κ := min κ₀ (1 / 2) with hκdef
  have hκ : 0 < κ := lt_min hκ₀ (by norm_num)
  have hκ2 : κ ≤ 1 / 2 := min_le_right _ _
  have hκκ₀ : κ ≤ κ₀ := min_le_left _ _
  set θ : ℝ := (3 : ℝ) ^ (-κ) with hθdef
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h3θ : 1 < 3 * θ := by
    have e : 3 * θ = (3 : ℝ) ^ (1 - κ) := by
      rw [hθdef, Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num),
        div_eq_mul_inv]
    rw [e]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have h9θ : 1 ≤ 9 * θ := by linarith
  have hpow : ∀ k : ℕ, (3 : ℝ) ^ (-(κ * k)) = θ ^ k := fun k => by
    rw [hθdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hpow₀ : ∀ k : ℕ, (3 : ℝ) ^ (-(κ₀ * k)) ≤ θ ^ k := fun k => by
    rw [← hpow k]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  set c₃ := 3 * θ / (3 * θ - 1) with hc₃
  have hc₃0 : 0 ≤ c₃ := div_nonneg (by positivity) (by linarith)
  set K₁ := 3 * C₀ * c₃ + 18 * C₀ with hK₁
  set K₂ := 3 * (C₀ + 4) * c₃ + 9 * (2 * C₀ + 6) with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨κ, hκ, fun Λ => ?_⟩
  set B := 2 * C₁ ^ 2 * (4 * ((1 / 2 : ℝ) * |Λ| + 3 / 2) + 8) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨B + 9 * C₁ ^ 2 * (K₁ + K₂), by positivity, fun P hP n p hp q hq v g hmax => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  have hΛ1 : 1 ≤ Λ := by
    rcases isEmpty_or_nonempty (CoefficientField d Λ) with h | h
    · have h0 : P = 0 := Measure.eq_zero_of_isEmpty P
      have h1 := measure_univ (μ := P)
      rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
      exact absurd h1 zero_ne_one
    · obtain ⟨a⟩ := h
      exact one_le_of_coefficientField a
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ1
  have hcEq : (averagedDualMatrix P (triadicCube d n))⁻¹.mulVec q - p =
      (expectedDualInvMatrix P (triadicCube d n)).mulVec q - p := by
    rw [inv_averagedDualMatrix hΛ1 (isOpen_triadicCube' n) (isBounded_triadicCube n)
      (convex_triadicCube n) (triadicCube_nonempty n)]
  rw [hcEq]
  set c := (expectedDualInvMatrix P (triadicCube d n)).mulVec q - p with hcdef
  set ck : ℕ → Vec d := fun k => (expectedDualInvMatrix P (triadicCube d k)).mulVec q - p with hck
  have hc4 : euclideanSq c ≤ 4 := euclideanSq_expectedDualInvMatrix_mulVec_sub_le hΛ1
    (isOpen_triadicCube' n) (isBounded_triadicCube n) (convex_triadicCube n)
    (triadicCube_nonempty n) hp hq
  set τ := additivityDefect P with hτdef
  have hτ0 : ∀ j, 0 ≤ τ j := fun j => additivityDefect_nonneg hΛ0 j
  set T := ∑ j ∈ Finset.range (n + 1), θ ^ (n - j) * τ j with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hθ0.le _) (hτ0 j)
  -- the measurable majorant
  set R : CoefficientField d Λ → ℝ := fun a =>
    2 * C₁ ^ 2 * (4 * dualityDefect a (triadicCube d (n + 1)) p q + 8) +
      C₁ ^ 2 * (3 : ℝ) ^ (n + 2) * ∑ k ∈ Finset.range (n + 2),
        (3 : ℝ) ^ k * scaleMajorant n k p q c (ck k) a with hRdef
  have hpt : ∀ a, centeredMeanSq (triadicCube d (n + 1)) (fun x => v a x - dot c x) ≤ R a := by
    intro a
    have h1 := centeredMeanSq_le_scaleDeviation h114 a n p q c hc4 (hmax a)
    have h2 : ∑ k ∈ Finset.range (n + 2), (3 : ℝ) ^ k * scaleDeviation n k (fun x => g a x - c) ≤
        ∑ k ∈ Finset.range (n + 2), (3 : ℝ) ^ k * scaleMajorant n k p q c (ck k) a :=
      Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (scaleDeviation_le_scaleMajorant a
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) p q c (ck k) (hmax a)) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ C₁ ^ 2 * (3 : ℝ) ^ (n + 2))
    show _ ≤ 2 * C₁ ^ 2 * (4 * dualityDefect a (triadicCube d (n + 1)) p q + 8) +
      C₁ ^ 2 * (3 : ℝ) ^ (n + 2) * ∑ k ∈ Finset.range (n + 2),
        (3 : ℝ) ^ k * scaleMajorant n k p q c (ck k) a
    linarith
  have hmaj := fun k (hk : k ∈ Finset.range (n + 2)) => integral_scaleMajorant_le hP hΛ1
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hp hq c
  have hJU : Integrable (fun a => dualityDefect a (triadicCube d (n + 1)) p q) P :=
    integrable_dualityDefect hΛ0 (isOpen_triadicCube' (n + 1)) (isBounded_triadicCube (n + 1))
      (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1)) hp hq
  have hR1 : Integrable (fun a => 2 * C₁ ^ 2 * (4 * dualityDefect a (triadicCube d (n + 1)) p q + 8)) P :=
    ((hJU.const_mul 4).add (integrable_const _)).const_mul _
  have hR2 : Integrable (fun a => ∑ k ∈ Finset.range (n + 2),
      (3 : ℝ) ^ k * scaleMajorant n k p q c (ck k) a) P :=
    integrable_finsetSum _ fun k hk => (hmaj k hk).1.const_mul _
  have hRi : Integrable R P := hR1.add (hR2.const_mul _)
  have hF0 : ∀ a, 0 ≤ centeredMeanSq (triadicCube d (n + 1)) (fun x => v a x - dot c x) :=
    fun a => by
      rw [centeredMeanSq_eq_sq_scalarRms]
      exact sq_nonneg _
  have hFm := measurable_centeredMeanSq_defectMaximizer hΛ0 (n + 1) p q c hmax
  have hFi : Integrable (fun a => centeredMeanSq (triadicCube d (n + 1))
      (fun x => v a x - dot c x)) P :=
    hRi.mono' hFm.aestronglyMeasurable (Eventually.of_forall fun a => by
      rw [Real.norm_of_nonneg (hF0 a)]
      exact hpt a)
  refine ⟨hFi, ?_⟩
  refine (integral_mono hFi hRi hpt).trans ?_
  -- the expectation of the majorant
  have hEJ : ∫ a, dualityDefect a (triadicCube d (n + 1)) p q ∂P ≤ (1 / 2 : ℝ) * |Λ| + 3 / 2 := by
    have h := integral_mono hJU (integrable_const ((1 / 2 : ℝ) * Λ + 3 / 2)) fun a =>
      (dualityDefect_le_of_mem_originBall a (isOpen_triadicCube' (n + 1))
        (isBounded_triadicCube (n + 1)) (convex_triadicCube (n + 1))
        (triadicCube_nonempty (n + 1)) hp hq).2
    rw [integral_const, probReal_univ, one_smul] at h
    rw [abs_of_nonneg hΛ0]
    exact h
  have hσ : ∀ k : ℕ, vecVariance P (fun a => meanGradient a (triadicCube d k) p q) ≤
      C₀ * θ ^ k + C₀ * ∑ j ∈ Finset.range (k + 1), θ ^ (k - j) * τ j := fun k => by
    refine (h213 Λ P hP p hp q hq k).trans ?_
    refine add_le_add (mul_le_mul_of_nonneg_left (hpow₀ k) hC₀)
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hC₀)
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine mul_le_mul_of_nonneg_right ?_ (hτ0 j)
    have e : ((k : ℝ) - j) = ((k - j : ℕ) : ℝ) := by rw [Nat.cast_sub hjk]
    rw [e]
    exact hpow₀ (k - j)
  -- the bound at each scale
  have hscale : ∀ k ∈ Finset.range (n + 1), θ ^ n * ((3 : ℝ) ^ k *
      ∫ a, scaleMajorant n k p q c (ck k) a ∂P) ≤
        (3 * θ) ^ k * (3 * (C₀ * θ ^ n + (C₀ + 4) * T)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := (hmaj k (Finset.mem_range.mpr (by omega))).2
    have h44 := euclideanSq_inv_averagedDualMatrix_sub_le hP hΛ1 k (n - k) hq
    rw [show k + (n - k) = n by omega, inv_averagedDualMatrix hΛ1 (isOpen_triadicCube' n)
      (isBounded_triadicCube n) (convex_triadicCube n) (triadicCube_nonempty n),
      inv_averagedDualMatrix hΛ1 (isOpen_triadicCube' k) (isBounded_triadicCube k)
      (convex_triadicCube k) (triadicCube_nonempty k)] at h44
    rw [← hτdef] at h1 h44
    have hsym : euclideanSq ((expectedDualInvMatrix P (triadicCube d k)).mulVec q - p - c) =
        euclideanSq ((expectedDualInvMatrix P (triadicCube d n)).mulVec q -
          (expectedDualInvMatrix P (triadicCube d k)).mulVec q) := by
      simp only [hcdef, euclideanSq, dot, Pi.sub_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hIco : ∑ j ∈ Finset.Ico k n, τ j ≤ ∑ j ∈ Finset.Ico k (n + 1), τ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
        fun j _ _ => hτ0 j
    have hT1 := pow_mul_sum_le_sum hθ0.le hτ0 hkn
    have hT2 := pow_mul_sum_Ico_le_sum (θ := θ) hθ0.le hθ1 hτ0 (k := k) (n := n)
    have hσk := hσ k
    -- θ^n = θ^(n-k) θ^k
    have hθn : θ ^ n = θ ^ (n - k) * θ ^ k := by rw [← pow_add, Nat.sub_add_cancel hkn]
    have hE : ∫ a, scaleMajorant n k p q c (ck k) a ∂P ≤
        3 * (C₀ * θ ^ k + C₀ * ∑ j ∈ Finset.range (k + 1), θ ^ (k - j) * τ j +
          4 * ∑ j ∈ Finset.Ico k (n + 1), τ j) := by
      refine h1.trans ?_
      rw [hsym]
      linarith
    have h3k : (0 : ℝ) ≤ 3 ^ k := by positivity
    have hθk : (0 : ℝ) ≤ θ ^ k := pow_nonneg hθ0.le k
    have hθnk : (0 : ℝ) ≤ θ ^ (n - k) := pow_nonneg hθ0.le _
    calc θ ^ n * ((3 : ℝ) ^ k * ∫ a, scaleMajorant n k p q c (ck k) a ∂P)
        ≤ θ ^ n * ((3 : ℝ) ^ k * (3 * (C₀ * θ ^ k + C₀ * ∑ j ∈ Finset.range (k + 1),
            θ ^ (k - j) * τ j + 4 * ∑ j ∈ Finset.Ico k (n + 1), τ j))) := by
          gcongr
      _ = (3 * θ) ^ k * (3 * (C₀ * θ ^ n + (C₀ * (θ ^ (n - k) * ∑ j ∈ Finset.range (k + 1),
            θ ^ (k - j) * τ j) + 4 * (θ ^ (n - k) * ∑ j ∈ Finset.Ico k (n + 1), τ j)))) := by
          rw [hθn, mul_pow]
          ring
      _ ≤ (3 * θ) ^ k * (3 * (C₀ * θ ^ n + (C₀ * T + 4 * T))) := by
          gcongr
      _ = (3 * θ) ^ k * (3 * (C₀ * θ ^ n + (C₀ + 4) * T)) := by ring
  -- the top scale
  have htop : (3 : ℝ) ^ (n + 1) * ∫ a, scaleMajorant n (n + 1) p q c (ck (n + 1)) a ∂P ≤
      (3 : ℝ) ^ n * (9 * (2 * C₀ * θ ^ n + (2 * C₀ + 6) * T)) := by
    have h1 := (hmaj (n + 1) (Finset.mem_range.mpr (by omega))).2
    have h44 := euclideanSq_inv_averagedDualMatrix_sub_le hP hΛ1 n 1 hq
    rw [inv_averagedDualMatrix hΛ1 (isOpen_triadicCube' (n + 1)) (isBounded_triadicCube (n + 1))
      (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1)),
      inv_averagedDualMatrix hΛ1 (isOpen_triadicCube' n) (isBounded_triadicCube n)
      (convex_triadicCube n) (triadicCube_nonempty n)] at h44
    simp only [Finset.Ico_self, Finset.sum_empty, Nat.Ico_succ_singleton,
      Finset.sum_singleton] at h1 h44
    have hσn1 := vecVariance_meanGradient_succ_le_two hP hΛ0 n hp hq
    rw [← hτdef] at h44 hσn1
    have hσn := hσ n
    have hτT : τ n ≤ T := by
      have := Finset.single_le_sum (f := fun j => θ ^ (n - j) * τ j)
        (fun j _ => mul_nonneg (pow_nonneg hθ0.le _) (hτ0 j)) (Finset.self_mem_range_succ n)
      simpa using this
    have hsym : euclideanSq ((expectedDualInvMatrix P (triadicCube d (n + 1))).mulVec q - p - c) =
        euclideanSq ((expectedDualInvMatrix P (triadicCube d (n + 1))).mulVec q -
          (expectedDualInvMatrix P (triadicCube d n)).mulVec q) := by
      simp only [hcdef, euclideanSq, dot, Pi.sub_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsym] at h1
    rw [← hTdef] at hσn
    rw [pow_succ]
    have h3n : (0 : ℝ) ≤ 3 ^ n := by positivity
    have hle : ∫ a, scaleMajorant n (n + 1) p q c (ck (n + 1)) a ∂P ≤
        3 * (2 * C₀ * θ ^ n + (2 * C₀ + 6) * T) := by
      refine h1.trans ?_
      linarith
    have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 3 ^ n * 3)
    calc 3 ^ n * 3 * ∫ a, scaleMajorant n (n + 1) p q c (ck (n + 1)) a ∂P
        ≤ 3 ^ n * 3 * (3 * (2 * C₀ * θ ^ n + (2 * C₀ + 6) * T)) := this
      _ = 3 ^ n * (9 * (2 * C₀ * θ ^ n + (2 * C₀ + 6) * T)) := by ring
  -- the sum over the scales
  have hsum : ∑ k ∈ Finset.range (n + 2), (3 : ℝ) ^ k *
      ∫ a, scaleMajorant n k p q c (ck k) a ∂P ≤ (3 : ℝ) ^ n * (K₁ * θ ^ n + K₂ * T) := by
    rw [Finset.sum_range_succ]
    have hgeom := geom_sum_le_of_one_lt h3θ n
    have hlow : θ ^ n * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k *
        ∫ a, scaleMajorant n k p q c (ck k) a ∂P ≤
          θ ^ n * ((3 : ℝ) ^ n * (c₃ * (3 * (C₀ * θ ^ n + (C₀ + 4) * T)))) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum hscale).trans ?_
      rw [← Finset.sum_mul]
      have hA0 : 0 ≤ 3 * (C₀ * θ ^ n + (C₀ + 4) * T) := by positivity
      calc (∑ k ∈ Finset.range (n + 1), (3 * θ) ^ k) * (3 * (C₀ * θ ^ n + (C₀ + 4) * T))
          ≤ (3 * θ / (3 * θ - 1) * (3 * θ) ^ n) * (3 * (C₀ * θ ^ n + (C₀ + 4) * T)) :=
            mul_le_mul_of_nonneg_right hgeom hA0
        _ = θ ^ n * ((3 : ℝ) ^ n * (c₃ * (3 * (C₀ * θ ^ n + (C₀ + 4) * T)))) := by
            rw [hc₃, mul_pow]
            ring
    have hlow' := le_of_mul_le_mul_left hlow (pow_pos hθ0 n)
    have e : (3 : ℝ) ^ n * (c₃ * (3 * (C₀ * θ ^ n + (C₀ + 4) * T))) +
        (3 : ℝ) ^ n * (9 * (2 * C₀ * θ ^ n + (2 * C₀ + 6) * T)) =
        (3 : ℝ) ^ n * (K₁ * θ ^ n + K₂ * T) := by
      rw [hK₁, hK₂]
      ring
    linarith
  -- the conclusion
  have hERint : ∫ a, R a ∂P = 2 * C₁ ^ 2 * (4 * ∫ a, dualityDefect a (triadicCube d (n + 1)) p q ∂P + 8) +
      C₁ ^ 2 * (3 : ℝ) ^ (n + 2) * ∑ k ∈ Finset.range (n + 2),
        (3 : ℝ) ^ k * ∫ a, scaleMajorant n k p q c (ck k) a ∂P := by
    rw [hRdef, integral_add hR1 (hR2.const_mul _), integral_const_mul, integral_const_mul,
      integral_add (hJU.const_mul 4) (integrable_const _), integral_const_mul, integral_const,
      probReal_univ, one_smul, integral_finsetSum _ fun k hk => (hmaj k hk).1.const_mul _]
    simp only [integral_const_mul]
    rfl
  rw [hERint]
  have hpow2 : (3 : ℝ) ^ (2 * n) = (3 : ℝ) ^ n * (3 : ℝ) ^ n := by rw [two_mul, pow_add]
  have hTeq : ∑ m ∈ Finset.range (n + 1), (3 : ℝ) ^ (-(κ * ((n : ℝ) - m))) * additivityDefect P m = T := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [show ((n : ℝ) - m) = ((n - m : ℕ) : ℝ) by rw [Nat.cast_sub hmn], hpow (n - m)]
  rw [hpow n, hTeq, hpow2]
  have h9n : 1 ≤ (3 : ℝ) ^ n * (3 : ℝ) ^ n * θ ^ n := by
    rw [← mul_pow, ← mul_pow]
    exact one_le_pow₀ (by nlinarith)
  have hC1 : 0 ≤ C₁ ^ 2 := sq_nonneg _
  have h3n2 : (3 : ℝ) ^ (n + 2) = 9 * (3 : ℝ) ^ n := by rw [pow_add]; ring
  rw [h3n2]
  have hθn0 : 0 ≤ θ ^ n := pow_nonneg hθ0.le n
  have h3n0 : 0 ≤ (3 : ℝ) ^ n := by positivity
  have hbig := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ C₁ ^ 2 * (9 * (3 : ℝ) ^ n))
  have hBle : 2 * C₁ ^ 2 * (4 * ∫ a, dualityDefect a (triadicCube d (n + 1)) p q ∂P + 8) ≤ B := by
    rw [hB]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hB9 : B ≤ B * ((3 : ℝ) ^ n * (3 : ℝ) ^ n * θ ^ n) := le_mul_of_one_le_right hB0 h9n
  set X := (3 : ℝ) ^ n * (3 : ℝ) ^ n with hX
  have hX0 : 0 ≤ X := mul_nonneg h3n0 h3n0
  have hXθ : 0 ≤ X * θ ^ n := mul_nonneg hX0 hθn0
  have hXT : 0 ≤ X * T := mul_nonneg hX0 hT0
  have e1 : C₁ ^ 2 * (9 * (3 : ℝ) ^ n) * ((3 : ℝ) ^ n * (K₁ * θ ^ n + K₂ * T)) =
      9 * C₁ ^ 2 * K₁ * (X * θ ^ n) + 9 * C₁ ^ 2 * K₂ * (X * T) := by rw [hX]; ring
  have e2 : (B + 9 * C₁ ^ 2 * (K₁ + K₂)) * X * (θ ^ n + T) =
      B * (X * θ ^ n) + 9 * C₁ ^ 2 * K₁ * (X * θ ^ n) + 9 * C₁ ^ 2 * K₂ * (X * T) +
        (B * (X * T) + 9 * C₁ ^ 2 * K₁ * (X * T) + 9 * C₁ ^ 2 * K₂ * (X * θ ^ n)) := by ring
  have hrest : 0 ≤ B * (X * T) + 9 * C₁ ^ 2 * K₁ * (X * T) + 9 * C₁ ^ 2 * K₂ * (X * θ ^ n) := by
    positivity
  rw [e2]
  rw [e1] at hbig
  have hB9' : B ≤ B * (X * θ ^ n) := by rw [hX]; exact hB9
  linarith

end QSH
