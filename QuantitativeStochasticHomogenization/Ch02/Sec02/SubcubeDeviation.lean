import QuantitativeStochasticHomogenization.Ch02.Sec02.PartitionMeanGradient

/-!
# The deviations of the subcube averages of the gradient of the maximizer

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Step 2 of the proof of Lemma 2.15, before expectations: for the maximizer
`v = v(·, □_{k+r}, p, q)` with gradient `g` and any vectors `c, c'`,
`3^{-dr} Σ_z |(g)_{z + □_k} - c|² ≤ 3 (2 (3^{-dr} Σ_z J(z + □_k) - J(□_{k+r}))
  + 3^{-dr} Σ_z |M(z + □_k) - c'|² + |c' - c|²)` (`sum_euclideanSq_vectorAverage_sub_le`), the
triangle inequality of the book written for squares, with Jensen's inequality and Lemma 2.12 for the
first term and (2.43) for the second. The right side is a measurable function of the coefficient
field. Also: `E J(□_k) - E J(□_{k+r}) ≤ Σ_{j=k}^{k+r-1} τ_j`
(`integral_dualityDefect_sub_le_sum`) and `σ²_{n+1} ≤ 2 σ²_n + 4 τ_n`
(`vecVariance_meanGradient_succ_le_two`), and Lemma 2.13 for the mean gradients
(`exists_vecVariance_meanGradient_le`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem euclideanSq_add_add_le_three (x y z : Vec d) :
    euclideanSq (x + y + z) ≤ 3 * (euclideanSq x + euclideanSq y + euclideanSq z) := by
  simp only [euclideanSq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    nlinarith [sq_nonneg (x i - y i), sq_nonneg (x i - z i), sq_nonneg (y i - z i)]

theorem vectorAverage_sub {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {G H : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict U)) (hH : MemLp H 2 (volume.restrict U)) :
    vectorAverage U (fun x => G x - H x) = vectorAverage U G - vectorAverage U H := by
  have := isFiniteMeasure_restrict.mpr hU
  funext i
  simp only [vectorAverage, Pi.sub_apply]
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub
    ((MemLp.eval hG i).integrable one_le_two) ((MemLp.eval hH i).integrable one_le_two), smul_sub]

theorem vectorAverage_sub_const {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (G : Vec d → Vec d) (hG : MemLp G 2 (volume.restrict U)) (c : Vec d) :
    vectorAverage U (fun x => G x - c) = vectorAverage U G - c := by
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  funext i
  simp only [vectorAverage, Pi.sub_apply]
  rw [setAverage_eq, setAverage_eq, integral_sub ((MemLp.eval hG i).integrable one_le_two)
    (integrable_const _), integral_const, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    measureReal_restrict_apply_univ]
  field_simp

/-- **Step 2 of Lemma 2.15, pointwise.** -/
theorem sum_euclideanSq_vectorAverage_sub_le [NeZero d] (a : CoefficientField d Λ) (k r : ℕ)
    (p q c c' : Vec d) {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : IsDefectMaximizer a (triadicCube d (k + r)) p q v g) :
    1 / ((3 : ℝ) ^ r) ^ d * ∑ z : Fin d → Fin (3 ^ r),
        euclideanSq (vectorAverage (partitionCube k r z) (fun x => g x - c)) ≤
      3 * (2 * (∑ z : Fin d → Fin (3 ^ r), 1 / ((3 : ℝ) ^ r) ^ d *
          dualityDefect a (partitionCube k r z) p q - dualityDefect a (triadicCube d (k + r)) p q) +
        ∑ z : Fin d → Fin (3 ^ r), 1 / ((3 : ℝ) ^ r) ^ d *
          euclideanSq (meanGradient a (partitionCube k r z) p q - c') +
        euclideanSq (c' - c)) := by
  set w : ℝ := 1 / ((3 : ℝ) ^ r) ^ d with hw
  have hw0 : 0 ≤ w := by positivity
  have hUb := isBounded_triadicCube (d := d) (k + r)
  have hUfin : volume (triadicCube d (k + r)) ≠ ⊤ := volume_triadicCube_ne_top d (k + r)
  choose wk h hwk using fun z => exists_isDefectMaximizer a (isOpen_partitionCube k r z)
    (isBounded_partitionCube k r z) (convex_partitionCube k r z) (partitionCube_nonempty k r z) p q
  have hS := sum_setAverage_euclideanSq_sub_le a hUb (isOpen_partitionCube k r)
    (pairwise_disjoint_partitionCube k r) (partitionCube_subset k r)
    (volume_triadicCube_diff_partitionCube k r) hw0 (fun z => volumeReal_partitionCube_div k r z)
    p q hv hwk
  have hgU : MemLp g 2 (volume.restrict (triadicCube d (k + r))) := hv.1.1.2.1
  have hQfin : ∀ z : Fin d → Fin (3 ^ r), volume (partitionCube k r z) ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top hUfin (measure_mono (partitionCube_subset k r z))
  have hQ0 : ∀ z : Fin d → Fin (3 ^ r), volume (partitionCube k r z) ≠ 0 := fun z =>
    ((isOpen_partitionCube k r z).measure_pos volume (partitionCube_nonempty k r z)).ne'
  have hgQ : ∀ z : Fin d → Fin (3 ^ r), MemLp g 2 (volume.restrict (partitionCube k r z)) :=
    fun z => hgU.mono_measure (Measure.restrict_mono (partitionCube_subset k r z) le_rfl)
  have hpt : ∀ z : Fin d → Fin (3 ^ r),
      euclideanSq (vectorAverage (partitionCube k r z) (fun x => g x - c)) ≤
        3 * ((⨍ x in partitionCube k r z, euclideanSq (g x - h z x)) +
          euclideanSq (meanGradient a (partitionCube k r z) p q - c') + euclideanSq (c' - c)) := by
    intro z
    have hM : meanGradient a (partitionCube k r z) p q = vectorAverage (partitionCube k r z) (h z) :=
      ((hwk z).setAverage_grad_eq (isOpen_partitionCube k r z) (isBounded_partitionCube k r z)
        (convex_partitionCube k r z) (partitionCube_nonempty k r z)).symm
    have e : vectorAverage (partitionCube k r z) (fun x => g x - c) =
        vectorAverage (partitionCube k r z) (fun x => g x - h z x) +
          (meanGradient a (partitionCube k r z) p q - c') + (c' - c) := by
      rw [vectorAverage_sub_const (hQ0 z) (hQfin z) g (hgQ z) c,
        vectorAverage_sub (hQfin z) (hgQ z) (hwk z).1.1.2.1, hM]
      abel
    rw [e]
    refine (euclideanSq_add_add_le_three _ _ _).trans ?_
    have hJ := euclideanSq_vectorAverage_le (hQ0 z) (hQfin z) ((hgQ z).sub (hwk z).1.1.2.1)
    have : euclideanSq (vectorAverage (partitionCube k r z) (fun x => g x - h z x)) ≤
        ⨍ x in partitionCube k r z, euclideanSq (g x - h z x) := hJ
    linarith
  have hsum := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpt z) hw0
  have hcard : ∑ _z : Fin d → Fin (3 ^ r), w * euclideanSq (c' - c) = euclideanSq (c' - c) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      mul_comm (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) w, hw, partition_weight_mul_card, one_mul]
  have e2 : ∑ z : Fin d → Fin (3 ^ r), w * (3 * ((⨍ x in partitionCube k r z,
      euclideanSq (g x - h z x)) + euclideanSq (meanGradient a (partitionCube k r z) p q - c') +
        euclideanSq (c' - c))) =
      3 * (∑ z, w * (⨍ x in partitionCube k r z, euclideanSq (g x - h z x)) +
        ∑ z, w * euclideanSq (meanGradient a (partitionCube k r z) p q - c') +
        ∑ _z : Fin d → Fin (3 ^ r), w * euclideanSq (c' - c)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [e2, hcard] at hsum
  rw [Finset.mul_sum]
  linarith

/-! ## Expectations -/

/-- `E J(□_k, p, q) - E J(□_{k+r}, p, q) ≤ Σ_{j=k}^{k+r-1} τ_j` for `p, q ∈ B₁`. -/
theorem integral_dualityDefect_sub_le_sum [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 0 ≤ Λ) {p q : Vec d} (hp : p ∈ originBall d 1)
    (hq : q ∈ originBall d 1) (k r : ℕ) :
    ∫ a, dualityDefect a (triadicCube d k) p q ∂P -
        ∫ a, dualityDefect a (triadicCube d (k + r)) p q ∂P ≤
      ∑ j ∈ Finset.Ico k (k + r), additivityDefect P j := by
  induction r with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have := sub_le_additivityDefect (P := P) hΛ (k + j) hp hq
    linarith

/-- `σ²_{n+1} ≤ 2 σ²_n + 4 τ_n`. -/
theorem vecVariance_meanGradient_succ_le_two [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n : ℕ) {p q : Vec d} (hp : p ∈ originBall d 1)
    (hq : q ∈ originBall d 1) :
    vecVariance P (fun a => meanGradient a (triadicCube d (n + 1)) p q) ≤
      2 * vecVariance P (fun a => meanGradient a (triadicCube d n) p q) +
        4 * additivityDefect P n := by
  have : IsProbabilityMeasure P := hP.1
  set w : ℝ := 1 / 3 ^ d with hw
  set Z : (Fin d → Fin 3) → CoefficientField d Λ → Vec d := fun k a =>
    meanGradient a (triadicSubcube n k) p q with hZdef
  set Y : CoefficientField d Λ → Vec d := fun a => w • ∑ k, Z k a with hYdef
  set X : CoefficientField d Λ → Vec d := fun a =>
    meanGradient a (triadicCube d (n + 1)) p q - Y a with hXdef
  have hZ : ∀ k i, MemLp (fun a => Z k a i) 2 P := fun k i =>
    memLp_meanGradient_apply hΛ (isOpen_triadicSubcube n k) (isBounded_triadicSubcube n k)
      (convex_triadicSubcube n k) (triadicSubcube_nonempty n k) hp hq i
  have hM : ∀ i, MemLp (fun a => meanGradient a (triadicCube d (n + 1)) p q i) 2 P := fun i =>
    memLp_meanGradient_apply hΛ (isOpen_triadicCube' (n + 1)) (isBounded_triadicCube (n + 1))
      (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1)) hp hq i
  have hY : ∀ i, MemLp (fun a => Y a i) 2 P := memLp_smul_sum_apply w hZ
  have hX : ∀ i, MemLp (fun a => X a i) 2 P := fun i => (hM i).sub (hY i)
  have hvar : ∀ k, vecVariance P (Z k) =
      vecVariance P (fun a => meanGradient a (triadicCube d n) p q) := fun k => by
    have e : Z k = fun a => meanGradient (translate (latticeShift (subcubeOffset n k)) a)
        (triadicCube d n) p q := funext fun a => meanGradient_triadicSubcube a n k p q
    rw [e]
    exact vecVariance_comp_translate hP _ fun i => measurable_meanGradient_apply
      (volume_triadicCube_ne_zero d n) (volume_triadicCube_ne_top d n) hΛ p q i
  have hYvar := vecVariance_smul_sum_le (P := P) w hZ hvar
  have hcard : (Fintype.card (Fin d → Fin 3) : ℝ) = 3 ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at hYvar
  have hY' : vecVariance P Y ≤ vecVariance P (fun a => meanGradient a (triadicCube d n) p q) := by
    refine hYvar.trans (le_of_eq ?_)
    rw [hw]
    have h3 : (0 : ℝ) < 3 ^ d := by positivity
    field_simp
  have hXvar : vecVariance P X ≤ 2 * additivityDefect P n :=
    (vecVariance_le_integral_euclideanSq hX).trans
      (integral_euclideanSq_meanGradient_succ_sub_le hP hΛ n hp hq)
  have hsplit : (fun a => meanGradient a (triadicCube d (n + 1)) p q) = fun a => X a + Y a :=
    funext fun a => (sub_add_cancel _ _).symm
  rw [hsplit]
  have h := vecVariance_add_le hX hY one_pos
  rw [inv_one] at h
  linarith

/-- **Lemma 2.13 for the mean gradients**: `σ²_m ≤ C 3^{-mκ} + C Σ_{n=0}^m 3^{-κ(m-n)} τ_n`. -/
theorem exists_vecVariance_meanGradient_le [NeZero d] :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧ ∀ (Λ : ℝ) (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ p ∈ originBall d 1, ∀ q ∈ originBall d 1, ∀ m : ℕ,
        vecVariance P (fun a => meanGradient a (triadicCube d m) p q) ≤
          C * (3 : ℝ) ^ (-(κ * m)) + C * ∑ n ∈ Finset.range (m + 1),
            (3 : ℝ) ^ (-(κ * ((m : ℝ) - n))) * additivityDefect P n := by
  obtain ⟨κ, C, hκ, hC, h⟩ := lemma_2_13 (d := d)
  refine ⟨κ, C, hκ, hC, fun Λ P hP p hp q hq m => ?_⟩
  choose v g hvg using fun a : CoefficientField d Λ => exists_isDefectMaximizer a
    (isOpen_triadicCube' m) (isBounded_triadicCube m) (convex_triadicCube m)
    (triadicCube_nonempty m) p q
  have h' := (h Λ P hP p hp q hq m v g hvg).2
  have hfun : (fun a i => ⨍ x in triadicCube d m, g a x i) =
      fun a => meanGradient a (triadicCube d m) p q := by
    funext a
    exact (hvg a).setAverage_grad_eq (isOpen_triadicCube' m) (isBounded_triadicCube m)
      (convex_triadicCube m) (triadicCube_nonempty m)
  rwa [hfun] at h'

end QSH
