import QuantitativeStochasticHomogenization.Ch02.Sec02.MaximizerMeasurability

/-!
# Mean gradients of the maximizers on the triadic partitions, and (2.44)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, the tools of the proofs of (2.44) and Lemma 2.15 on the partition of `□_{n+r}` into the
`3^{dr}` translates `z + □_n` (`partitionCube n r z`):

* Lemma 2.12 and `a ≥ Id`: `3^{-dr} Σ_z ⨍_{z + □_n} |∇v - ∇v_z|² ≤ 2 (3^{-dr} Σ_z J(z + □_n) - J(□_{n+r}))`
  (`sum_setAverage_euclideanSq_sub_le`, for any partition by open sets of equal volume), and the same
  bound for `|M(□_{n+r}) - 3^{-dr} Σ_z M(z + □_n)|²` (`euclideanSq_meanGradient_sub_le_partition`);
* stationarity: `E J(z + □_n) = E J(□_n)` and the mean gradients `M(z + □_n)` have the law of
  `M(□_n)` (`integral_dualityDefect_partitionCube`, `meanGradient_partitionCube`);
* `E M(U) = E[a*⁻¹(U)] q - p = ā_U⁻¹ q - p` (`integral_meanGradient_apply`), and **(2.44)**: for
  `m ≤ n` and `q ∈ B₁`, `|ā_n⁻¹ q - ā_m⁻¹ q|² ≤ 2 Σ_{k=m}^{n-1} τ_k`
  (`euclideanSq_expectedDualInvMatrix_sub_le`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The partition cubes -/

theorem convex_partitionCube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) : Convex ℝ (partitionCube n r k) :=
  convex_preimage_sub (convex_triadicCube n) _

theorem isBounded_partitionCube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    Bornology.IsBounded (partitionCube n r k) :=
  (isBounded_triadicCube (n + r)).subset (partitionCube_subset n r k)

theorem partitionCube_nonempty (n r : ℕ) (k : Fin d → Fin (3 ^ r)) : (partitionCube n r k).Nonempty :=
  ⟨latticeShift (partitionCenter n r k), by
    show latticeShift (partitionCenter n r k) - latticeShift (partitionCenter n r k) ∈ triadicCube d n
    rw [sub_self]
    exact mem_triadicCube_iff.mpr fun i => by simp⟩

theorem partition_weight_mul_card (r : ℕ) :
    1 / ((3 : ℝ) ^ r) ^ d * (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) = 1 := by
  rw [card_partitionIndex]
  have : (0 : ℝ) < ((3 : ℝ) ^ r) ^ d := by positivity
  field_simp

/-! ## Lemma 2.12 on a partition -/

/-- `⨍_V |G|² ≤ 2 ⨍_V ½ G·aG`, from `a ≥ Id`. -/
theorem setAverage_euclideanSq_le_two_mul (a : CoefficientField d Λ) {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) {G : Vec d → Vec d} (hG : MemLp G 2 (volume.restrict V)) :
    ⨍ x in V, euclideanSq (G x) ≤ 2 * ⨍ x in V, (1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)) := by
  have := isFiniteMeasure_restrict.mpr hV
  have hi1 : Integrable (fun x => euclideanSq (G x)) (volume.restrict V) :=
    integrable_euclideanSq_of_memLp hG
  have hi2 : Integrable (fun x => (1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)))
      (volume.restrict V) := (integrable_dot_mulVec a V hG).const_mul (1 / 2 : ℝ)
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm 2, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr measureReal_nonneg)
  rw [← integral_const_mul]
  refine integral_mono hi1 (hi2.const_mul 2) fun x => ?_
  have := (a.elliptic x (G x)).1
  show euclideanSq (G x) ≤ 2 * ((1 / 2 : ℝ) * dot (G x) ((a x).mulVec (G x)))
  linarith

/-- `Σ_k w ⨍_{Q_k} |∇v - ∇v_k|² ≤ 2 (Σ_k w J(Q_k) - J(U))` for a partition of `U` by open sets with
`|Q_k| / |U| = w`. -/
theorem sum_setAverage_euclideanSq_sub_le (a : CoefficientField d Λ) {ι : Type*} [Fintype ι]
    {U : Set (Vec d)} (hUb : Bornology.IsBounded U) {Q : ι → Set (Vec d)}
    (hQo : ∀ k, IsOpen (Q k)) (hdisj : Pairwise (Function.onFun Disjoint Q)) (hsub : ∀ k, Q k ⊆ U)
    (hcover : volume (U \ ⋃ k, Q k) = 0) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ k, volume.real (Q k) / volume.real U = w)
    (p q : Vec d) {v : Vec d → ℝ} {g : Vec d → Vec d} (hv : IsDefectMaximizer a U p q v g)
    {wk : ι → Vec d → ℝ} {h : ι → Vec d → Vec d}
    (hwk : ∀ k, IsDefectMaximizer a (Q k) p q (wk k) (h k)) :
    ∑ k, w * ⨍ x in Q k, euclideanSq (g x - h k x) ≤
      2 * (∑ k, w * dualityDefect a (Q k) p q - dualityDefect a U p q) := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hL := lemma_2_12 a hUb hQo hdisj hsub hcover p q hv hwk
  simp only [hw] at hL
  have hgU : MemLp g 2 (volume.restrict U) := hv.1.1.2.1
  rw [← hL, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hQ : volume (Q k) ≠ ⊤ := ne_top_of_le_ne_top hU (measure_mono (hsub k))
  have hgQ : MemLp g 2 (volume.restrict (Q k)) :=
    hgU.mono_measure (Measure.restrict_mono (hsub k) le_rfl)
  have hGk : MemLp (fun x => g x - h k x) 2 (volume.restrict (Q k)) := hgQ.sub (hwk k).1.1.2.1
  have h1 := setAverage_euclideanSq_le_two_mul a hQ hGk
  have h2 := mul_le_mul_of_nonneg_left h1 hw0
  linarith

/-- Jensen's inequality for the uniform average over `{0, …, 3^r - 1}^d`. -/
theorem sq_sum_partition_le (r : ℕ) (y : (Fin d → Fin (3 ^ r)) → ℝ) :
    (∑ k, 1 / ((3 : ℝ) ^ r) ^ d * y k) ^ 2 ≤ ∑ k, 1 / ((3 : ℝ) ^ r) ^ d * y k ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d → Fin (3 ^ r)))) (f := y)
  rw [Finset.card_univ, card_partitionIndex] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow]
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ r) ^ d := by positivity
  calc (1 / ((3 : ℝ) ^ r) ^ d) ^ 2 * (∑ k, y k) ^ 2
      ≤ (1 / ((3 : ℝ) ^ r) ^ d) ^ 2 * (((3 : ℝ) ^ r) ^ d * ∑ k, y k ^ 2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = 1 / ((3 : ℝ) ^ r) ^ d * ∑ k, y k ^ 2 := by field_simp

/-- **Step 1 of Lemma 2.13 on the partition of `□_{n+r}`**:
`|M(□_{n+r}) - 3^{-dr} Σ_z M(z + □_n)|² ≤ 2 (3^{-dr} Σ_z J(z + □_n) - J(□_{n+r}))`. -/
theorem euclideanSq_meanGradient_sub_le_partition [NeZero d] (a : CoefficientField d Λ)
    (n r : ℕ) (p q : Vec d) :
    euclideanSq (meanGradient a (triadicCube d (n + r)) p q -
        (1 / ((3 : ℝ) ^ r) ^ d) • ∑ k : Fin d → Fin (3 ^ r), meanGradient a (partitionCube n r k) p q) ≤
      2 * (∑ k : Fin d → Fin (3 ^ r), 1 / ((3 : ℝ) ^ r) ^ d * dualityDefect a (partitionCube n r k) p q -
        dualityDefect a (triadicCube d (n + r)) p q) := by
  set w : ℝ := 1 / ((3 : ℝ) ^ r) ^ d with hw
  have hw0 : 0 ≤ w := by positivity
  have hUo := isOpen_triadicCube' (d := d) (n + r)
  have hUb := isBounded_triadicCube (d := d) (n + r)
  have hUc := convex_triadicCube (d := d) (n + r)
  have hne := triadicCube_nonempty (d := d) (n + r)
  have hUfin : volume (triadicCube d (n + r)) ≠ ⊤ := volume_triadicCube_ne_top d (n + r)
  have : IsFiniteMeasure (volume.restrict (triadicCube d (n + r))) :=
    isFiniteMeasure_restrict.mpr hUfin
  obtain ⟨v, g, hv⟩ := exists_isDefectMaximizer a hUo hUb hUc hne p q
  choose wk h hwk using fun k => exists_isDefectMaximizer a (isOpen_partitionCube n r k)
    (isBounded_partitionCube n r k) (convex_partitionCube n r k) (partitionCube_nonempty n r k) p q
  have hS := sum_setAverage_euclideanSq_sub_le a hUb (isOpen_partitionCube n r)
    (pairwise_disjoint_partitionCube n r) (partitionCube_subset n r)
    (volume_triadicCube_diff_partitionCube n r) hw0 (fun k => volumeReal_partitionCube_div n r k)
    p q hv hwk
  have hgU : MemLp g 2 (volume.restrict (triadicCube d (n + r))) := hv.1.1.2.1
  have hQfin : ∀ k : Fin d → Fin (3 ^ r), volume (partitionCube n r k) ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hUfin (measure_mono (partitionCube_subset n r k))
  have hfinQ : ∀ k : Fin d → Fin (3 ^ r), IsFiniteMeasure (volume.restrict (partitionCube n r k)) := fun k =>
    isFiniteMeasure_restrict.mpr (hQfin k)
  have hQ0 : ∀ k : Fin d → Fin (3 ^ r), volume (partitionCube n r k) ≠ 0 := fun k =>
    ((isOpen_partitionCube n r k).measure_pos volume (partitionCube_nonempty n r k)).ne'
  have hgQ : ∀ k : Fin d → Fin (3 ^ r), MemLp g 2 (volume.restrict (partitionCube n r k)) := fun k =>
    hgU.mono_measure (Measure.restrict_mono (partitionCube_subset n r k) le_rfl)
  have hD : ∀ k : Fin d → Fin (3 ^ r), MemLp (fun x => g x - h k x) 2 (volume.restrict (partitionCube n r k)) :=
    fun k => (hgQ k).sub (hwk k).1.1.2.1
  set A : (Fin d → Fin (3 ^ r)) → Fin d → ℝ := fun k i =>
    ⨍ x in partitionCube n r k, (g x i - h k x i) with hAdef
  have hX : ∀ i, (meanGradient a (triadicCube d (n + r)) p q -
      w • ∑ k : Fin d → Fin (3 ^ r), meanGradient a (partitionCube n r k) p q) i =
      ∑ k, w * A k i := by
    intro i
    have hpart := setAverage_eq_sum_of_partition hUfin (isOpen_partitionCube n r)
      (pairwise_disjoint_partitionCube n r) (partitionCube_subset n r)
      (volume_triadicCube_diff_partitionCube n r) ((MemLp.eval hgU i).integrable one_le_two)
    simp only [volumeReal_partitionCube_div] at hpart
    have hQi : ∀ k : Fin d → Fin (3 ^ r), meanGradient a (partitionCube n r k) p q i =
        ⨍ x in partitionCube n r k, h k x i := fun k =>
      congrFun ((hwk k).setAverage_grad_eq (isOpen_partitionCube n r k)
        (isBounded_partitionCube n r k) (convex_partitionCube n r k)
        (partitionCube_nonempty n r k)).symm i
    have hUi : meanGradient a (triadicCube d (n + r)) p q i = ⨍ x in triadicCube d (n + r), g x i :=
      congrFun (hv.setAverage_grad_eq hUo hUb hUc hne).symm i
    rw [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hUi,
      Finset.sum_congr rfl fun k _ => hQi k, hpart, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hfinQ k
    have i1 := (MemLp.eval (hgQ k) i).integrable one_le_two
    have i2 := (MemLp.eval ((hwk k).1.1.2.1) i).integrable one_le_two
    have hsub : (⨍ x in partitionCube n r k, (g x i - h k x i)) =
        (⨍ x in partitionCube n r k, g x i) - ⨍ x in partitionCube n r k, h k x i := by
      rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub i1 i2, smul_sub]
    rw [hAdef]
    simp only
    rw [hsub]
    ring
  have hA2 : ∀ (k : Fin d → Fin (3 ^ r)) (i : Fin d), A k i ^ 2 ≤ ⨍ x in partitionCube n r k, (g x i - h k x i) ^ 2 := fun k i => by
    have := hfinQ k
    exact sq_setAverage_le (hQ0 k) (hQfin k) ((MemLp.eval (hD k) i).integrable one_le_two)
      (MemLp.eval (hD k) i).integrable_sq
  have hsumsq : ∀ k : Fin d → Fin (3 ^ r), ∑ i, ⨍ x in partitionCube n r k, (g x i - h k x i) ^ 2 =
      ⨍ x in partitionCube n r k, euclideanSq (g x - h k x) := fun k => by
    have := hfinQ k
    have hint : ∀ i, Integrable (fun x => (g x i - h k x i) ^ 2)
        (volume.restrict (partitionCube n r k)) := fun i => (MemLp.eval (hD k) i).integrable_sq
    rw [setAverage_eq, smul_eq_mul]
    simp only [euclideanSq, dot, Pi.sub_apply, ← sq]
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [setAverage_eq, smul_eq_mul]
  calc euclideanSq (meanGradient a (triadicCube d (n + r)) p q -
        w • ∑ k : Fin d → Fin (3 ^ r), meanGradient a (partitionCube n r k) p q)
      = ∑ i, (∑ k, w * A k i) ^ 2 := by simp only [euclideanSq, dot, ← sq, hX]
    _ ≤ ∑ i, ∑ k, w * A k i ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_sum_partition_le r (fun k => A k i)
    _ ≤ ∑ i, ∑ k, w * ⨍ x in partitionCube n r k, (g x i - h k x i) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hA2 k i) hw0
    _ = ∑ k, w * ⨍ x in partitionCube n r k, euclideanSq (g x - h k x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, hsumsq k]
    _ ≤ _ := hS

/-! ## Stationarity on the partition -/

theorem meanGradient_partitionCube (a : CoefficientField d Λ) (n r : ℕ) (k : Fin d → Fin (3 ^ r))
    (p q : Vec d) :
    meanGradient a (partitionCube n r k) p q =
      meanGradient (translate (latticeShift (partitionCenter n r k)) a) (triadicCube d n) p q := by
  unfold meanGradient partitionCube
  rw [coarseDualInvMatrix_preimage_sub _ a (isOpen_triadicCube n)]

theorem integral_dualityDefect_partitionCube {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n r : ℕ) (k : Fin d → Fin (3 ^ r)) (p q : Vec d) :
    ∫ a, dualityDefect a (partitionCube n r k) p q ∂P =
      ∫ a, dualityDefect a (triadicCube d n) p q ∂P := by
  have hf := measurable_dualityDefect (volume_triadicCube_ne_zero d n)
    (volume_triadicCube_ne_top d n) hΛ p q
  rw [← integral_comp_translate hP (partitionCenter n r k) hf]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact dualityDefect_preimage_sub _ a (isOpen_triadicCube n) (volume_triadicCube_ne_top d n) p q

theorem integral_meanGradient_partitionCube {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n r : ℕ) (k : Fin d → Fin (3 ^ r)) (p q : Vec d)
    (i : Fin d) :
    ∫ a, meanGradient a (partitionCube n r k) p q i ∂P =
      ∫ a, meanGradient a (triadicCube d n) p q i ∂P := by
  simp only [meanGradient_partitionCube]
  exact integral_comp_translate hP _ (f := fun a => meanGradient a (triadicCube d n) p q i)
    (measurable_meanGradient_apply (volume_triadicCube_ne_zero d n)
      (volume_triadicCube_ne_top d n) hΛ p q i)

/-! ## The expectation of the mean gradient and (2.44) -/

/-- `E M(U) = E[a*⁻¹(U)] q - p`. -/
theorem integral_meanGradient_apply [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) (p q : Vec d) (i : Fin d) :
    ∫ a, meanGradient a U p q i ∂P = ((expectedDualInvMatrix P U).mulVec q - p) i := by
  have hint := integrable_coarseDualInvMatrix_apply P hUo hUb hUc hne hΛ
  unfold meanGradient
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, expectedDualInvMatrix, Matrix.of_apply]
  rw [integral_sub (integrable_finsetSum _ fun j _ => (hint i j).mul_const _) (integrable_const _),
    integral_finsetSum _ fun j _ => (hint i j).mul_const _, integral_const, probReal_univ, one_smul]
  simp only [integral_mul_const]

theorem det_expectedDualInvMatrix_ne_zero [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) :
    (expectedDualInvMatrix P U).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hb := (expectedDualInvMatrix_bounds P hUo hUb hUc hne hΛ v).1
  rw [hv] at hb
  have hz : dot v 0 = 0 := by simp [dot]
  rw [hz] at hb
  have hpos : 0 < euclideanSq v := by
    have hne' : v ≠ 0 := hv0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne'
    have hi' : v i ≠ 0 := by simpa using hi
    have h1 := sq_apply_le_euclideanSq v i
    have h2 : 0 < v i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi'))
    linarith
  have hΛ0 : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  nlinarith

/-- `ā_U⁻¹ = E[a*⁻¹(U)]`. -/
theorem inv_averagedDualMatrix [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) :
    (averagedDualMatrix P U)⁻¹ = expectedDualInvMatrix P U := by
  unfold averagedDualMatrix
  exact Matrix.nonsing_inv_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (det_expectedDualInvMatrix_ne_zero hΛ hUo hUb hUc hne))

/-- **(2.44)**: for `q ∈ B₁` and `m ≤ m + r`, `|ā_{m+r}⁻¹ q - ā_m⁻¹ q|² ≤ 2 Σ_{k=m}^{m+r-1} τ_k`. -/
theorem euclideanSq_inv_averagedDualMatrix_sub_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 1 ≤ Λ) (m r : ℕ) {q : Vec d} (hq : q ∈ originBall d 1) :
    euclideanSq ((averagedDualMatrix P (triadicCube d (m + r)))⁻¹.mulVec q -
        (averagedDualMatrix P (triadicCube d m))⁻¹.mulVec q) ≤
      2 * ∑ k ∈ Finset.Ico m (m + r), additivityDefect P k := by
  have : IsProbabilityMeasure P := hP.1
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have h0 : (0 : Vec d) ∈ originBall d 1 := zero_mem_originBall
  rw [inv_averagedDualMatrix hΛ (isOpen_triadicCube' _) (isBounded_triadicCube _)
      (convex_triadicCube _) (triadicCube_nonempty _),
    inv_averagedDualMatrix hΛ (isOpen_triadicCube' _) (isBounded_triadicCube _)
      (convex_triadicCube _) (triadicCube_nonempty _)]
  set w : ℝ := 1 / ((3 : ℝ) ^ r) ^ d with hw
  set X : CoefficientField d Λ → Vec d := fun a => meanGradient a (triadicCube d (m + r)) 0 q -
    w • ∑ k : Fin d → Fin (3 ^ r), meanGradient a (partitionCube m r k) 0 q with hX
  have hMm : ∀ (U : Set (Vec d)), IsOpen U → Bornology.IsBounded U → Convex ℝ U → U.Nonempty →
      ∀ i, MemLp (fun a => meanGradient a U 0 q i) 2 P := fun U h1 h2 h3 h4 i =>
    memLp_meanGradient_apply hΛ0 h1 h2 h3 h4 h0 hq i
  have hXi : ∀ i, MemLp (fun a => X a i) 2 P := fun i => by
    have h1 := hMm _ (isOpen_triadicCube' (m + r)) (isBounded_triadicCube (m + r))
      (convex_triadicCube (m + r)) (triadicCube_nonempty (m + r)) i
    have h2 := memLp_smul_sum_apply (P := P) w (fun k i => hMm _ (isOpen_partitionCube m r k)
      (isBounded_partitionCube m r k) (convex_partitionCube m r k) (partitionCube_nonempty m r k) i) i
    exact h1.sub h2
  -- the expectation of `X`
  have hEX : ∀ i, ∫ a, X a i ∂P = ((expectedDualInvMatrix P (triadicCube d (m + r))).mulVec q -
      (expectedDualInvMatrix P (triadicCube d m)).mulVec q) i := fun i => by
    have hint : ∀ k : Fin d → Fin (3 ^ r), Integrable (fun a => meanGradient a (partitionCube m r k) 0 q i) P := fun k =>
      (hMm _ (isOpen_partitionCube m r k) (isBounded_partitionCube m r k)
        (convex_partitionCube m r k) (partitionCube_nonempty m r k) i).integrable one_le_two
    have e : (fun a => X a i) = fun a => meanGradient a (triadicCube d (m + r)) 0 q i -
        w * ∑ k : Fin d → Fin (3 ^ r), meanGradient a (partitionCube m r k) 0 q i := by
      funext a
      simp only [hX, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [e, integral_sub ((hMm _ (isOpen_triadicCube' (m + r)) (isBounded_triadicCube (m + r))
      (convex_triadicCube (m + r)) (triadicCube_nonempty (m + r)) i).integrable one_le_two)
      ((integrable_finsetSum _ fun k _ => hint k).const_mul w), integral_const_mul,
      integral_finsetSum _ fun k _ => hint k]
    simp only [integral_meanGradient_partitionCube hP hΛ0 m r _ 0 q i]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hw,
      partition_weight_mul_card, one_mul,
      integral_meanGradient_apply hΛ (isOpen_triadicCube' _) (isBounded_triadicCube _)
        (convex_triadicCube _) (triadicCube_nonempty _),
      integral_meanGradient_apply hΛ (isOpen_triadicCube' _) (isBounded_triadicCube _)
        (convex_triadicCube _) (triadicCube_nonempty _)]
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
  -- Jensen and Step 1
  have hJ : ∀ k : ℕ, Integrable (fun a => dualityDefect a (triadicCube d k) 0 q) P := fun k =>
    integrable_dualityDefect hΛ0 (isOpen_triadicCube' k) (isBounded_triadicCube k)
      (convex_triadicCube k) (triadicCube_nonempty k) h0 hq
  have hJQ : ∀ k : Fin d → Fin (3 ^ r), Integrable (fun a => dualityDefect a (partitionCube m r k) 0 q) P := fun k =>
    integrable_dualityDefect hΛ0 (isOpen_partitionCube m r k) (isBounded_partitionCube m r k)
      (convex_partitionCube m r k) (partitionCube_nonempty m r k) h0 hq
  have hsum : Integrable (fun a => ∑ k : Fin d → Fin (3 ^ r), w *
      dualityDefect a (partitionCube m r k) 0 q) P :=
    integrable_finsetSum _ fun k _ => (hJQ k).const_mul _
  have hR : Integrable (fun a => 2 * (∑ k : Fin d → Fin (3 ^ r), w *
      dualityDefect a (partitionCube m r k) 0 q - dualityDefect a (triadicCube d (m + r)) 0 q)) P :=
    (hsum.sub (hJ (m + r))).const_mul 2
  have hstep : ∫ a, euclideanSq (X a) ∂P ≤
      2 * (∫ a, dualityDefect a (triadicCube d m) 0 q ∂P -
        ∫ a, dualityDefect a (triadicCube d (m + r)) 0 q ∂P) := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun a => euclideanSq_nonneg _) hR
      (Eventually.of_forall fun a => euclideanSq_meanGradient_sub_le_partition a m r 0 q)).trans
      (le_of_eq ?_)
    rw [integral_const_mul, integral_sub hsum (hJ (m + r)),
      integral_finsetSum _ fun k _ => (hJQ k).const_mul _]
    simp only [integral_const_mul, integral_dualityDefect_partitionCube hP hΛ0 m r _ 0 q]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hw,
      mul_comm _ (1 / ((3 : ℝ) ^ r) ^ d), partition_weight_mul_card, one_mul]
  -- the telescoping sum of the additivity defects
  have htel : ∀ r' : ℕ, ∫ a, dualityDefect a (triadicCube d m) 0 q ∂P -
      ∫ a, dualityDefect a (triadicCube d (m + r')) 0 q ∂P ≤
        ∑ k ∈ Finset.Ico m (m + r'), additivityDefect P k := by
    intro r'
    induction r' with
    | zero => simp
    | succ j ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have := sub_le_additivityDefect (P := P) hΛ0 (m + j) h0 hq
      linarith
  have hsq : euclideanSq ((expectedDualInvMatrix P (triadicCube d (m + r))).mulVec q -
      (expectedDualInvMatrix P (triadicCube d m)).mulVec q) ≤ ∫ a, euclideanSq (X a) ∂P := by
    have e : ∫ a, euclideanSq (X a) ∂P = ∑ i, ∫ a, X a i ^ 2 ∂P := by
      simp only [euclideanSq, dot, ← sq]
      exact integral_finsetSum _ fun i _ => (hXi i).integrable_sq
    rw [e]
    simp only [euclideanSq, dot, ← sq]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← hEX i]
    exact sq_integral_le_integral_sq ((hXi i).integrable one_le_two) (hXi i).integrable_sq
  have h1 := htel r
  linarith

end QSH
