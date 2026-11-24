import QuantitativeStochasticHomogenization.Ch02.Sec02.SubcubeVariance

/-!
# Lemma 2.13: the variance of the mean gradient of the maximizer of `J`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Lemma 2.13, (2.34): there are `κ(d) > 0` and `C < ∞` such that for every law satisfying
(0.10)–(0.11), `p, q ∈ B₁` and `m ∈ ℕ`,
`var[⨍_{□_m} ∇v(·, □_m, p, q)] ≤ C 3^{-mκ} + C Σ_{n=0}^m 3^{-κ(m-n)} τ_n` (`lemma_2_13`); the
constant `C` depends only on `d`.

The proof is the book's. By (2.43) the mean gradient is `M_n = a*⁻¹(□_n) q - p`
(`meanGradient`). Step 1 (`integral_euclideanSq_meanGradient_succ_sub_le`):
`E|M_{n+1} - 3^{-d} Σ_z M(z + □_n)|² ≤ 2 τ_n`. Step 2: the `M(z + □_n)` have the law of `M_n`
(stationarity), and for `n ≥ 1` the two opposite corner subcubes of `□_{n+1}` are at distance
`3ⁿ > 1`, so the components of their mean gradients are independent; hence
`var[3^{-d} Σ_z M(z + □_n)] ≤ (1 - 2·9^{-d}) var[M_n]` (`vecVariance_smul_sum_le_of_indepFun`).
Step 3: by `var[X + Y] ≤ (1 + t) var[Y] + (1 + t⁻¹) var[X]` with `t = 9^{-d}`,
`σ²_{n+1} ≤ (1 - 9^{-d}) σ²_n + 2(1 + 9^d) τ_n` for `n ≥ 1`, and iteration with `σ²_1 ≤ 4` gives
(2.34) with `3^{-κ} = 1 - 9^{-d}`. The book separates the subcubes at distance `1`, the unit range
of dependence of (0.11); the separation in `LawHypotheses` is larger than `1`, which the corner
subcubes of `□_1` do not have, so the contraction is used from `n = 1` on, and the book's
recursion for `σ_n` is replaced by the same recursion for `σ²_n` (Young's inequality in place of the
triangle inequality).
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The mean gradient -/

theorem measurable_meanGradient_apply {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (hΛ : 0 ≤ Λ) (p q : Vec d) (i : Fin d) :
    Measurable fun a : CoefficientField d Λ => meanGradient a U p q i := by
  unfold meanGradient
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  exact (Finset.measurable_sum _ fun j _ =>
    (measurable_coarseDualInvMatrix_apply hU0 hU hΛ i j).mul_const _).sub_const _

theorem measurable_meanGradient_apply_localSigma {U : Set (Vec d)} (hUo : IsOpen U)
    (hUc : Uᶜ.Nonempty) (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (p q : Vec d)
    (i : Fin d) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma U) _ fun a => meanGradient a U p q i := by
  unfold meanGradient
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  exact (Finset.measurable_sum _ fun j _ =>
    (measurable_coarseDualInvMatrix_apply_localSigma hUo hUc hU0 hU hΛ i j).mul_const _).sub_const _

theorem euclideanSq_sub_le_two (v w : Vec d) :
    euclideanSq (v - w) ≤ 2 * euclideanSq v + 2 * euclideanSq w := by
  simp only [euclideanSq, dot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (v i + w i)]

/-- `|M(U)|² ≤ 4` for `p, q ∈ B₁`. -/
theorem euclideanSq_meanGradient_le [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty)
    {p q : Vec d} (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) :
    euclideanSq (meanGradient a U p q) ≤ 4 := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le (one_le_of_coefficientField a)
  have h0 : ∀ v : Vec d, 0 ≤ dot v ((coarseDualInvMatrix a U).mulVec v) := fun v =>
    (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg v)).trans
      (inv_mul_le_dot_coarseDualInvMatrix a hUo hUb hUc hne v)
  have h1 : ∀ v : Vec d, dot v ((coarseDualInvMatrix a U).mulVec v) ≤ 1 * euclideanSq v :=
    fun v => by rw [one_mul]; exact dot_coarseDualInvMatrix_le a hUo hUb hUc hne v
  have hA := euclideanSq_mulVec_le_of_dot_le (coarseDualInvMatrix_transpose a hUo hUb hUc hne)
    h0 h1 q
  have hp1 := euclideanSq_le_one_of_mem_originBall hp
  have hq1 := euclideanSq_le_one_of_mem_originBall hq
  have h := euclideanSq_sub_le_two ((coarseDualInvMatrix a U).mulVec q) p
  unfold meanGradient
  nlinarith

theorem memLp_meanGradient_apply [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 0 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) {p q : Vec d}
    (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) (i : Fin d) :
    MemLp (fun a => meanGradient a U p q i) 2 P :=
  memLp_two_of_bound (measurable_meanGradient_apply (hUo.measure_pos volume hne).ne'
    hUb.measure_lt_top.ne hΛ p q i) fun a =>
      (sq_apply_le_euclideanSq _ i).trans (euclideanSq_meanGradient_le a hUo hUb hUc hne hp hq)

/-- **Stationarity of the mean gradient** on the subcubes of `□_{n+1}`. -/
theorem meanGradient_triadicSubcube (a : CoefficientField d Λ) (n : ℕ) (k : Fin d → Fin 3)
    (p q : Vec d) :
    meanGradient a (triadicSubcube n k) p q =
      meanGradient (translate (latticeShift (subcubeOffset n k)) a) (triadicCube d n) p q := by
  unfold meanGradient triadicSubcube
  rw [coarseDualInvMatrix_preimage_sub _ a (isOpen_triadicCube n)]

theorem vecVariance_comp_translate {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (z : LatticeIndex d) {X : CoefficientField d Λ → Vec d} (hX : ∀ i, Measurable fun a => X a i) :
    vecVariance P (fun a => X (translate (latticeShift z) a)) = vecVariance P X := by
  unfold vecVariance
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : ∫ a, X (translate (latticeShift z) a) i ∂P = ∫ a, X a i ∂P :=
    integral_comp_translate hP z (hX i)
  rw [hm]
  exact integral_comp_translate hP z (f := fun a => (X a i - ∫ b, X b i ∂P) ^ 2)
    (((hX i).sub_const _).pow_const 2)

/-! ## Independence of the corner subcubes -/

theorem triadicSubcube_compl_nonempty (n : ℕ) (k : Fin d → Fin 3) [NeZero d] :
    (triadicSubcube n k)ᶜ.Nonempty := by
  refine ⟨fun _ => (3 : ℝ) ^ (n + 1), fun hx => ?_⟩
  have h := mem_triadicCube_iff.mp (triadicSubcube_subset n k hx) 0
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n + 1) := by positivity
  rw [abs_of_pos h3] at h
  linarith

/-- The opposite corner subcubes `3ⁿ(0 - 1) + □_n` and `3ⁿ(2 - 1) + □_n` of `□_{n+1}` are at
distance at least `3ⁿ`. -/
theorem le_euclideanNorm_sub_of_corner [NeZero d] {n : ℕ} {x y : Vec d}
    (hx : x ∈ triadicSubcube n (fun _ => 0)) (hy : y ∈ triadicSubcube n (fun _ => 2)) :
    (3 : ℝ) ^ n ≤ euclideanNorm (x - y) := by
  have hx0 := mem_triadicSubcube_iff.mp hx 0
  have hy0 := mem_triadicSubcube_iff.mp hy 0
  simp only [Fin.isValue, Fin.val_zero, Nat.cast_zero, zero_sub, neg_one_mul, Fin.val_two,
    Nat.cast_ofNat] at hx0 hy0
  have h1 := (abs_lt.mp hx0)
  have h2 := (abs_lt.mp hy0)
  have h := abs_apply_le_euclideanNorm (x - y) 0
  rw [Pi.sub_apply] at h
  have h3 : (3 : ℝ) ^ n ≤ |x 0 - y 0| := by
    rw [abs_sub_comm, abs_of_pos (by nlinarith)]
    nlinarith
  exact h3.trans h

theorem indepFun_meanGradient_corner [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) {n : ℕ} (hn : 1 ≤ n) (p q : Vec d) (i : Fin d) :
    IndepFun (fun a => meanGradient a (triadicSubcube n (fun _ => 0)) p q i)
      (fun a => meanGradient a (triadicSubcube n (fun _ => 2)) p q i) P := by
  set U := triadicSubcube (d := d) n (fun _ => 0)
  set W := triadicSubcube (d := d) n (fun _ => 2)
  have hsep : ∃ t : ℝ, 1 < t ∧ ∀ x ∈ U, ∀ y ∈ W, t ≤ euclideanNorm (x - y) :=
    ⟨(3 : ℝ) ^ n, one_lt_pow₀ (by norm_num) (by omega), fun x hx y hy =>
      le_euclideanNorm_sub_of_corner hx hy⟩
  have hind := hP.2.2 U W (isOpen_triadicSubcube n _).measurableSet
    (isOpen_triadicSubcube n _).measurableSet hsep
  have hmeas : ∀ k : Fin d → Fin 3, @Measurable (CoefficientField d Λ) ℝ
      (localSigma (triadicSubcube n k)) _ fun a => meanGradient a (triadicSubcube n k) p q i :=
    fun k => measurable_meanGradient_apply_localSigma (isOpen_triadicSubcube n k)
      (triadicSubcube_compl_nonempty n k)
      ((isOpen_triadicSubcube n k).measure_pos volume (triadicSubcube_nonempty n k)).ne'
      (isBounded_triadicSubcube n k).measure_lt_top.ne hΛ p q i
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind (hmeas _).comap_le)
    (hmeas _).comap_le

/-! ## Step 1 in expectation -/

/-- **Step 1 of Lemma 2.13**: `E|M_{n+1} - 3^{-d} Σ_z M(z + □_n)|² ≤ 2 τ_n` for `p, q ∈ B₁`. -/
theorem integral_euclideanSq_meanGradient_succ_sub_le [NeZero d]
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n : ℕ) {p q : Vec d}
    (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) :
    ∫ a, euclideanSq (meanGradient a (triadicCube d (n + 1)) p q -
        (1 / 3 ^ d : ℝ) • ∑ k : Fin d → Fin 3, meanGradient a (triadicSubcube n k) p q) ∂P ≤
      2 * additivityDefect P n := by
  have : IsProbabilityMeasure P := hP.1
  have hJn := integrable_dualityDefect (P := P) hΛ (isOpen_triadicCube' (d := d) (n + 1))
    (isBounded_triadicCube (n + 1)) (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1)) hp hq
  have hJk : ∀ k : Fin d → Fin 3, Integrable (fun a => dualityDefect a (triadicSubcube n k) p q) P :=
    fun k => integrable_dualityDefect hΛ (isOpen_triadicSubcube n k) (isBounded_triadicSubcube n k)
      (convex_triadicSubcube n k) (triadicSubcube_nonempty n k) hp hq
  have hsum : Integrable (fun a => ∑ k : Fin d → Fin 3, (1 / 3 ^ d : ℝ) *
      dualityDefect a (triadicSubcube n k) p q) P :=
    integrable_finsetSum _ fun k _ => (hJk k).const_mul _
  have hR : Integrable (fun a => 2 * (∑ k : Fin d → Fin 3, (1 / 3 ^ d : ℝ) *
      dualityDefect a (triadicSubcube n k) p q - dualityDefect a (triadicCube d (n + 1)) p q)) P :=
    (hsum.sub hJn).const_mul 2
  refine (integral_mono_of_nonneg (Eventually.of_forall fun a => euclideanSq_nonneg _) hR
    (Eventually.of_forall fun a => euclideanSq_meanGradient_succ_sub_le a n p q)).trans ?_
  rw [integral_const_mul, integral_sub hsum hJn, integral_finsetSum _ fun k _ => (hJk k).const_mul _]
  simp only [integral_const_mul, integral_dualityDefect_triadicSubcube hP hΛ n _ p q]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
  have := sub_le_additivityDefect (P := P) hΛ n hp hq
  linarith

/-! ## The recursion -/

theorem memLp_smul_sum_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    [Fintype ι] {Z : ι → Ω → Vec d} (w : ℝ) (hZ : ∀ k i, MemLp (fun ω => Z k ω i) 2 P)
    (i : Fin d) : MemLp (fun ω => (w • ∑ k, Z k ω) i) 2 P := by
  have e : (fun ω => (w • ∑ k, Z k ω) i) = fun ω => w * ∑ k, Z k ω i := by
    funext ω
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [e]
  exact (memLp_finsetSum _ fun k _ => hZ k i).const_mul w

/-- `σ²_n ≤ 4`. -/
theorem vecVariance_meanGradient_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 0 ≤ Λ) (n : ℕ) {p q : Vec d} (hp : p ∈ originBall d 1)
    (hq : q ∈ originBall d 1) :
    vecVariance P (fun a => meanGradient a (triadicCube d n) p q) ≤ 4 := by
  refine (vecVariance_le_integral_euclideanSq fun i => memLp_meanGradient_apply hΛ
    (isOpen_triadicCube' n) (isBounded_triadicCube n) (convex_triadicCube n)
    (triadicCube_nonempty n) hp hq i).trans ?_
  have h := integral_mono_of_nonneg (Eventually.of_forall fun a => euclideanSq_nonneg _)
    (integrable_const (μ := P) (4 : ℝ)) (Eventually.of_forall fun a =>
      euclideanSq_meanGradient_le a (isOpen_triadicCube' (d := d) n) (isBounded_triadicCube n)
        (convex_triadicCube n) (triadicCube_nonempty n) hp hq)
  rwa [integral_const, probReal_univ, one_smul] at h

/-- **The recursion** `σ²_{n+1} ≤ (1 - 9^{-d}) σ²_n + 2 (1 + 9^d) τ_n` for `n ≥ 1`. -/
theorem vecVariance_meanGradient_succ_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) {n : ℕ} (hn : 1 ≤ n) {p q : Vec d}
    (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) :
    vecVariance P (fun a => meanGradient a (triadicCube d (n + 1)) p q) ≤
      (1 - 1 / 9 ^ d) * vecVariance P (fun a => meanGradient a (triadicCube d n) p q) +
        2 * (1 + 9 ^ d) * additivityDefect P n := by
  have : IsProbabilityMeasure P := hP.1
  set w : ℝ := 1 / 3 ^ d with hw
  set Z : (Fin d → Fin 3) → CoefficientField d Λ → Vec d := fun k a =>
    meanGradient a (triadicSubcube n k) p q with hZdef
  set Y : CoefficientField d Λ → Vec d := fun a => w • ∑ k, Z k a with hYdef
  set X : CoefficientField d Λ → Vec d := fun a =>
    meanGradient a (triadicCube d (n + 1)) p q - Y a with hXdef
  set σ2 := vecVariance P (fun a => meanGradient a (triadicCube d n) p q) with hσ2
  have hZm : ∀ k i, Measurable fun a => Z k a i := fun k i =>
    measurable_meanGradient_apply ((isOpen_triadicSubcube n k).measure_pos volume
      (triadicSubcube_nonempty n k)).ne' (isBounded_triadicSubcube n k).measure_lt_top.ne hΛ p q i
  have hZ : ∀ k i, MemLp (fun a => Z k a i) 2 P := fun k i =>
    memLp_meanGradient_apply hΛ (isOpen_triadicSubcube n k) (isBounded_triadicSubcube n k)
      (convex_triadicSubcube n k) (triadicSubcube_nonempty n k) hp hq i
  have hM : ∀ i, MemLp (fun a => meanGradient a (triadicCube d (n + 1)) p q i) 2 P := fun i =>
    memLp_meanGradient_apply hΛ (isOpen_triadicCube' (n + 1)) (isBounded_triadicCube (n + 1))
      (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1)) hp hq i
  have hY : ∀ i, MemLp (fun a => Y a i) 2 P := memLp_smul_sum_apply w hZ
  have hX : ∀ i, MemLp (fun a => X a i) 2 P := fun i => (hM i).sub (hY i)
  -- stationarity
  have hvar : ∀ k, vecVariance P (Z k) = σ2 := fun k => by
    have e : Z k = fun a => meanGradient (translate (latticeShift (subcubeOffset n k)) a)
        (triadicCube d n) p q := funext fun a => meanGradient_triadicSubcube a n k p q
    rw [e]
    exact vecVariance_comp_translate hP _ fun i => measurable_meanGradient_apply
      (volume_triadicCube_ne_zero d n) (volume_triadicCube_ne_top d n) hΛ p q i
  -- Step 2: the variance of the average over the subcubes
  have hk : (fun _ : Fin d => (0 : Fin 3)) ≠ fun _ => 2 := fun h => by
    have := congrFun h 0
    exact absurd this (by decide)
  have hYvar := vecVariance_smul_sum_le_of_indepFun (P := P) w hZm hZ hvar hk
    fun i => indepFun_meanGradient_corner hP hΛ hn p q i
  have hcard : (Fintype.card (Fin d → Fin 3) : ℝ) = 3 ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at hYvar
  have hY' : vecVariance P Y ≤ (1 - 2 / 9 ^ d) * σ2 := by
    refine hYvar.trans (le_of_eq ?_)
    rw [hw]
    have h3 : (0 : ℝ) < 3 ^ d := by positivity
    have h9 : (9 : ℝ) ^ d = (3 ^ d) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h9]
    field_simp
  -- Step 1
  have hXvar : vecVariance P X ≤ 2 * additivityDefect P n :=
    (vecVariance_le_integral_euclideanSq hX).trans
      (integral_euclideanSq_meanGradient_succ_sub_le hP hΛ n hp hq)
  -- Step 3: Young's inequality with `t = 9^{-d}`
  have ht : (0 : ℝ) < 1 / 9 ^ d := by positivity
  have hsplit : (fun a => meanGradient a (triadicCube d (n + 1)) p q) = fun a => X a + Y a :=
    funext fun a => (sub_add_cancel _ _).symm
  rw [hsplit]
  refine (vecVariance_add_le hX hY ht).trans ?_
  have hσ0 : 0 ≤ σ2 := vecVariance_nonneg _
  have hτ0 := additivityDefect_nonneg (P := P) hΛ n
  have h9 : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
  have hinv : (1 / 9 ^ d : ℝ)⁻¹ = 9 ^ d := by rw [one_div, inv_inv]
  rw [hinv]
  have e1 : (1 + 1 / 9 ^ d) * (1 - 2 / 9 ^ d) ≤ (1 - 1 / 9 ^ d : ℝ) := by
    have h0 : 0 < (9 : ℝ) ^ d := by positivity
    simp only [div_eq_mul_inv]
    have hi : 0 < ((9 : ℝ) ^ d)⁻¹ := inv_pos.mpr h0
    nlinarith
  have e2 := mul_le_mul_of_nonneg_left hY' (by positivity : (0 : ℝ) ≤ 1 + 1 / 9 ^ d)
  have e3 := mul_le_mul_of_nonneg_left hXvar (by positivity : (0 : ℝ) ≤ 1 + 9 ^ d)
  have e4 := mul_le_mul_of_nonneg_right e1 hσ0
  nlinarith

/-! ## The iteration -/

theorem le_of_recursion {σ τ : ℕ → ℝ} {ρ B K : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hB0 : 0 ≤ B)
    (hK : 0 ≤ K)
    (hτ : ∀ n, 0 ≤ τ n) (hσB : ∀ n, σ n ≤ B)
    (hrec : ∀ n, 1 ≤ n → σ (n + 1) ≤ ρ * σ n + K * τ n) (m : ℕ) :
    σ m ≤ B / ρ * ρ ^ m + K / ρ * ∑ n ∈ Finset.range (m + 1), ρ ^ (m - n) * τ n := by
  have hsum0 : ∀ j, 0 ≤ ∑ n ∈ Finset.range j, ρ ^ (j - 1 - n) * τ n := fun j =>
    Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hρ0.le _) (hτ n)
  -- the claim for `m = j + 1`
  have claim : ∀ j : ℕ, σ (j + 1) ≤ B * ρ ^ j + K * ∑ n ∈ Finset.range (j + 1), ρ ^ (j - n) * τ n := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero, mul_one, zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self]
      have := mul_nonneg hK (hτ 0)
      linarith [hσB 1]
    | succ j ih =>
      have h := hrec (j + 1) (by omega)
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, mul_add]
      have e : ∑ n ∈ Finset.range (j + 1), ρ ^ (j + 1 - n) * τ n =
          ρ * ∑ n ∈ Finset.range (j + 1), ρ ^ (j - n) * τ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnj : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        rw [Nat.succ_sub hnj, pow_succ]
        ring
      rw [e, pow_succ]
      have := mul_le_mul_of_nonneg_left ih hρ0.le
      nlinarith
  have hsumnn : ∀ j, 0 ≤ ∑ n ∈ Finset.range j, ρ ^ (m - n) * τ n := fun j =>
    Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hρ0.le _) (hτ n)
  have hKρ : 0 ≤ K / ρ := div_nonneg hK hρ0.le
  rcases m with _ | j
  · simp only [pow_zero, mul_one]
    have h1 : B ≤ B / ρ := by
      rw [le_div_iff₀ hρ0]
      nlinarith
    have := mul_nonneg hKρ (hsumnn 1)
    linarith [hσB 0]
  · have h := claim j
    have e1 : B * ρ ^ j = B / ρ * ρ ^ (j + 1) := by
      rw [pow_succ]
      field_simp
    have e2 : K * ∑ n ∈ Finset.range (j + 1), ρ ^ (j - n) * τ n =
        K / ρ * ∑ n ∈ Finset.range (j + 1), ρ ^ (j + 1 - n) * τ n := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnj : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [Nat.succ_sub hnj, pow_succ]
      field_simp
    have e3 : ∑ n ∈ Finset.range (j + 1), ρ ^ (j + 1 - n) * τ n ≤
        ∑ n ∈ Finset.range (j + 1 + 1), ρ ^ (j + 1 - n) * τ n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _))
        fun n _ _ => mul_nonneg (pow_nonneg hρ0.le _) (hτ n)
    rw [e1, e2] at h
    have := mul_le_mul_of_nonneg_left e3 hKρ
    linarith

/-! ## Lemma 2.13 -/

/-- **Lemma 2.13**, (2.34): there are `κ(d) > 0` and `C(d) < ∞` such that, for every law
satisfying (0.10)–(0.11), every `p, q ∈ B₁`, every `m ∈ ℕ` and every choice of the maximizers
`v(·, □_m, p, q)` of (2.9), the spatial averages `⨍_{□_m} ∇v(·, □_m, p, q)` are integrable and
`var[⨍_{□_m} ∇v(·, □_m, p, q)] ≤ C 3^{-mκ} + C Σ_{n=0}^m 3^{-κ(m-n)} τ_n`. -/
theorem lemma_2_13 [NeZero d] :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧ ∀ (Λ : ℝ) (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ p ∈ originBall d 1, ∀ q ∈ originBall d 1, ∀ m : ℕ,
      ∀ (v : CoefficientField d Λ → Vec d → ℝ) (g : CoefficientField d Λ → Vec d → Vec d),
        (∀ a, IsDefectMaximizer a (triadicCube d m) p q (v a) (g a)) →
        (∀ i, Integrable (fun a => ⨍ x in triadicCube d m, g a x i) P) ∧
        vecVariance P (fun a i => ⨍ x in triadicCube d m, g a x i) ≤
          C * (3 : ℝ) ^ (-(κ * m)) + C * ∑ n ∈ Finset.range (m + 1),
            (3 : ℝ) ^ (-(κ * ((m : ℝ) - n))) * additivityDefect P n := by
  set ρ : ℝ := 1 - 1 / 9 ^ d with hρdef
  have h9 : (1 : ℝ) < 9 ^ d := one_lt_pow₀ (by norm_num) (NeZero.ne d)
  have hρ0 : 0 < ρ := by
    rw [hρdef, sub_pos, div_lt_one (by positivity)]
    exact h9
  have hρ1 : ρ < 1 := by
    rw [hρdef]
    have : (0 : ℝ) < 1 / 9 ^ d := by positivity
    linarith
  set κ : ℝ := Real.logb 3 ρ⁻¹ with hκdef
  have hκ : 0 < κ := Real.logb_pos (by norm_num) (one_lt_inv₀ hρ0 |>.mpr hρ1)
  have h3κ : (3 : ℝ) ^ (-κ) = ρ := by
    rw [Real.rpow_neg (by norm_num), hκdef, Real.rpow_logb (by norm_num) (by norm_num)
      (inv_pos.mpr hρ0), inv_inv]
  have hpowκ : ∀ k : ℕ, (3 : ℝ) ^ (-(κ * k)) = ρ ^ k := fun k => by
    rw [← h3κ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  set K : ℝ := 2 * (1 + 9 ^ d) with hK
  refine ⟨κ, max (4 / ρ) (K / ρ), hκ, le_max_of_le_left (by positivity), ?_⟩
  intro Λ P hP p hp q hq m v g hmax
  have : IsProbabilityMeasure P := hP.1
  have hΛ : 0 ≤ Λ := by
    obtain ⟨a⟩ : Nonempty (CoefficientField d Λ) := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := measure_univ (μ := P)
      rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
      exact zero_ne_one this
    exact zero_le_one.trans (one_le_of_coefficientField a)
  have hfun : (fun a i => ⨍ x in triadicCube d m, g a x i) =
      fun a => meanGradient a (triadicCube d m) p q := by
    funext a
    exact (hmax a).setAverage_grad_eq (isOpen_triadicCube' m) (isBounded_triadicCube m)
      (convex_triadicCube m) (triadicCube_nonempty m)
  refine ⟨fun i => ?_, ?_⟩
  · have e : (fun a => ⨍ x in triadicCube d m, g a x i) =
        fun a => meanGradient a (triadicCube d m) p q i := by
      funext a
      exact congrFun (congrFun hfun a) i
    rw [e]
    exact (memLp_meanGradient_apply hΛ (isOpen_triadicCube' m) (isBounded_triadicCube m)
      (convex_triadicCube m) (triadicCube_nonempty m) hp hq i).integrable one_le_two
  rw [hfun]
  have hrec := le_of_recursion (σ := fun n => vecVariance P
      (fun a => meanGradient a (triadicCube d n) p q)) (τ := additivityDefect P) hρ0 hρ1.le
    (by norm_num) (by positivity) (fun n => additivityDefect_nonneg hΛ n)
    (fun n => vecVariance_meanGradient_le hΛ n hp hq)
    (fun n hn => vecVariance_meanGradient_succ_le hP hΛ hn hp hq) m
  refine hrec.trans ?_
  have hC1 : 4 / ρ ≤ max (4 / ρ) (K / ρ) := le_max_left _ _
  have hC2 : K / ρ ≤ max (4 / ρ) (K / ρ) := le_max_right _ _
  have hpm : (3 : ℝ) ^ (-(κ * m)) = ρ ^ m := hpowκ m
  have hterm : ∀ n ∈ Finset.range (m + 1),
      (3 : ℝ) ^ (-(κ * ((m : ℝ) - n))) = ρ ^ (m - n) := fun n hn => by
    have hnm : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [← hpowκ (m - n), Nat.cast_sub hnm]
  have hsum_eq : ∑ n ∈ Finset.range (m + 1),
      (3 : ℝ) ^ (-(κ * ((m : ℝ) - n))) * additivityDefect P n =
      ∑ n ∈ Finset.range (m + 1), ρ ^ (m - n) * additivityDefect P n :=
    Finset.sum_congr rfl fun n hn => by rw [hterm n hn]
  rw [hpm, hsum_eq]
  have hs0 : 0 ≤ ∑ n ∈ Finset.range (m + 1), ρ ^ (m - n) * additivityDefect P n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hρ0.le _) (additivityDefect_nonneg hΛ n)
  have hρm : 0 ≤ ρ ^ m := pow_nonneg hρ0.le m
  have := mul_le_mul_of_nonneg_right hC1 hρm
  have := mul_le_mul_of_nonneg_right hC2 hs0
  linarith

end QSH
