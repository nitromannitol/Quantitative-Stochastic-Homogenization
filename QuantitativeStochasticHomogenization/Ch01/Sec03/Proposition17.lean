import QuantitativeStochasticHomogenization.Ch01.Sec02.Lemma11
import QuantitativeStochasticHomogenization.Ch01.Sec03.LocalMeasurability
import QuantitativeStochasticHomogenization.Ch01.Sec03.TriadicPartition
import QuantitativeStochasticHomogenization.Ch03.Sec04.FrobeniusNorm

/-!
# Proposition 1.7: convergence of `a(□_m)` in `L¹(Ω, P)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3, (1.27) and Proposition 1.7, (1.30)–(1.32).

* `homogenizedMatrix P`: the matrix `ā` of Definition 1.2, `μ̄(p) = ½ p·āp`
  (`limitDirichletEnergy_eq_homogenizedMatrix`);
* `omegaModulus P n`: the modulus `ω(n) = sup_{p ∈ B₁} (E μ(□_n, p) - μ̄(p))` of (1.27), with its
  bound (`bddAbove_omegaModulus`) and its monotonicity;
* `integral_sq_posPart_le`: (1.31), `E[(μ(□_{n+r}, p) - E μ(□_n, p))₊²] ≤ C 3^{-dr}`, from the
  subadditivity on the partition of `□_{n+r}` into translates of `□_n`, the vanishing of the
  covariances of subcubes at distance at least `2` (unit range of dependence and (1.29)) and the
  bound `0 ≤ μ ≤ ½Λ|p|²` for the others;
* `integral_abs_sub_limitDirichletEnergy_le`: (1.32);
* `proposition_1_7`: (1.30), `E|a(□_m) - ā| ≤ C 3^{-dm/4} + C ω(⌈m/2⌉)` with `C` depending only on
  `d` and `Λ`, for the Frobenius norm of matrices.

In Step 2 the bound `E|μ(□_m, p) - μ̄(p)| ≤ 2 E[(μ(□_m, p) - E μ(□_n, p))₊] + 2ω(n)` is used; it
follows from the same three facts as the book's `… + ω(m) + 2ω(n)`.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The limit `μ̄` and the homogenized matrix -/

theorem limitDirichletEnergy_le_expected (P : Measure (CoefficientField d Λ)) (n : ℕ)
    (e : Vec d) : limitDirichletEnergy P e ≤ expectedDirichletEnergy P n e :=
  ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact expectedDirichletEnergy_nonneg P k e⟩ n

theorem limitDirichletEnergy_nonneg (P : Measure (CoefficientField d Λ)) (e : Vec d) :
    0 ≤ limitDirichletEnergy P e :=
  le_ciInf fun n => expectedDirichletEnergy_nonneg P n e

theorem limitDirichletEnergy_le {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (e : Vec d) : limitDirichletEnergy P e ≤ (1 / 2 : ℝ) * Λ * euclideanSq e :=
  (limitDirichletEnergy_le_expected P 0 e).trans (expectedDirichletEnergy_le hP hΛ 0 e)

theorem limitDirichletEnergy_parallelogram {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (e f : Vec d) :
    limitDirichletEnergy P (e + f) + limitDirichletEnergy P (e - f) =
      2 * limitDirichletEnergy P e + 2 * limitDirichletEnergy P f := by
  have h1 := (tendsto_expectedDirichletEnergy hP hΛ (e + f)).add
    (tendsto_expectedDirichletEnergy hP hΛ (e - f))
  have h2 := ((tendsto_expectedDirichletEnergy hP hΛ e).const_mul 2).add
    ((tendsto_expectedDirichletEnergy hP hΛ f).const_mul 2)
  simp_rw [expectedDirichletEnergy_parallelogram hP hΛ] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The homogenized matrix `ā`** of Definition 1.2. -/
def homogenizedMatrix (P : Measure (CoefficientField d Λ)) : Mat d :=
  polarizationMatrix (limitDirichletEnergy P)

theorem homogenizedMatrix_transpose {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) : (homogenizedMatrix P).transpose = homogenizedMatrix P :=
  polarizationMatrix_transpose (limitDirichletEnergy_parallelogram hP hΛ)

/-- `μ̄(p) = ½ p·āp`. -/
theorem limitDirichletEnergy_eq_homogenizedMatrix {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (e : Vec d) :
    limitDirichletEnergy P e = (1 / 2 : ℝ) * dot e ((homogenizedMatrix P).mulVec e) :=
  eq_half_dot_polarizationMatrix (limitDirichletEnergy_parallelogram hP hΛ)
    (by positivity : (0 : ℝ) ≤ 1 / 2 * Λ) (fun x => by
      rw [abs_of_nonneg (limitDirichletEnergy_nonneg P x)]
      exact limitDirichletEnergy_le hP hΛ x) e

/-! ## The modulus `ω` of (1.27) -/

theorem zero_mem_originBall : (0 : Vec d) ∈ originBall d 1 := by
  simp [originBall, euclideanNorm, euclideanSq, dot]

instance : Nonempty (originBall d 1) := ⟨⟨0, zero_mem_originBall⟩⟩

theorem euclideanSq_le_one_of_mem_originBall {p : Vec d} (hp : p ∈ originBall d 1) :
    euclideanSq p ≤ 1 := by
  have h : euclideanNorm p < 1 := hp
  have h0 : 0 ≤ euclideanNorm p := Real.sqrt_nonneg _
  rw [← euclideanNorm_sq]
  nlinarith

/-- **The modulus `ω(n)`** of (1.27): `sup_{p ∈ B₁} (E μ(□_n, p) - μ̄(p))`. -/
def omegaModulus (P : Measure (CoefficientField d Λ)) (n : ℕ) : ℝ :=
  ⨆ p : originBall d 1, (expectedDirichletEnergy P n p - limitDirichletEnergy P p)

theorem bddAbove_omegaModulus {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (n : ℕ) :
    BddAbove (range fun p : originBall d 1 =>
      expectedDirichletEnergy P n p - limitDirichletEnergy P p) := by
  refine ⟨(1 / 2 : ℝ) * Λ, ?_⟩
  rintro _ ⟨p, rfl⟩
  have h1 := expectedDirichletEnergy_le hP hΛ n p
  have h2 := limitDirichletEnergy_nonneg P p
  have h3 := euclideanSq_le_one_of_mem_originBall p.2
  have : (1 / 2 : ℝ) * Λ * euclideanSq (p : Vec d) ≤ (1 / 2 : ℝ) * Λ := by nlinarith
  simp only
  linarith

theorem sub_le_omegaModulus {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (n : ℕ) {p : Vec d} (hp : p ∈ originBall d 1) :
    expectedDirichletEnergy P n p - limitDirichletEnergy P p ≤ omegaModulus P n :=
  le_ciSup (f := fun p : originBall d 1 =>
    expectedDirichletEnergy P n p - limitDirichletEnergy P p) (bddAbove_omegaModulus hP hΛ n) ⟨p, hp⟩

theorem omegaModulus_nonneg {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (n : ℕ) : 0 ≤ omegaModulus P n :=
  (sub_nonneg.mpr (limitDirichletEnergy_le_expected P n 0)).trans
    (sub_le_omegaModulus hP hΛ n zero_mem_originBall)

theorem antitone_omegaModulus {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) : Antitone (omegaModulus P) := fun n _ hnm =>
  ciSup_le fun p => (sub_le_sub_right (antitone_expectedDirichletEnergy hP hΛ p hnm) _).trans
    (sub_le_omegaModulus hP hΛ n p.2)

/-! ## Step 1: the variance bound (1.31) -/

theorem card_near_le {N : ℕ} (k : Fin d → Fin N) :
    ((Finset.univ : Finset (Fin d → Fin N)).filter
      fun l => ∀ i, |((k i : ℕ) : ℤ) - ((l i : ℕ) : ℤ)| ≤ 2).card ≤ 5 ^ d := by
  set S : Fin d → Finset (Fin N) := fun i =>
    Finset.univ.filter fun j : Fin N => |((k i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ 2
  have hsub : ((Finset.univ : Finset (Fin d → Fin N)).filter
      fun l => ∀ i, |((k i : ℕ) : ℤ) - ((l i : ℕ) : ℤ)| ≤ 2) ⊆ Fintype.piFinset S := by
    intro l hl
    rw [Finset.mem_filter] at hl
    rw [Fintype.mem_piFinset]
    intro i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hl.2 i
  have hS : ∀ i, (S i).card ≤ 5 := by
    intro i
    have h := Finset.card_le_card_of_injOn (fun j : Fin N => ((j : ℕ) : ℤ))
      (s := S i) (t := Finset.Icc (((k i : ℕ) : ℤ) - 2) (((k i : ℕ) : ℤ) + 2))
      (fun j hj => by
        simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
        rw [Finset.coe_Icc, Set.mem_Icc]
        rw [abs_le] at hj
        constructor <;> linarith [hj.1, hj.2])
      (fun j _ j' _ h => Fin.ext (by
        have h' : ((j : ℕ) : ℤ) = ((j' : ℕ) : ℤ) := h
        exact_mod_cast h'))
    rw [Int.card_Icc] at h
    have : (((k i : ℕ) : ℤ) + 2 + 1 - (((k i : ℕ) : ℤ) - 2)).toNat = 5 := by omega
    rw [this] at h
    exact h
  calc _ ≤ (Fintype.piFinset S).card := Finset.card_le_card hsub
    _ = ∏ i, (S i).card := Fintype.card_piFinset S
    _ ≤ ∏ _i : Fin d, 5 := Finset.prod_le_prod fun i _ => hS i
    _ = 5 ^ d := by simp

theorem volume_partitionCube_ne_top (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    volume (partitionCube n r k) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_triadicCube_ne_top d (n + r)) (measure_mono (partitionCube_subset n r k))

theorem volume_partitionCube_ne_zero (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    volume (partitionCube n r k) ≠ 0 := by
  intro h
  have h1 := volumeReal_partitionCube (d := d) n r k
  rw [measureReal_def, h, ENNReal.toReal_zero] at h1
  have : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  linarith

theorem compl_partitionCube_nonempty [NeZero d] (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    (partitionCube n r k)ᶜ.Nonempty := by
  refine ⟨fun _ => (3 : ℝ) ^ (n + r), fun hx => ?_⟩
  have h := mem_triadicCube_iff.mp (partitionCube_subset n r k hx) 0
  have hpos : (0 : ℝ) < 3 ^ (n + r) := by positivity
  rw [abs_of_pos hpos] at h
  linarith

/-- **(1.31)**: `E[(μ(□_{n+r}, p) - E μ(□_n, p))₊²] ≤ 5^d (½Λ|p|²)² 3^{-dr}`. -/
theorem integral_sq_posPart_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n r : ℕ) (e : Vec d) :
    ∫ a, (max (dirichletEnergy a (triadicCube d (n + r)) e - expectedDirichletEnergy P n e) 0) ^ 2
      ∂P ≤ 5 ^ d * ((1 / 2 : ℝ) * Λ * euclideanSq e) ^ 2 / ((3 : ℝ) ^ r) ^ d := by
  have := hP.1
  set B : ℝ := (1 / 2 : ℝ) * Λ * euclideanSq e with hB
  have hB0 : 0 ≤ B := by have := euclideanSq_nonneg e; positivity
  set m : ℝ := expectedDirichletEnergy P n e
  set Y : (Fin d → Fin (3 ^ r)) → CoefficientField d Λ → ℝ :=
    fun k a => dirichletEnergy a (partitionCube n r k) e - m with hY
  have hm0 : 0 ≤ m := expectedDirichletEnergy_nonneg P n e
  have hmB : m ≤ B := expectedDirichletEnergy_le hP hΛ n e
  have hYmeas : ∀ k, Measurable (Y k) := fun k =>
    (measurable_dirichletEnergy (volume_partitionCube_ne_top n r k) hΛ e).sub_const m
  have hYbd : ∀ k a, |Y k a| ≤ B := by
    intro k a
    have h1 := dirichletEnergy_nonneg a (partitionCube n r k) e
    have h2 := dirichletEnergy_le a (volume_partitionCube_ne_zero n r k)
      (volume_partitionCube_ne_top n r k) hΛ e
    rw [abs_le]
    constructor <;> linarith
  have hYint : ∀ k, Integrable (Y k) P := fun k =>
    (integrable_const B).mono' (hYmeas k).aestronglyMeasurable
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hYbd k a)
  have hYYint : ∀ k l, Integrable (fun a => Y k a * Y l a) P := fun k l =>
    (integrable_const (B * B)).mono' ((hYmeas k).mul (hYmeas l)).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hYbd k a) (hYbd l a) (abs_nonneg _) hB0)
  have hYmean : ∀ k, ∫ a, Y k a ∂P = 0 := by
    intro k
    have hint : Integrable (fun a => dirichletEnergy a (partitionCube n r k) e) P :=
      (hYint k).add (integrable_const m) |>.congr (Eventually.of_forall fun a => by
        simp only [hY, Pi.add_apply]; ring)
    rw [integral_sub hint (integrable_const m), integral_const, probReal_univ, one_smul]
    simp_rw [dirichletEnergy_partitionCube]
    rw [integral_comp_translate hP _ (measurable_dirichletEnergy_triadicCube hΛ n e)]
    exact sub_self _
  -- covariances of separated subcubes vanish
  have hfar : ∀ k l, (∃ i, 3 ≤ |((k i : ℕ) : ℤ) - ((l i : ℕ) : ℤ)|) →
      ∫ a, Y k a * Y l a ∂P = 0 := by
    rintro k l ⟨i, hi⟩
    have hind : Indep (localSigma (partitionCube n r k)) (localSigma (partitionCube n r l)) P :=
      hP.2.2 _ _ (isOpen_partitionCube n r k).measurableSet
        (isOpen_partitionCube n r l).measurableSet
        ⟨2, one_lt_two, fun x hx y hy => two_le_euclideanNorm_sub_of_three_le hi hx hy⟩
    have hmk : @Measurable _ ℝ (localSigma (partitionCube n r k)) _ (Y k) :=
      (measurable_dirichletEnergy_localSigma (isOpen_partitionCube n r k)
        (compl_partitionCube_nonempty n r k) (volume_partitionCube_ne_top n r k) hΛ e).sub_const m
    have hml : @Measurable _ ℝ (localSigma (partitionCube n r l)) _ (Y l) :=
      (measurable_dirichletEnergy_localSigma (isOpen_partitionCube n r l)
        (compl_partitionCube_nonempty n r l) (volume_partitionCube_ne_top n r l) hΛ e).sub_const m
    have hfun : IndepFun (Y k) (Y l) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hmk.comap_le)
        hml.comap_le
    have h := hfun.integral_mul_eq_mul_integral (hYmeas k).aestronglyMeasurable
      (hYmeas l).aestronglyMeasurable
    change ∫ a, Y k a * Y l a ∂P = (∫ a, Y k a ∂P) * ∫ a, Y l a ∂P at h
    rw [h, hYmean k, zero_mul]
  -- the near covariances are bounded
  have hcov : ∀ k l, ∫ a, Y k a * Y l a ∂P ≤
      if (∀ i, |((k i : ℕ) : ℤ) - ((l i : ℕ) : ℤ)| ≤ 2) then B ^ 2 else 0 := by
    intro k l
    split_ifs with hnear
    · have h := integral_mono (hYYint k l) (integrable_const (B ^ 2)) fun a => by
        have h1 := hYbd k a
        have h2 := hYbd l a
        have : Y k a * Y l a ≤ |Y k a| * |Y l a| := by
          rw [← abs_mul]; exact le_abs_self _
        calc Y k a * Y l a ≤ |Y k a| * |Y l a| := this
          _ ≤ B * B := mul_le_mul h1 h2 (abs_nonneg _) hB0
          _ = B ^ 2 := by ring
      rwa [integral_const, probReal_univ, one_smul] at h
    · push Not at hnear
      obtain ⟨i, hi⟩ := hnear
      exact (hfar k l ⟨i, by omega⟩).le
  -- the second moment of the sum
  set N : ℝ := ((3 : ℝ) ^ r) ^ d with hN
  have hNpos : 0 < N := by positivity
  have hcard : (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) = N := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hsum2 : ∫ a, (∑ k, Y k a) ^ 2 ∂P ≤ N * (5 ^ d * B ^ 2) := by
    have hexp : ∀ a, (∑ k, Y k a) ^ 2 = ∑ k, ∑ l, Y k a * Y l a := fun a => by
      rw [sq, Finset.sum_mul_sum]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hYYint k l]
    simp_rw [integral_finsetSum _ fun l _ => hYYint _ l]
    calc ∑ k, ∑ l, ∫ a, Y k a * Y l a ∂P
        ≤ ∑ k : Fin d → Fin (3 ^ r), ∑ l : Fin d → Fin (3 ^ r),
            (if (∀ i, |((k i : ℕ) : ℤ) - ((l i : ℕ) : ℤ)| ≤ 2) then B ^ 2 else 0) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hcov k l
      _ ≤ ∑ _k : Fin d → Fin (3 ^ r), (5 ^ d * B ^ 2 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          have := card_near_le k
          have h5 : ((((Finset.univ : Finset (Fin d → Fin (3 ^ r))).filter
              fun l => ∀ i, |((k i : ℕ) : ℤ) - ((l i : ℕ) : ℤ)| ≤ 2).card : ℕ) : ℝ) ≤ 5 ^ d := by
            exact_mod_cast this
          have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
          nlinarith
      _ = N * (5 ^ d * B ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  -- the pointwise bound from subadditivity
  have hpt : ∀ a, (max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0) ^ 2 ≤
      (1 / N) ^ 2 * (∑ k, Y k a) ^ 2 := by
    intro a
    have hsub := dirichletEnergy_triadicCube_add_le a n r e
    have hrw : ∀ k : Fin d → Fin (3 ^ r), (1 / N) *
        dirichletEnergy (translate (latticeShift (partitionCenter n r k)) a) (triadicCube d n) e =
        (1 / N) * (Y k a + m) := by
      intro k
      rw [← dirichletEnergy_partitionCube]
      simp only [hY]
      ring
    rw [Finset.sum_congr rfl fun k _ => hrw k, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsub
    have hle : dirichletEnergy a (triadicCube d (n + r)) e - m ≤ (1 / N) * ∑ k, Y k a := by
      have : (1 / N) * ((∑ k, Y k a) + N * m) = (1 / N) * ∑ k, Y k a + m := by
        field_simp
      linarith
    have h0 : 0 ≤ max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0 := le_max_right _ _
    have h1 : max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0 ≤
        |(1 / N) * ∑ k, Y k a| := max_le (hle.trans (le_abs_self _)) (abs_nonneg _)
    calc (max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0) ^ 2
        ≤ |(1 / N) * ∑ k, Y k a| ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (1 / N) ^ 2 * (∑ k, Y k a) ^ 2 := by rw [sq_abs, mul_pow]
  have hint2 : Integrable (fun a => (∑ k, Y k a) ^ 2) P := by
    have hexp : (fun a => (∑ k, Y k a) ^ 2) = fun a => ∑ k, ∑ l, Y k a * Y l a := by
      funext a; rw [sq, Finset.sum_mul_sum]
    rw [hexp]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hYYint k l
  have hmeas : Measurable fun a =>
      (max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0) ^ 2 :=
    (((measurable_dirichletEnergy_triadicCube hΛ (n + r) e).sub_const m).max
      measurable_const).pow_const 2
  have hintL : Integrable (fun a =>
      (max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0) ^ 2) P :=
    (hint2.const_mul ((1 / N) ^ 2)).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpt a)
  calc ∫ a, (max (dirichletEnergy a (triadicCube d (n + r)) e - m) 0) ^ 2 ∂P
      ≤ ∫ a, (1 / N) ^ 2 * (∑ k, Y k a) ^ 2 ∂P := integral_mono hintL (hint2.const_mul _) hpt
    _ = (1 / N) ^ 2 * ∫ a, (∑ k, Y k a) ^ 2 ∂P := integral_const_mul _ _
    _ ≤ (1 / N) ^ 2 * (N * (5 ^ d * B ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum2 (sq_nonneg _)
    _ = 5 ^ d * B ^ 2 / N := by field_simp

/-! ## Step 2: (1.32) -/

theorem integral_le_sqrt_integral_sq {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
    {f : CoefficientField d Λ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) :
    ∫ a, f a ∂P ≤ Real.sqrt (∫ a, f a ^ 2 ∂P) := by
  have hmem : MemLp f 2 P := MemLp.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hM a)
  have hv := variance_nonneg f P
  rw [variance_eq_sub hmem] at hv
  have h : (∫ a, f a ∂P) ^ 2 ≤ ∫ a, f a ^ 2 ∂P := by
    have : ∫ a, (f ^ 2) a ∂P = ∫ a, f a ^ 2 ∂P := rfl
    linarith
  calc ∫ a, f a ∂P ≤ |∫ a, f a ∂P| := le_abs_self _
    _ = Real.sqrt ((∫ a, f a ∂P) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∫ a, f a ^ 2 ∂P) := Real.sqrt_le_sqrt h

/-- **(1.32)** at a mesoscale `n`: for `p ∈ B₁`,
`E|μ(□_{n+r}, p) - μ̄(p)| ≤ 2 (E[(μ(□_{n+r}, p) - E μ(□_n, p))₊²])^{1/2} + 2ω(n)`. -/
theorem integral_abs_sub_limitDirichletEnergy_le {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n r : ℕ) {e : Vec d} (he : e ∈ originBall d 1) :
    ∫ a, |dirichletEnergy a (triadicCube d (n + r)) e - limitDirichletEnergy P e| ∂P ≤
      2 * Real.sqrt (∫ a, (max (dirichletEnergy a (triadicCube d (n + r)) e -
        expectedDirichletEnergy P n e) 0) ^ 2 ∂P) + 2 * omegaModulus P n := by
  have := hP.1
  set X : CoefficientField d Λ → ℝ := fun a => dirichletEnergy a (triadicCube d (n + r)) e
  set L := limitDirichletEnergy P e
  set m := expectedDirichletEnergy P n e
  set m' := expectedDirichletEnergy P (n + r) e
  have hXm : Measurable X := measurable_dirichletEnergy_triadicCube hΛ (n + r) e
  have hXi : Integrable X P := integrable_dirichletEnergy_triadicCube hΛ (n + r) e
  have hEX : ∫ a, X a ∂P = m' := rfl
  have hmm' : m' ≤ m := antitone_expectedDirichletEnergy hP hΛ e (Nat.le_add_right n r)
  have hLm' : L ≤ m' := limitDirichletEnergy_le_expected P (n + r) e
  have hω : m - L ≤ omegaModulus P n := sub_le_omegaModulus hP hΛ n he
  have hpt : ∀ a, |X a - L| ≤ 2 * max (X a - m) 0 + (2 * (m - m') + (m' - L)) - (X a - m') := by
    intro a
    have h1 : |X a - L| ≤ |X a - m'| + (m' - L) := by
      calc |X a - L| = |(X a - m') + (m' - L)| := by rw [sub_add_sub_cancel]
        _ ≤ |X a - m'| + |m' - L| := abs_add_le _ _
        _ = |X a - m'| + (m' - L) := by rw [abs_of_nonneg (sub_nonneg.mpr hLm')]
    have h2 : |X a - m'| = 2 * max (X a - m') 0 - (X a - m') := by
      rcases le_total 0 (X a - m') with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    have h3 : max (X a - m') 0 ≤ max (X a - m) 0 + (m - m') := by
      refine max_le ?_ ?_
      · linarith [le_max_left (X a - m) 0]
      · linarith [le_max_right (X a - m) 0]
    linarith
  have hBd : ∀ a, |max (X a - m) 0| ≤ (1 / 2 : ℝ) * Λ * euclideanSq e := by
    intro a
    have h1 := dirichletEnergy_nonneg a (triadicCube d (n + r)) e
    have h2 := dirichletEnergy_le a (volume_triadicCube_ne_zero d (n + r))
      (volume_triadicCube_ne_top d (n + r)) hΛ e
    have h3 := expectedDirichletEnergy_nonneg P n e
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by simp only [X] at h2 ⊢; linarith) (by have := euclideanSq_nonneg e; positivity)
  have hmaxm : Measurable fun a => max (X a - m) 0 := (hXm.sub_const m).max measurable_const
  have hmaxi : Integrable (fun a => max (X a - m) 0) P :=
    (integrable_const ((1 / 2 : ℝ) * Λ * euclideanSq e)).mono' hmaxm.aestronglyMeasurable
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hBd a)
  set c : ℝ := 2 * (m - m') + (m' - L)
  have i1 : Integrable (fun a => 2 * max (X a - m) 0) P := hmaxi.const_mul 2
  have i2 : Integrable (fun a => 2 * max (X a - m) 0 + c) P := i1.add (integrable_const c)
  have i3 : Integrable (fun a => X a - m') P := hXi.sub (integrable_const m')
  have hint_rhs : Integrable (fun a => 2 * max (X a - m) 0 + c - (X a - m')) P := i2.sub i3
  have habsi : Integrable (fun a => |X a - L|) P := (hXi.sub (integrable_const L)).abs
  have hstep : ∫ a, |X a - L| ∂P ≤ 2 * ∫ a, max (X a - m) 0 ∂P + (2 * (m - m') + (m' - L)) := by
    calc ∫ a, |X a - L| ∂P ≤ ∫ a, (2 * max (X a - m) 0 + (2 * (m - m') + (m' - L)) -
          (X a - m')) ∂P := integral_mono habsi hint_rhs hpt
      _ = 2 * ∫ a, max (X a - m) 0 ∂P + (2 * (m - m') + (m' - L)) := by
          rw [integral_sub i2 i3, integral_add i1 (integrable_const c),
            integral_sub hXi (integrable_const m'), integral_const_mul, integral_const,
            integral_const, probReal_univ, one_smul, one_smul, hEX]
          ring
  have hsq := integral_le_sqrt_integral_sq (P := P) hmaxm hBd
  have hm_L : m - L ≤ omegaModulus P n := hω
  have : 2 * (m - m') + (m' - L) ≤ 2 * omegaModulus P n := by linarith
  linarith

/-! ## Proposition 1.7 -/

theorem measurable_coarseMatrix_apply (hΛ : 0 ≤ Λ) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (i j : Fin d) : Measurable fun a : CoefficientField d Λ => coarseMatrix a U i j := by
  simp only [coarseMatrix, polarizationMatrix, Matrix.of_apply, polarization]
  exact measurable_const.mul (((measurable_dirichletEnergy hU hΛ _).sub
    (measurable_dirichletEnergy hU hΛ _)).div_const _)

theorem sum_sq_le_sq_sum_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hf hi) (hf i hi)

theorem frobeniusNorm_le_sum_abs (A : Mat d) : frobeniusNorm A ≤ ∑ i, ∑ j, |A i j| := by
  unfold frobeniusNorm frobeniusSq
  have hnn : 0 ≤ ∑ i, ∑ j, |A i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have h : ∑ i, ∑ j, A i j * A i j ≤ (∑ i, ∑ j, |A i j|) ^ 2 := by
    calc ∑ i, ∑ j, A i j * A i j = ∑ i, ∑ j, |A i j| ^ 2 := by
          simp_rw [sq_abs, sq]
      _ ≤ ∑ i, (∑ j, |A i j|) ^ 2 := Finset.sum_le_sum fun i _ =>
          sum_sq_le_sq_sum_of_nonneg _ _ fun j _ => abs_nonneg _
      _ ≤ (∑ i, ∑ j, |A i j|) ^ 2 := sum_sq_le_sq_sum_of_nonneg _ _ fun i _ =>
          Finset.sum_nonneg fun j _ => abs_nonneg _
  calc Real.sqrt (∑ i, ∑ j, A i j * A i j) ≤ Real.sqrt ((∑ i, ∑ j, |A i j|) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = ∑ i, ∑ j, |A i j| := Real.sqrt_sq hnn

theorem measurable_frobeniusNorm_coarseMatrix_sub (hΛ : 0 ≤ Λ) {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) (A : Mat d) :
    Measurable fun a : CoefficientField d Λ => frobeniusNorm (coarseMatrix a U - A) := by
  unfold frobeniusNorm frobeniusSq
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  simp only [Matrix.sub_apply]
  exact ((measurable_coarseMatrix_apply hΛ hU i j).sub_const _).mul
    ((measurable_coarseMatrix_apply hΛ hU i j).sub_const _)

theorem dirichletEnergy_smul (a : CoefficientField d Λ) {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) (hΛ : 0 ≤ Λ) (c : ℝ) (e : Vec d) :
    dirichletEnergy a U (c • e) = c ^ 2 * dirichletEnergy a U e := by
  rw [dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ, dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ]
  simp only [dot_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem limitDirichletEnergy_smul {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (c : ℝ) (e : Vec d) :
    limitDirichletEnergy P (c • e) = c ^ 2 * limitDirichletEnergy P e := by
  rw [limitDirichletEnergy_eq_homogenizedMatrix hP hΛ, limitDirichletEnergy_eq_homogenizedMatrix hP hΛ]
  simp only [dot_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem euclideanSq_unitVector (k : Fin d) : euclideanSq (unitVector k) = 1 := by
  simp [euclideanSq, dot, unitVector, Pi.single_apply]

theorem mem_originBall_quarter (i j : Fin d) (s : ℝ) (hs : |s| ≤ 1) :
    (1 / 4 : ℝ) • (unitVector i + s • unitVector j) ∈ originBall d 1 := by
  have hsq : euclideanSq ((1 / 4 : ℝ) • (unitVector i + s • unitVector j)) ≤ 1 / 4 := by
    have h1 : euclideanSq ((1 / 4 : ℝ) • (unitVector i + s • unitVector j)) =
        (1 / 16 : ℝ) * euclideanSq (unitVector i + s • unitVector j) := by
      simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : euclideanSq (unitVector i + s • unitVector j) ≤ 4 := by
      have hpar := dot_parallelogram (1 : Mat d) (unitVector i) (s • unitVector j)
      simp only [Matrix.one_mulVec] at hpar
      have hsj : dot (s • unitVector j) (s • unitVector j) = s ^ 2 := by
        have := euclideanSq_unitVector j
        simp only [euclideanSq] at this
        simp only [dot_eq_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul] at this ⊢
        rw [this]; ring
      have hnn : 0 ≤ dot (unitVector i - s • unitVector j) (unitVector i - s • unitVector j) :=
        euclideanSq_nonneg _
      have hi := euclideanSq_unitVector i
      simp only [euclideanSq] at hi ⊢
      have hs2 : s ^ 2 ≤ 1 := by
        have := sq_abs s
        nlinarith [abs_nonneg s]
      linarith
    rw [h1]
    linarith
  have h0 : 0 ≤ euclideanSq ((1 / 4 : ℝ) • (unitVector i + s • unitVector j)) :=
    euclideanSq_nonneg _
  show Real.sqrt _ < 1
  rw [Real.sqrt_lt' one_pos]
  linarith

/-- `B(x, y) = 4 (L(¼(x + y)) - L(¼(x - y)))` for a function with `L(c x) = c² L(x)`. -/
theorem polarization_eq_quarter {L : Vec d → ℝ} (hL : ∀ (c : ℝ) (x : Vec d), L (c • x) = c ^ 2 * L x)
    (x y : Vec d) :
    polarization L x y = 4 * (L ((1 / 4 : ℝ) • (x + y)) - L ((1 / 4 : ℝ) • (x - y))) := by
  have h4 : (4 : ℝ) * (1 / 4) = 1 := by norm_num
  have h1 : x + y = (4 : ℝ) • ((1 / 4 : ℝ) • (x + y)) := by rw [smul_smul, h4, one_smul]
  have h2 : x - y = (4 : ℝ) • ((1 / 4 : ℝ) • (x - y)) := by rw [smul_smul, h4, one_smul]
  unfold polarization
  conv_lhs => rw [h1, h2]
  rw [hL 4 ((1 / 4 : ℝ) • (x + y)), hL 4 ((1 / 4 : ℝ) • (x - y))]
  ring

/-- The deviation `μ(U, p) - μ̄(p)`. -/
def energyDeviation (P : Measure (CoefficientField d Λ)) (U : Set (Vec d)) (q : Vec d)
    (a : CoefficientField d Λ) : ℝ :=
  dirichletEnergy a U q - limitDirichletEnergy P q

/-- The entries of `a(U) - ā` from the deviations at `¼(eᵢ ± eⱼ)`. -/
theorem coarseMatrix_sub_homogenizedMatrix_apply {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (i j : Fin d) :
    (coarseMatrix a U - homogenizedMatrix P) i j =
      8 * (energyDeviation P U ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a -
        energyDeviation P U ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a) := by
  simp only [Matrix.sub_apply, coarseMatrix, homogenizedMatrix, polarizationMatrix, Matrix.of_apply,
    energyDeviation]
  rw [polarization_eq_quarter (dirichletEnergy_smul a hU0 hU hΛ),
    polarization_eq_quarter (limitDirichletEnergy_smul hP hΛ)]
  ring

theorem sqrt_inv_three_pow_le (d m : ℕ) :
    Real.sqrt (1 / ((3 : ℝ) ^ (m / 2)) ^ d) ≤
      (3 : ℝ) ^ ((d : ℝ) / 4) * (3 : ℝ) ^ (-((d : ℝ) * m) / 4) := by
  have h3 : (1 : ℝ) ≤ 3 := by norm_num
  have hrw : (1 / ((3 : ℝ) ^ (m / 2)) ^ d) = (3 : ℝ) ^ (-((d : ℝ) * ((m / 2 : ℕ) : ℝ))) := by
    rw [Real.rpow_neg (by norm_num), ← pow_mul, ← Real.rpow_natCast, one_div]
    congr 2
    push_cast
    ring
  rw [hrw, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le h3 ?_
  have hm : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
    have : m ≤ 2 * (m / 2) + 1 := by omega
    exact_mod_cast this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- **Proposition 1.7**, (1.30): there is `C(d, Λ)` such that for every law satisfying
(0.10)–(0.11) and every `m`, `E|a(□_m) - ā| ≤ C 3^{-dm/4} + C ω(⌈m/2⌉)`, with
`⌈m/2⌉ = (m + 1)/2` and the Frobenius norm of matrices. -/
theorem proposition_1_7 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ m : ℕ,
      Integrable (fun a => frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P))
        P ∧
      ∫ a, frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) ∂P ≤
        C * (3 : ℝ) ^ (-((d : ℝ) * m) / 4) + C * omegaModulus P ((m + 1) / 2) := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = Real.sqrt (5 ^ d * Λ ^ 2 / 4) := ⟨_, rfl⟩
  have hS : 0 ≤ S := hSdef ▸ Real.sqrt_nonneg _
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (3 : ℝ) ^ ((d : ℝ) / 4) := ⟨_, rfl⟩
  have hK : 0 ≤ K := hKdef ▸ by positivity
  refine ⟨32 * (d : ℝ) ^ 2 * (S * K + 1), by positivity, fun P hP m => ?_⟩
  have := hP.1
  have hΛ : 0 ≤ Λ := by
    rcases isEmpty_or_nonempty (CoefficientField d Λ) with h | h
    · have h0 : P = 0 := Measure.eq_zero_of_isEmpty P
      have h1 := measure_univ (μ := P)
      rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
      exact absurd h1 zero_ne_one
    · obtain ⟨a⟩ := h
      exact zero_le_one.trans (one_le_of_coefficientField a)
  have hnr : (m + 1) / 2 + m / 2 = m := by omega
  have hU0 : volume (triadicCube d m) ≠ 0 := volume_triadicCube_ne_zero d m
  have hUt : volume (triadicCube d m) ≠ ⊤ := volume_triadicCube_ne_top d m
  have hqp : ∀ i j : Fin d, (1 / 4 : ℝ) • (unitVector i + unitVector j) ∈ originBall d 1 :=
    fun i j => by simpa using mem_originBall_quarter i j 1 (by simp)
  have hqm : ∀ i j : Fin d, (1 / 4 : ℝ) • (unitVector i - unitVector j) ∈ originBall d 1 :=
    fun i j => by
      simpa [neg_one_smul, ← sub_eq_add_neg] using mem_originBall_quarter i j (-1) (by simp)
  have hDi : ∀ q, Integrable (fun a => |energyDeviation P (triadicCube d m) q a|) P := fun q =>
    ((integrable_dirichletEnergy_triadicCube hΛ m q).sub (integrable_const _)).abs
  have hterm : ∀ i j : Fin d, Integrable (fun a =>
      8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a| +
      8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a|)
      P := fun i j => ((hDi _).const_mul 8).add ((hDi _).const_mul 8)
  have hGi : Integrable (fun a => ∑ i, ∑ j,
      (8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a| +
      8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a|))
      P := integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j
  have hpt : ∀ a, frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) ≤
      ∑ i, ∑ j,
      (8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a| +
      8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a|) := by
    intro a
    refine (frobeniusNorm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => ?_)
    rw [coarseMatrix_sub_homogenizedMatrix_apply hP hΛ a hU0 hUt, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    have := abs_sub (energyDeviation P (triadicCube d m)
      ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a)
      (energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a)
    linarith
  have hmeas := measurable_frobeniusNorm_coarseMatrix_sub hΛ hUt (homogenizedMatrix P)
  have hint : Integrable (fun a => frobeniusNorm (coarseMatrix a (triadicCube d m) -
      homogenizedMatrix P)) P :=
    hGi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ frobeniusNorm (coarseMatrix a (triadicCube d m) -
        homogenizedMatrix P) from Real.sqrt_nonneg _)]
      exact hpt a)
  refine ⟨hint, ?_⟩
  set ω := omegaModulus P ((m + 1) / 2)
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = S * (K * (3 : ℝ) ^ (-((d : ℝ) * m) / 4)) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := omegaModulus_nonneg hP hΛ _
  have hD : ∀ q ∈ originBall d 1, ∫ a, |energyDeviation P (triadicCube d m) q a| ∂P ≤
      2 * T + 2 * ω := by
    intro q hq
    have h1 := integral_abs_sub_limitDirichletEnergy_le hP hΛ ((m + 1) / 2) (m / 2) hq
    have h2 := integral_sq_posPart_le hP hΛ ((m + 1) / 2) (m / 2) q
    rw [hnr] at h1 h2
    have hq1 := euclideanSq_le_one_of_mem_originBall hq
    have hB : ((1 / 2 : ℝ) * Λ * euclideanSq q) ^ 2 ≤ Λ ^ 2 / 4 := by
      have h0 : 0 ≤ (1 / 2 : ℝ) * Λ * euclideanSq q := by
        have := euclideanSq_nonneg q; positivity
      have h3 : (1 / 2 : ℝ) * Λ * euclideanSq q ≤ (1 / 2 : ℝ) * Λ := by nlinarith
      nlinarith
    have h3 : Real.sqrt (∫ a, (max (dirichletEnergy a (triadicCube d m) q -
        expectedDirichletEnergy P ((m + 1) / 2) q) 0) ^ 2 ∂P) ≤ T := by
      have h4 : 5 ^ d * ((1 / 2 : ℝ) * Λ * euclideanSq q) ^ 2 / ((3 : ℝ) ^ (m / 2)) ^ d ≤
          5 ^ d * Λ ^ 2 / 4 * (1 / ((3 : ℝ) ^ (m / 2)) ^ d) := by
        rw [div_eq_mul_one_div, mul_div_assoc]
        gcongr
      calc _ ≤ Real.sqrt (5 ^ d * Λ ^ 2 / 4 * (1 / ((3 : ℝ) ^ (m / 2)) ^ d)) :=
            Real.sqrt_le_sqrt (h2.trans h4)
        _ = S * Real.sqrt (1 / ((3 : ℝ) ^ (m / 2)) ^ d) := by
            rw [Real.sqrt_mul (by positivity), hSdef]
        _ ≤ T := by
            rw [hTdef, hKdef]
            exact mul_le_mul_of_nonneg_left (sqrt_inv_three_pow_le d m) hS
    unfold energyDeviation
    linarith
  calc ∫ a, frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) ∂P
      ≤ ∫ a, ∑ i, ∑ j,
          (8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a| +
          8 * |energyDeviation P (triadicCube d m) ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a|)
          ∂P := integral_mono hint hGi hpt
    _ = ∑ i, ∑ j, (8 * ∫ a, |energyDeviation P (triadicCube d m)
          ((1 / 4 : ℝ) • (unitVector i + unitVector j)) a| ∂P +
          8 * ∫ a, |energyDeviation P (triadicCube d m)
            ((1 / 4 : ℝ) • (unitVector i - unitVector j)) a| ∂P) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hterm i j]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_add ((hDi _).const_mul 8) ((hDi _).const_mul 8), integral_const_mul,
          integral_const_mul]
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (32 * T + 32 * ω) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have := hD _ (hqp i j)
          have := hD _ (hqm i j)
          linarith
    _ = (d : ℝ) ^ 2 * (32 * T + 32 * ω) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 32 * (d : ℝ) ^ 2 * (S * K + 1) * (3 : ℝ) ^ (-((d : ℝ) * m) / 4) +
          32 * (d : ℝ) ^ 2 * (S * K + 1) * ω := by
        have h3m : 0 ≤ (3 : ℝ) ^ (-((d : ℝ) * m) / 4) := by positivity
        have hd2 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
        have key : 32 * (d : ℝ) ^ 2 * (S * K + 1) * (3 : ℝ) ^ (-((d : ℝ) * m) / 4) +
            32 * (d : ℝ) ^ 2 * (S * K + 1) * ω - (d : ℝ) ^ 2 * (32 * T + 32 * ω) =
            32 * ((d : ℝ) ^ 2 * (3 : ℝ) ^ (-((d : ℝ) * m) / 4)) + 32 * ((d : ℝ) ^ 2 * S * K * ω) := by
          rw [hTdef]; ring
        have e1 : 0 ≤ (d : ℝ) ^ 2 * (3 : ℝ) ^ (-((d : ℝ) * m) / 4) := mul_nonneg hd2 h3m
        have e2 : 0 ≤ (d : ℝ) ^ 2 * S * K * ω :=
          mul_nonneg (mul_nonneg (mul_nonneg hd2 hS) hK) hω0
        linarith

end QSH
