import QuantitativeStochasticHomogenization.Ch01.Sec03.Proposition17

/-!
# Proposition 1.11: the expectation of the random variable `E(m)`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, (1.39), Proposition 1.11, (1.41) and (1.52).

* `coarseDeviation P m a`: the random variable
  `E(m) = (Σ_{n=0}^m 3^{n-m} (|Z_n|⁻¹ Σ_{z ∈ Z_n} |a(z + □_n) - ā|)^{1/2})²` of (1.39), with the
  Frobenius norm of matrices;
* `coarseDeviation_le`: the bound (1.52), `E(m) ≤ (3/2) Σ_{n=0}^m 3^{n-m} |Z_n|⁻¹ Σ_z |a(z + □_n) - ā|`;
* `proposition_1_11`: `E[E(m)] ≤ C Σ_{n=0}^m 3^{n-m} (3^{-dn/4} + ω(⌈n/2⌉))`, the second display
  of the proof, from stationarity and Proposition 1.7;
* `proposition_1_11_of_ne_four`: (1.41) for `d ≠ 4`,
  `E[E(m)] ≤ C 3^{-(d/4 ∧ 1)m} + C Σ_{n=0}^m 3^{n-m} ω(⌈n/2⌉)`. For `d = 4` the sum
  `Σ_{n=0}^m 3^{n-m} 3^{-n} = (m + 1) 3^{-m}` is not bounded by `C 3^{-m}`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem coarseMatrix_partitionCube (a : CoefficientField d Λ) (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    coarseMatrix a (partitionCube n r k) =
      coarseMatrix (translate (latticeShift (partitionCenter n r k)) a) (triadicCube d n) := by
  ext i j
  simp only [coarseMatrix, polarizationMatrix, Matrix.of_apply, polarization,
    dirichletEnergy_partitionCube]

/-- The average `|Z_n|⁻¹ Σ_{z ∈ Z_n} |a(z + □_n) - ā|` over the subcubes `z + □_n` of `□_m`. -/
def subcubeDeviation (P : Measure (CoefficientField d Λ)) (m n : ℕ) (a : CoefficientField d Λ) :
    ℝ :=
  (1 / ((3 : ℝ) ^ (m - n)) ^ d) * ∑ k : Fin d → Fin (3 ^ (m - n)),
    frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P)

/-- **The random variable `E(m)`** of (1.39). -/
def coarseDeviation (P : Measure (CoefficientField d Λ)) (m : ℕ) (a : CoefficientField d Λ) : ℝ :=
  (∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * Real.sqrt (subcubeDeviation P m n a)) ^ 2

theorem subcubeDeviation_nonneg (P : Measure (CoefficientField d Λ)) (m n : ℕ)
    (a : CoefficientField d Λ) : 0 ≤ subcubeDeviation P m n a :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _)

theorem sum_inv_three_pow_le (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ ≤ 3 / 2 := by
  rw [← Finset.sum_range_reflect]
  have h : ∀ j ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - (m + 1 - 1 - j)))⁻¹ = (1 / 3 : ℝ) ^ j := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show m - (m + 1 - 1 - j) = j by omega, one_div, inv_pow]
  rw [Finset.sum_congr rfl h, geom_sum_eq (by norm_num) (m + 1)]
  have hp : 0 ≤ (1 / 3 : ℝ) ^ (m + 1) := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  nlinarith

/-- **(1.52)**: `E(m) ≤ (3/2) Σ_{n=0}^m 3^{n-m} |Z_n|⁻¹ Σ_z |a(z + □_n) - ā|`. -/
theorem coarseDeviation_le (P : Measure (CoefficientField d Λ)) (m : ℕ)
    (a : CoefficientField d Λ) :
    coarseDeviation P m a ≤
      3 / 2 * ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * subcubeDeviation P m n a := by
  unfold coarseDeviation
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m + 1))
    (fun n => Real.sqrt (((3 : ℝ) ^ (m - n))⁻¹))
    (fun n => Real.sqrt (((3 : ℝ) ^ (m - n))⁻¹ * subcubeDeviation P m n a))
  have h1 : ∀ n, Real.sqrt (((3 : ℝ) ^ (m - n))⁻¹) *
      Real.sqrt (((3 : ℝ) ^ (m - n))⁻¹ * subcubeDeviation P m n a) =
      ((3 : ℝ) ^ (m - n))⁻¹ * Real.sqrt (subcubeDeviation P m n a) := by
    intro n
    have hw : 0 ≤ ((3 : ℝ) ^ (m - n))⁻¹ := by positivity
    rw [Real.sqrt_mul hw, ← mul_assoc, Real.mul_self_sqrt hw]
  simp_rw [h1, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ (m - _))⁻¹),
    Real.sq_sqrt (mul_nonneg (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ (m - _))⁻¹)
      (subcubeDeviation_nonneg P m _ a))] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right (sum_inv_three_pow_le m)
    (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (subcubeDeviation_nonneg P m n a)))

theorem measurable_subcubeDeviation (hΛ : 0 ≤ Λ) (P : Measure (CoefficientField d Λ)) (m n : ℕ) :
    Measurable (subcubeDeviation P m n) :=
  measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    measurable_frobeniusNorm_coarseMatrix_sub hΛ (volume_partitionCube_ne_top n (m - n) k) _)

theorem integral_subcubeDeviation {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (m n : ℕ) (hint : Integrable (fun a => frobeniusNorm (coarseMatrix a
      (triadicCube d n) - homogenizedMatrix P)) P) :
    Integrable (subcubeDeviation P m n) P ∧
    ∫ a, subcubeDeviation P m n a ∂P =
      ∫ a, frobeniusNorm (coarseMatrix a (triadicCube d n) - homogenizedMatrix P) ∂P := by
  have := hP.1
  have hmeas := measurable_frobeniusNorm_coarseMatrix_sub hΛ (volume_triadicCube_ne_top d n)
    (homogenizedMatrix P)
  have hk : ∀ k : Fin d → Fin (3 ^ (m - n)), Integrable (fun a =>
      frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P)) P := by
    intro k
    have h : Integrable (fun a => frobeniusNorm (coarseMatrix (translate (latticeShift
        (partitionCenter n (m - n) k)) a) (triadicCube d n) - homogenizedMatrix P)) P := by
      have hmap : Measure.map (translate (latticeShift (partitionCenter n (m - n) k))) P = P :=
        hP.2.1 _
      have h' : Integrable (fun a => frobeniusNorm (coarseMatrix a (triadicCube d n) -
          homogenizedMatrix P)) (Measure.map (translate (latticeShift
            (partitionCenter n (m - n) k))) P) := by rw [hmap]; exact hint
      exact h'.comp_measurable (measurable_translateCoefficient _)
    exact h.congr (Eventually.of_forall fun a => by simp only [coarseMatrix_partitionCube])
  have hsum : Integrable (fun a => ∑ k : Fin d → Fin (3 ^ (m - n)),
      frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P)) P :=
    integrable_finsetSum _ fun k _ => hk k
  refine ⟨hsum.const_mul _, ?_⟩
  unfold subcubeDeviation
  rw [integral_const_mul, integral_finsetSum _ fun k _ => hk k]
  have hE : ∀ k : Fin d → Fin (3 ^ (m - n)), ∫ a, frobeniusNorm (coarseMatrix a
      (partitionCube n (m - n) k) - homogenizedMatrix P) ∂P =
      ∫ a, frobeniusNorm (coarseMatrix a (triadicCube d n) - homogenizedMatrix P) ∂P := by
    intro k
    simp_rw [coarseMatrix_partitionCube]
    exact integral_comp_translate hP _ hmeas
  rw [Finset.sum_congr rfl fun k _ => hE k, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Fin d → Fin (3 ^ (m - n))) : ℝ) = ((3 : ℝ) ^ (m - n)) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  rw [hc]
  field_simp

/-- **The bound of the proof of Proposition 1.11**: there is `C(d, Λ)` such that for every law satisfying (0.10)–(0.11) and
every `m`, `E[E(m)] ≤ C Σ_{n=0}^m 3^{n-m} (3^{-dn/4} + ω(⌈n/2⌉))`. -/
theorem proposition_1_11 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ m : ℕ,
      Integrable (coarseDeviation P m) P ∧
      ∫ a, coarseDeviation P m a ∂P ≤ C * ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
        ((3 : ℝ) ^ (-((d : ℝ) * n) / 4) + omegaModulus P ((n + 1) / 2)) := by
  obtain ⟨C, hC, h17⟩ := proposition_1_7 (d := d) (Λ := Λ)
  refine ⟨3 / 2 * C, by positivity, fun P hP m => ?_⟩
  have := hP.1
  have hΛ : 0 ≤ Λ := by
    rcases isEmpty_or_nonempty (CoefficientField d Λ) with h | h
    · have h0 : P = 0 := Measure.eq_zero_of_isEmpty P
      have h1 := measure_univ (μ := P)
      rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
      exact absurd h1 zero_ne_one
    · obtain ⟨a⟩ := h
      exact zero_le_one.trans (one_le_of_coefficientField a)
  have hX : ∀ n, Integrable (subcubeDeviation P m n) P ∧
      ∫ a, subcubeDeviation P m n a ∂P ≤
        C * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) + C * omegaModulus P ((n + 1) / 2) := by
    intro n
    obtain ⟨hi, hb⟩ := h17 P hP n
    obtain ⟨hi', he⟩ := integral_subcubeDeviation hP hΛ m n hi
    exact ⟨hi', he ▸ hb⟩
  have hdom : Integrable (fun a => 3 / 2 * ∑ n ∈ Finset.range (m + 1),
      ((3 : ℝ) ^ (m - n))⁻¹ * subcubeDeviation P m n a) P :=
    (integrable_finsetSum _ fun n _ => (hX n).1.const_mul _).const_mul _
  have hmeas : Measurable (coarseDeviation P m) := by
    unfold coarseDeviation
    exact (Finset.measurable_sum _ fun n _ => measurable_const.mul
      (measurable_subcubeDeviation hΛ P m n).sqrt).pow_const 2
  have hint : Integrable (coarseDeviation P m) P :=
    hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact coarseDeviation_le P m a)
  refine ⟨hint, ?_⟩
  calc ∫ a, coarseDeviation P m a ∂P
      ≤ ∫ a, 3 / 2 * ∑ n ∈ Finset.range (m + 1),
          ((3 : ℝ) ^ (m - n))⁻¹ * subcubeDeviation P m n a ∂P :=
        integral_mono hint hdom fun a => coarseDeviation_le P m a
    _ = 3 / 2 * ∑ n ∈ Finset.range (m + 1),
          ((3 : ℝ) ^ (m - n))⁻¹ * ∫ a, subcubeDeviation P m n a ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun n _ => (hX n).1.const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ 3 / 2 * ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
          (C * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) + C * omegaModulus P ((n + 1) / 2)) := by
        gcongr with n hn
        exact (hX n).2
    _ = 3 / 2 * C * ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
          ((3 : ℝ) ^ (-((d : ℝ) * n) / 4) + omegaModulus P ((n + 1) / 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring

/-! ## The geometric sum and the limit -/

theorem inv_three_pow_mul_rpow_eq (m n : ℕ) (hn : n ≤ m) :
    ((3 : ℝ) ^ (m - n))⁻¹ * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) =
      (3 : ℝ) ^ (-(m : ℝ)) * ((3 : ℝ) ^ (1 - (d : ℝ) / 4)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast [hn]
  ring

/-- `Σ_{n=0}^m 3^{n-m} 3^{-dn/4} ≤ C 3^{-(d/4 ∧ 1) m}` for `d ≠ 4`. -/
theorem sum_geometric_le_of_ne_four (hd : d ≠ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∑ n ∈ Finset.range (m + 1),
      ((3 : ℝ) ^ (m - n))⁻¹ * (3 : ℝ) ^ (-((d : ℝ) * n) / 4) ≤
        K * (3 : ℝ) ^ (-(min ((d : ℝ) / 4) 1) * m) := by
  set x : ℝ := (3 : ℝ) ^ (1 - (d : ℝ) / 4)
  have hx0 : 0 < x := by positivity
  have hrw : ∀ m : ℕ, ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
      (3 : ℝ) ^ (-((d : ℝ) * n) / 4) = (3 : ℝ) ^ (-(m : ℝ)) * ∑ n ∈ Finset.range (m + 1), x ^ n := by
    intro m
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn =>
      inv_three_pow_mul_rpow_eq m n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · -- `d < 4`: `x > 1`
    have hd4 : (d : ℝ) < 4 := by exact_mod_cast hlt
    have hx1 : 1 < x := Real.one_lt_rpow (by norm_num) (by linarith)
    refine ⟨x / (x - 1), div_nonneg hx0.le (by linarith), fun m => ?_⟩
    rw [hrw m, geom_sum_eq hx1.ne' (m + 1), min_eq_left (by linarith)]
    have hxm : x ^ m = (3 : ℝ) ^ ((1 - (d : ℝ) / 4) * m) := by
      rw [Real.rpow_mul_natCast (by norm_num)]
    have hkey : (3 : ℝ) ^ (-(m : ℝ)) * x ^ m = (3 : ℝ) ^ (-((d : ℝ) / 4) * m) := by
      rw [hxm, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have hp : 0 < (3 : ℝ) ^ (-(m : ℝ)) := by positivity
    calc (3 : ℝ) ^ (-(m : ℝ)) * ((x ^ (m + 1) - 1) / (x - 1))
        ≤ (3 : ℝ) ^ (-(m : ℝ)) * (x ^ (m + 1) / (x - 1)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (by linarith)) hp.le
      _ = x / (x - 1) * ((3 : ℝ) ^ (-(m : ℝ)) * x ^ m) := by rw [pow_succ]; ring
      _ = _ := by rw [hkey]
  · -- `d > 4`: `x < 1`
    have hd4 : (4 : ℝ) < d := by exact_mod_cast hgt
    have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    refine ⟨1 / (1 - x), div_nonneg zero_le_one (by linarith), fun m => ?_⟩
    rw [hrw m, geom_sum_eq hx1.ne (m + 1), min_eq_right (by linarith)]
    have hp : 0 < (3 : ℝ) ^ (-(m : ℝ)) := by positivity
    have hxp : 0 ≤ x ^ (m + 1) := by positivity
    have hle : (x ^ (m + 1) - 1) / (x - 1) ≤ 1 / (1 - x) := by
      rw [show (x ^ (m + 1) - 1) / (x - 1) = (1 - x ^ (m + 1)) / (1 - x) by
        rw [← neg_sub (x ^ (m + 1)), ← neg_sub x, neg_div_neg_eq]]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    calc (3 : ℝ) ^ (-(m : ℝ)) * ((x ^ (m + 1) - 1) / (x - 1)) ≤ (3 : ℝ) ^ (-(m : ℝ)) * (1 / (1 - x)) :=
          mul_le_mul_of_nonneg_left hle hp.le
      _ = 1 / (1 - x) * (3 : ℝ) ^ (-1 * (m : ℝ)) := by rw [neg_one_mul]; ring

/-- **Proposition 1.11**, (1.41), for `d ≠ 4`: `E[E(m)] ≤ C 3^{-(d/4 ∧ 1)m} +
C Σ_{n=0}^m 3^{n-m} ω(⌈n/2⌉)`. -/
theorem proposition_1_11_of_ne_four [NeZero d] (hd : d ≠ 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ m : ℕ,
      Integrable (coarseDeviation P m) P ∧
      ∫ a, coarseDeviation P m a ∂P ≤ C * (3 : ℝ) ^ (-(min ((d : ℝ) / 4) 1) * m) +
        C * ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * omegaModulus P ((n + 1) / 2) := by
  obtain ⟨C, hC, h111⟩ := proposition_1_11 (d := d) (Λ := Λ)
  obtain ⟨K, hK, hgeom⟩ := sum_geometric_le_of_ne_four (d := d) hd
  refine ⟨C * (K + 1), by positivity, fun P hP m => ?_⟩
  obtain ⟨hint, hb⟩ := h111 P hP m
  refine ⟨hint, hb.trans ?_⟩
  simp_rw [mul_add, Finset.sum_add_distrib]
  have h1 := hgeom m
  have h3 : 0 ≤ (3 : ℝ) ^ (-(min ((d : ℝ) / 4) 1) * m) := by positivity
  have hS : 0 ≤ ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * omegaModulus P ((n + 1) / 2) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (omegaModulus_nonneg hP
      (by
        rcases isEmpty_or_nonempty (CoefficientField d Λ) with h | h
        · have := hP.1
          have h0 : P = 0 := Measure.eq_zero_of_isEmpty P
          have h1 := measure_univ (μ := P)
          rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
          exact absurd h1 zero_ne_one
        · obtain ⟨a⟩ := h
          exact zero_le_one.trans (one_le_of_coefficientField a)) _)
  have e1 := mul_le_mul_of_nonneg_left h1 hC
  nlinarith [mul_nonneg hC h3, mul_nonneg (mul_nonneg hC hK) h3, mul_nonneg hC hS,
    mul_nonneg (mul_nonneg hC hK) hS]

/-- **The limit in (1.28)**: `ω(n) → 0`. -/
theorem tendsto_omegaModulus {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) : Tendsto (omegaModulus P) atTop (𝓝 0) := by
  set M : ℕ → Mat d := fun n =>
    polarizationMatrix (expectedDirichletEnergy P n) - homogenizedMatrix P
  have hEq : ∀ n e, expectedDirichletEnergy P n e =
      (1 / 2 : ℝ) * dot e ((polarizationMatrix (expectedDirichletEnergy P n)).mulVec e) := by
    intro n e
    exact eq_half_dot_polarizationMatrix (expectedDirichletEnergy_parallelogram hP hΛ n)
      (by positivity : (0 : ℝ) ≤ 1 / 2 * Λ) (fun x => by
        rw [abs_of_nonneg (expectedDirichletEnergy_nonneg P n x)]
        exact expectedDirichletEnergy_le hP hΛ n x) e
  have hbound : ∀ n, omegaModulus P n ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, |M n i j| := by
    intro n
    refine ciSup_le fun p => ?_
    have hp : ∀ i, |(p : Vec d) i| ≤ 1 := fun i =>
      (abs_coord_le_euclideanNorm (p : Vec d) i).trans (le_of_lt p.2)
    rw [hEq n p, limitDirichletEnergy_eq_homogenizedMatrix hP hΛ, ← mul_sub]
    have hsub : dot (p : Vec d) ((polarizationMatrix (expectedDirichletEnergy P n)).mulVec p) -
        dot (p : Vec d) ((homogenizedMatrix P).mulVec p) = ∑ i, ∑ j, (p : Vec d) i * M n i j *
          (p : Vec d) j := by
      simp only [M, dot, Matrix.mulVec, dotProduct, Matrix.sub_apply, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsub]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
      (by norm_num)
    calc (p : Vec d) i * M n i j * (p : Vec d) j ≤ |(p : Vec d) i * M n i j * (p : Vec d) j| :=
          le_abs_self _
      _ = |(p : Vec d) i| * |M n i j| * |(p : Vec d) j| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |M n i j| * 1 := by
          gcongr
          · exact hp i
          · exact hp j
      _ = |M n i j| := by ring
  have hM : ∀ i j, Tendsto (fun n => M n i j) atTop (𝓝 0) := by
    intro i j
    simp only [M, Matrix.sub_apply, homogenizedMatrix, polarizationMatrix, Matrix.of_apply,
      polarization]
    have h1 := tendsto_expectedDirichletEnergy hP hΛ (unitVector i + unitVector j)
    have h2 := tendsto_expectedDirichletEnergy hP hΛ (unitVector i - unitVector j)
    have := (((h1.sub h2).div_const 4).const_mul 2).sub_const
      (2 * ((limitDirichletEnergy P (unitVector i + unitVector j) -
        limitDirichletEnergy P (unitVector i - unitVector j)) / 4))
    rw [sub_self] at this
    exact this
  have hb : Tendsto (fun n => (1 / 2 : ℝ) * ∑ i, ∑ j, |M n i j|) atTop (𝓝 0) := by
    have := (tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ => (hM i j).abs).const_mul
        (1 / 2 : ℝ)
    simpa using this
  exact squeeze_zero (fun n => omegaModulus_nonneg hP hΛ n) hbound hb

theorem tendsto_weighted_sum {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0)) {S : ℝ}
    (hS : ∀ n, |s n| ≤ S) :
    Tendsto (fun m => ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * s n) atTop (𝓝 0) := by
  set f : ℕ → ℕ → ℝ := fun m j => if j ≤ m then (1 / 3 : ℝ) ^ j * s (m - j) else 0
  have hfin : ∀ m, ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * s n = ∑' j, f m j := by
    intro m
    rw [tsum_eq_sum (s := Finset.range (m + 1)) fun j hj => by
      simp only [f, Finset.mem_range, not_lt] at hj ⊢
      split_ifs with h
      · exact absurd h (by omega)
      · rfl]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [f, hj', ↓reduceIte]
    rw [show m - (m + 1 - 1 - j) = j by omega, show m + 1 - 1 - j = m - j by omega, one_div,
      inv_pow]
  simp_rw [hfin]
  suffices key : Tendsto (fun m => ∑' j, f m j) atTop (𝓝 (∑' _j : ℕ, (0 : ℝ))) by
    rwa [tsum_zero] at key
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => S * (1 / 3 : ℝ) ^ j)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left S) (fun j => ?_)
    (Eventually.of_forall fun m j => ?_)
  · have hev : ∀ᶠ m in atTop, (1 / 3 : ℝ) ^ j * s (m - j) = f m j := by
      filter_upwards [eventually_ge_atTop j] with m hm
      simp only [f, hm, ↓reduceIte]
    refine Tendsto.congr' hev ?_
    have := (hs.comp (tendsto_sub_atTop_nat j)).const_mul ((1 / 3 : ℝ) ^ j)
    rw [mul_zero] at this
    exact this
  · simp only [f]
    split_ifs
    · rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3), mul_comm]
      exact mul_le_mul_of_nonneg_right (hS _) (by positivity)
    · rw [norm_zero]
      exact mul_nonneg ((abs_nonneg (s 0)).trans (hS 0)) (by positivity)

/-- **Proposition 1.11, the limit**: `E[E(m)] → 0`. -/
theorem tendsto_integral_coarseDeviation [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) : Tendsto (fun m => ∫ a, coarseDeviation P m a ∂P) atTop (𝓝 0) := by
  have := hP.1
  have hΛ : 0 ≤ Λ := by
    rcases isEmpty_or_nonempty (CoefficientField d Λ) with h | h
    · have h0 : P = 0 := Measure.eq_zero_of_isEmpty P
      have h1 := measure_univ (μ := P)
      rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
      exact absurd h1 zero_ne_one
    · obtain ⟨a⟩ := h
      exact zero_le_one.trans (one_le_of_coefficientField a)
  obtain ⟨C, hC, h111⟩ := proposition_1_11 (d := d) (Λ := Λ)
  set s : ℕ → ℝ := fun n => (3 : ℝ) ^ (-((d : ℝ) * n) / 4) + omegaModulus P ((n + 1) / 2)
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hs : Tendsto s atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (3 : ℝ) ^ (-((d : ℝ) * n) / 4)) atTop (𝓝 0) := by
      have hfun : (fun n : ℕ => (3 : ℝ) ^ (-((d : ℝ) * n) / 4)) =
          fun n : ℕ => ((3 : ℝ) ^ (-(d : ℝ) / 4)) ^ n := funext fun n => by
        rw [← Real.rpow_mul_natCast (by norm_num)]
        congr 1
        ring
      rw [hfun]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
    have h2 : Tendsto (fun n : ℕ => omegaModulus P ((n + 1) / 2)) atTop (𝓝 0) :=
      (tendsto_omegaModulus hP hΛ).comp (Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨2 * b, fun n hn => by omega⟩)
    simpa using h1.add h2
  have hS : ∀ n, |s n| ≤ 1 + (1 / 2 : ℝ) * Λ := by
    intro n
    have h1 : (3 : ℝ) ^ (-((d : ℝ) * n) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have : (0 : ℝ) ≤ (d : ℝ) * n := by positivity
        linarith)
    have h2 : omegaModulus P ((n + 1) / 2) ≤ (1 / 2 : ℝ) * Λ :=
      ciSup_le fun p => by
        have := expectedDirichletEnergy_le hP hΛ ((n + 1) / 2) p
        have := limitDirichletEnergy_nonneg P p
        have := euclideanSq_le_one_of_mem_originBall p.2
        nlinarith
    have h0 : 0 ≤ s n := add_nonneg (by positivity) (omegaModulus_nonneg hP hΛ _)
    rw [abs_of_nonneg h0]
    simp only [s]
    linarith
  have hlim := (tendsto_weighted_sum hs hS).const_mul C
  rw [mul_zero] at hlim
  refine squeeze_zero (fun m => integral_nonneg fun a => sq_nonneg _) (fun m => (h111 P hP m).2) hlim

end QSH
