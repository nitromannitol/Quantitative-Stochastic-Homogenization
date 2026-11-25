import QuantitativeStochasticHomogenization.Ch02.Sec01.Theorem24

/-!
# The stochastic bounds of `E(m)` and of `|a(□_m) - ā| + |a*(□_m) - ā|` in Theorem 2.17

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.3, the proof of Theorem 2.17 from (2.67) on, with the bound of Theorem 2.4 as a
hypothesis `|a(□_n) - ā| + |a*(□_n) - ā| ≤ c 3^{-nγ} + O₁(θ 3^{-nσ})` for every `n`:

* `osBound_subcubeDeviation_sub`: by stationarity, the same bound for the average
  `|Z_n|⁻¹ Σ_{z ∈ Z_n} |a(z + □_n) - ā|` over the subcubes of `□_m`;
* `sqrt_coarseDeviation_le_os`, the claim (2.68): `E(m)^{1/2} ≤ C 3^{-mγ/2} + ρ + V` with
  `V ≤ O₁(K ρ^{1-2d} 3^{-mσ})`, for every `ρ > 0`. The proof is the book's: the square roots of the
  averages exceed `(c 3^{-nγ})^{1/2}` by at most `O₂`, they are bounded, so by Lemma A.3 by
  `O_{2d}(C 3^{-nσ/(2d)})` (the book uses `O_d`; `2d > 2` lets Lemma A.3 apply also for `d = 2`);
  the weighted sum over `n` is `O_{2d}(C 3^{-mσ/(2d)})` by the triangle inequality, and Young's
  inequality (2.23) of Remark 2.6 turns `O_{2d}` into `ρ + O₁`;
* `sqrt_le_two_mul_sqrt_add_os`, the inequality (2.65) in the form used for `J(□_m, ā⁻¹q, q)`:
  `X^{1/2} ≤ 2 c^{1/2} + c^{-1/2} (X - c)₊` with `c^{-1/2} (X - c)₊ ≤ O₁(c^{-1/2} θ)`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Elementary inequalities -/

/-- `Σ_{n=0}^m 3^{n-m} 3^{-nγ} ≤ (1 - 3^{γ-1})⁻¹ 3^{-mγ}` for `0 ≤ γ < 1`. -/
theorem sum_inv_three_pow_mul_rpow_le {γ : ℝ} (hγ1 : γ < 1) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * (3 : ℝ) ^ (-((n : ℝ) * γ)) ≤
      (1 - (3 : ℝ) ^ (γ - 1))⁻¹ * (3 : ℝ) ^ (-((m : ℝ) * γ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hx0 : 0 < (3 : ℝ) ^ (γ - 1) := Real.rpow_pos_of_pos h3 _
  have hx1 : (3 : ℝ) ^ (γ - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ n ∈ Finset.range (m + 1),
      ((3 : ℝ) ^ (m - n))⁻¹ * (3 : ℝ) ^ (-((n : ℝ) * γ)) =
        (3 : ℝ) ^ (-((m : ℝ) * γ)) * ((3 : ℝ) ^ (γ - 1)) ^ (m - n) := by
    intro n hn
    have hnm : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [← Real.rpow_natCast (3 : ℝ) (m - n), ← Real.rpow_neg h3.le,
      ← Real.rpow_natCast ((3 : ℝ) ^ (γ - 1)) (m - n), ← Real.rpow_mul h3.le,
      ← Real.rpow_add h3, ← Real.rpow_add h3, Nat.cast_sub hnm]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_comm]
  have hrefl : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (γ - 1)) ^ (m - n) =
      ∑ j ∈ Finset.range (m + 1), ((3 : ℝ) ^ (γ - 1)) ^ j := by
    rw [← Finset.sum_range_reflect (fun j => ((3 : ℝ) ^ (γ - 1)) ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  rw [hrefl]
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1) hx0.le hx1
  rw [← Finset.range_eq_Ico, pow_zero, one_div] at hg
  exact mul_le_mul_of_nonneg_right hg (by positivity)

/-- **Young's inequality (2.23)** of Remark 2.6: `Z ≤ ρ + ρ^{1-r} Z^r` for `Z ≥ 0`, `ρ > 0`,
`r ≥ 1`. -/
theorem le_add_rpow_mul_rpow {Z ρ r : ℝ} (hZ : 0 ≤ Z) (hρ : 0 < ρ) (hr : 1 ≤ r) :
    Z ≤ ρ + ρ ^ (1 - r) * Z ^ r := by
  rcases le_or_gt Z ρ with h | h
  · have : 0 ≤ ρ ^ (1 - r) * Z ^ r := by positivity
    linarith
  · have hZ0 : 0 < Z := hρ.trans h
    have h1 : ρ ^ (r - 1) ≤ Z ^ (r - 1) := Real.rpow_le_rpow hρ.le h.le (by linarith)
    have h2 : Z ^ r = Z * Z ^ (r - 1) := by
      calc Z ^ r = Z ^ ((1 : ℝ) + (r - 1)) := by congr 1; ring
        _ = Z ^ (1 : ℝ) * Z ^ (r - 1) := Real.rpow_add hZ0 _ _
        _ = Z * Z ^ (r - 1) := by rw [Real.rpow_one]
    have h3 : ρ ^ (1 - r) * ρ ^ (r - 1) = 1 := by
      rw [← Real.rpow_add hρ]
      simp
    have h4 : Z ≤ ρ ^ (1 - r) * Z ^ r := by
      rw [h2]
      calc Z = Z * (ρ ^ (1 - r) * ρ ^ (r - 1)) := by rw [h3, mul_one]
        _ ≤ Z * (ρ ^ (1 - r) * Z ^ (r - 1)) := by gcongr
        _ = ρ ^ (1 - r) * (Z * Z ^ (r - 1)) := by ring
    linarith

/-- `(√x - √y)₊ ≤ √((x - y)₊)` for `y ≥ 0`. -/
theorem max_sqrt_sub_sqrt_le {x y : ℝ} (hy : 0 ≤ y) :
    max (√x - √y) 0 ≤ √(max (x - y) 0) := by
  refine max_le ?_ (Real.sqrt_nonneg _)
  have hM : 0 ≤ max (x - y) 0 := le_max_right _ _
  have h1 : √x ≤ √(y + max (x - y) 0) :=
    Real.sqrt_le_sqrt (by linarith [le_max_left (x - y) 0])
  have h2 : √(y + max (x - y) 0) ≤ √y + √(max (x - y) 0) := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 := Real.sq_sqrt hy
    have e2 := Real.sq_sqrt hM
    nlinarith [mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg (max (x - y) 0))]
  linarith

/-- `√y ≤ t + t⁻¹ y` for `y ≥ 0` and `t > 0`. -/
theorem sqrt_le_add_inv_mul {y t : ℝ} (hy : 0 ≤ y) (ht : 0 < t) : √y ≤ t + t⁻¹ * y := by
  have h1 : √y * t ≤ t ^ 2 + y := by
    nlinarith [sq_nonneg (√y - t), Real.sq_sqrt hy, Real.sqrt_nonneg y]
  have e : t + t⁻¹ * y = (t ^ 2 + y) / t := by
    field_simp
  rw [e, le_div_iff₀ ht]
  exact h1

/-- The positive part of a variable `X ≤ O_s(θ)` is `O_s(θ)`. -/
theorem OsBound.sup_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {s θ : ℝ} (h : OsBound P X s θ) : OsBound P (fun ω => max (X ω) 0) s θ := by
  obtain ⟨hm, hs, hθ, hint⟩ := h
  refine ⟨hm.max measurable_const, hs, hθ, ?_⟩
  have e : ∀ ω, max (max (X ω) 0) 0 = max (X ω) 0 := fun ω => max_eq_left (le_max_right _ _)
  simpa only [e] using hint

/-! ## The averages over the subcubes -/

theorem card_fun_fin_three_pow (r : ℕ) :
    ((Fintype.card (Fin d → Fin (3 ^ r)) : ℕ) : ℝ) = ((3 : ℝ) ^ r) ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  ring

/-- **The averages over the subcubes**: if `|a(□_n) - ā| + |a*(□_n) - ā| ≤ c + O₁(θ)`, then by
stationarity `|Z_n|⁻¹ Σ_{z ∈ Z_n} |a(z + □_n) - ā| ≤ c + O₁(θ)` for the subcubes of `□_m`. -/
theorem osBound_subcubeDeviation_sub {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (m n : ℕ) {c θ : ℝ}
    (h : OsBound P (fun a =>
      frobeniusNorm (coarseMatrix a (triadicCube d n) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix a (triadicCube d n) - homogenizedMatrix P) - c) 1 θ) :
    OsBound P (fun a => subcubeDeviation P m n a - c) 1 θ := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((3 : ℝ) ^ (m - n)) ^ d := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; positivity
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin d → Fin (3 ^ (m - n)))), OsBound P (fun a => N⁻¹ *
      (frobeniusNorm (coarseMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) - c)) 1 (N⁻¹ * θ) := fun k _ =>
    (h.comp_measurePreserving ⟨measurable_translateCoefficient _, hP.2.1 _⟩).const_mul
      (inv_pos.mpr hN0)
  have hne : (Finset.univ : Finset (Fin d → Fin (3 ^ (m - n)))).Nonempty :=
    ⟨fun _ => ⟨0, pow_pos (by norm_num) _⟩, Finset.mem_univ _⟩
  have hsum := osBound_finset_sum Finset.univ hne le_rfl hX
  have hscale : ∑ _k : Fin d → Fin (3 ^ (m - n)), N⁻¹ * θ = θ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_fun_fin_three_pow, ← hN,
      ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
  rw [hscale] at hsum
  refine hsum.of_le ((measurable_subcubeDeviation hΛ P m n).sub_const c) fun a => ?_
  have hk : ∀ k : Fin d → Fin (3 ^ (m - n)),
      frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P) ≤
        frobeniusNorm (coarseMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) := fun k => by
    rw [coarseMatrix_partitionCube]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have e : ∑ k : Fin d → Fin (3 ^ (m - n)), N⁻¹ *
      (frobeniusNorm (coarseMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) - c) =
      N⁻¹ * ∑ k : Fin d → Fin (3 ^ (m - n)),
        (frobeniusNorm (coarseMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix (translate (latticeShift (partitionCenter n (m - n) k)) a)
          (triadicCube d n) - homogenizedMatrix P)) - c := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, card_fun_fin_three_pow, ← hN, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ hN0.ne', one_mul]
  rw [e]
  unfold subcubeDeviation
  rw [← hN, one_div]
  have h1 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun k _ => hk k)
    (inv_nonneg.mpr hN0.le)
  linarith

/-- The averages over the subcubes are bounded by the structural constant. -/
theorem subcubeDeviation_le_structuralMatrixConst [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (m n : ℕ) (a : CoefficientField d Λ) :
    subcubeDeviation P m n a ≤ structuralMatrixConst d Λ := by
  have hk : ∀ k : Fin d → Fin (3 ^ (m - n)),
      frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P) ≤
        structuralMatrixConst d Λ := fun k => by
    rw [coarseMatrix_partitionCube]
    refine le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (frobeniusNorm_sub_homogenizedMatrix_add_le hP _ (isOpen_triadicCube' n)
        (isBounded_triadicCube n) (convex_triadicCube n) (triadicCube_nonempty n))
  have hN0 : (0 : ℝ) < ((3 : ℝ) ^ (m - n)) ^ d := by positivity
  have h1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_fun_fin_three_pow] at h1
  unfold subcubeDeviation
  calc 1 / ((3 : ℝ) ^ (m - n)) ^ d * ∑ k : Fin d → Fin (3 ^ (m - n)),
        frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P)
      ≤ 1 / ((3 : ℝ) ^ (m - n)) ^ d * (((3 : ℝ) ^ (m - n)) ^ d * structuralMatrixConst d Λ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = structuralMatrixConst d Λ := by field_simp

/-! ## The bound (2.68) of `E(m)` -/

/-- **(2.68)**: if for every `n`, `|a(□_n) - ā| + |a*(□_n) - ā| ≤ c 3^{-nγ} + O₁(θ 3^{-nσ})` with
`γ ≤ 1` and `0 < σ < d`, then there is `K > 0` such that for every `m ∈ ℕ` and `ρ > 0` there is
`V ≤ O₁(K ρ^{1-2d} 3^{-mσ})` with
`E(m)^{1/2} ≤ c^{1/2} (1 - 3^{γ/2-1})⁻¹ 3^{-mγ/2} + ρ + V`. -/
theorem sqrt_coarseDeviation_le_os (hd : 2 ≤ d) {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) {c θ σ γ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hσ : 0 < σ)
    (hσd : σ < d) (hγ1 : γ ≤ 1)
    (h24 : ∀ n : ℕ, OsBound P (fun a =>
      frobeniusNorm (coarseMatrix a (triadicCube d n) - homogenizedMatrix P) +
        frobeniusNorm (coarseDualMatrix a (triadicCube d n) - homogenizedMatrix P) -
          c * (3 : ℝ) ^ (-((n : ℝ) * γ))) 1 (θ * (3 : ℝ) ^ (-((n : ℝ) * σ)))) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ∃ V : CoefficientField d Λ → ℝ,
      OsBound P V 1 (K * ρ ^ (1 - 2 * (d : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) * σ))) ∧
      ∀ a, √(coarseDeviation P m a) ≤
        √c * (1 - (3 : ℝ) ^ (γ / 2 - 1))⁻¹ * (3 : ℝ) ^ (-((m : ℝ) * (γ / 2))) + ρ + V a := by
  have : NeZero d := ⟨by omega⟩
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) < 2 * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : (1 : ℝ) ≤ 2 * d := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = √(structuralMatrixConst d Λ) + 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = σ / (2 * d) := ⟨_, rfl⟩
  have hκ1 : κ < 1 := by
    rw [hκ, div_lt_one (by positivity)]
    linarith
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = B * (B⁻¹ * θ ^ (1 / 2 : ℝ)) ^ ((2 : ℝ) / (2 * d)) :=
    ⟨_, rfl⟩
  have hK₃0 : 0 < K₃ := by rw [hK₃]; positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (1 - (3 : ℝ) ^ (κ - 1))⁻¹ := ⟨_, rfl⟩
  have hG0 : 0 < G := by
    rw [hG]
    have : (3 : ℝ) ^ (κ - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_pos.mpr (by linarith)
  refine ⟨(K₃ * G) ^ (2 * (d : ℝ)), by positivity, fun m ρ hρ => ?_⟩
  -- the square roots of the averages over the subcubes
  have hW : ∀ n : ℕ, OsBound P (fun a => max (√(subcubeDeviation P m n a) -
      √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0) (2 * d) (K₃ * (3 : ℝ) ^ (-((n : ℝ) * κ))) := by
    intro n
    have hcn : 0 ≤ c * (3 : ℝ) ^ (-((n : ℝ) * γ)) := by positivity
    have h1 := (osBound_subcubeDeviation_sub hP hΛ m n (h24 n)).sup_zero.rpow
      (fun a => le_max_right _ _) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at h1
    have hWm : Measurable fun a => max (√(subcubeDeviation P m n a) -
        √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0 :=
      ((measurable_subcubeDeviation hΛ P m n).sqrt.sub_const _).max measurable_const
    have h2 := h1.of_le hWm fun a => by
      rw [← Real.sqrt_eq_rpow]
      exact max_sqrt_sub_sqrt_le hcn
    have hW0 : ∀ a, 0 ≤ max (√(subcubeDeviation P m n a) -
        √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0 := fun a => le_max_right _ _
    have hWB : ∀ a, max (√(subcubeDeviation P m n a) -
        √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0 ≤ B := fun a => by
      refine max_le ?_ hB0.le
      have := Real.sqrt_le_sqrt (subcubeDeviation_le_structuralMatrixConst hP m n a)
      have := Real.sqrt_nonneg (c * (3 : ℝ) ^ (-((n : ℝ) * γ)))
      rw [hB]
      linarith
    have h3' := (h2.const_mul (inv_pos.mpr hB0)).of_mem_Icc
      (fun a => mul_nonneg (inv_nonneg.mpr hB0.le) (hW0 a))
      (fun a => by
        rw [inv_mul_le_iff₀ hB0, mul_one]
        exact hWB a) hd2
    have h4 := (h3'.const_mul hB0).of_le hWm fun a => by
      rw [← mul_assoc, mul_inv_cancel₀ hB0.ne', one_mul]
    have e : B * (B⁻¹ * (θ * (3 : ℝ) ^ (-((n : ℝ) * σ))) ^ (1 / 2 : ℝ)) ^ ((2 : ℝ) / (2 * d)) =
        K₃ * (3 : ℝ) ^ (-((n : ℝ) * κ)) := by
      rw [Real.mul_rpow hθ.le (by positivity), ← mul_assoc,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul h3.le,
        ← Real.rpow_mul h3.le, ← mul_assoc, hK₃, hκ]
      congr 2
      field_simp
    rw [← e]
    exact h4
  -- the weighted sum over the scales
  have hZ := osBound_finset_sum (Finset.range (m + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
    (X := fun n a => ((3 : ℝ) ^ (m - n))⁻¹ * max (√(subcubeDeviation P m n a) -
      √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0)
    (θ := fun n => ((3 : ℝ) ^ (m - n))⁻¹ * (K₃ * (3 : ℝ) ^ (-((n : ℝ) * κ)))) hd1
    (fun n _ => (hW n).const_mul (by positivity))
  have hscale : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
      (K₃ * (3 : ℝ) ^ (-((n : ℝ) * κ))) ≤ K₃ * (G * (3 : ℝ) ^ (-((m : ℝ) * κ))) := by
    have e : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
        (K₃ * (3 : ℝ) ^ (-((n : ℝ) * κ))) = K₃ * ∑ n ∈ Finset.range (m + 1),
          ((3 : ℝ) ^ (m - n))⁻¹ * (3 : ℝ) ^ (-((n : ℝ) * κ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e, hG]
    exact mul_le_mul_of_nonneg_left (sum_inv_three_pow_mul_rpow_le hκ1 m) hK₃0.le
  have hZ' := hZ.mono_scale hscale
  have hZ0 : ∀ a, 0 ≤ ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
      max (√(subcubeDeviation P m n a) - √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0 := fun a =>
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (le_max_right _ _)
  have h5 := hZ'.rpow hZ0 (by positivity : (0 : ℝ) < 2 * d)
  rw [div_self (by positivity : (2 : ℝ) * d ≠ 0)] at h5
  have h6 := h5.const_mul (Real.rpow_pos_of_pos hρ (1 - 2 * (d : ℝ)))
  refine ⟨fun a => ρ ^ (1 - 2 * (d : ℝ)) * (∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
      max (√(subcubeDeviation P m n a) - √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0) ^ (2 * (d : ℝ)),
    ?_, fun a => ?_⟩
  · have e : (K₃ * G) ^ (2 * (d : ℝ)) * ρ ^ (1 - 2 * (d : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) * σ)) =
        ρ ^ (1 - 2 * (d : ℝ)) * (K₃ * (G * (3 : ℝ) ^ (-((m : ℝ) * κ)))) ^ (2 * (d : ℝ)) := by
      rw [← mul_assoc K₃, Real.mul_rpow (x := K₃ * G) (y := (3 : ℝ) ^ (-((m : ℝ) * κ)))
        (by positivity) (by positivity), ← Real.rpow_mul h3.le,
        hκ, show -((m : ℝ) * (σ / (2 * d))) * (2 * d) = -((m : ℝ) * σ) by field_simp]
      ring
    rw [e]
    exact h6
  · have hE : √(coarseDeviation P m a) = ∑ n ∈ Finset.range (m + 1),
        ((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m n a) := by
      unfold coarseDeviation
      exact Real.sqrt_sq (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity)
        (Real.sqrt_nonneg _))
    have hsplit : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m n a) ≤
        ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ * √(c * (3 : ℝ) ^ (-((n : ℝ) * γ))) +
        ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
          max (√(subcubeDeviation P m n a) - √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := le_max_left (√(subcubeDeviation P m n a) -
        √(c * (3 : ℝ) ^ (-((n : ℝ) * γ)))) 0
      linarith
    have hD : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
        √(c * (3 : ℝ) ^ (-((n : ℝ) * γ))) ≤
        √c * (1 - (3 : ℝ) ^ (γ / 2 - 1))⁻¹ * (3 : ℝ) ^ (-((m : ℝ) * (γ / 2))) := by
      have e : ∀ n : ℕ, √(c * (3 : ℝ) ^ (-((n : ℝ) * γ))) =
          √c * (3 : ℝ) ^ (-((n : ℝ) * (γ / 2))) := fun n => by
        rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow ((3 : ℝ) ^ _), ← Real.rpow_mul h3.le]
        congr 2
        ring
      have e2 : ∑ n ∈ Finset.range (m + 1), ((3 : ℝ) ^ (m - n))⁻¹ *
          √(c * (3 : ℝ) ^ (-((n : ℝ) * γ))) = √c * ∑ n ∈ Finset.range (m + 1),
            ((3 : ℝ) ^ (m - n))⁻¹ * (3 : ℝ) ^ (-((n : ℝ) * (γ / 2))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by rw [e n]; ring
      rw [e2, mul_assoc]
      exact mul_le_mul_of_nonneg_left (sum_inv_three_pow_mul_rpow_le (by linarith) m)
        (Real.sqrt_nonneg _)
    have hY := le_add_rpow_mul_rpow (hZ0 a) hρ hd1
    rw [hE]
    linarith

/-! ## The inequality (2.65) -/

/-- **(2.65)** in the form used for `J(□_m, ā⁻¹q, q)`: if `X ≤ c + O₁(θ)` with `c > 0`,
then `X^{1/2} ≤ 2 c^{1/2} + c^{-1/2} (X - c)₊` and `c^{-1/2} (X - c)₊ ≤ O₁(c^{-1/2} θ)`. -/
theorem sqrt_le_two_mul_sqrt_add_os {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {c θ : ℝ} (hc : 0 < c) (h : OsBound P (fun ω => X ω - c) 1 θ) :
    OsBound P (fun ω => (√c)⁻¹ * max (X ω - c) 0) 1 ((√c)⁻¹ * θ) ∧
      ∀ ω, √(X ω) ≤ 2 * √c + (√c)⁻¹ * max (X ω - c) 0 := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  refine ⟨h.sup_zero.const_mul (inv_pos.mpr hsc), fun ω => ?_⟩
  have h1 := max_sqrt_sub_sqrt_le (x := X ω) hc.le
  have h2 := sqrt_le_add_inv_mul (le_max_right (X ω - c) 0) hsc
  have h3 := le_max_left (√(X ω) - √c) 0
  linarith

end QSH
