import QuantitativeStochasticHomogenization.Ch01.Sec04.SubcubeAverages
import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition112
import QuantitativeStochasticHomogenization.Ch01.Sec04.Proposition111

/-!
# Proposition 1.10: weak convergence of the gradient and the flux of the minimizer

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, Proposition 1.10, (1.40): there is `C(d, Λ) < ∞` such that, for every `m ∈ ℕ` and
`p ∈ B₁`,
`3^{-2m} ‖∇v(·, □_m, p) - p‖²_{Ĥ̲⁻¹(□_m)} + 3^{-2m} ‖a∇v(·, □_m, p) - āp‖²_{Ĥ̲⁻¹(□_m)} ≤
C 3^{-2m} + C E(m)`,
with `E(m)` of (1.39) (`coarseDeviation`) and the `Ĥ̲⁻¹` norm of a vector field the sum of the norms
of its components (`vectorHatNegativeSobolevNorm`).

The proof is the book's Step 2: the multiscale Poincaré inequality (Proposition 1.12) for each
component of `∇v - p = g` and of `a∇v - āp`, the bounds (1.14) and (1.16) of their `L̲²(□_m)`
norms, and, for every scale `n < m`, the bounds of the subcube averages
(`subcube_averages_le`) by `|Z_n|⁻¹ Σ_z |a(z + □_n) - ā| + |a(□_m) - ā|`
(`subcube_averages_le_deviation`); finally
`Σ_{n<m} 3^{n-m} ((|Z_n|⁻¹ Σ_z |a(z + □_n) - ā|)^{1/2} + |a(□_m) - ā|^{1/2}) ≤ (5/2) E(m)^{1/2}`
(`sum_three_pow_mul_sqrt_le`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Matrix bounds -/

/-- A symmetric matrix with `0 ≤ ξ·Aξ ≤ c|ξ|²` satisfies `|Aξ| ≤ c|ξ|`. -/
theorem euclideanSq_mulVec_le_of_dot_le {A : Mat d} (hA : A.transpose = A) {c : ℝ}
    (h0 : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v)) (h1 : ∀ v : Vec d, dot v (A.mulVec v) ≤ c * euclideanSq v)
    (v : Vec d) : euclideanSq (A.mulVec v) ≤ c ^ 2 * euclideanSq v := by
  have hcs := sq_dot_mulVec_le hA h0 v (A.mulVec v)
  change euclideanSq (A.mulVec v) ^ 2 ≤ _ at hcs
  have h2 := h1 (A.mulVec v)
  have h3 := h1 v
  have h4 := h0 (A.mulVec v)
  have h5 := h0 v
  have h6 : dot (A.mulVec v) (A.mulVec (A.mulVec v)) * dot v (A.mulVec v) ≤
      (c * euclideanSq (A.mulVec v)) * (c * euclideanSq v) := mul_le_mul h2 h3 h5 (h4.trans h2)
  have hS : 0 ≤ euclideanSq (A.mulVec v) := euclideanSq_nonneg _
  rcases hS.eq_or_lt with h7 | h7
  · rw [← h7]
    exact mul_nonneg (sq_nonneg _) (euclideanSq_nonneg _)
  · have h8 : euclideanSq (A.mulVec v) * euclideanSq (A.mulVec v) ≤
        (c ^ 2 * euclideanSq v) * euclideanSq (A.mulVec v) := by nlinarith
    exact le_of_mul_le_mul_right h8 h7

theorem mulVec_unitVector_apply (A : Mat d) (i j : Fin d) : A.mulVec (unitVector j) i = A i j := by
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

theorem abs_apply_le_of_dot_le {A : Mat d} (hA : A.transpose = A) {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v)) (h1 : ∀ v : Vec d, dot v (A.mulVec v) ≤ c * euclideanSq v)
    (i j : Fin d) : |A i j| ≤ c := by
  have h := euclideanSq_mulVec_le_of_dot_le hA h0 h1 (unitVector j)
  rw [euclideanSq_unitVector, mul_one] at h
  have h2 := sq_apply_le_euclideanSq (A.mulVec (unitVector j)) i
  rw [mulVec_unitVector_apply] at h2
  have := Real.abs_le_sqrt (h2.trans h)
  rwa [Real.sqrt_sq hc] at this

theorem frobeniusNorm_sub_le_of_dot_le {A B : Mat d} {c : ℝ} (hc : 0 ≤ c) (hA : A.transpose = A)
    (hB : B.transpose = B) (hA0 : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v))
    (hA1 : ∀ v : Vec d, dot v (A.mulVec v) ≤ c * euclideanSq v)
    (hB0 : ∀ v : Vec d, 0 ≤ dot v (B.mulVec v))
    (hB1 : ∀ v : Vec d, dot v (B.mulVec v) ≤ c * euclideanSq v) :
    frobeniusNorm (A - B) ≤ 2 * c * d ^ 2 := by
  refine (frobeniusNorm_le_sum_abs _).trans ?_
  have h : ∀ i j, |(A - B) i j| ≤ 2 * c := fun i j => by
    rw [Matrix.sub_apply]
    have h1 := abs_sub (A i j) (B i j)
    have h2 := abs_apply_le_of_dot_le hA hc hA0 hA1 i j
    have h3 := abs_apply_le_of_dot_le hB hc hB0 hB1 i j
    linarith
  calc ∑ i, ∑ j, |(A - B) i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, 2 * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 2 * c * d ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem euclideanSq_mulVec_le_frobeniusSq (M : Mat d) (v : Vec d) :
    euclideanSq (M.mulVec v) ≤ frobeniusSq M * euclideanSq v := by
  unfold euclideanSq dot frobeniusSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) v
  simp only [Matrix.mulVec, dotProduct]
  simpa only [pow_two] using h

theorem abs_dot_mulVec_le_frobeniusNorm (M : Mat d) (v : Vec d) :
    |dot v (M.mulVec v)| ≤ frobeniusNorm M * euclideanSq v := by
  have h1 : dot v (M.mulVec v) ^ 2 ≤ euclideanSq v * euclideanSq (M.mulVec v) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (M.mulVec v)
    simpa only [euclideanSq, dot, pow_two] using this
  have h2 := euclideanSq_mulVec_le_frobeniusSq M v
  have hF : frobeniusNorm M ^ 2 = frobeniusSq M := Real.sq_sqrt (frobeniusSq_nonneg M)
  have hv := euclideanSq_nonneg v
  have h3 : dot v (M.mulVec v) ^ 2 ≤ (frobeniusNorm M * euclideanSq v) ^ 2 := by
    calc dot v (M.mulVec v) ^ 2 ≤ euclideanSq v * euclideanSq (M.mulVec v) := h1
      _ ≤ euclideanSq v * (frobeniusSq M * euclideanSq v) := mul_le_mul_of_nonneg_left h2 hv
      _ = (frobeniusNorm M * euclideanSq v) ^ 2 := by rw [← hF]; ring
  have hf0 : 0 ≤ frobeniusNorm M := Real.sqrt_nonneg _
  have := Real.abs_le_sqrt h3
  rwa [Real.sqrt_sq (mul_nonneg hf0 hv)] at this

theorem euclideanSq_sub_mulVec_le_of_dot_le {A B : Mat d} {c : ℝ} (hc : 0 ≤ c)
    (hA : A.transpose = A) (hB : B.transpose = B) (hA0 : ∀ v : Vec d, 0 ≤ dot v (A.mulVec v))
    (hA1 : ∀ v : Vec d, dot v (A.mulVec v) ≤ c * euclideanSq v)
    (hB0 : ∀ v : Vec d, 0 ≤ dot v (B.mulVec v))
    (hB1 : ∀ v : Vec d, dot v (B.mulVec v) ≤ c * euclideanSq v) {e : Vec d}
    (he : euclideanSq e ≤ 1) :
    euclideanSq ((A - B).mulVec e) ≤ 2 * c * d ^ 2 * frobeniusNorm (A - B) := by
  have h1 := euclideanSq_mulVec_le_frobeniusSq (A - B) e
  have hF : frobeniusSq (A - B) = frobeniusNorm (A - B) * frobeniusNorm (A - B) :=
    (Real.mul_self_sqrt (frobeniusSq_nonneg _)).symm
  have hb := frobeniusNorm_sub_le_of_dot_le hc hA hB hA0 hA1 hB0 hB1
  have hf0 : 0 ≤ frobeniusNorm (A - B) := Real.sqrt_nonneg _
  calc euclideanSq ((A - B).mulVec e) ≤ frobeniusSq (A - B) * euclideanSq e := h1
    _ ≤ frobeniusSq (A - B) * 1 := mul_le_mul_of_nonneg_left he (frobeniusSq_nonneg _)
    _ = frobeniusNorm (A - B) * frobeniusNorm (A - B) := by rw [mul_one, hF]
    _ ≤ 2 * c * d ^ 2 * frobeniusNorm (A - B) := mul_le_mul_of_nonneg_right hb hf0

theorem dot_sub_right' (v x y : Vec d) : dot v (x - y) = dot v x - dot v y := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-! ## Averages -/

theorem setAverage_mono_of_integrableOn {U : Set (Vec d)} {f h : Vec d → ℝ}
    (hf : IntegrableOn f U) (hh : IntegrableOn h U) (hfh : ∀ x, f x ≤ h x) :
    ⨍ x in U, f x ≤ ⨍ x in U, h x := by
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono hf hh hfh) (inv_nonneg.mpr measureReal_nonneg)

theorem setAverage_mul_add_const {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    {A : Vec d → ℝ} (hA : IntegrableOn A U) (c₁ c₂ : ℝ) :
    ⨍ x in U, (c₁ * A x + c₂) = c₁ * (⨍ x in U, A x) + c₂ := by
  rw [setAverage_add_of_integrableOn (hA.const_mul c₁) (integrableOn_const hU),
    setAverage_const hU0 hU]
  congr 1
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, integral_const_mul]
  ring

theorem setAverage_sub_const_of_integrableOn {U : Set (Vec d)} (hU0 : volume U ≠ 0)
    (hU : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : IntegrableOn f U) (c : ℝ) :
    ⨍ x in U, (f x - c) = (⨍ x in U, f x) - c := by
  have h := setAverage_mul_add_const hU0 hU hf 1 (-c)
  simp only [one_mul, ← sub_eq_add_neg] at h
  exact h

theorem euclideanSq_sub_le (x y : Vec d) :
    euclideanSq (x - y) ≤ 2 * euclideanSq x + 2 * euclideanSq y := by
  simp only [euclideanSq, dot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (x i + y i)]

/-- **(1.14), (1.16)**: the minimizer satisfies `⨍_U |p + g|² ≤ Λ|p|²`. -/
theorem IsDirichletMinimizer.setAverage_euclideanSq_le [NeZero d] {a : CoefficientField d Λ}
    {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) {e : Vec d} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hmin : IsDirichletMinimizer a U e u g) :
    ⨍ x in U, euclideanSq (e + g x) ≤ Λ * euclideanSq e := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  have := isFiniteMeasure_restrict.mpr hU
  have hEG : MemLp (fun x => e + g x) 2 (volume.restrict U) := (memLp_const e).add hmin.1.2.1
  have h1 : ⨍ x in U, euclideanSq (e + g x) ≤
      ⨍ x in U, 2 * ((1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x))) :=
    setAverage_mono_of_integrableOn (integrable_euclideanSq_of_memLp hEG)
      ((integrable_energyDensity a hU e hmin.1.2.1).const_mul 2) fun x => by
        have := (a.elliptic x (e + g x)).1
        linarith
  have h2 : ⨍ x in U, 2 * ((1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x))) =
      2 * ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, integral_const_mul]
    ring
  have h3 : ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) =
      dirichletEnergy a U e := hmin.2
  have h4 := dirichletEnergy_le a hU0 hU hΛ e
  linarith

/-! ## The subcube averages and `E(m)` -/

theorem subcubeMean_partitionCube_of_eq_zero (m : ℕ) (F : Set (Vec d) → ℝ) :
    ∀ r, r = 0 → subcubeMean r (fun k => F (partitionCube m r k)) = F (triadicCube d m) := by
  rintro r rfl
  simp only [subcubeMean, partitionCube_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, pow_zero, one_pow, one_smul]
  norm_num

/-- The deviation of the single subcube `□_m` of `□_m`: `|a(□_m) - ā|`. -/
theorem subcubeDeviation_self (P : Measure (CoefficientField d Λ)) (m : ℕ)
    (a : CoefficientField d Λ) :
    subcubeDeviation P m m a = frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) :=
  subcubeMean_partitionCube_of_eq_zero m
    (fun Q => frobeniusNorm (coarseMatrix a Q - homogenizedMatrix P)) (m - m) (Nat.sub_self m)

theorem dirichletEnergy_sub_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (a : CoefficientField d Λ) {U V : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    (hV0 : volume V ≠ 0) (hV : volume V ≠ ⊤) {e : Vec d} (he : euclideanSq e ≤ 1) :
    dirichletEnergy a U e - dirichletEnergy a V e ≤
      (1 / 2 : ℝ) * frobeniusNorm (coarseMatrix a U - homogenizedMatrix P) +
        (1 / 2 : ℝ) * frobeniusNorm (coarseMatrix a V - homogenizedMatrix P) := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  rw [dirichletEnergy_eq_coarseMatrix a hU0 hU hΛ, dirichletEnergy_eq_coarseMatrix a hV0 hV hΛ]
  have h1 := abs_dot_mulVec_le_frobeniusNorm (coarseMatrix a U - homogenizedMatrix P) e
  have h2 := abs_dot_mulVec_le_frobeniusNorm (coarseMatrix a V - homogenizedMatrix P) e
  rw [Matrix.sub_mulVec, dot_sub_right'] at h1 h2
  have hf1 : 0 ≤ frobeniusNorm (coarseMatrix a U - homogenizedMatrix P) := Real.sqrt_nonneg _
  have hf2 : 0 ≤ frobeniusNorm (coarseMatrix a V - homogenizedMatrix P) := Real.sqrt_nonneg _
  have h1' := mul_le_mul_of_nonneg_left he hf1
  have h2' := mul_le_mul_of_nonneg_left he hf2
  rw [abs_le] at h1 h2
  obtain ⟨_, h1b⟩ := h1
  obtain ⟨h2a, _⟩ := h2
  linarith

/-- **The subcube averages at the scale `n ≤ m`**: with `D_n = |Z_n|⁻¹ Σ_z |a(z + □_n) - ā|`,
`|Z_n|⁻¹ Σ_z |(g)_{z+□_n}|² ≤ D_n + |a(□_m) - ā|` and
`|Z_n|⁻¹ Σ_z |(a(p + g))_{z+□_n} - āp|² ≤ (6Λd² + 3Λ²)(D_n + |a(□_m) - ā|)`. -/
theorem subcube_averages_le_deviation [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (a : CoefficientField d Λ) {m n : ℕ} (hnm : n ≤ m) {e : Vec d}
    (he : euclideanSq e ≤ 1) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a (triadicCube d m) e u g) :
    subcubeMean (m - n) (fun k => euclideanSq (vectorAverage (partitionCube n (m - n) k) g)) ≤
        subcubeDeviation P m n a + subcubeDeviation P m m a ∧
      subcubeMean (m - n) (fun k => euclideanSq (vectorAverage (partitionCube n (m - n) k)
          (fun x => (a x).mulVec (e + g x)) - (homogenizedMatrix P).mulVec e)) ≤
        (6 * Λ * d ^ 2 + 3 * Λ ^ 2) * (subcubeDeviation P m n a + subcubeDeviation P m m a) := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  have hm : triadicCube d m = triadicCube d (n + (m - n)) := by rw [Nat.add_sub_cancel' hnm]
  rw [hm] at hmin
  obtain ⟨h1, h2⟩ := subcube_averages_le a n (m - n) hmin (homogenizedMatrix P)
  rw [← hm] at h1 h2
  rw [subcubeDeviation_self]
  have hD : subcubeMean (m - n)
      (fun k => frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P)) =
      subcubeDeviation P m n a := rfl
  have hDW : 0 ≤ frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) :=
    Real.sqrt_nonneg _
  have hDn : 0 ≤ subcubeDeviation P m n a := subcubeDeviation_nonneg P m n a
  have hΔ : subcubeMean (m - n) (fun k => dirichletEnergy a (partitionCube n (m - n) k) e) -
      dirichletEnergy a (triadicCube d m) e ≤ (1 / 2 : ℝ) * subcubeDeviation P m n a +
        (1 / 2 : ℝ) * frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P) := by
    have hk : ∀ k, dirichletEnergy a (partitionCube n (m - n) k) e ≤
        dirichletEnergy a (triadicCube d m) e +
          ((1 / 2 : ℝ) * frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) -
            homogenizedMatrix P) +
          (1 / 2 : ℝ) * frobeniusNorm (coarseMatrix a (triadicCube d m) - homogenizedMatrix P)) :=
      fun k => by
        have := dirichletEnergy_sub_le (P := P) a (volume_partitionCube_ne_zero n (m - n) k)
          (volume_partitionCube_ne_top n (m - n) k) (volume_triadicCube_ne_zero d m)
          (volume_triadicCube_ne_top d m) he
        linarith
    have := subcubeMean_le (m - n) hk
    simp only [subcubeMean_add, subcubeMean_const_mul, subcubeMean_const] at this
    rw [hD] at this
    linarith
  -- the matrices
  have hAbar0 : ∀ v : Vec d, 0 ≤ dot v ((homogenizedMatrix P).mulVec v) := fun v => by
    have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ v
    have := limitDirichletEnergy_nonneg P v
    linarith
  have hAbar1 : ∀ v : Vec d, dot v ((homogenizedMatrix P).mulVec v) ≤ Λ * euclideanSq v :=
    fun v => by
      have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ v
      have := limitDirichletEnergy_le hP hΛ v
      linarith
  have hk2 : ∀ k, euclideanSq ((coarseMatrix a (partitionCube n (m - n) k) -
      homogenizedMatrix P).mulVec e) ≤ 2 * Λ * d ^ 2 *
        frobeniusNorm (coarseMatrix a (partitionCube n (m - n) k) - homogenizedMatrix P) := by
    intro k
    have hQ0 := volume_partitionCube_ne_zero (d := d) n (m - n) k
    have hQt := volume_partitionCube_ne_top (d := d) n (m - n) k
    exact euclideanSq_sub_mulVec_le_of_dot_le hΛ (coarseMatrix_transpose a hQt)
      (homogenizedMatrix_transpose hP hΛ)
      (fun v => (euclideanSq_nonneg v).trans (coarseMatrix_bounds a hQ0 hQt hΛ v).1)
      (fun v => (coarseMatrix_bounds a hQ0 hQt hΛ v).2) hAbar0 hAbar1 he
  have hm2 := subcubeMean_le (m - n) hk2
  simp only [subcubeMean_const_mul] at hm2
  rw [hD] at hm2
  refine ⟨by linarith, ?_⟩
  have h6 : 0 ≤ 6 * Λ ^ 2 := by positivity
  have h7 := mul_le_mul_of_nonneg_left hΔ h6
  have h8 : 0 ≤ 6 * Λ * d ^ 2 * frobeniusNorm (coarseMatrix a (triadicCube d m) -
      homogenizedMatrix P) := by positivity
  nlinarith

/-- `Σ_{n<m} 3^n (D_n^{1/2} + D_m^{1/2}) ≤ (5/2) 3^m E(m)^{1/2}`. -/
theorem sum_three_pow_mul_sqrt_le (P : Measure (CoefficientField d Λ)) (m : ℕ)
    (a : CoefficientField d Λ) :
    ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
      (√(subcubeDeviation P m n a) + √(subcubeDeviation P m m a)) ≤
      (3 : ℝ) ^ m * (5 / 2 * √(coarseDeviation P m a)) := by
  have hw : ∀ n, 0 ≤ ((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m n a) := fun n =>
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hR : √(coarseDeviation P m a) = ∑ n ∈ Finset.range (m + 1),
      ((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m n a) := by
    rw [coarseDeviation, Real.sqrt_sq (Finset.sum_nonneg fun n _ => hw n)]
  have hconv : ∀ n ∈ Finset.range m, (3 : ℝ) ^ n *
      (√(subcubeDeviation P m n a) + √(subcubeDeviation P m m a)) =
      (3 : ℝ) ^ m * (((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m n a) +
        ((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m m a)) := by
    intro n hn
    have hnm : n ≤ m := (Finset.mem_range.mp hn).le
    have h3 : (3 : ℝ) ^ m = (3 : ℝ) ^ n * (3 : ℝ) ^ (m - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hnm]
    have h0 : (3 : ℝ) ^ (m - n) ≠ 0 := by positivity
    have h4 : (3 : ℝ) ^ m * ((3 : ℝ) ^ (m - n))⁻¹ = (3 : ℝ) ^ n := by
      rw [h3, mul_assoc, mul_inv_cancel₀ h0, mul_one]
    rw [← h4]
    ring
  rw [Finset.sum_congr rfl hconv, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hS1 : ∑ n ∈ Finset.range m, ((3 : ℝ) ^ (m - n))⁻¹ * √(subcubeDeviation P m n a) ≤
      √(coarseDeviation P m a) := by
    rw [hR, Finset.sum_range_succ]
    linarith [hw m]
  have hS2 : √(subcubeDeviation P m m a) ≤ √(coarseDeviation P m a) := by
    rw [hR]
    have := Finset.single_le_sum (fun n _ => hw n) (Finset.self_mem_range_succ m)
    simpa using this
  have hS3 : ∑ n ∈ Finset.range m, ((3 : ℝ) ^ (m - n))⁻¹ ≤ 3 / 2 := by
    refine le_trans ?_ (sum_inv_three_pow_le m)
    rw [Finset.sum_range_succ]
    have : (0 : ℝ) ≤ ((3 : ℝ) ^ (m - m))⁻¹ := by positivity
    linarith
  have h0 : 0 ≤ √(subcubeDeviation P m m a) := Real.sqrt_nonneg _
  have h5 := mul_le_mul_of_nonneg_right hS3 h0
  linarith

/-! ## Proposition 1.10 -/

/-- **Proposition 1.10**, (1.40): there is `C(d, Λ) < ∞` such that, for every law `P` satisfying
the assumptions, `m ∈ ℕ`, `a`, `p ∈ B₁` and the minimizer `v(·, □_m, p) = ℓ_p + u` of (1.8) with
gradient `p + g`,
`3^{-2m} ‖∇v(·, □_m, p) - p‖²_{Ĥ̲⁻¹(□_m)} + 3^{-2m} ‖a∇v(·, □_m, p) - āp‖²_{Ĥ̲⁻¹(□_m)} ≤
C 3^{-2m} + C E(m)`. -/
theorem proposition_1_10 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Measure (CoefficientField d Λ)), LawHypotheses P →
      ∀ (m : ℕ) (a : CoefficientField d Λ) (e : Vec d), e ∈ originBall d 1 →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsDirichletMinimizer a (triadicCube d m) e u g →
        ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2) * vectorHatNegativeSobolevNorm (triadicCube d m) g ^ 2 +
          ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2) * vectorHatNegativeSobolevNorm (triadicCube d m)
            (fun x => (a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) ^ 2 ≤
        ENNReal.ofReal (C * ((3 : ℝ) ^ m)⁻¹ ^ 2 + C * coarseDeviation P m a) := by
  by_cases hΛ1 : 1 ≤ Λ
  swap
  · exact ⟨0, le_rfl, fun P _ m a => absurd (one_le_of_coefficientField a) hΛ1⟩
  have hΛ : 0 ≤ Λ := zero_le_one.trans hΛ1
  obtain ⟨C₁, hC₁, h12⟩ := proposition_1_12 (d := d)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 6 * Λ * d ^ 2 + 3 * Λ ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Λ * √(2 * (Λ + 1)) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hB2 : B ^ 2 = Λ ^ 2 * (2 * (Λ + 1)) := by
    rw [hB, mul_pow, Real.sq_sqrt (by positivity)]
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = C₁ * (B + 5 / 2 * (1 + √K)) := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  refine ⟨4 * d ^ 2 * C₂ ^ 2, by positivity, fun P hP m a e he u g hmin => ?_⟩
  have he1 := euclideanSq_le_one_of_mem_originBall he
  have hW0 := volume_triadicCube_ne_zero d m
  have hWt := volume_triadicCube_ne_top d m
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) := isFiniteMeasure_restrict.mpr hWt
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = √(coarseDeviation P m a) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hE0 : 0 ≤ coarseDeviation P m a := sq_nonneg _
  have hE : coarseDeviation P m a = R ^ 2 := by rw [hR, Real.sq_sqrt hE0]
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hX0 : 0 ≤ (3 : ℝ) ^ m * R := mul_nonneg h3m.le hR0
  -- the bounds of `ā`
  have hAbar0 : ∀ v : Vec d, 0 ≤ dot v ((homogenizedMatrix P).mulVec v) := fun v => by
    have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ v
    have := limitDirichletEnergy_nonneg P v
    linarith
  have hAbar1 : ∀ v : Vec d, dot v ((homogenizedMatrix P).mulVec v) ≤ Λ * euclideanSq v :=
    fun v => by
      have h := limitDirichletEnergy_eq_homogenizedMatrix hP hΛ v
      have := limitDirichletEnergy_le hP hΛ v
      linarith
  -- the `L̲²` bounds (1.14), (1.16)
  have hmemg := hmin.1.2.1
  have hmemEG : MemLp (fun x => e + g x) 2 (volume.restrict (triadicCube d m)) :=
    (memLp_const e).add hmemg
  have hEg : ⨍ x in triadicCube d m, euclideanSq (e + g x) ≤ Λ :=
    (hmin.setAverage_euclideanSq_le hW0 hWt).trans (mul_le_of_le_one_right hΛ he1)
  have hIEG : IntegrableOn (fun x => euclideanSq (e + g x)) (triadicCube d m) :=
    integrable_euclideanSq_of_memLp hmemEG
  have hB2' : 2 * (Λ + 1) ≤ B ^ 2 := by
    rw [hB2]
    nlinarith
  have hrms0 : ∀ f : Vec d → ℝ, 0 ≤ scalarRms volume (triadicCube d m) f := fun f =>
    Real.sqrt_nonneg _
  have hrms_g : ∀ i, scalarRms volume (triadicCube d m) (fun x => g x i) ≤ B := by
    intro i
    rw [scalarRms, ← Real.sqrt_sq hB0]
    refine Real.sqrt_le_sqrt ?_
    have hpt : ∀ x, g x i ^ 2 ≤ 2 * euclideanSq (e + g x) + 2 * euclideanSq e := fun x => by
      have h1 := sq_apply_le_euclideanSq (g x) i
      have h2 := euclideanSq_sub_le (e + g x) e
      rw [add_sub_cancel_left] at h2
      linarith
    have hint2 : IntegrableOn (fun x => 2 * euclideanSq (e + g x) + 2 * euclideanSq e)
        (triadicCube d m) := (hIEG.const_mul 2).add (integrableOn_const hWt)
    have h1 := setAverage_mono_of_integrableOn ((hmemg.eval i).integrable_sq) hint2 hpt
    rw [setAverage_mul_add_const hW0 hWt hIEG] at h1
    linarith
  have hrms_q : ∀ i, scalarRms volume (triadicCube d m)
      (fun x => ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i) ≤ B := by
    intro i
    rw [scalarRms, ← Real.sqrt_sq hB0]
    refine Real.sqrt_le_sqrt ?_
    have hpt : ∀ x, ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i ^ 2 ≤
        (2 * Λ ^ 2) * euclideanSq (e + g x) + 2 * Λ ^ 2 * euclideanSq e := fun x => by
      have h1 := sq_apply_le_euclideanSq
        ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i
      have h2 := euclideanSq_sub_le ((a x).mulVec (e + g x)) ((homogenizedMatrix P).mulVec e)
      have h3 := euclideanSq_coefficient_mulVec_le a x (e + g x)
      have h4 := euclideanSq_mulVec_le_of_dot_le (homogenizedMatrix_transpose hP hΛ) hAbar0
        hAbar1 e
      linarith
    have hq : MemLp (fun x => ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i) 2
        (volume.restrict (triadicCube d m)) :=
      (memLp_coefficient_mulVec_apply a hmemEG i).sub (memLp_const _)
    have hint2 : IntegrableOn (fun x => (2 * Λ ^ 2) * euclideanSq (e + g x) +
        2 * Λ ^ 2 * euclideanSq e) (triadicCube d m) :=
      (hIEG.const_mul (2 * Λ ^ 2)).add (integrableOn_const hWt)
    have h1 := setAverage_mono_of_integrableOn hq.integrable_sq hint2 hpt
    rw [setAverage_mul_add_const hW0 hWt hIEG] at h1
    have h2 := mul_le_mul_of_nonneg_left hEg (by positivity : (0 : ℝ) ≤ 2 * Λ ^ 2)
    have h3 := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ 2 * Λ ^ 2)
    rw [hB2]
    linarith
  -- the multiscale sums
  have hsum := sum_three_pow_mul_sqrt_le P m a
  rw [← hR] at hsum
  have hD0 : ∀ n, 0 ≤ subcubeDeviation P m n a := fun n => subcubeDeviation_nonneg P m n a
  have hS_g : ∀ i, ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
      √(1 / ((3 : ℝ) ^ (m - n)) ^ d *
        ∑ k : Fin d → Fin (3 ^ (m - n)), (⨍ x in partitionCube n (m - n) k, g x i) ^ 2) ≤
      (3 : ℝ) ^ m * (5 / 2 * R) := by
    intro i
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) hsum
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnm : n ≤ m := (Finset.mem_range.mp hn).le
    have h1 := (subcube_averages_le_deviation hP a hnm he1 hmin).1
    have h2 : subcubeMean (m - n) (fun k => (⨍ x in partitionCube n (m - n) k, g x i) ^ 2) ≤
        subcubeMean (m - n)
          (fun k => euclideanSq (vectorAverage (partitionCube n (m - n) k) g)) :=
      subcubeMean_le (m - n) fun k =>
        sq_apply_le_euclideanSq (vectorAverage (partitionCube n (m - n) k) g) i
    change √(subcubeMean (m - n) (fun k => (⨍ x in partitionCube n (m - n) k, g x i) ^ 2)) ≤ _
    exact (Real.sqrt_le_sqrt (h2.trans h1)).trans (sqrt_add_le_add_sqrt (hD0 n) (hD0 m))
  have hS_q : ∀ i, ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
      √(1 / ((3 : ℝ) ^ (m - n)) ^ d * ∑ k : Fin d → Fin (3 ^ (m - n)),
        (⨍ x in partitionCube n (m - n) k,
          ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i) ^ 2) ≤
      √K * ((3 : ℝ) ^ m * (5 / 2 * R)) := by
    intro i
    calc _ ≤ ∑ n ∈ Finset.range m, √K * ((3 : ℝ) ^ n *
          (√(subcubeDeviation P m n a) + √(subcubeDeviation P m m a))) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hnm : n ≤ m := (Finset.mem_range.mp hn).le
          rw [mul_left_comm]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 := (subcube_averages_le_deviation hP a hnm he1 hmin).2
          rw [← hK] at h1
          have h2 : subcubeMean (m - n) (fun k => (⨍ x in partitionCube n (m - n) k,
              ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i) ^ 2) ≤
              subcubeMean (m - n) (fun k => euclideanSq (vectorAverage (partitionCube n (m - n) k)
                (fun x => (a x).mulVec (e + g x)) - (homogenizedMatrix P).mulVec e)) := by
            refine subcubeMean_le (m - n) fun k => ?_
            have hQ0 := volume_partitionCube_ne_zero (d := d) n (m - n) k
            have hQt := volume_partitionCube_ne_top (d := d) n (m - n) k
            have hQW : partitionCube n (m - n) k ⊆ triadicCube d m := by
              have := partitionCube_subset (d := d) n (m - n) k
              rwa [Nat.add_sub_cancel' hnm] at this
            have hIW : IntegrableOn (fun x => (a x).mulVec (e + g x) i) (triadicCube d m) :=
              (memLp_coefficient_mulVec_apply a hmemEG i).integrable (by norm_num)
            have hI : IntegrableOn (fun x => (a x).mulVec (e + g x) i) (partitionCube n (m - n) k) :=
              hIW.mono_set hQW
            have h3 : ⨍ x in partitionCube n (m - n) k,
                ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i =
                (vectorAverage (partitionCube n (m - n) k) (fun x => (a x).mulVec (e + g x)) -
                  (homogenizedMatrix P).mulVec e) i :=
              setAverage_sub_const_of_integrableOn hQ0 hQt hI _
            rw [h3]
            exact sq_apply_le_euclideanSq _ i
          change √(subcubeMean (m - n) (fun k => (⨍ x in partitionCube n (m - n) k,
            ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i) ^ 2)) ≤ _
          calc _ ≤ √(K * (subcubeDeviation P m n a + subcubeDeviation P m m a)) :=
                Real.sqrt_le_sqrt (h2.trans h1)
            _ = √K * √(subcubeDeviation P m n a + subcubeDeviation P m m a) :=
                Real.sqrt_mul hK0 _
            _ ≤ √K * (√(subcubeDeviation P m n a) + √(subcubeDeviation P m m a)) :=
                mul_le_mul_of_nonneg_left (sqrt_add_le_add_sqrt (hD0 n) (hD0 m))
                  (Real.sqrt_nonneg _)
      _ = √K * ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
          (√(subcubeDeviation P m n a) + √(subcubeDeviation P m m a)) := by
          rw [Finset.mul_sum]
      _ ≤ √K * ((3 : ℝ) ^ m * (5 / 2 * R)) :=
          mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
  -- the `Ĥ̲⁻¹` bounds of the components
  have hreal : ∀ {r S : ℝ}, 0 ≤ r → r ≤ B → 0 ≤ S → S ≤ (1 + √K) * ((3 : ℝ) ^ m * (5 / 2 * R)) →
      C₁ * r + C₁ * S ≤ C₂ * (1 + (3 : ℝ) ^ m * R) := by
    intro r S _ hr _ hS
    have h1 := mul_le_mul_of_nonneg_left hr hC₁
    have h2 := mul_le_mul_of_nonneg_left hS hC₁
    rw [hC₂]
    nlinarith [mul_nonneg (mul_nonneg hC₁ hB0) hX0, mul_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg K)) hX0,
      mul_nonneg hC₁ (Real.sqrt_nonneg K), mul_nonneg hC₁ hX0]
  have hS_nonneg : ∀ f : Vec d → ℝ, 0 ≤ ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
      √(1 / ((3 : ℝ) ^ (m - n)) ^ d *
        ∑ k : Fin d → Fin (3 ^ (m - n)), (⨍ x in partitionCube n (m - n) k, f x) ^ 2) :=
    fun f => Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hT0 : 0 ≤ (3 : ℝ) ^ m * (5 / 2 * R) := mul_nonneg h3m.le (by linarith)
  have hhat_g : ∀ i, hatNegativeSobolevNorm (triadicCube d m) (fun x => g x i) ≤
      ENNReal.ofReal (C₂ * (1 + (3 : ℝ) ^ m * R)) := fun i =>
    (h12 m (fun x => g x i) (hmemg.eval i)).trans (ENNReal.ofReal_le_ofReal
      (hreal (hrms0 _) (hrms_g i) (hS_nonneg _)
        ((hS_g i).trans (le_mul_of_one_le_left hT0 (by linarith [Real.sqrt_nonneg K])))))
  have hhat_q : ∀ i, hatNegativeSobolevNorm (triadicCube d m)
      (fun x => ((a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) i) ≤
      ENNReal.ofReal (C₂ * (1 + (3 : ℝ) ^ m * R)) := fun i =>
    (h12 m _ ((memLp_coefficient_mulVec_apply a hmemEG i).sub (memLp_const _))).trans
      (ENNReal.ofReal_le_ofReal (hreal (hrms0 _) (hrms_q i) (hS_nonneg _)
        ((hS_q i).trans (mul_le_mul_of_nonneg_right (by linarith) hT0))))
  -- the vector fields
  have hb0 : 0 ≤ C₂ * (1 + (3 : ℝ) ^ m * R) := mul_nonneg hC₂0 (by linarith)
  have hY0 : 0 ≤ d * (C₂ * (1 + (3 : ℝ) ^ m * R)) := mul_nonneg (Nat.cast_nonneg d) hb0
  have hsumd : ∑ _j : Fin d, ENNReal.ofReal (C₂ * (1 + (3 : ℝ) ^ m * R)) =
      ENNReal.ofReal (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun _ : Fin d => C₂ * (1 + (3 : ℝ) ^ m * R)) (fun j _ => hb0)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvg : vectorHatNegativeSobolevNorm (triadicCube d m) g ≤
      ENNReal.ofReal (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) := by
    rw [← hsumd]
    exact Finset.sum_le_sum fun j _ => hhat_g j
  have hvq : vectorHatNegativeSobolevNorm (triadicCube d m)
      (fun x => (a x).mulVec (e + g x) - (homogenizedMatrix P).mulVec e) ≤
      ENNReal.ofReal (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) := by
    rw [← hsumd]
    exact Finset.sum_le_sum fun j _ => hhat_q j
  have hc0 : (0 : ℝ) ≤ ((3 : ℝ) ^ m)⁻¹ ^ 2 := by positivity
  have hsq : ∀ X : ℝ≥0∞, X ≤ ENNReal.ofReal (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) →
      ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2) * X ^ 2 ≤
        ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹ ^ 2 * (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) ^ 2) := by
    intro X hX
    rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow hY0]
    gcongr
  refine (add_le_add (hsq _ hvg) (hsq _ hvq)).trans ?_
  have hA0 : 0 ≤ ((3 : ℝ) ^ m)⁻¹ ^ 2 * (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) ^ 2 := by positivity
  rw [← ENNReal.ofReal_add hA0 hA0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hts : ((3 : ℝ) ^ m)⁻¹ * (3 : ℝ) ^ m = 1 := inv_mul_cancel₀ h3m.ne'
  have e1 : ((3 : ℝ) ^ m)⁻¹ ^ 2 * (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) ^ 2 =
      (d * C₂) ^ 2 * (((3 : ℝ) ^ m)⁻¹ + R) ^ 2 := by
    have h : ((3 : ℝ) ^ m)⁻¹ * (1 + (3 : ℝ) ^ m * R) = ((3 : ℝ) ^ m)⁻¹ + R := by
      rw [mul_add, mul_one, ← mul_assoc, hts, one_mul]
    calc ((3 : ℝ) ^ m)⁻¹ ^ 2 * (d * (C₂ * (1 + (3 : ℝ) ^ m * R))) ^ 2
        = (d * C₂) ^ 2 * (((3 : ℝ) ^ m)⁻¹ * (1 + (3 : ℝ) ^ m * R)) ^ 2 := by ring
      _ = _ := by rw [h]
  rw [e1, hE]
  have h2 : (((3 : ℝ) ^ m)⁻¹ + R) ^ 2 ≤ 2 * ((3 : ℝ) ^ m)⁻¹ ^ 2 + 2 * R ^ 2 := by
    nlinarith [sq_nonneg (((3 : ℝ) ^ m)⁻¹ - R)]
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg ((d : ℝ) * C₂))
  linarith

end QSH
