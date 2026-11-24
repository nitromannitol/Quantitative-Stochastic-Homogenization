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

/-- **(2.55), pointwise**: for the maximizer `w` of `J(□_{n+1}, p, q)` with gradient `h`,
`J(□_n, p, q) ≤ (Λ + ½) ⨍_{□_n} |h|² + 4·3^d Λ² (3^{-d} Σ_z J(z + □_n, p, q) - J(□_{n+1}, p, q))`. -/
theorem dualityDefect_triadicCube_le_center [NeZero d] (a : CoefficientField d Λ) (hΛ : 1 ≤ Λ)
    (n : ℕ) (p q : Vec d) {w : Vec d → ℝ} {h : Vec d → Vec d}
    (hw : IsDefectMaximizer a (triadicCube d (n + 1)) p q w h) :
    dualityDefect a (triadicCube d n) p q ≤
      (Λ + 1 / 2) * (⨍ x in triadicCube d n, euclideanSq (h x)) +
        4 * 3 ^ d * Λ ^ 2 * (∑ z : Fin d → Fin 3, (1 / 3 ^ d : ℝ) *
          dualityDefect a (triadicSubcube n z) p q - dualityDefect a (triadicCube d (n + 1)) p q) := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hUo := isOpen_triadicCube' (d := d) n
  have hUb := isBounded_triadicCube (d := d) n
  have hUc := convex_triadicCube (d := d) n
  have hne := triadicCube_nonempty (d := d) n
  have hU : volume (triadicCube d n) ≠ ⊤ := volume_triadicCube_ne_top d n
  have hU0 : volume (triadicCube d n) ≠ 0 := volume_triadicCube_ne_zero d n
  have := isFiniteMeasure_restrict.mpr hU
  have hV : 0 < volume.real (triadicCube d n) := ENNReal.toReal_pos hU0 hU
  obtain ⟨v, g, hv⟩ := exists_isDefectMaximizer a hUo hUb hUc hne p q
  have hJ := hv.dualityDefect_eq hUb hU0
  have hgL : MemLp g 2 (volume.restrict (triadicCube d n)) := hv.1.1.2.1
  have hsub : triadicCube d n ⊆ triadicCube d (n + 1) := by
    rw [← triadicSubcube_one]
    exact triadicSubcube_subset n _
  have hhL : MemLp h 2 (volume.restrict (triadicCube d n)) :=
    hw.1.1.2.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  -- Lemma 2.12 and the centre subcube
  choose wk hk hwk using fun z => exists_isDefectMaximizer a (isOpen_triadicSubcube n z)
    (isBounded_triadicSubcube n z) (convex_triadicSubcube n z) (triadicSubcube_nonempty n z) p q
  have hS := sum_setAverage_euclideanSq_sub_le a (isBounded_triadicCube (n + 1))
    (isOpen_triadicSubcube n) (pairwise_disjoint_triadicSubcube n) (triadicSubcube_subset n)
    (volume_triadicCube_diff n) (by positivity : (0 : ℝ) ≤ 1 / 3 ^ d)
    (fun z => volumeReal_triadicSubcube_div n z) p q hw hwk
  have hcentre := Finset.single_le_sum (f := fun z : Fin d → Fin 3 => (1 / 3 ^ d : ℝ) *
    ⨍ x in triadicSubcube n z, euclideanSq (h x - hk z x))
    (fun z _ => mul_nonneg (by positivity) (by
      rw [setAverage_eq, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
        (integral_nonneg fun _ => euclideanSq_nonneg _))) (Finset.mem_univ (fun _ => (1 : Fin 3)))
  have hk1 := hwk (fun _ => 1)
  rw [triadicSubcube_one] at hk1 hcentre
  have hae := hk1.ae_eq hUb hU0 hv
  have hcongr : ⨍ x in triadicCube d n, euclideanSq (h x - hk (fun _ => 1) x) =
      ⨍ x in triadicCube d n, euclideanSq (g x - h x) := by
    refine average_congr ?_
    filter_upwards [hae] with x hx
    rw [hx]
    simp only [euclideanSq, dot, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hcongr] at hcentre
  have hgh : ⨍ x in triadicCube d n, euclideanSq (g x - h x) ≤
      2 * 3 ^ d * (∑ z : Fin d → Fin 3, (1 / 3 ^ d : ℝ) *
        dualityDefect a (triadicSubcube n z) p q - dualityDefect a (triadicCube d (n + 1)) p q) := by
    have h3 : (0 : ℝ) < 3 ^ d := by positivity
    have := hcentre.trans hS
    have e : (3 : ℝ) ^ d * ((1 / 3 ^ d : ℝ) * ⨍ x in triadicCube d n, euclideanSq (g x - h x)) =
        ⨍ x in triadicCube d n, euclideanSq (g x - h x) := by field_simp
    rw [← e]
    have h4 := mul_le_mul_of_nonneg_left this h3.le
    linarith
  -- the pointwise splitting, averaged
  have hiG : Integrable (fun x => euclideanSq (g x)) (volume.restrict (triadicCube d n)) :=
    integrable_euclideanSq_of_memLp hgL
  have hiH : Integrable (fun x => euclideanSq (h x)) (volume.restrict (triadicCube d n)) :=
    integrable_euclideanSq_of_memLp hhL
  have hiD : Integrable (fun x => euclideanSq (g x - h x)) (volume.restrict (triadicCube d n)) :=
    integrable_euclideanSq_of_memLp (hgL.sub hhL)
  have hiJ : Integrable (fun x => (1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)))
      (volume.restrict (triadicCube d n)) := (integrable_dot_mulVec a _ hgL).const_mul _
  have hiR : Integrable (fun x => (1 / 2 : ℝ) * Λ * euclideanSq (h x) + Λ ^ 2 * euclideanSq (g x - h x) +
      (1 / 4 : ℝ) * (euclideanSq (g x) + euclideanSq (h x))) (volume.restrict (triadicCube d n)) :=
    ((hiH.const_mul _).add (hiD.const_mul _)).add ((hiG.add hiH).const_mul _)
  have hmono : ⨍ x in triadicCube d n, (1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) ≤
      ⨍ x in triadicCube d n, ((1 / 2 : ℝ) * Λ * euclideanSq (h x) + Λ ^ 2 * euclideanSq (g x - h x) +
        (1 / 4 : ℝ) * (euclideanSq (g x) + euclideanSq (h x))) := by
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (integral_mono hiJ hiR fun x => half_dot_le_split a hΛ x _ _)
      (inv_nonneg.mpr measureReal_nonneg)
  have hlin : ⨍ x in triadicCube d n, ((1 / 2 : ℝ) * Λ * euclideanSq (h x) +
      Λ ^ 2 * euclideanSq (g x - h x) + (1 / 4 : ℝ) * (euclideanSq (g x) + euclideanSq (h x))) =
      (1 / 2 : ℝ) * Λ * (⨍ x in triadicCube d n, euclideanSq (h x)) +
        Λ ^ 2 * (⨍ x in triadicCube d n, euclideanSq (g x - h x)) +
        (1 / 4 : ℝ) * ((⨍ x in triadicCube d n, euclideanSq (g x)) +
          ⨍ x in triadicCube d n, euclideanSq (h x)) := by
    have i1 : Integrable (fun x => (1 / 2 : ℝ) * Λ * euclideanSq (h x))
        (volume.restrict (triadicCube d n)) := hiH.const_mul _
    have i2 : Integrable (fun x => Λ ^ 2 * euclideanSq (g x - h x))
        (volume.restrict (triadicCube d n)) := hiD.const_mul _
    have i12 : Integrable (fun x => (1 / 2 : ℝ) * Λ * euclideanSq (h x) +
        Λ ^ 2 * euclideanSq (g x - h x)) (volume.restrict (triadicCube d n)) := i1.add i2
    have iGH : Integrable (fun x => euclideanSq (g x) + euclideanSq (h x))
        (volume.restrict (triadicCube d n)) := hiG.add hiH
    have i3 : Integrable (fun x => (1 / 4 : ℝ) * (euclideanSq (g x) + euclideanSq (h x)))
        (volume.restrict (triadicCube d n)) := iGH.const_mul _
    simp only [setAverage_eq, smul_eq_mul]
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add hiG hiH]
    ring
  have hg2 := setAverage_euclideanSq_le_two_mul a hU hgL
  rw [← hJ] at hg2 hmono
  rw [hlin] at hmono
  have hΛ2 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
  have := mul_le_mul_of_nonneg_left hgh hΛ2
  have hh0 : 0 ≤ ⨍ x in triadicCube d n, euclideanSq (h x) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun _ => euclideanSq_nonneg _)
  nlinarith

end QSH
