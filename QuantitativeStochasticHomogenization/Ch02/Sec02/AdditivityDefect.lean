import QuantitativeStochasticHomogenization.Ch02.Sec02.Proposition211
import QuantitativeStochasticHomogenization.Ch02.Sec02.DualEnergyTranslation

/-!
# The additivity defect `τ_n`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, the quantity
`τ_n = sup_{p, q ∈ B₁} (E[J(□_n, p, q)] - E[J(□_{n+1}, p, q)])` (`additivityDefect`), the supremum
of a set bounded above (`bddAbove_additivityDefect`), with `τ_n ≥ 0`
(`additivityDefect_nonneg`). For `p, q ∈ B₁`, `0 ≤ J(U, p, q) ≤ ½Λ + 3/2`
(`dualityDefect_le_of_mem_originBall`), so the expectations are of integrable variables, and by
stationarity `E[J(z + □_n, p, q)] = E[J(□_n, p, q)]` for the subcubes `z + □_n` of `□_{n+1}`
(`integral_dualityDefect_triadicSubcube`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The subcubes of `□_{n+1}` -/

theorem convex_preimage_sub {U : Set (Vec d)} (hU : Convex ℝ U) (y : Vec d) :
    Convex ℝ {x : Vec d | x - y ∈ U} := by
  have h := hU.translate_preimage_left (-y)
  convert h using 1
  ext x
  simp [sub_eq_add_neg]

theorem convex_triadicSubcube (n : ℕ) (k : Fin d → Fin 3) : Convex ℝ (triadicSubcube n k) :=
  convex_preimage_sub (convex_triadicCube n) _

theorem isBounded_triadicSubcube (n : ℕ) (k : Fin d → Fin 3) :
    Bornology.IsBounded (triadicSubcube n k) :=
  (isBounded_triadicCube (n + 1)).subset (triadicSubcube_subset n k)

theorem triadicSubcube_nonempty (n : ℕ) (k : Fin d → Fin 3) : (triadicSubcube n k).Nonempty :=
  ⟨latticeShift (subcubeOffset n k), by
    show latticeShift (subcubeOffset n k) - latticeShift (subcubeOffset n k) ∈ triadicCube d n
    rw [sub_self]
    exact mem_triadicCube_iff.mpr fun i => by simp⟩

/-! ## Bounds and integrability of `J` -/

/-- `0 ≤ J(U, p, q) ≤ ½Λ + 3/2` for `p, q ∈ B₁`. -/
theorem dualityDefect_le_of_mem_originBall [NeZero d] (a : CoefficientField d Λ)
    {U : Set (Vec d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {p q : Vec d} (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) :
    0 ≤ dualityDefect a U p q ∧ dualityDefect a U p q ≤ (1 / 2 : ℝ) * Λ + 3 / 2 := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  refine ⟨?_, ?_⟩
  · have := dot_le_dirichletEnergy_add_dualEnergy a hUb hU0 p q
    unfold dualityDefect
    linarith
  · have hJ := dualityDefect_eq_coarseMatrix a hUo hUb hUc hne p q
    have h1 := (coarseMatrix_bounds a hU0 hU hΛ p).2
    have h2 := dot_coarseDualInvMatrix_le a hUo hUb hUc hne q
    have hp1 := euclideanSq_le_one_of_mem_originBall hp
    have hq1 := euclideanSq_le_one_of_mem_originBall hq
    have hpq : -dot p q ≤ 1 := by
      have h := euclideanSq_nonneg (p + q)
      simp only [euclideanSq, dot, Pi.add_apply] at h hp1 hq1 ⊢
      have e : ∑ i, (p i + q i) * (p i + q i) =
          ∑ i, p i * p i + 2 * ∑ i, p i * q i + ∑ i, q i * q i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e] at h
      linarith
    have h5 := mul_le_mul_of_nonneg_left hp1 hΛ
    rw [hJ]
    nlinarith

theorem integrable_dualityDefect [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsFiniteMeasure P] (hΛ : 0 ≤ Λ) {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) {p q : Vec d}
    (hp : p ∈ originBall d 1) (hq : q ∈ originBall d 1) :
    Integrable (fun a => dualityDefect a U p q) P := by
  have hU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hU0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  refine Integrable.of_bound (C := (1 / 2 : ℝ) * Λ + 3 / 2)
    (measurable_dualityDefect hU0 hU hΛ p q).aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  have h := dualityDefect_le_of_mem_originBall a hUo hUb hUc hne hp hq
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- **Stationarity**: `E[J(z + □_n, p, q)] = E[J(□_n, p, q)]` for the subcubes of `□_{n+1}`. -/
theorem integral_dualityDefect_triadicSubcube {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n : ℕ) (k : Fin d → Fin 3) (p q : Vec d) :
    ∫ a, dualityDefect a (triadicSubcube n k) p q ∂P = ∫ a, dualityDefect a (triadicCube d n) p q ∂P := by
  have hf := measurable_dualityDefect (volume_triadicCube_ne_zero d n)
    (volume_triadicCube_ne_top d n) hΛ p q
  rw [← integral_comp_translate hP (subcubeOffset n k) hf]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact dualityDefect_preimage_sub _ a (isOpen_triadicCube n) (volume_triadicCube_ne_top d n) p q

/-! ## The additivity defect -/

/-- **The additivity defect** `τ_n = sup_{p, q ∈ B₁} (E[J(□_n, p, q)] - E[J(□_{n+1}, p, q)])`. -/
def additivityDefect (P : Measure (CoefficientField d Λ)) (n : ℕ) : ℝ :=
  ⨆ pq : originBall d 1 × originBall d 1,
    (∫ a, dualityDefect a (triadicCube d n) pq.1 pq.2 ∂P -
      ∫ a, dualityDefect a (triadicCube d (n + 1)) pq.1 pq.2 ∂P)

theorem bddAbove_additivityDefect [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 0 ≤ Λ) (n : ℕ) :
    BddAbove (Set.range fun pq : originBall d 1 × originBall d 1 =>
      ∫ a, dualityDefect a (triadicCube d n) pq.1 pq.2 ∂P -
        ∫ a, dualityDefect a (triadicCube d (n + 1)) pq.1 pq.2 ∂P) := by
  refine ⟨(1 / 2 : ℝ) * Λ + 3 / 2, ?_⟩
  rintro _ ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, rfl⟩
  have h1 : ∫ a, dualityDefect a (triadicCube d n) p q ∂P ≤ (1 / 2 : ℝ) * Λ + 3 / 2 := by
    have h := integral_mono (integrable_dualityDefect (P := P) hΛ (isOpen_triadicCube' n)
      (isBounded_triadicCube n) (convex_triadicCube n) (triadicCube_nonempty n) hp hq)
      (integrable_const ((1 / 2 : ℝ) * Λ + 3 / 2)) fun a =>
        (dualityDefect_le_of_mem_originBall a (isOpen_triadicCube' n) (isBounded_triadicCube n)
          (convex_triadicCube n) (triadicCube_nonempty n) hp hq).2
    rwa [integral_const, probReal_univ, one_smul] at h
  have h2 : 0 ≤ ∫ a, dualityDefect a (triadicCube d (n + 1)) p q ∂P :=
    integral_nonneg fun a => (dualityDefect_le_of_mem_originBall a (isOpen_triadicCube' (n + 1))
      (isBounded_triadicCube (n + 1)) (convex_triadicCube (n + 1)) (triadicCube_nonempty (n + 1))
      hp hq).1
  show _ - _ ≤ _
  linarith

theorem sub_le_additivityDefect [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 0 ≤ Λ) (n : ℕ) {p q : Vec d} (hp : p ∈ originBall d 1)
    (hq : q ∈ originBall d 1) :
    ∫ a, dualityDefect a (triadicCube d n) p q ∂P -
        ∫ a, dualityDefect a (triadicCube d (n + 1)) p q ∂P ≤ additivityDefect P n :=
  le_ciSup (f := fun pq : originBall d 1 × originBall d 1 =>
    ∫ a, dualityDefect a (triadicCube d n) pq.1 pq.2 ∂P -
      ∫ a, dualityDefect a (triadicCube d (n + 1)) pq.1 pq.2 ∂P)
    (bddAbove_additivityDefect hΛ n) (⟨p, hp⟩, ⟨q, hq⟩)

theorem dualityDefect_zero_zero [NeZero d] (a : CoefficientField d Λ) {U : Set (Vec d)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUc : Convex ℝ U) (hne : U.Nonempty) :
    dualityDefect a U 0 0 = 0 := by
  rw [dualityDefect_eq_coarseMatrix a hUo hUb hUc hne]
  simp [dot]

theorem additivityDefect_nonneg [NeZero d] {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (hΛ : 0 ≤ Λ) (n : ℕ) : 0 ≤ additivityDefect P n := by
  have h := sub_le_additivityDefect (P := P) hΛ n zero_mem_originBall zero_mem_originBall
  have e1 : ∀ m : ℕ, ∫ a, dualityDefect a (triadicCube d m) 0 0 ∂P = 0 := fun m => by
    rw [integral_congr_ae (Eventually.of_forall fun a => dualityDefect_zero_zero a
      (isOpen_triadicCube' m) (isBounded_triadicCube m) (convex_triadicCube m)
      (triadicCube_nonempty m)), integral_zero]
  rw [e1, e1, sub_zero] at h
  exact h

end QSH
