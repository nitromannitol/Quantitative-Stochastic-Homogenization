import QuantitativeStochasticHomogenization.Ch02.Sec02.AdditivityDefect
import QuantitativeStochasticHomogenization.Ch02.Sec02.MaximizerAverage
import QuantitativeStochasticHomogenization.Ch02.Sec02.Lemma212

/-!
# The mean gradients of the maximizers on `□_{n+1}` and on its subcubes

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2, Step 1 of the proof of Lemma 2.13, (2.37)–(2.38) for `m = n + 1`. Write
`M(U) = a*⁻¹(U) q - p` for the mean gradient of the maximizer `v(·, U, p, q)` (`meanGradient`; it is
`⨍_U ∇v(·, U, p, q)` by (2.43)). Then, with the `3^d` subcubes `z + □_n` of `□_{n+1}`,
`|M(□_{n+1}) - 3^{-d} Σ_z M(z + □_n)|² ≤ 2 (3^{-d} Σ_z J(z + □_n, p, q) - J(□_{n+1}, p, q))`
(`euclideanSq_meanGradient_succ_sub_le`): the left side is `|3^{-d} Σ_z ⨍_{z + □_n} (∇v - ∇v_z)|²`,
bounded by Jensen's inequality and `a ≥ Id` by `3^{-d} Σ_z ⨍_{z + □_n} (∇v - ∇v_z)·a(∇v - ∇v_z)`,
which Lemma 2.12 evaluates. Taking expectations and using stationarity, the expectation of the left
side is at most `2 τ_n` for `p, q ∈ B₁` (`integral_euclideanSq_meanGradient_succ_sub_le`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The mean gradient `a*⁻¹(U) q - p` of the maximizer of `J(U, p, q)`, (2.43). -/
def meanGradient (a : CoefficientField d Λ) (U : Set (Vec d)) (p q : Vec d) : Vec d :=
  (coarseDualInvMatrix a U).mulVec q - p

/-- The average over `U` is the weighted sum of the averages over a partition of `U`, up to a null
set, by pairwise disjoint open sets. -/
theorem setAverage_eq_sum_of_partition {ι : Type*} [Fintype ι] {U : Set (Vec d)}
    (hU : volume U ≠ ⊤) {Q : ι → Set (Vec d)} (hQo : ∀ k, IsOpen (Q k))
    (hdisj : Pairwise (Function.onFun Disjoint Q)) (hsub : ∀ k, Q k ⊆ U)
    (hcover : volume (U \ ⋃ k, Q k) = 0) {f : Vec d → ℝ} (hf : IntegrableOn f U volume) :
    ⨍ x in U, f x = ∑ k, (volume.real (Q k) / volume.real U) * ⨍ x in Q k, f x := by
  have hae : U =ᵐ[volume] ⋃ k, Q k := by
    refine ae_eq_set.mpr ⟨hcover, ?_⟩
    rw [sdiff_eq_empty.mpr (iUnion_subset hsub), measure_empty]
  have hsplit : ∫ x in U, f x = ∑ k, ∫ x in Q k, f x := by
    rw [setIntegral_congr_set hae, integral_iUnion_fintype (fun k => (hQo k).measurableSet) hdisj
      fun k => hf.mono_set (hsub k)]
  rw [setAverage_eq, smul_eq_mul, hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hQ : volume (Q k) ≠ ⊤ := ne_top_of_le_ne_top hU (measure_mono (hsub k))
  rw [setAverage_eq, smul_eq_mul]
  rcases eq_or_ne (volume (Q k)) 0 with h0 | h0
  · rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
    simp [Measure.real, h0]
  · have hpos : 0 < volume.real (Q k) := ENNReal.toReal_pos h0 hQ
    field_simp

/-- Jensen's inequality for the uniform average over `{0, 1, 2}^d`. -/
theorem sq_sum_div_le_sum_sq_div (y : (Fin d → Fin 3) → ℝ) :
    (∑ k, (1 / 3 ^ d : ℝ) * y k) ^ 2 ≤ ∑ k, (1 / 3 ^ d : ℝ) * y k ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d → Fin 3))) (f := y)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow]
  have h3 : (0 : ℝ) < 3 ^ d := by positivity
  push_cast at h
  calc (1 / 3 ^ d : ℝ) ^ 2 * (∑ k, y k) ^ 2 ≤ (1 / 3 ^ d : ℝ) ^ 2 * (3 ^ d * ∑ k, y k ^ 2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = (1 / 3 ^ d : ℝ) * ∑ k, y k ^ 2 := by field_simp

/-- **Step 1 of Lemma 2.13** at one scale: `|M(□_{n+1}) - 3^{-d} Σ_z M(z + □_n)|²` is at most
`2 (3^{-d} Σ_z J(z + □_n, p, q) - J(□_{n+1}, p, q))`. -/
theorem euclideanSq_meanGradient_succ_sub_le [NeZero d] (a : CoefficientField d Λ) (n : ℕ)
    (p q : Vec d) :
    euclideanSq (meanGradient a (triadicCube d (n + 1)) p q -
        (1 / 3 ^ d : ℝ) • ∑ k : Fin d → Fin 3, meanGradient a (triadicSubcube n k) p q) ≤
      2 * (∑ k : Fin d → Fin 3, (1 / 3 ^ d : ℝ) * dualityDefect a (triadicSubcube n k) p q -
        dualityDefect a (triadicCube d (n + 1)) p q) := by
  set U := triadicCube d (n + 1) with hUdef
  set Q := triadicSubcube (d := d) n with hQdef
  have hUo := isOpen_triadicCube' (d := d) (n + 1)
  have hUb := isBounded_triadicCube (d := d) (n + 1)
  have hUc := convex_triadicCube (d := d) (n + 1)
  have hne := triadicCube_nonempty (d := d) (n + 1)
  have hUfin : volume U ≠ ⊤ := volume_triadicCube_ne_top d (n + 1)
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUfin
  obtain ⟨v, g, hv⟩ := exists_isDefectMaximizer a hUo hUb hUc hne p q
  choose w h hw using fun k => exists_isDefectMaximizer a (isOpen_triadicSubcube n k)
    (isBounded_triadicSubcube n k) (convex_triadicSubcube n k) (triadicSubcube_nonempty n k) p q
  have hL := lemma_2_12 a hUb (isOpen_triadicSubcube n) (pairwise_disjoint_triadicSubcube n)
    (triadicSubcube_subset n) (volume_triadicCube_diff n) p q hv hw
  have hratio : ∀ k, volume.real (triadicSubcube (d := d) n k) / volume.real U = 1 / 3 ^ d :=
    fun k => volumeReal_triadicSubcube_div n k
  simp only [volumeReal_triadicSubcube_div] at hL
  have hMU : meanGradient a U p q = fun i => ⨍ x in U, g x i :=
    (hv.setAverage_grad_eq hUo hUb hUc hne).symm
  have hMQ : ∀ k, meanGradient a (Q k) p q = fun i => ⨍ x in Q k, h k x i := fun k =>
    ((hw k).setAverage_grad_eq (isOpen_triadicSubcube n k) (isBounded_triadicSubcube n k)
      (convex_triadicSubcube n k) (triadicSubcube_nonempty n k)).symm
  have hgU : MemLp g 2 (volume.restrict U) := hv.1.1.2.1
  have hhk : ∀ k, MemLp (h k) 2 (volume.restrict (Q k)) := fun k => (hw k).1.1.2.1
  have hgQ : ∀ k, MemLp g 2 (volume.restrict (Q k)) := fun k =>
    hgU.mono_measure (Measure.restrict_mono (triadicSubcube_subset n k) le_rfl)
  have hQfin : ∀ k, volume (Q k) ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hUfin (measure_mono (triadicSubcube_subset n k))
  have hfinQ : ∀ k, IsFiniteMeasure (volume.restrict (Q k)) := fun k =>
    isFiniteMeasure_restrict.mpr (hQfin k)
  have hQ0 : ∀ k, volume (Q k) ≠ 0 := fun k =>
    ((isOpen_triadicSubcube n k).measure_pos volume (triadicSubcube_nonempty n k)).ne'
  -- the components of the difference
  set A : (Fin d → Fin 3) → Fin d → ℝ := fun k i => ⨍ x in Q k, (g x i - h k x i) with hAdef
  have hX : ∀ i, (meanGradient a U p q -
      (1 / 3 ^ d : ℝ) • ∑ k : Fin d → Fin 3, meanGradient a (Q k) p q) i =
      ∑ k, (1 / 3 ^ d : ℝ) * A k i := by
    intro i
    have hpart := setAverage_eq_sum_of_partition hUfin (isOpen_triadicSubcube n)
      (pairwise_disjoint_triadicSubcube n) (triadicSubcube_subset n) (volume_triadicCube_diff n)
      ((MemLp.eval hgU i).integrable one_le_two)
    simp only [hratio] at hpart
    have hQi : ∀ k, meanGradient a (Q k) p q i = ⨍ x in Q k, h k x i := fun k => congrFun (hMQ k) i
    have hUi : meanGradient a U p q i = ⨍ x in U, g x i := congrFun hMU i
    rw [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hUi,
      Finset.sum_congr rfl fun k _ => hQi k, hpart, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hfinQ k
    have i1 := (MemLp.eval (hgQ k) i).integrable one_le_two
    have i2 := (MemLp.eval (hhk k) i).integrable one_le_two
    have hsub : (⨍ x in Q k, (g x i - h k x i)) = (⨍ x in Q k, g x i) - ⨍ x in Q k, h k x i := by
      rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub i1 i2, smul_sub]
    rw [hAdef]
    simp only
    rw [hsub]
    ring
  -- Jensen's inequality, twice
  have hA2 : ∀ k i, A k i ^ 2 ≤ ⨍ x in Q k, (g x i - h k x i) ^ 2 := fun k i => by
    have := hfinQ k
    exact sq_setAverage_le (hQ0 k) (hQfin k) ((MemLp.eval ((hgQ k).sub (hhk k)) i).integrable one_le_two)
      ((MemLp.eval ((hgQ k).sub (hhk k)) i).integrable_sq)
  have hsumsq : ∀ k, ∑ i, ⨍ x in Q k, (g x i - h k x i) ^ 2 =
      ⨍ x in Q k, euclideanSq (g x - h k x) := fun k => by
    have := hfinQ k
    have hint : ∀ i, Integrable (fun x => (g x i - h k x i) ^ 2) (volume.restrict (Q k)) :=
      fun i => (MemLp.eval ((hgQ k).sub (hhk k)) i).integrable_sq
    rw [setAverage_eq, smul_eq_mul]
    simp only [euclideanSq, dot, Pi.sub_apply, ← sq]
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [setAverage_eq, smul_eq_mul]
  have hell : ∀ k, ⨍ x in Q k, euclideanSq (g x - h k x) ≤
      2 * ⨍ x in Q k, (1 / 2 : ℝ) * dot (g x - h k x) ((a x).mulVec (g x - h k x)) := fun k => by
    have := hfinQ k
    have hi1 : Integrable (fun x => euclideanSq (g x - h k x)) (volume.restrict (Q k)) := by
      simp only [euclideanSq, dot]
      exact integrable_finsetSum _ fun i _ =>
        (MemLp.eval ((hgQ k).sub (hhk k)) i).integrable_mul (MemLp.eval ((hgQ k).sub (hhk k)) i)
    have hi2 : Integrable (fun x => (1 / 2 : ℝ) * dot (g x - h k x) ((a x).mulVec (g x - h k x)))
        (volume.restrict (Q k)) :=
      (integrable_dot_mulVec a (Q k) ((hgQ k).sub (hhk k))).const_mul (1 / 2 : ℝ)
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      mul_comm 2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr measureReal_nonneg)
    rw [← integral_const_mul]
    refine integral_mono hi1 (hi2.const_mul 2) fun x => ?_
    have := (a.elliptic x (g x - h k x)).1
    show euclideanSq (g x - h k x) ≤ 2 * ((1 / 2 : ℝ) * dot (g x - h k x) ((a x).mulVec (g x - h k x)))
    linarith
  calc euclideanSq (meanGradient a U p q -
        (1 / 3 ^ d : ℝ) • ∑ k : Fin d → Fin 3, meanGradient a (Q k) p q)
      = ∑ i, (∑ k, (1 / 3 ^ d : ℝ) * A k i) ^ 2 := by
        simp only [euclideanSq, dot, ← sq, hX]
    _ ≤ ∑ i, ∑ k, (1 / 3 ^ d : ℝ) * A k i ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_sum_div_le_sum_sq_div (fun k => A k i)
    _ ≤ ∑ i, ∑ k, (1 / 3 ^ d : ℝ) * ⨍ x in Q k, (g x i - h k x i) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hA2 k i) (by positivity)
    _ = ∑ k, (1 / 3 ^ d : ℝ) * ⨍ x in Q k, euclideanSq (g x - h k x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, hsumsq k]
    _ ≤ ∑ k, (1 / 3 ^ d : ℝ) *
          (2 * ⨍ x in Q k, (1 / 2 : ℝ) * dot (g x - h k x) ((a x).mulVec (g x - h k x))) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hell k) (by positivity)
    _ = 2 * ∑ k, (1 / 3 ^ d : ℝ) *
          ⨍ x in Q k, (1 / 2 : ℝ) * dot (g x - h k x) ((a x).mulVec (g x - h k x)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by rw [hL]

end QSH
