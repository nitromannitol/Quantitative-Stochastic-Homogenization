import QuantitativeStochasticHomogenization.Ch01.Sec03.MinimizerOscillation

/-!
# The children of the subcubes of a triadic cube

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the notation (0.20): each subcube `z + □_{n+1}` of the partition of `□_{n+1+r}` is, up to a null
set, the disjoint union of the `3^d` subcubes `y + □_n` of the partition of `□_{n+(r+1)}` that it
contains. The subcube of `□_{n+(r+1)}` with index `3k + j` (`childIndexEquiv`) lies in the subcube
of `□_{n+1+r}` with index `k`.

* `partitionCube_childIndexEquiv_subset`: `y + □_n ⊆ z + □_{n+1}`;
* `setIntegral_partitionCube_succ_eq_sum`: `∫_{z + □_{n+1}} f = Σ_y ∫_{y + □_n} f`;
* `sum_childIndexEquiv`: sums over the subcubes `y + □_n` as sums over the pairs (parent,
  position in the parent);
* `partitionCube_zero`: the partition of `□_m` into one subcube.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The index `3k + j` of the subcube of `□_{n+(r+1)}` in position `j ∈ {0, 1, 2}^d` in the
subcube of `□_{n+1+r}` with index `k`. -/
def childIndexEquiv (r : ℕ) :
    (Fin d → Fin (3 ^ r)) × (Fin d → Fin 3) ≃ (Fin d → Fin (3 ^ (r + 1))) :=
  (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Fin (3 ^ r)) (fun _ => Fin 3)).symm.trans
    (Equiv.piCongrRight fun _ => finProdFinEquiv.trans (finCongr (pow_succ 3 r).symm))

theorem childIndexEquiv_apply_val (r : ℕ) (k : Fin d → Fin (3 ^ r)) (j : Fin d → Fin 3)
    (i : Fin d) : ((childIndexEquiv r (k, j) i : Fin (3 ^ (r + 1))) : ℕ) = j i + 3 * k i :=
  rfl

/-- **A child lies in its parent**: `y + □_n ⊆ z + □_{n+1}`. -/
theorem partitionCube_childIndexEquiv_subset (n r : ℕ) (k : Fin d → Fin (3 ^ r))
    (j : Fin d → Fin 3) :
    partitionCube n (r + 1) (childIndexEquiv r (k, j)) ⊆ partitionCube (n + 1) r k := by
  intro x hx
  rw [mem_partitionCube_iff] at hx ⊢
  intro i
  have h := hx i
  rw [childIndexEquiv_apply_val] at h
  push_cast at h
  have hj : ((j i : ℕ) : ℝ) ≤ 2 := by
    have := (j i).isLt
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hc : (0 : ℝ) < 3 ^ n := by positivity
  have e1 : 0 ≤ (3 : ℝ) ^ n * ((j i : ℕ) : ℝ) := by positivity
  have e2 : (3 : ℝ) ^ n * ((j i : ℕ) : ℝ) ≤ (3 : ℝ) ^ n * 2 :=
    mul_le_mul_of_nonneg_left hj hc.le
  have hp1 : (3 : ℝ) ^ (r + 1) = 3 * 3 ^ r := by ring
  have hp2 : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
  rw [hp1] at h
  rw [hp2]
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  rw [abs_lt]
  constructor <;> linarith

/-- Up to a null set, `z + □_{n+1}` is the union of its children. -/
theorem partitionCube_ae_eq_iUnion_child (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    partitionCube (n + 1) r k =ᵐ[volume]
      ⋃ j, partitionCube n (r + 1) (childIndexEquiv r (k, j)) := by
  refine ae_eq_set.mpr ⟨?_, ?_⟩
  · refine measure_mono_null ?_ (volume_triadicCube_diff_partitionCube n (r + 1))
    rintro x ⟨hxP, hxC⟩
    refine ⟨?_, ?_⟩
    · have := partitionCube_subset (n + 1) r k hxP
      rwa [show n + 1 + r = n + (r + 1) by omega] at this
    · simp only [mem_iUnion, not_exists] at hxC ⊢
      intro k' hk'
      obtain ⟨⟨k'', j⟩, rfl⟩ := (childIndexEquiv r).surjective k'
      by_cases hkk : k'' = k
      · subst hkk
        exact hxC j hk'
      · exact Set.disjoint_left.mp (pairwise_disjoint_partitionCube (n + 1) r hkk)
          (partitionCube_childIndexEquiv_subset n r k'' j hk') hxP
  · rw [sdiff_eq_empty.mpr (iUnion_subset fun j => partitionCube_childIndexEquiv_subset n r k j),
      measure_empty]

/-- **`∫_{z + □_{n+1}} f = Σ_y ∫_{y + □_n} f`** over the children `y + □_n` of `z + □_{n+1}`. -/
theorem setIntegral_partitionCube_succ_eq_sum (n r : ℕ) (k : Fin d → Fin (3 ^ r))
    {f : Vec d → ℝ} (hf : IntegrableOn f (partitionCube (n + 1) r k)) :
    ∫ x in partitionCube (n + 1) r k, f x =
      ∑ j : Fin d → Fin 3, ∫ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), f x := by
  rw [setIntegral_congr_set (partitionCube_ae_eq_iUnion_child n r k),
    integral_iUnion_fintype (fun j => (isOpen_partitionCube n (r + 1) _).measurableSet)
      (fun j j' hjj' => by
        have hne : childIndexEquiv r (k, j) ≠ childIndexEquiv r (k, j') := fun h =>
          hjj' (congrArg Prod.snd ((childIndexEquiv r).injective h))
        exact pairwise_disjoint_partitionCube n (r + 1) hne)
      (fun j => hf.mono_set (partitionCube_childIndexEquiv_subset n r k j))]

/-- A sum over the subcubes `y + □_n` of `□_{n+(r+1)}` as a sum over their parents and their
positions in the parents. -/
theorem sum_childIndexEquiv {M : Type*} [AddCommMonoid M] (r : ℕ)
    (F : (Fin d → Fin (3 ^ (r + 1))) → M) :
    ∑ k, F k = ∑ k : Fin d → Fin (3 ^ r), ∑ j : Fin d → Fin 3, F (childIndexEquiv r (k, j)) := by
  rw [← Fintype.sum_equiv (childIndexEquiv r) (fun p => F (childIndexEquiv r p)) F
    (fun _ => rfl), Fintype.sum_prod_type]

/-- The partition of `□_m` into translates of `□_m` has the single element `□_m`. -/
theorem partitionCube_zero (m : ℕ) (k : Fin d → Fin (3 ^ 0)) :
    partitionCube m 0 k = triadicCube d m := by
  ext x
  rw [mem_partitionCube_iff, mem_triadicCube_iff]
  simp

end QSH
