import QuantitativeStochasticHomogenization.Ch01.Sec03.SubadditiveLimit

/-!
# The partition of `□_{n+r}` into the translates of `□_n`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
the notation (0.20) and Section 1.3: up to a null set, `□_{n+r}` is the disjoint union of the
`3^{dr}` cubes `z + □_n` with `z ∈ 3^n ℤ^d ∩ □_{n+r}`. They are indexed by
`k ∈ {0, …, 3^r - 1}^d`, with centers `z_k = 3^n (k - (3^r - 1)/2)` (`partitionCenter`).

* `dirichletEnergy_triadicCube_add_le`: the subadditivity (1.11) on this partition,
  `μ(□_{n+r}, p) ≤ 3^{-dr} Σ_k μ(□_n, p)(T_{z_k} a)`;
* `two_le_euclideanNorm_sub_of_three_le`: two subcubes whose indices differ by at least `3` in
  one coordinate are at distance at least `2`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- The center `3^n (k - (3^r - 1)/2)` of the subcube of `□_{n+r}` with index
`k ∈ {0, …, 3^r - 1}^d`. -/
def partitionCenter (n r : ℕ) (k : Fin d → Fin (3 ^ r)) : LatticeIndex d :=
  fun i => 3 ^ n * (((k i : ℕ) : ℤ) - (((3 ^ r - 1) / 2 : ℕ) : ℤ))

/-- The subcube `z_k + □_n` of `□_{n+r}`. -/
def partitionCube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) : Set (Vec d) :=
  {x | x - latticeShift (partitionCenter n r k) ∈ triadicCube d n}

theorem cast_half_three_pow_sub_one (r : ℕ) :
    (((3 ^ r - 1) / 2 : ℕ) : ℝ) = ((3 : ℝ) ^ r - 1) / 2 := by
  have hodd : Odd (3 ^ r) := Odd.pow (by decide)
  have heven : Even (3 ^ r - 1) := Nat.Odd.sub_odd hodd odd_one
  have h2 : 2 * ((3 ^ r - 1) / 2) = 3 ^ r - 1 := Nat.two_mul_div_two_of_even heven
  have h1 : 1 ≤ 3 ^ r := Nat.one_le_pow _ _ (by norm_num)
  have h3 : (2 : ℝ) * (((3 ^ r - 1) / 2 : ℕ) : ℝ) = (3 : ℝ) ^ r - 1 := by
    have := congrArg (fun m : ℕ => (m : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_ofNat] at this
    rw [this, Nat.cast_sub h1]
    simp
  linarith

theorem latticeShift_partitionCenter_apply (n r : ℕ) (k : Fin d → Fin (3 ^ r)) (i : Fin d) :
    latticeShift (partitionCenter n r k) i =
      (3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2) := by
  simp only [latticeShift, partitionCenter, Int.cast_mul, Int.cast_sub, Int.cast_pow,
    Int.cast_natCast, Int.cast_ofNat, cast_half_three_pow_sub_one]

theorem mem_partitionCube_iff {n r : ℕ} {k : Fin d → Fin (3 ^ r)} {x : Vec d} :
    x ∈ partitionCube n r k ↔
      ∀ i, |x i - (3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)| < (3 : ℝ) ^ n / 2 := by
  simp only [partitionCube, mem_ofPred_eq, mem_triadicCube_iff, Pi.sub_apply,
    latticeShift_partitionCenter_apply]

theorem isOpen_partitionCube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) : IsOpen (partitionCube n r k) :=
  (isOpen_triadicCube n).preimage (continuous_id.sub continuous_const)

theorem pairwise_disjoint_partitionCube (n r : ℕ) :
    Pairwise (Function.onFun Disjoint (partitionCube (d := d) n r)) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := Function.ne_iff.mp hkk'
  obtain ⟨h1a, h1b⟩ := abs_lt.mp (mem_partitionCube_iff.mp hx i)
  obtain ⟨h2a, h2b⟩ := abs_lt.mp (mem_partitionCube_iff.mp hx' i)
  have ht : (0 : ℝ) < 3 ^ n := by positivity
  have hne : (k i : ℕ) ≠ (k' i : ℕ) := fun h => hi (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hc : ((k i : ℕ) : ℝ) + 1 ≤ ((k' i : ℕ) : ℝ) := by exact_mod_cast hlt
    nlinarith
  · have hc : ((k' i : ℕ) : ℝ) + 1 ≤ ((k i : ℕ) : ℝ) := by exact_mod_cast hlt
    nlinarith

theorem partitionCube_subset (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    partitionCube n r k ⊆ triadicCube d (n + r) := by
  intro x hx
  rw [mem_triadicCube_iff]
  intro i
  have h1 := mem_partitionCube_iff.mp hx i
  have hk : (k i : ℕ) < 3 ^ r := (k i).isLt
  have hk0 : (0 : ℝ) ≤ ((k i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk2 : ((k i : ℕ) : ℝ) + 1 ≤ (3 : ℝ) ^ r := by exact_mod_cast hk
  have ht : (0 : ℝ) < 3 ^ n := by positivity
  have hc : |(3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)| ≤
      (3 : ℝ) ^ n * (((3 : ℝ) ^ r - 1) / 2) := by
    rw [abs_mul, abs_of_pos ht]
    refine mul_le_mul_of_nonneg_left ?_ ht.le
    rw [abs_le]
    constructor <;> linarith
  calc |x i| = |(x i - (3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)) +
        (3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)| := by rw [sub_add_cancel]
    _ ≤ |x i - (3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)| +
        |(3 : ℝ) ^ n * (((k i : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)| := abs_add_le _ _
    _ < 3 ^ n / 2 + (3 : ℝ) ^ n * (((3 : ℝ) ^ r - 1) / 2) := by linarith
    _ = 3 ^ (n + r) / 2 := by ring

theorem triadicCube_diff_partitionCube_subset (n r : ℕ) :
    triadicCube d (n + r) \ ⋃ k, partitionCube n r k ⊆
      ⋃ i : Fin d, ⋃ j : ℤ, {x : Vec d | x i = (3 : ℝ) ^ n * j - (3 : ℝ) ^ (n + r) / 2} := by
  intro x ⟨hx, hxQ⟩
  by_contra hbad
  simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hbad
  apply hxQ
  have hx' := mem_triadicCube_iff.mp hx
  have ht : (0 : ℝ) < 3 ^ n := by positivity
  have hex : ∀ i, ∃ j : Fin (3 ^ r), |x i - (3 : ℝ) ^ n * (((j : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)|
      < (3 : ℝ) ^ n / 2 := by
    intro i
    obtain ⟨hb1, hb2⟩ := abs_lt.mp (hx' i)
    set t : ℝ := (x i + (3 : ℝ) ^ (n + r) / 2) / 3 ^ n with ht_def
    have hpow : (3 : ℝ) ^ (n + r) = 3 ^ n * 3 ^ r := pow_add _ _ _
    have hxt : x i = 3 ^ n * t - (3 : ℝ) ^ (n + r) / 2 := by
      rw [ht_def]; field_simp; ring
    have ht0 : 0 < t := by
      rw [ht_def]; exact div_pos (by linarith) ht
    have htr : t < (3 : ℝ) ^ r := by
      rw [ht_def, div_lt_iff₀ ht]; rw [hpow] at hb2; nlinarith
    have hnint : ∀ j : ℤ, t ≠ j := by
      intro j hj
      apply hbad i j
      rw [hxt, hj]
    have hfl : (Nat.floor t : ℝ) < t := by
      rcases (Nat.floor_le ht0.le).lt_or_eq with h | h
      · exact h
      · exact absurd h.symm (by simpa using hnint (Nat.floor t))
    have hfl2 : t < (Nat.floor t : ℝ) + 1 := Nat.lt_floor_add_one t
    have hfr : Nat.floor t < 3 ^ r := by
      have := Nat.floor_lt ht0.le |>.mpr (by exact_mod_cast htr : t < ((3 ^ r : ℕ) : ℝ))
      exact this
    refine ⟨⟨Nat.floor t, hfr⟩, ?_⟩
    show |x i - (3 : ℝ) ^ n * (((Nat.floor t : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2)| < 3 ^ n / 2
    have hdiff : x i - (3 : ℝ) ^ n * (((Nat.floor t : ℕ) : ℝ) - ((3 : ℝ) ^ r - 1) / 2) =
        3 ^ n * (t - Nat.floor t - 1 / 2) := by
      rw [hxt, hpow]; ring
    rw [hdiff, abs_mul, abs_of_pos ht]
    have : |t - (Nat.floor t : ℝ) - 1 / 2| < 1 / 2 := by
      rw [abs_lt]; constructor <;> linarith
    nlinarith
  choose k hk using hex
  exact mem_iUnion.mpr ⟨k, mem_partitionCube_iff.mpr hk⟩

theorem volume_triadicCube_diff_partitionCube (n r : ℕ) :
    volume (triadicCube d (n + r) \ ⋃ k, partitionCube n r k) = 0 :=
  measure_mono_null (triadicCube_diff_partitionCube_subset n r)
    (measure_iUnion_null fun i => measure_iUnion_null fun _ => volume_coordinate_eq_null i _)

theorem volumeReal_partitionCube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    volume.real (partitionCube n r k) = ((3 : ℝ) ^ n) ^ d := by
  rw [← volumeReal_triadicCube n, measureReal_def, measureReal_def]
  congr 1
  exact (measurePreserving_sub_right volume (latticeShift (partitionCenter n r k))).measure_preimage_emb
    (MeasurableEquiv.subRight _).measurableEmbedding (triadicCube d n)

theorem volumeReal_partitionCube_div (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    volume.real (partitionCube n r k) / volume.real (triadicCube d (n + r)) =
      1 / ((3 : ℝ) ^ r) ^ d := by
  rw [volumeReal_partitionCube, volumeReal_triadicCube, pow_add, mul_pow]
  have : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  rw [div_mul_eq_div_div, div_self this.ne']

theorem dirichletEnergy_partitionCube (a : CoefficientField d Λ) (n r : ℕ)
    (k : Fin d → Fin (3 ^ r)) (e : Vec d) :
    dirichletEnergy a (partitionCube n r k) e =
      dirichletEnergy (translate (latticeShift (partitionCenter n r k)) a) (triadicCube d n) e :=
  dirichletEnergy_preimage_sub a (volume_triadicCube_ne_top d n) _ e

/-- **Subadditivity on the partition of `□_{n+r}` into translates of `□_n`**:
`μ(□_{n+r}, p) ≤ 3^{-dr} Σ_k μ(□_n, p)(T_{z_k} a)`. -/
theorem dirichletEnergy_triadicCube_add_le (a : CoefficientField d Λ) (n r : ℕ) (e : Vec d) :
    dirichletEnergy a (triadicCube d (n + r)) e ≤
      ∑ k : Fin d → Fin (3 ^ r), (1 / ((3 : ℝ) ^ r) ^ d) *
        dirichletEnergy (translate (latticeShift (partitionCenter n r k)) a)
          (triadicCube d n) e := by
  have h := dirichletEnergy_le_sum_of_partition a (volume_triadicCube_ne_top d (n + r))
    (isOpen_partitionCube n r) (pairwise_disjoint_partitionCube n r) (partitionCube_subset n r)
    (volume_triadicCube_diff_partitionCube n r) e
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [volumeReal_partitionCube_div, dirichletEnergy_partitionCube]

theorem abs_coord_le_euclideanNorm (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have := Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)
  simpa [euclideanSq, dot, pow_two] using this

/-- Two subcubes whose indices differ by at least `3` in one coordinate are at distance at least
`2`. -/
theorem two_le_euclideanNorm_sub_of_three_le {n r : ℕ} {k k' : Fin d → Fin (3 ^ r)} {i : Fin d}
    (hkk : 3 ≤ |((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ)|) {x y : Vec d} (hx : x ∈ partitionCube n r k)
    (hy : y ∈ partitionCube n r k') : 2 ≤ euclideanNorm (x - y) := by
  have h1 := abs_lt.mp (mem_partitionCube_iff.mp hx i)
  have h2 := abs_lt.mp (mem_partitionCube_iff.mp hy i)
  have ht : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hk : (3 : ℝ) ≤ |((k i : ℕ) : ℝ) - ((k' i : ℕ) : ℝ)| := by exact_mod_cast hkk
  have hxy : 2 ≤ |x i - y i| := by
    rcases le_abs'.mp hk with h | h
    · rw [le_abs']
      left
      nlinarith
    · rw [le_abs']
      right
      nlinarith
  exact hxy.trans (by simpa using abs_coord_le_euclideanNorm (x - y) i)

end QSH
