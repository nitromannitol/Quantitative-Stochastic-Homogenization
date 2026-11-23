import QuantitativeStochasticHomogenization.Ch01.Sec02.DirichletEnergyTests
import QuantitativeStochasticHomogenization.Ch01.Sec03.ParallelogramQuadratic
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma

/-!
# Section 1.3: the limit of the subadditive quantity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3, (1.21), (1.22) and Definition 1.2.

The cube `□_{n+1}` is partitioned, up to a null set, into the `3^d` translates
`3^n (k - 1) + □_n`, `k ∈ {0, 1, 2}^d` (`triadicSubcube`). Subadditivity (1.11) and the translation
covariance of `μ` give `μ(□_{n+1}, e) ≤ 3^{-d} Σ_k μ(□_n, e)(T_{3^n (k - 1)} a)`, and stationarity
gives the monotonicity (1.21) of `E μ(□_n, e)`. The expectations are bounded below, so they
converge (1.22); the limit satisfies the parallelogram identity and the bound `μ̄(e) ≤ ½Λ|e|²`,
hence `μ̄(e) = ½ e·āe` for a symmetric matrix `ā` (`exists_homogenizedMatrix`).
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The triadic partition -/

/-- The lattice offset `3^n (k - 1)` of the subcube of `□_{n+1}` with index `k ∈ {0, 1, 2}^d`. -/
def subcubeOffset (n : ℕ) (k : Fin d → Fin 3) : LatticeIndex d :=
  fun i => (((k i : ℕ) : ℤ) - 1) * 3 ^ n

/-- The subcube `3^n (k - 1) + □_n` of `□_{n+1}`. -/
def triadicSubcube (n : ℕ) (k : Fin d → Fin 3) : Set (Vec d) :=
  {x | x - latticeShift (subcubeOffset n k) ∈ triadicCube d n}

theorem latticeShift_subcubeOffset_apply (n : ℕ) (k : Fin d → Fin 3) (i : Fin d) :
    latticeShift (subcubeOffset n k) i = (((k i : ℕ) : ℝ) - 1) * 3 ^ n := by
  simp [latticeShift, subcubeOffset]

theorem mem_triadicCube_iff {n : ℕ} {x : Vec d} :
    x ∈ triadicCube d n ↔ ∀ i, |x i| < (3 : ℝ) ^ n / 2 := by
  simp only [triadicCube, mem_univ_pi, mem_Ioo, abs_lt]
  constructor
  · intro h i
    exact ⟨by linarith [(h i).1], (h i).2⟩
  · intro h i
    exact ⟨by linarith [(h i).1], (h i).2⟩

theorem mem_triadicSubcube_iff {n : ℕ} {k : Fin d → Fin 3} {x : Vec d} :
    x ∈ triadicSubcube n k ↔ ∀ i, |x i - (((k i : ℕ) : ℝ) - 1) * 3 ^ n| < (3 : ℝ) ^ n / 2 := by
  simp only [triadicSubcube, mem_ofPred_eq, mem_triadicCube_iff, Pi.sub_apply,
    latticeShift_subcubeOffset_apply]

theorem isOpen_triadicCube (n : ℕ) : IsOpen (triadicCube d n) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem isOpen_triadicSubcube (n : ℕ) (k : Fin d → Fin 3) : IsOpen (triadicSubcube n k) :=
  (isOpen_triadicCube n).preimage (continuous_id.sub continuous_const)

theorem pairwise_disjoint_triadicSubcube (n : ℕ) :
    Pairwise (Function.onFun Disjoint (triadicSubcube (d := d) n)) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := Function.ne_iff.mp hkk'
  obtain ⟨h1a, h1b⟩ := abs_lt.mp (mem_triadicSubcube_iff.mp hx i)
  obtain ⟨h2a, h2b⟩ := abs_lt.mp (mem_triadicSubcube_iff.mp hx' i)
  have ht : (0 : ℝ) < 3 ^ n := by positivity
  have hne : (k i : ℕ) ≠ (k' i : ℕ) := fun h => hi (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hc : ((k i : ℕ) : ℝ) + 1 ≤ ((k' i : ℕ) : ℝ) := by exact_mod_cast hlt
    nlinarith
  · have hc : ((k' i : ℕ) : ℝ) + 1 ≤ ((k i : ℕ) : ℝ) := by exact_mod_cast hlt
    nlinarith

theorem triadicSubcube_subset (n : ℕ) (k : Fin d → Fin 3) :
    triadicSubcube n k ⊆ triadicCube d (n + 1) := by
  intro x hx
  rw [mem_triadicCube_iff]
  intro i
  have h1 := mem_triadicSubcube_iff.mp hx i
  have hk : (k i : ℕ) < 3 := (k i).isLt
  have hk0 : (0 : ℝ) ≤ ((k i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk2 : ((k i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hk
  have ht : (0 : ℝ) < 3 ^ n := by positivity
  have hc : |(((k i : ℕ) : ℝ) - 1) * 3 ^ n| ≤ 3 ^ n := by
    rw [abs_mul, abs_of_pos ht]
    have : |((k i : ℕ) : ℝ) - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  calc |x i| = |(x i - (((k i : ℕ) : ℝ) - 1) * 3 ^ n) + (((k i : ℕ) : ℝ) - 1) * 3 ^ n| := by
        rw [sub_add_cancel]
    _ ≤ |x i - (((k i : ℕ) : ℝ) - 1) * 3 ^ n| + |(((k i : ℕ) : ℝ) - 1) * 3 ^ n| := abs_add_le _ _
    _ < 3 ^ n / 2 + 3 ^ n := by linarith
    _ = 3 ^ (n + 1) / 2 := by ring

theorem exists_fin_three {t y : ℝ} (h1 : -(3 * t / 2) < y) (h2 : y < 3 * t / 2)
    (hne1 : y ≠ t / 2) (hne2 : y ≠ -(t / 2)) :
    ∃ j : Fin 3, |y - (((j : ℕ) : ℝ) - 1) * t| < t / 2 := by
  by_cases ha : y < -(t / 2)
  · refine ⟨⟨0, by norm_num⟩, ?_⟩
    show |y - (((0 : ℕ) : ℝ) - 1) * t| < t / 2
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  · have ha' : -(t / 2) < y := lt_of_le_of_ne (not_lt.mp ha) (Ne.symm hne2)
    by_cases hb : y < t / 2
    · refine ⟨⟨1, by norm_num⟩, ?_⟩
      show |y - (((1 : ℕ) : ℝ) - 1) * t| < t / 2
      rw [abs_lt]
      push_cast
      constructor <;> linarith
    · have hb' : t / 2 < y := lt_of_le_of_ne (not_lt.mp hb) (Ne.symm hne1)
      refine ⟨⟨2, by norm_num⟩, ?_⟩
      show |y - (((2 : ℕ) : ℝ) - 1) * t| < t / 2
      rw [abs_lt]
      push_cast
      constructor <;> linarith

theorem triadicCube_diff_subset (n : ℕ) :
    triadicCube d (n + 1) \ ⋃ k, triadicSubcube n k ⊆
      ⋃ i : Fin d, {x : Vec d | x i = (3 : ℝ) ^ n / 2 ∨ x i = -((3 : ℝ) ^ n / 2)} := by
  intro x ⟨hx, hxQ⟩
  by_contra hbad
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_or] at hbad
  apply hxQ
  have hx' := mem_triadicCube_iff.mp hx
  have ht : (0 : ℝ) < 3 ^ n := by positivity
  have hex : ∀ i, ∃ j : Fin 3, |x i - (((j : ℕ) : ℝ) - 1) * 3 ^ n| < (3 : ℝ) ^ n / 2 := by
    intro i
    obtain ⟨hb1, hb2⟩ := abs_lt.mp (hx' i)
    have hpow : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
    rw [hpow] at hb1 hb2
    exact exists_fin_three hb1 hb2 (hbad i).1 (hbad i).2
  choose k hk using hex
  exact mem_iUnion.mpr ⟨k, mem_triadicSubcube_iff.mpr hk⟩

theorem volume_coordinate_eq_null (i : Fin d) (c : ℝ) :
    volume {x : Vec d | x i = c} = 0 := by
  have h : {x : Vec d | x i = c} = (Function.eval i : Vec d → ℝ) ⁻¹' ({c} : Set ℝ) := rfl
  rw [h, volume_pi]
  exact Measure.pi_eval_preimage_null _ Real.volume_singleton

theorem volume_triadicCube_diff (n : ℕ) :
    volume (triadicCube d (n + 1) \ ⋃ k, triadicSubcube n k) = 0 := by
  refine measure_mono_null (triadicCube_diff_subset n) (measure_iUnion_null fun i => ?_)
  have h : {x : Vec d | x i = (3 : ℝ) ^ n / 2 ∨ x i = -((3 : ℝ) ^ n / 2)} =
      {x : Vec d | x i = (3 : ℝ) ^ n / 2} ∪ {x : Vec d | x i = -((3 : ℝ) ^ n / 2)} := rfl
  rw [h]
  exact measure_union_null (volume_coordinate_eq_null i _) (volume_coordinate_eq_null i _)

theorem volume_triadicCube (n : ℕ) :
    volume (triadicCube d n) = ENNReal.ofReal ((3 : ℝ) ^ n) ^ d := by
  rw [triadicCube, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  ring

theorem volume_triadicCube_ne_top (n : ℕ) : volume (triadicCube d n) ≠ ⊤ := by
  rw [volume_triadicCube]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem volume_triadicCube_ne_zero (n : ℕ) : volume (triadicCube d n) ≠ 0 := by
  rw [volume_triadicCube]
  exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem volumeReal_triadicCube (n : ℕ) : volume.real (triadicCube d n) = ((3 : ℝ) ^ n) ^ d := by
  rw [measureReal_def, volume_triadicCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

theorem volumeReal_triadicSubcube (n : ℕ) (k : Fin d → Fin 3) :
    volume.real (triadicSubcube n k) = ((3 : ℝ) ^ n) ^ d := by
  rw [← volumeReal_triadicCube n, measureReal_def, measureReal_def]
  congr 1
  exact (measurePreserving_sub_right volume (latticeShift (subcubeOffset n k))).measure_preimage_emb
    (MeasurableEquiv.subRight _).measurableEmbedding (triadicCube d n)

theorem volumeReal_triadicSubcube_div (n : ℕ) (k : Fin d → Fin 3) :
    volume.real (triadicSubcube n k) / volume.real (triadicCube d (n + 1)) = 1 / 3 ^ d := by
  rw [volumeReal_triadicSubcube, volumeReal_triadicCube, pow_succ, mul_pow]
  have : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  rw [div_mul_eq_div_div, div_self this.ne']

/-! ## Subadditivity and monotonicity -/

/-- **Subadditivity on the triadic partition**:
`μ(□_{n+1}, e) ≤ 3^{-d} Σ_k μ(□_n, e)(T_{3^n (k - 1)} a)`. -/
theorem dirichletEnergy_triadicCube_succ_le (a : CoefficientField d Λ) (n : ℕ)
    (e : Vec d) :
    dirichletEnergy a (triadicCube d (n + 1)) e ≤
      ∑ k : Fin d → Fin 3, (1 / 3 ^ d : ℝ) *
        dirichletEnergy (translate (latticeShift (subcubeOffset n k)) a) (triadicCube d n) e := by
  have h := dirichletEnergy_le_sum_of_partition a (volume_triadicCube_ne_top (n + 1))
    (isOpen_triadicSubcube n) (pairwise_disjoint_triadicSubcube n) (triadicSubcube_subset n)
    (volume_triadicCube_diff n) e
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [volumeReal_triadicSubcube_div, triadicSubcube,
    dirichletEnergy_preimage_sub a (volume_triadicCube_ne_top n)]

theorem measurable_dirichletEnergy_triadicCube (hΛ : 0 ≤ Λ) (n : ℕ) (e : Vec d) :
    Measurable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) e) :=
  measurable_dirichletEnergy (volume_triadicCube_ne_top n) hΛ e

theorem integrable_dirichletEnergy_triadicCube {P : Measure (CoefficientField d Λ)}
    [IsFiniteMeasure P] (hΛ : 0 ≤ Λ) (n : ℕ) (e : Vec d) :
    Integrable (fun a : CoefficientField d Λ => dirichletEnergy a (triadicCube d n) e) P := by
  refine (integrable_const ((1 / 2 : ℝ) * Λ * euclideanSq e)).mono'
    (measurable_dirichletEnergy_triadicCube hΛ n e).aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (dirichletEnergy_nonneg a _ e)]
  exact dirichletEnergy_le a (volume_triadicCube_ne_zero n) (volume_triadicCube_ne_top n) hΛ e

theorem integral_comp_translate {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (z : LatticeIndex d) {f : CoefficientField d Λ → ℝ} (hf : Measurable f) :
    ∫ a, f (translate (latticeShift z) a) ∂P = ∫ a, f a ∂P := by
  rw [← integral_map (measurable_translateCoefficient _).aemeasurable hf.aestronglyMeasurable,
    hP.2.1 z]

/-- **Monotonicity (1.21)**: `E μ(□_{n+1}, e) ≤ E μ(□_n, e)`. -/
theorem integral_dirichletEnergy_triadicCube_succ_le {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n : ℕ) (e : Vec d) :
    ∫ a, dirichletEnergy a (triadicCube d (n + 1)) e ∂P ≤
      ∫ a, dirichletEnergy a (triadicCube d n) e ∂P := by
  have := hP.1
  have hint : ∀ k : Fin d → Fin 3, Integrable (fun a => (1 / 3 ^ d : ℝ) *
      dirichletEnergy (translate (latticeShift (subcubeOffset n k)) a) (triadicCube d n) e) P :=
    fun k => ((integrable_dirichletEnergy_triadicCube hΛ n e).comp_measurable
      (measurable_translateCoefficient _)).const_mul _
  refine (integral_mono (integrable_dirichletEnergy_triadicCube hΛ (n + 1) e)
    (integrable_finsetSum _ fun k _ => hint k)
    fun a => dirichletEnergy_triadicCube_succ_le a n e).trans (le_of_eq ?_)
  rw [integral_finsetSum _ fun k _ => hint k]
  simp_rw [integral_const_mul]
  simp only [integral_comp_translate hP _ (measurable_dirichletEnergy_triadicCube hΛ n e)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul]

/-! ## The limit (1.22) and the homogenized matrix -/

/-- The expectation `E μ(□_n, e)`. -/
def expectedDirichletEnergy (P : Measure (CoefficientField d Λ)) (n : ℕ) (e : Vec d) : ℝ :=
  ∫ a, dirichletEnergy a (triadicCube d n) e ∂P

theorem antitone_expectedDirichletEnergy {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (e : Vec d) :
    Antitone fun n => expectedDirichletEnergy P n e :=
  antitone_nat_of_succ_le fun n => integral_dirichletEnergy_triadicCube_succ_le hP hΛ n e

theorem expectedDirichletEnergy_nonneg (P : Measure (CoefficientField d Λ)) (n : ℕ)
    (e : Vec d) : 0 ≤ expectedDirichletEnergy P n e :=
  integral_nonneg fun a => dirichletEnergy_nonneg a _ e

theorem expectedDirichletEnergy_le {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) (n : ℕ) (e : Vec d) :
    expectedDirichletEnergy P n e ≤ (1 / 2 : ℝ) * Λ * euclideanSq e := by
  have := hP.1
  have h := integral_mono (integrable_dirichletEnergy_triadicCube (P := P) hΛ n e)
    (integrable_const ((1 / 2 : ℝ) * Λ * euclideanSq e))
    fun a => dirichletEnergy_le a (volume_triadicCube_ne_zero n) (volume_triadicCube_ne_top n) hΛ e
  rwa [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h

theorem expectedDirichletEnergy_parallelogram {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n : ℕ) (e f : Vec d) :
    expectedDirichletEnergy P n (e + f) + expectedDirichletEnergy P n (e - f) =
      2 * expectedDirichletEnergy P n e + 2 * expectedDirichletEnergy P n f := by
  have := hP.1
  have hi : ∀ p : Vec d, Integrable (fun a => dirichletEnergy a (triadicCube d n) p) P :=
    fun p => integrable_dirichletEnergy_triadicCube hΛ n p
  unfold expectedDirichletEnergy
  rw [← integral_add (hi _) (hi _), ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi _).const_mul _) ((hi _).const_mul _)]
  congr 1
  funext a
  exact dirichletEnergy_parallelogram a (volume_triadicCube_ne_top n) e f

/-- The limit `μ̄(e) = lim E μ(□_n, e)` of (1.22). -/
def limitDirichletEnergy (P : Measure (CoefficientField d Λ)) (e : Vec d) : ℝ :=
  ⨅ n, expectedDirichletEnergy P n e

theorem tendsto_expectedDirichletEnergy {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (e : Vec d) :
    Tendsto (fun n => expectedDirichletEnergy P n e) atTop (𝓝 (limitDirichletEnergy P e)) :=
  tendsto_atTop_ciInf (antitone_expectedDirichletEnergy hP hΛ e)
    ⟨0, by rintro _ ⟨n, rfl⟩; exact expectedDirichletEnergy_nonneg P n e⟩

/-- **The homogenized matrix**, Definition 1.2: for a law satisfying (0.10)-(0.11) there is a
symmetric matrix `ā` with `E μ(□_n, e) → ½ e·āe` for every `e`. -/
theorem exists_homogenizedMatrix {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P)
    (hΛ : 0 ≤ Λ) :
    ∃ A : Mat d, A.transpose = A ∧ ∀ e : Vec d,
      Tendsto (fun n : ℕ => ∫ a, dirichletEnergy a (triadicCube d n) e ∂P) atTop
        (𝓝 ((1 / 2 : ℝ) * dot e (A.mulVec e))) := by
  set L := limitDirichletEnergy P
  have hpar : ∀ e f, L (e + f) + L (e - f) = 2 * L e + 2 * L f := by
    intro e f
    have h1 := (tendsto_expectedDirichletEnergy hP hΛ (e + f)).add
      (tendsto_expectedDirichletEnergy hP hΛ (e - f))
    have h2 := ((tendsto_expectedDirichletEnergy hP hΛ e).const_mul 2).add
      ((tendsto_expectedDirichletEnergy hP hΛ f).const_mul 2)
    simp_rw [expectedDirichletEnergy_parallelogram hP hΛ] at h1
    exact tendsto_nhds_unique h1 h2
  have hbound : ∀ e, |L e| ≤ (1 / 2 * Λ) * euclideanSq e := by
    intro e
    have h0 : 0 ≤ L e := ge_of_tendsto' (tendsto_expectedDirichletEnergy hP hΛ e)
      fun n => expectedDirichletEnergy_nonneg P n e
    have h1 : L e ≤ (1 / 2 : ℝ) * Λ * euclideanSq e :=
      le_of_tendsto' (tendsto_expectedDirichletEnergy hP hΛ e)
        fun n => expectedDirichletEnergy_le hP hΛ n e
    rw [abs_of_nonneg h0]
    exact h1
  obtain ⟨A, hA, hLA⟩ := exists_symmetric_of_parallelogram hpar (by positivity) hbound
  refine ⟨A, hA, fun e => ?_⟩
  rw [← hLA e]
  exact tendsto_expectedDirichletEnergy hP hΛ e

end QSH
