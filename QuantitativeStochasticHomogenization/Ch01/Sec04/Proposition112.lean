import QuantitativeStochasticHomogenization.Ch01.Sec04.CubePoincare
import QuantitativeStochasticHomogenization.Ch01.Sec04.TriadicChildren

/-!
# Proposition 1.12: the multiscale Poincaré inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.4, Proposition 1.12, (1.42): there is `C(d) < ∞` such that, for every `m ∈ ℕ` and
`f ∈ L²(□_m)`,
`‖f‖_{Ĥ̲⁻¹(□_m)} ≤ C ‖f‖_{L̲²(□_m)} + C Σ_{n=0}^{m-1} 3^n (|Z_n|⁻¹ Σ_{y ∈ Z_n} |(f)_{y+□_n}|²)^{1/2}`.

The proof is the book's. For a test `g ∈ H¹(□_m)` and the scale `n`, let
`T_n = Σ_{z ∈ Z_n} ∫_{z+□_n} f (g - (g)_{z+□_n})` (`oscillationPairing`). Splitting each
`z + □_{n+1}` into its children `y + □_n`,
`T_{n+1} - T_n = Σ_y |□_n| (f)_{y+□_n} ((g)_{y+□_n} - (g)_{z+□_{n+1}})` (`oscillationPairing_succ`),
which the Cauchy–Schwarz, Jensen and Poincaré inequalities bound by
`C 3^n |□_n|^{1/2} (Σ_y |(f)_{y+□_n}|²)^{1/2} ‖∇g‖_{L²(□_m)}`
(`abs_oscillationPairing_succ_sub_le`). Iterating from `T_0`, bounded by the Poincaré inequality on
the unit cubes, to `T_m = ∫_{□_m} f (g - (g)_{□_m})` and adding `|□_m| (f)_{□_m} (g)_{□_m}` gives
`|⨍_{□_m} f g|` (`abs_setAverage_mul_le_multiscale`); the last term is bounded by Jensen's inequality
on the children of `□_m` (`three_pow_mul_abs_setAverage_le`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

open BaseExponent

/-- `Σ_{z ∈ Z_n} ∫_{z+□_n} f (g - (g)_{z+□_n})` over the partition of `□_{n+r}`. -/
def oscillationPairing (n r : ℕ) (f g : Vec d → ℝ) : ℝ :=
  ∑ k : Fin d → Fin (3 ^ r),
    ∫ x in partitionCube n r k, f x * (g x - ⨍ y in partitionCube n r k, g y)

/-- `Σ_{z ∈ Z_n} |(f)_{z+□_n}|²` over the partition of `□_{n+r}`. -/
def averageSqSum (n r : ℕ) (f : Vec d → ℝ) : ℝ :=
  ∑ k : Fin d → Fin (3 ^ r), (⨍ x in partitionCube n r k, f x) ^ 2

theorem setIntegral_mul_sub_const_eq {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : IntegrableOn (fun x => f x * g x) U) (hf : IntegrableOn f U) (a b : ℝ) :
    ∫ x in U, f x * (g x - a) = (∫ x in U, f x * (g x - b)) + (b - a) * ∫ x in U, f x := by
  have e : (fun x => f x * (g x - a)) = fun x => f x * (g x - b) + (b - a) * f x := by
    funext x; ring
  have i1 : IntegrableOn (fun x => f x * (g x - b)) U := by
    have e' : (fun x => f x * (g x - b)) = fun x => f x * g x - b * f x := by funext x; ring
    rw [e']
    exact hfg.sub (hf.const_mul b)
  rw [e, integral_add i1 (hf.const_mul _), integral_const_mul]

/-- **The iteration identity**: `T_{n+1} = T_n + Σ_y |□_n| (f)_{y+□_n} ((g)_{y+□_n} - (g)_{z+□_{n+1}})`,
the sum over the children `y + □_n` of the subcubes `z + □_{n+1}`. -/
theorem oscillationPairing_succ (n r : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (triadicCube d (n + (r + 1)))))
    (hg : MemLp g 2 (volume.restrict (triadicCube d (n + (r + 1))))) :
    oscillationPairing (n + 1) r f g = oscillationPairing n (r + 1) f g +
      ∑ p : (Fin d → Fin (3 ^ r)) × (Fin d → Fin 3),
        ((3 : ℝ) ^ n) ^ d * (⨍ x in partitionCube n (r + 1) (childIndexEquiv r p), f x) *
          ((⨍ x in partitionCube n (r + 1) (childIndexEquiv r p), g x) -
            ⨍ x in partitionCube (n + 1) r p.1, g x) := by
  have hWt : volume (triadicCube d (n + (r + 1))) ≠ ⊤ := volume_triadicCube_ne_top d _
  have : IsFiniteMeasure (volume.restrict (triadicCube d (n + (r + 1)))) :=
    isFiniteMeasure_restrict.mpr hWt
  have hfI : IntegrableOn f (triadicCube d (n + (r + 1))) := hf.integrable (by norm_num)
  have hfgI : IntegrableOn (fun x => f x * g x) (triadicCube d (n + (r + 1))) :=
    hf.integrable_mul hg
  have hPW : ∀ k : Fin d → Fin (3 ^ r),
      partitionCube (n + 1) r k ⊆ triadicCube d (n + (r + 1)) := fun k => by
    have := partitionCube_subset (d := d) (n + 1) r k
    rwa [show n + 1 + r = n + (r + 1) by omega] at this
  have hCW : ∀ k', partitionCube (d := d) n (r + 1) k' ⊆ triadicCube d (n + (r + 1)) :=
    partitionCube_subset n (r + 1)
  have hint : ∀ U : Set (Vec d), U ⊆ triadicCube d (n + (r + 1)) → ∀ a : ℝ,
      IntegrableOn (fun x => f x * (g x - a)) U := fun U hU a => by
    have e : (fun x => f x * (g x - a)) = fun x => f x * g x - a * f x := by funext x; ring
    rw [e]
    exact (hfgI.sub (hfI.const_mul a)).mono_set hU
  unfold oscillationPairing
  rw [sum_childIndexEquiv r, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  dsimp only
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, setIntegral_partitionCube_succ_eq_sum n r k (hint _ (hPW k) _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [setIntegral_mul_sub_const_eq (hfgI.mono_set (hCW _)) (hfI.mono_set (hCW _)) _
      (⨍ y in partitionCube n (r + 1) (childIndexEquiv r (k, j)), g y),
    setIntegral_eq_volume_mul_setAverage (volume_partitionCube_ne_zero n (r + 1) _)
      (volume_partitionCube_ne_top n (r + 1) (childIndexEquiv r (k, j))) f,
    volumeReal_partitionCube]
  ring

/-- Jensen's and the Poincaré inequality on a parent cube:
`|□_n| Σ_y ((g)_{y+□_n} - (g)_{z+□_{n+1}})² ≤ C 3^{2(n+1)} ∫_{z+□_{n+1}} |∇g|²`. -/
theorem sum_sq_setAverage_child_sub_le (n r : ℕ) (k : Fin d → Fin (3 ^ r)) {g : Vec d → ℝ}
    {G : Vec d → Vec d} (hg : H1 (partitionCube (n + 1) r k) g G) :
    ((3 : ℝ) ^ n) ^ d * ∑ j : Fin d → Fin 3,
      ((⨍ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), g x) -
        ⨍ x in partitionCube (n + 1) r k, g x) ^ 2 ≤
      cubePoincareConstant d * ((3 : ℝ) ^ (n + 1)) ^ 2 *
        ∫ x in partitionCube (n + 1) r k, euclideanSq (G x) := by
  set a := ⨍ x in partitionCube (n + 1) r k, g x with ha
  have hPt := volume_partitionCube_ne_top (d := d) (n + 1) r k
  have : IsFiniteMeasure (volume.restrict (partitionCube (d := d) (n + 1) r k)) :=
    isFiniteMeasure_restrict.mpr hPt
  have hga : MemLp (fun x => g x - a) 2 (volume.restrict (partitionCube (n + 1) r k)) :=
    hg.1.sub (memLp_const a)
  have hgI : IntegrableOn g (partitionCube (n + 1) r k) := hg.1.integrable (by norm_num)
  have hgaI : IntegrableOn (fun x => g x - a) (partitionCube (n + 1) r k) :=
    hga.integrable (by norm_num)
  have hga2 : IntegrableOn (fun x => (g x - a) ^ 2) (partitionCube (n + 1) r k) :=
    hga.integrable_sq
  have hchild : ∀ j : Fin d → Fin 3,
      ((⨍ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), g x) - a) ^ 2 *
          ((3 : ℝ) ^ n) ^ d ≤
        ∫ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), (g x - a) ^ 2 := by
    intro j
    have hCP := partitionCube_childIndexEquiv_subset (d := d) n r k j
    have hC0 := volume_partitionCube_ne_zero (d := d) n (r + 1) (childIndexEquiv r (k, j))
    have hCt := volume_partitionCube_ne_top (d := d) n (r + 1) (childIndexEquiv r (k, j))
    have hV : 0 < volume.real (partitionCube (d := d) n (r + 1) (childIndexEquiv r (k, j))) :=
      ENNReal.toReal_pos hC0 hCt
    have havg : (⨍ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), g x) - a =
        ⨍ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), (g x - a) := by
      rw [setAverage_eq, setAverage_eq, integral_sub (hgI.mono_set hCP) (integrableOn_const hCt),
        setIntegral_const, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hV.ne', one_mul]
    have hJ := sq_setAverage_le hC0 hCt (hgaI.mono_set hCP) (hga2.mono_set hCP)
    rw [havg, setIntegral_eq_volume_mul_setAverage hC0 hCt (fun x => (g x - a) ^ 2),
      volumeReal_partitionCube]
    have hV' : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ d := by positivity
    nlinarith
  calc ((3 : ℝ) ^ n) ^ d * ∑ j : Fin d → Fin 3,
        ((⨍ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), g x) - a) ^ 2
      = ∑ j : Fin d → Fin 3,
          ((⨍ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), g x) - a) ^ 2 *
            ((3 : ℝ) ^ n) ^ d := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ ∑ j : Fin d → Fin 3,
          ∫ x in partitionCube n (r + 1) (childIndexEquiv r (k, j)), (g x - a) ^ 2 :=
        Finset.sum_le_sum fun j _ => hchild j
    _ = ∫ x in partitionCube (n + 1) r k, (g x - a) ^ 2 :=
        (setIntegral_partitionCube_succ_eq_sum n r k hga2).symm
    _ ≤ _ := setIntegral_sq_sub_setAverage_le_partitionCube (n + 1) r k hg

/-- **One step of the iteration**:
`|T_{n+1} - T_n| ≤ (|□_n| Σ_y (f)_{y+□_n}²)^{1/2} (C 3^{2(n+1)} ∫_{□_m} |∇g|²)^{1/2}`. -/
theorem abs_oscillationPairing_succ_sub_le (m n r : ℕ) (hm : n + (r + 1) = m)
    {f g : Vec d → ℝ} {G : Vec d → Vec d} (hf : MemLp f 2 (volume.restrict (triadicCube d m)))
    (hg : H1 (triadicCube d m) g G) :
    |oscillationPairing (n + 1) r f g - oscillationPairing n (r + 1) f g| ≤
      √(((3 : ℝ) ^ n) ^ d * averageSqSum n (r + 1) f) *
        √(cubePoincareConstant d * ((3 : ℝ) ^ (n + 1)) ^ 2 *
          ∫ x in triadicCube d m, euclideanSq (G x)) := by
  subst hm
  rw [oscillationPairing_succ n r hf hg.1, add_sub_cancel_left]
  have hV : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have e : ∀ x y : ℝ, ((3 : ℝ) ^ n) ^ d * x * y =
      (√(((3 : ℝ) ^ n) ^ d) * x) * (√(((3 : ℝ) ^ n) ^ d) * y) := by
    intro x y
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hV.le, mul_assoc]
  simp_rw [e]
  refine (abs_sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  refine mul_le_mul (Real.sqrt_le_sqrt (le_of_eq ?_)) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)
  · simp_rw [mul_pow, Real.sq_sqrt hV.le]
    rw [← Finset.mul_sum, averageSqSum, sum_childIndexEquiv r, Fintype.sum_prod_type]
  · simp_rw [mul_pow, Real.sq_sqrt hV.le]
    rw [Fintype.sum_prod_type]
    have hPW : ∀ k : Fin d → Fin (3 ^ r),
        partitionCube (n + 1) r k ⊆ triadicCube d (n + (r + 1)) := fun k => by
      have := partitionCube_subset (d := d) (n + 1) r k
      rwa [show n + 1 + r = n + (r + 1) by omega] at this
    have hGW : IntegrableOn (fun x => euclideanSq (G x)) (triadicCube d (n + 1 + r)) := by
      rw [show n + 1 + r = n + (r + 1) by omega]
      exact integrable_euclideanSq_of_memLp hg.2.1
    refine le_trans (le_of_eq ?_) ((Finset.sum_le_sum (s := Finset.univ) fun k _ =>
      sum_sq_setAverage_child_sub_le n r k (hg.mono (hPW k))).trans (le_of_eq ?_))
    · simp only [Finset.mul_sum]
    · rw [← Finset.mul_sum, ← setIntegral_triadicCube_eq_sum (n + 1) r hGW,
        show n + 1 + r = n + (r + 1) by omega]

/-- **The iteration from the unit scale**: `|T_n - T_0| ≤ Σ_{i<n} B_i` with the bounds `B_i` of
`abs_oscillationPairing_succ_sub_le`. -/
theorem abs_oscillationPairing_sub_le (m : ℕ) {f g : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict (triadicCube d m))) (hg : H1 (triadicCube d m) g G) :
    ∀ n, n ≤ m → |oscillationPairing n (m - n) f g - oscillationPairing 0 m f g| ≤
      ∑ i ∈ Finset.range n, √(((3 : ℝ) ^ i) ^ d * averageSqSum i (m - i) f) *
        √(cubePoincareConstant d * ((3 : ℝ) ^ (i + 1)) ^ 2 *
          ∫ x in triadicCube d m, euclideanSq (G x)) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := abs_oscillationPairing_succ_sub_le m n (m - (n + 1)) (by omega) hf hg
    rw [show m - (n + 1) + 1 = m - n by omega] at h2
    rw [Finset.sum_range_succ]
    have h3 := abs_sub_le (oscillationPairing (n + 1) (m - (n + 1)) f g)
      (oscillationPairing n (m - n) f g) (oscillationPairing 0 m f g)
    linarith

/-- **The unit scale**: `|T_0| ≤ (∫_{□_m} f²)^{1/2} (C ∫_{□_m} |∇g|²)^{1/2}`. -/
theorem abs_oscillationPairing_zero_le (m : ℕ) {f g : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict (triadicCube d m))) (hg : H1 (triadicCube d m) g G) :
    |oscillationPairing 0 m f g| ≤
      √(∫ x in triadicCube d m, f x ^ 2) *
        √(cubePoincareConstant d * ∫ x in triadicCube d m, euclideanSq (G x)) := by
  have hQW : ∀ k : Fin d → Fin (3 ^ m), partitionCube 0 m k ⊆ triadicCube d m := fun k => by
    have := partitionCube_subset (d := d) 0 m k
    rwa [Nat.zero_add] at this
  have hk : ∀ k : Fin d → Fin (3 ^ m),
      |∫ x in partitionCube 0 m k, f x * (g x - ⨍ y in partitionCube 0 m k, g y)| ≤
        √(∫ x in partitionCube 0 m k, f x ^ 2) *
          √(cubePoincareConstant d * ∫ x in partitionCube 0 m k, euclideanSq (G x)) := by
    intro k
    have hgk := hg.mono (hQW k)
    have : IsFiniteMeasure (volume.restrict (partitionCube (d := d) 0 m k)) :=
      isFiniteMeasure_restrict.mpr (volume_partitionCube_ne_top 0 m k)
    have hga : MemLp (fun x => g x - ⨍ y in partitionCube 0 m k, g y) 2
        (volume.restrict (partitionCube 0 m k)) := hgk.1.sub (memLp_const _)
    refine (abs_setIntegral_mul_le
      (hf.mono_measure (Measure.restrict_mono (hQW k) le_rfl)) hga).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    have h := setIntegral_sq_sub_setAverage_le_partitionCube 0 m k hgk
    simpa using h
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin d → Fin (3 ^ m)))
    (f := fun k => ∫ x in partitionCube 0 m k, f x ^ 2)
    (g := fun k => cubePoincareConstant d * ∫ x in partitionCube 0 m k, euclideanSq (G x))
    (fun k => integral_nonneg fun x => sq_nonneg _)
    (fun k => mul_nonneg (cubePoincareConstant_nonneg d)
      (integral_nonneg fun x => euclideanSq_nonneg _))
  have hfW : IntegrableOn (fun x => f x ^ 2) (triadicCube d (0 + m)) := by
    rw [Nat.zero_add]
    exact hf.integrable_sq
  have hGW : IntegrableOn (fun x => euclideanSq (G x)) (triadicCube d (0 + m)) := by
    rw [Nat.zero_add]
    exact integrable_euclideanSq_of_memLp hg.2.1
  unfold oscillationPairing
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hk k).trans
    (hcs.trans (le_of_eq ?_)))
  rw [← Finset.mul_sum, ← setIntegral_triadicCube_eq_sum 0 m hfW,
    ← setIntegral_triadicCube_eq_sum 0 m hGW, Nat.zero_add]

/-- Jensen's inequality `|(f)_U| ≤ ‖f‖_{L̲²(U)}`. -/
theorem abs_setAverage_le_scalarRms {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    |⨍ x in U, f x| ≤ scalarRms volume U f := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU
  exact Real.abs_le_sqrt (sq_setAverage_le hU0 hU (hf.integrable (by norm_num)) hf.integrable_sq)

/-- Jensen's inequality on the children of `□_{m+1}`:
`|(f)_{□_{m+1}}| ≤ (3^{-d} Σ_y |(f)_{y+□_m}|²)^{1/2}`. -/
theorem abs_setAverage_triadicCube_succ_le (m : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (triadicCube d (m + 1)))) :
    |⨍ x in triadicCube d (m + 1), f x| ≤ √(1 / ((3 : ℝ) ^ 1) ^ d * averageSqSum m 1 f) := by
  have hN : (0 : ℝ) < ((3 : ℝ) ^ 1) ^ d := by positivity
  have hWt := volume_triadicCube_ne_top d (m + 1)
  have : IsFiniteMeasure (volume.restrict (triadicCube d (m + 1))) :=
    isFiniteMeasure_restrict.mpr hWt
  have hfI : IntegrableOn f (triadicCube d (m + 1)) := hf.integrable (by norm_num)
  have havg : ⨍ x in triadicCube d (m + 1), f x = 1 / ((3 : ℝ) ^ 1) ^ d *
      ∑ k : Fin d → Fin (3 ^ 1), ⨍ x in partitionCube m 1 k, f x := by
    rw [setAverage_eq volume f (triadicCube d (m + 1)), smul_eq_mul, setIntegral_triadicCube_eq_sum m 1 hfI,
      Finset.sum_congr rfl fun k _ => setIntegral_eq_volume_mul_setAverage
        (volume_partitionCube_ne_zero m 1 k) (volume_partitionCube_ne_top m 1 k) f]
    simp_rw [volumeReal_partitionCube]
    rw [← Finset.mul_sum, ← mul_assoc, volumeReal_triadicCube_add m 1]
    congr 1
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity : ((3 : ℝ) ^ m) ^ d ≠ 0), mul_one,
      one_div]
  rw [havg]
  apply Real.abs_le_sqrt
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d → Fin (3 ^ 1))))
    (f := fun k => ⨍ x in partitionCube m 1 k, f x)
  rw [Finset.card_univ, card_partitionIndex] at hcs
  calc (1 / ((3 : ℝ) ^ 1) ^ d * ∑ k : Fin d → Fin (3 ^ 1), ⨍ x in partitionCube m 1 k, f x) ^ 2
      = (1 / ((3 : ℝ) ^ 1) ^ d) ^ 2 *
          (∑ k : Fin d → Fin (3 ^ 1), ⨍ x in partitionCube m 1 k, f x) ^ 2 := by ring
    _ ≤ (1 / ((3 : ℝ) ^ 1) ^ d) ^ 2 * (((3 : ℝ) ^ 1) ^ d * averageSqSum m 1 f) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = 1 / ((3 : ℝ) ^ 1) ^ d * averageSqSum m 1 f * (((3 : ℝ) ^ 1) ^ d * (1 / ((3 : ℝ) ^ 1) ^ d)) := by
        ring
    _ = 1 / ((3 : ℝ) ^ 1) ^ d * averageSqSum m 1 f := by
        rw [mul_one_div_cancel hN.ne', mul_one]

/-- The mean term: `3^m |(f)_{□_m}| ≤ ‖f‖_{L̲²(□_m)} + 3 Σ_{n<m} 3^n (|Z_n|⁻¹ Σ_y |(f)_{y+□_n}|²)^{1/2}`. -/
theorem three_pow_mul_abs_setAverage_le (m : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (triadicCube d m))) :
    (3 : ℝ) ^ m * |⨍ x in triadicCube d m, f x| ≤ scalarRms volume (triadicCube d m) f +
      3 * ∑ n ∈ Finset.range m,
        (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) := by
  have hS : ∀ m', 0 ≤ ∑ n ∈ Finset.range m',
      (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) := fun m' =>
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  cases m with
  | zero =>
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    exact abs_setAverage_le_scalarRms (volume_triadicCube_ne_zero d 0)
      (volume_triadicCube_ne_top d 0) hf
  | succ m =>
    have h1 := abs_setAverage_triadicCube_succ_le m hf
    have hS' := hS m
    rw [Finset.sum_range_succ, show m + 1 - m = 1 by omega]
    have hrms : 0 ≤ scalarRms volume (triadicCube d (m + 1)) f := Real.sqrt_nonneg _
    have h2 : (3 : ℝ) ^ (m + 1) * |⨍ x in triadicCube d (m + 1), f x| ≤
        3 * ((3 : ℝ) ^ m * √(1 / ((3 : ℝ) ^ 1) ^ d * averageSqSum m 1 f)) := by
      rw [pow_succ (3 : ℝ) m]
      calc (3 : ℝ) ^ m * 3 * |⨍ x in triadicCube d (m + 1), f x|
          = 3 * ((3 : ℝ) ^ m * |⨍ x in triadicCube d (m + 1), f x|) := by ring
        _ ≤ _ := by gcongr
    linarith

/-- **The pairing bound**: for `f ∈ L²(□_m)` and `g ∈ H¹(□_m)`,
`|⨍_{□_m} f g| ≤ (C^{1/2} ‖f‖ + 3 C^{1/2} Σ_{n<m} 3^n (|Z_n|⁻¹ Σ_y |(f)_{y+□_n}|²)^{1/2}) ‖∇g‖
+ |(g)_{□_m}| |(f)_{□_m}|`, all norms in `L̲²(□_m)`. -/
theorem abs_setAverage_mul_le_multiscale (m : ℕ) {f g : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict (triadicCube d m))) (hg : H1 (triadicCube d m) g G) :
    |⨍ x in triadicCube d m, f x * g x| ≤
      (√(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f +
        3 * √(cubePoincareConstant d) * ∑ n ∈ Finset.range m,
          (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f)) *
          vectorRms volume (triadicCube d m) G +
      |⨍ x in triadicCube d m, g x| * |⨍ x in triadicCube d m, f x| := by
  have hK : 0 ≤ cubePoincareConstant d := cubePoincareConstant_nonneg d
  have hW0 : volume (triadicCube d m) ≠ 0 := volume_triadicCube_ne_zero d m
  have hWt : volume (triadicCube d m) ≠ ⊤ := volume_triadicCube_ne_top d m
  have : IsFiniteMeasure (volume.restrict (triadicCube d m)) := isFiniteMeasure_restrict.mpr hWt
  have hfI : IntegrableOn f (triadicCube d m) := hf.integrable (by norm_num)
  have hfgI : IntegrableOn (fun x => f x * g x) (triadicCube d m) := hf.integrable_mul hg.1
  have hdec : ∫ x in triadicCube d m, f x * g x = oscillationPairing m 0 f g +
      (⨍ x in triadicCube d m, g x) * ∫ x in triadicCube d m, f x := by
    have h := setIntegral_mul_sub_const_eq hfgI hfI 0 (⨍ x in triadicCube d m, g x)
    simp only [sub_zero] at h
    rw [h]
    congr 1
    simp only [oscillationPairing, partitionCube_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, pow_zero, one_pow, one_smul]
  have hsqf := sqrt_setIntegral_sq_eq hW0 hWt f
  have hsqG := sqrt_setIntegral_euclideanSq_eq hW0 hWt G
  have hfa0 := setIntegral_eq_volume_mul_setAverage hW0 hWt f
  have hvol0 : 0 < volume.real (triadicCube d m) := ENNReal.toReal_pos hW0 hWt
  have hvolW0 : volume.real (triadicCube d m) = ((3 : ℝ) ^ m) ^ d := volumeReal_triadicCube m
  have hLHS0 : ⨍ x in triadicCube d m, f x * g x = (volume.real (triadicCube d m))⁻¹ *
      (oscillationPairing m 0 f g + (⨍ x in triadicCube d m, g x) * ∫ x in triadicCube d m, f x) := by
    rw [← hdec, setAverage_eq volume (fun x => f x * g x) (triadicCube d m), smul_eq_mul]
  have htel := abs_oscillationPairing_sub_le m hf hg m le_rfl
  rw [Nat.sub_self] at htel
  have h0 := abs_oscillationPairing_zero_le m hf hg
  rw [hsqf, Real.sqrt_mul hK, hsqG] at h0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = vectorRms volume (triadicCube d m) G := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ n ∈ Finset.range m,
      (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = volume.real (triadicCube d m) := ⟨_, rfl⟩
  rw [← hR] at hsqG h0
  rw [← hR, ← hS, hLHS0]
  rw [← hV] at hvol0 hvolW0 hsqf hsqG hfa0 h0 ⊢
  have hvv : √V * √V = V := Real.mul_self_sqrt hvol0.le
  have hterm : ∀ n ∈ Finset.range m,
      √(((3 : ℝ) ^ n) ^ d * averageSqSum n (m - n) f) *
        √(cubePoincareConstant d * ((3 : ℝ) ^ (n + 1)) ^ 2 *
          ∫ x in triadicCube d m, euclideanSq (G x)) =
      V * (3 * √(cubePoincareConstant d) *
        ((3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f)) * R) := by
    intro n hn
    have hnm : n ≤ m := (Finset.mem_range.mp hn).le
    have hN : (0 : ℝ) < ((3 : ℝ) ^ (m - n)) ^ d := by positivity
    have hsplit : V = ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ (m - n)) ^ d := by
      rw [hvolW0, ← mul_pow, ← pow_add, Nat.add_sub_cancel' hnm]
    have e0 : ((3 : ℝ) ^ n) ^ d * averageSqSum n (m - n) f =
        V * (1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) := by
      rw [hsplit]
      calc ((3 : ℝ) ^ n) ^ d * averageSqSum n (m - n) f
          = ((3 : ℝ) ^ n) ^ d * averageSqSum n (m - n) f *
              (((3 : ℝ) ^ (m - n)) ^ d * (1 / ((3 : ℝ) ^ (m - n)) ^ d)) := by
            rw [mul_one_div_cancel hN.ne', mul_one]
        _ = _ := by ring
    have hx : 0 ≤ cubePoincareConstant d * ((3 : ℝ) ^ (n + 1)) ^ 2 :=
      mul_nonneg hK (by positivity)
    have h3n : (0 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := by positivity
    rw [e0, Real.sqrt_mul hvol0.le, Real.sqrt_mul hx, Real.sqrt_mul hK, Real.sqrt_sq h3n, hsqG]
    calc √V * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) *
          (√(cubePoincareConstant d) * (3 : ℝ) ^ (n + 1) * (√V * R))
        = (√V * √V) * (3 * √(cubePoincareConstant d) *
          ((3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f)) * R) := by
          ring
      _ = _ := by rw [hvv]
  have hsum : ∑ n ∈ Finset.range m, √(((3 : ℝ) ^ n) ^ d * averageSqSum n (m - n) f) *
        √(cubePoincareConstant d * ((3 : ℝ) ^ (n + 1)) ^ 2 *
          ∫ x in triadicCube d m, euclideanSq (G x)) =
      V * (3 * √(cubePoincareConstant d) * S * R) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← hS]
  rw [hsum] at htel
  have h0' : |oscillationPairing 0 m f g| ≤
      V * (√(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f * R) := by
    refine h0.trans (le_of_eq ?_)
    calc √V * scalarRms volume (triadicCube d m) f * (√(cubePoincareConstant d) * (√V * R))
        = (√V * √V) * (√(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f * R) := by
          ring
      _ = _ := by rw [hvv]
  have hT : |oscillationPairing m 0 f g| ≤
      V * (√(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f * R) +
        V * (3 * √(cubePoincareConstant d) * S * R) := by
    have := abs_sub_abs_le_abs_sub (oscillationPairing m 0 f g) (oscillationPairing 0 m f g)
    linarith
  have hfa : |∫ x in triadicCube d m, f x| = V * |⨍ x in triadicCube d m, f x| := by
    rw [hfa0, abs_mul, abs_of_pos hvol0]
  rw [abs_mul, abs_inv, abs_of_pos hvol0, inv_mul_le_iff₀ hvol0]
  calc |oscillationPairing m 0 f g + (⨍ x in triadicCube d m, g x) * ∫ x in triadicCube d m, f x|
      ≤ |oscillationPairing m 0 f g| +
          |⨍ x in triadicCube d m, g x| * |∫ x in triadicCube d m, f x| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ V * (√(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f * R) +
          V * (3 * √(cubePoincareConstant d) * S * R) +
          |⨍ x in triadicCube d m, g x| * (V * |⨍ x in triadicCube d m, f x|) := by
        rw [hfa]
        linarith
    _ = _ := by ring

/-- The normalizing factor `|□_m|^{-1/d} = 3^{-m}` of the normalized `H¹(□_m)` norm. -/
theorem toReal_volume_triadicCube_rpow [NeZero d] (m : ℕ) :
    (volume (triadicCube d m)).toReal ^ ((-1 : ℝ) / d) = ((3 : ℝ) ^ m)⁻¹ := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ m := by positivity
  rw [← measureReal_def, volumeReal_triadicCube, ← Real.rpow_natCast ((3 : ℝ) ^ m) d,
    ← Real.rpow_mul h3, show (d : ℝ) * ((-1 : ℝ) / d) = -1 by field_simp, Real.rpow_neg_one]

/-- **Proposition 1.12 (multiscale Poincaré inequality)**, (1.42): there is `C(d) < ∞` such that,
for every `m ∈ ℕ` and `f ∈ L²(□_m)`,
`‖f‖_{Ĥ̲⁻¹(□_m)} ≤ C ‖f‖_{L̲²(□_m)} + C Σ_{n=0}^{m-1} 3^n (|Z_n|⁻¹ Σ_{y ∈ Z_n} |(f)_{y+□_n}|²)^{1/2}`.
The points `y ∈ Z_n = 3^n ℤ^d ∩ □_m` are the centers of the subcubes `partitionCube n (m - n) k`,
`k ∈ {0, …, 3^{m-n} - 1}^d`, and `|Z_n| = 3^{d(m-n)}`. -/
theorem proposition_1_12 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (f : Vec d → ℝ), MemLp f 2 (volume.restrict (triadicCube d m)) →
      hatNegativeSobolevNorm (triadicCube d m) f ≤
        ENNReal.ofReal (C * scalarRms volume (triadicCube d m) f +
          C * ∑ n ∈ Finset.range m, (3 : ℝ) ^ n *
            √(1 / ((3 : ℝ) ^ (m - n)) ^ d *
              ∑ k : Fin d → Fin (3 ^ (m - n)), (⨍ x in partitionCube n (m - n) k, f x) ^ 2)) := by
  refine ⟨3 * (√(cubePoincareConstant d) + 1), by positivity, fun m f hf => ?_⟩
  refine hatNegativeSobolevNorm_le_ofReal fun g G hg hgn => ?_
  change _ ≤ 3 * (√(cubePoincareConstant d) + 1) * scalarRms volume (triadicCube d m) f +
    3 * (√(cubePoincareConstant d) + 1) * ∑ n ∈ Finset.range m,
      (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f)
  have hW0 : volume (triadicCube d m) ≠ 0 := volume_triadicCube_ne_zero d m
  have hWt : volume (triadicCube d m) ≠ ⊤ := volume_triadicCube_ne_top d m
  unfold h1Norm at hgn
  rw [toReal_volume_triadicCube_rpow m] at hgn
  have hrg : 0 ≤ scalarRms volume (triadicCube d m) g := Real.sqrt_nonneg _
  have hrf : 0 ≤ scalarRms volume (triadicCube d m) f := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hg0 : 0 ≤ ((3 : ℝ) ^ m)⁻¹ * scalarRms volume (triadicCube d m) g :=
    mul_nonneg (inv_nonneg.mpr h3.le) hrg
  have hRle : vectorRms volume (triadicCube d m) G ≤ 1 := by linarith
  have hgle : scalarRms volume (triadicCube d m) g ≤ (3 : ℝ) ^ m := by
    have hG0 : 0 ≤ vectorRms volume (triadicCube d m) G := Real.sqrt_nonneg _
    have h' : ((3 : ℝ) ^ m)⁻¹ * scalarRms volume (triadicCube d m) g ≤ 1 := by linarith
    have := (inv_mul_le_iff₀ h3).mp h'
    linarith
  have hga : |⨍ x in triadicCube d m, g x| ≤ (3 : ℝ) ^ m :=
    (abs_setAverage_le_scalarRms hW0 hWt hg.1).trans hgle
  have hmain := abs_setAverage_mul_le_multiscale m hf hg
  have hfa := three_pow_mul_abs_setAverage_le m hf
  have hS0 : 0 ≤ ∑ n ∈ Finset.range m,
      (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hsK : 0 ≤ √(cubePoincareConstant d) := Real.sqrt_nonneg _
  have h1 : (√(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f +
      3 * √(cubePoincareConstant d) * ∑ n ∈ Finset.range m,
        (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f)) *
        vectorRms volume (triadicCube d m) G ≤
      √(cubePoincareConstant d) * scalarRms volume (triadicCube d m) f +
        3 * √(cubePoincareConstant d) * ∑ n ∈ Finset.range m,
          (3 : ℝ) ^ n * √(1 / ((3 : ℝ) ^ (m - n)) ^ d * averageSqSum n (m - n) f) :=
    mul_le_of_le_one_right (add_nonneg (mul_nonneg hsK hrf)
      (mul_nonneg (mul_nonneg (by norm_num) hsK) hS0)) hRle
  have h2 : |⨍ x in triadicCube d m, g x| * |⨍ x in triadicCube d m, f x| ≤
      (3 : ℝ) ^ m * |⨍ x in triadicCube d m, f x| :=
    mul_le_mul_of_nonneg_right hga (abs_nonneg _)
  linarith [mul_nonneg hsK hrf, mul_nonneg hsK hS0]

end QSH
