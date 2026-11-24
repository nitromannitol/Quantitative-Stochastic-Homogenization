import QuantitativeStochasticHomogenization.Ch01.Sec03.Proposition17

/-!
# The deterministic estimate (1.35) of the proof of Proposition 1.8

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3, Step 1 of the proof of Proposition 1.8, (1.35)–(1.36): for the minimizer
`v(·, □_m, p) = ℓ_p + u` and `n ≤ m`,
`3^{-2m} ⨍_{□_m} u² ≤ C 3^{2(n-m)} |p|² + C (|Z_n|⁻¹ Σ_z μ(z + □_n, p) - μ(□_m, p))`.

The book glues the minimizers of the subcubes `z + □_n` (1.18) and uses the first inequality of
(1.19). Here tests `w_z` of the subcubes with energies within `δ` of `μ(z + □_n, p)` are glued
into a test `w` of `□_m`; the quadratic response (1.13) bounds `⨍_{□_m} |∇w - g|²`, the Poincaré
inequality in `H¹₀(□_m)` bounds `⨍_{□_m} (u - w)²`, the Poincaré inequality in each subcube bounds
`⨍_{z + □_n} w_z²`, and `δ → 0`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

theorem triadicCube_subset_cube (m : ℕ) : triadicCube d m ⊆ cube 0 ((3 : ℝ) ^ m) := by
  intro x hx i
  have := mem_triadicCube_iff.mp hx i
  simpa using this

theorem partitionCube_subset_cube (n r : ℕ) (k : Fin d → Fin (3 ^ r)) :
    partitionCube n r k ⊆ cube (latticeShift (partitionCenter n r k)) ((3 : ℝ) ^ n) := by
  intro x hx i
  have := mem_partitionCube_iff.mp hx i
  rw [latticeShift_partitionCenter_apply]
  exact this

/-- Splitting an integral over `□_{n+r}` along the partition into the translates of `□_n`. -/
theorem setIntegral_triadicCube_eq_sum (n r : ℕ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (triadicCube d (n + r))) :
    ∫ x in triadicCube d (n + r), f x = ∑ k, ∫ x in partitionCube n r k, f x := by
  have hae : triadicCube d (n + r) =ᵐ[volume] ⋃ k, partitionCube n r k := by
    refine ae_eq_set.mpr ⟨volume_triadicCube_diff_partitionCube n r, ?_⟩
    rw [sdiff_eq_empty.mpr (iUnion_subset (partitionCube_subset n r)), measure_empty]
  rw [setIntegral_congr_set hae, integral_iUnion_fintype
    (fun k => (isOpen_partitionCube n r k).measurableSet) (pairwise_disjoint_partitionCube n r)
    (fun k => hf.mono_set (partitionCube_subset n r k))]

theorem glue_eq_of_mem {n r : ℕ} {w : (Fin d → Fin (3 ^ r)) → Vec d → ℝ}
    (hw : ∀ k, IsSpatialTest (partitionCube n r k) (w k)) {k : Fin d → Fin (3 ^ r)} {x : Vec d}
    (hx : x ∈ partitionCube n r k) : ∑ j, w j x = w k x := by
  rw [Finset.sum_eq_single k]
  · intro j _ hjk
    refine image_eq_zero_of_notMem_tsupport fun hxj => ?_
    exact Set.disjoint_left.mp (pairwise_disjoint_partitionCube n r hjk) ((hw j).2.2 hxj) hx
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem glue_gradient_eq_of_mem {n r : ℕ} {w : (Fin d → Fin (3 ^ r)) → Vec d → ℝ}
    (hw : ∀ k, IsSpatialTest (partitionCube n r k) (w k)) {k : Fin d → Fin (3 ^ r)} {x : Vec d}
    (hx : x ∈ partitionCube n r k) : gradient (fun x => ∑ j, w j x) x = gradient (w k) x := by
  have hwW : ∀ j ∈ (Finset.univ : Finset (Fin d → Fin (3 ^ r))),
      IsSpatialTest (triadicCube d (n + r)) (w j) := fun j _ =>
    ⟨(hw j).1, (hw j).2.1, (hw j).2.2.trans (partitionCube_subset n r j)⟩
  rw [IsSpatialTest.gradient_finsetSum Finset.univ hwW x, Finset.sum_eq_single k]
  · intro j _ hjk
    have hxs : x ∉ tsupport (w j) := fun hxj =>
      Set.disjoint_left.mp (pairwise_disjoint_partitionCube n r hjk) ((hw j).2.2 hxj) hx
    have h0 : fderiv ℝ (w j) x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    funext l
    simp [gradient, coordinateDerivative, h0]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem card_partitionIndex (r : ℕ) :
    (Fintype.card (Fin d → Fin (3 ^ r)) : ℝ) = ((3 : ℝ) ^ r) ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rfl

theorem volumeReal_triadicCube_add (n r : ℕ) :
    volume.real (triadicCube d (n + r)) = ((3 : ℝ) ^ r) ^ d * ((3 : ℝ) ^ n) ^ d := by
  rw [volumeReal_triadicCube, pow_add, mul_pow, mul_comm]

/-- **(1.35)**: for the minimizer `(u, g)` of `μ(□_{n+r}, p)`,
`3^{-2(n+r)} ⨍_{□_{n+r}} u² ≤ 4C (3^{-dr} Σ_k μ(z_k + □_n, p) - μ(□_{n+r}, p)) +
2C (3^n/3^{n+r})² (2Λ + 2)|p|²`, with `C` the constant of the Poincaré inequality for tests. -/
theorem minimizer_setAverage_sq_le [NeZero d] (a : CoefficientField d Λ) (n r : ℕ) (e : Vec d)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hmin : IsDirichletMinimizer a (triadicCube d (n + r)) e u g) :
    ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u x ^ 2 ≤
      4 * testPoincareConstant d * (∑ k : Fin d → Fin (3 ^ r), (1 / ((3 : ℝ) ^ r) ^ d) *
          dirichletEnergy a (partitionCube n r k) e - dirichletEnergy a (triadicCube d (n + r)) e) +
        2 * testPoincareConstant d * ((3 : ℝ) ^ n / (3 : ℝ) ^ (n + r)) ^ 2 *
          ((2 * Λ + 2) * euclideanSq e) := by
  have hc : 0 ≤ testPoincareConstant d := testPoincareConstant_nonneg d
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_of_coefficientField a)
  have hWt : volume (triadicCube d (n + r)) ≠ ⊤ := volume_triadicCube_ne_top d (n + r)
  have := isFiniteMeasure_restrict.mpr hWt
  obtain ⟨Vn, hVn_def⟩ : ∃ Vn : ℝ, Vn = ((3 : ℝ) ^ n) ^ d := ⟨_, rfl⟩
  obtain ⟨N, hN_def⟩ : ∃ N : ℝ, N = ((3 : ℝ) ^ r) ^ d := ⟨_, rfl⟩
  have hVn : 0 < Vn := by rw [hVn_def]; positivity
  have hN : 0 < N := by rw [hN_def]; positivity
  have hVm : volume.real (triadicCube d (n + r)) = N * Vn := by
    rw [volumeReal_triadicCube_add n r, hN_def, hVn_def]
  have hVmpos : 0 < volume.real (triadicCube d (n + r)) := by rw [hVm]; positivity
  have hQt : ∀ k : Fin d → Fin (3 ^ r), volume (partitionCube (d := d) n r k) ≠ ⊤ :=
    volume_partitionCube_ne_top n r
  have hQV : ∀ k : Fin d → Fin (3 ^ r), volume.real (partitionCube (d := d) n r k) = Vn :=
    fun k => by rw [volumeReal_partitionCube n r, hVn_def]
  have hcard : ((Finset.univ : Finset (Fin d → Fin (3 ^ r))).card : ℝ) = N := by
    rw [Finset.card_univ, card_partitionIndex, hN_def]
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n + r) := by positivity
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = (3 : ℝ) ^ n / (3 : ℝ) ^ (n + r) := ⟨_, rfl⟩
  rw [← hρ_def, ← hN_def]
  have hρ0 : 0 ≤ ρ := by rw [hρ_def]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ_def, div_le_one hR]
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n r)
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0 hρ1
  have he0 : 0 ≤ euclideanSq e := euclideanSq_nonneg e
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = ε / (12 * testPoincareConstant d + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; positivity
  have hδc : δ * (4 * testPoincareConstant d + 8 * testPoincareConstant d * ρ ^ 2) ≤ ε := by
    have h1 : 4 * testPoincareConstant d + 8 * testPoincareConstant d * ρ ^ 2 ≤
        12 * testPoincareConstant d + 1 := by
      have := mul_le_mul_of_nonneg_left hρ2 hc
      linarith
    calc δ * (4 * testPoincareConstant d + 8 * testPoincareConstant d * ρ ^ 2)
        ≤ δ * (12 * testPoincareConstant d + 1) := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = ε := by rw [hδ_def]; field_simp
  choose w hw hwE using fun k => exists_test_trialEnergy_lt a (hQt k) e hδ
  have hwWt : IsSpatialTest (triadicCube d (n + r)) (fun x => ∑ k, w k x) :=
    IsSpatialTest.finsetSum Finset.univ fun k _ =>
      ⟨(hw k).1, (hw k).2.1, (hw k).2.2.trans (partitionCube_subset n r k)⟩
  -- (C): the energy of the glued test
  have hEglue : trialEnergy a (triadicCube d (n + r)) e (gradient fun x => ∑ k, w k x) =
      ∑ k, (1 / N) * trialEnergy a (partitionCube n r k) e (gradient (w k)) := by
    rw [trialEnergy_eq, setIntegral_triadicCube_eq_sum n r
      (integrable_energyDensity a hWt e (hwWt.memLp_gradient _)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [trialEnergy_eq, hQV k, setIntegral_congr_fun (isOpen_partitionCube n r k).measurableSet
      fun x hx => by rw [glue_gradient_eq_of_mem hw hx], hVm]
    field_simp
  -- (B): quadratic response
  have hqr := (hmin.quadraticResponse hWt hwWt.h01).1
  rw [setAverage_eq, smul_eq_mul, hEglue] at hqr
  -- (A): Poincaré in `H¹₀(□_{n+r})`
  have hA := setIntegral_sq_le_of_H01 0 hR (triadicCube_subset_cube (n + r)) (hmin.1.sub hwWt.h01)
  -- (D), (E): the glued test
  have hDk : ∀ k, ∫ x in partitionCube n r k, w k x ^ 2 ≤
      testPoincareConstant d * ((3 : ℝ) ^ n) ^ 2 *
        (Vn * (4 * (dirichletEnergy a (partitionCube n r k) e + δ) + 2 * euclideanSq e)) := by
    intro k
    have hP := setIntegral_sq_le_of_isSpatialTest _ (by positivity)
      (partitionCube_subset_cube n r k) (hw k)
    refine hP.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hG := (hw k).memLp_gradient (volume.restrict (partitionCube n r k))
    have := isFiniteMeasure_restrict.mpr (hQt k)
    have hpt : ∀ x, euclideanSq (gradient (w k) x) ≤
        4 * ((1 / 2 : ℝ) * dot (e + gradient (w k) x) ((a x).mulVec (e + gradient (w k) x))) +
          2 * euclideanSq e := by
      intro x
      have h1 := (a.elliptic x (e + gradient (w k) x)).1
      have h2 : euclideanSq (gradient (w k) x) ≤ 2 * euclideanSq (e + gradient (w k) x) +
          2 * euclideanSq e := by
        have hpar := dot_parallelogram (1 : Mat d) (e + gradient (w k) x) e
        simp only [Matrix.one_mulVec] at hpar
        have hsub : e + gradient (w k) x - e = gradient (w k) x := by abel
        rw [hsub] at hpar
        have hnn := euclideanSq_nonneg (e + gradient (w k) x + e)
        simp only [euclideanSq] at hnn ⊢
        linarith
      linarith
    have iρ := integrable_energyDensity a (hQt k) e hG
    have hint : ∫ x in partitionCube n r k, euclideanSq (gradient (w k) x) ≤
        ∫ x in partitionCube n r k, (4 * ((1 / 2 : ℝ) * dot (e + gradient (w k) x)
          ((a x).mulVec (e + gradient (w k) x))) + 2 * euclideanSq e) :=
      integral_mono (integrable_euclideanSq_of_memLp hG) ((iρ.const_mul 4).add (integrable_const _))
        hpt
    rw [integral_add (iρ.const_mul 4) (integrable_const _), integral_const_mul, setIntegral_const,
      hQV k, smul_eq_mul] at hint
    have hE := hwE k
    rw [trialEnergy_eq, hQV k] at hE
    have hE' : ∫ x in partitionCube n r k, (1 / 2 : ℝ) * dot (e + gradient (w k) x)
        ((a x).mulVec (e + gradient (w k) x)) ≤
        Vn * (dirichletEnergy a (partitionCube n r k) e + δ) := by
      have := mul_lt_mul_of_pos_left hE hVn
      rw [← mul_assoc, mul_inv_cancel₀ hVn.ne', one_mul] at this
      exact this.le
    nlinarith
  have hwW2 : ∫ x in triadicCube d (n + r), (∑ k, w k x) ^ 2 =
      ∑ k, ∫ x in partitionCube n r k, w k x ^ 2 := by
    rw [setIntegral_triadicCube_eq_sum n r ((hwWt.memLp_two _).integrable_sq)]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact setIntegral_congr_fun (isOpen_partitionCube n r k).measurableSet
      fun x hx => by rw [glue_eq_of_mem hw hx]
  -- (F)
  have hu2 := hmin.1.1
  have hF : ∫ x in triadicCube d (n + r), u x ^ 2 ≤
      2 * (∫ x in triadicCube d (n + r), (u x - ∑ k, w k x) ^ 2) +
        2 * ∫ x in triadicCube d (n + r), (∑ k, w k x) ^ 2 := by
    have i1 : Integrable (fun x => (u x - ∑ k, w k x) ^ 2)
        (volume.restrict (triadicCube d (n + r))) :=
      (hu2.sub (hwWt.memLp_two _)).integrable_sq
    have i2 : Integrable (fun x => (∑ k, w k x) ^ 2) (volume.restrict (triadicCube d (n + r))) :=
      (hwWt.memLp_two _).integrable_sq
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
      (i2.const_mul _)]
    refine integral_mono hu2.integrable_sq ((i1.const_mul _).add (i2.const_mul _)) fun x => ?_
    simp only
    nlinarith [sq_nonneg (u x - 2 * ∑ k, w k x)]
  have hμk : ∀ k, dirichletEnergy a (partitionCube n r k) e ≤ (1 / 2 : ℝ) * Λ * euclideanSq e :=
    fun k => dirichletEnergy_le a (volume_partitionCube_ne_zero n r k) (hQt k) hΛ e
  -- combining
  set Δ := ∑ k, (1 / N) * dirichletEnergy a (partitionCube n r k) e -
    dirichletEnergy a (triadicCube d (n + r)) e with hΔ
  have hgrad : ∫ x in triadicCube d (n + r), euclideanSq (g x - gradient (fun x => ∑ k, w k x) x)
      ≤ 2 * volume.real (triadicCube d (n + r)) * (Δ + δ) := by
    have hsum : ∑ k, (1 / N) * trialEnergy a (partitionCube n r k) e (gradient (w k)) ≤
        ∑ k, (1 / N) * dirichletEnergy a (partitionCube n r k) e + δ := by
      have : ∑ _k : Fin d → Fin (3 ^ r), (1 / N) * δ = δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp
      rw [← this, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (hwE k).le (by positivity)
    have hcomm : ∫ x in triadicCube d (n + r), euclideanSq (g x - gradient (fun x => ∑ k, w k x) x)
        = ∫ x in triadicCube d (n + r), euclideanSq (gradient (fun x => ∑ k, w k x) x - g x) :=
      integral_congr_ae (Eventually.of_forall fun x => euclideanSq_sub_comm _ _)
    rw [hcomm]
    have h1 : (volume.real (triadicCube d (n + r)))⁻¹ *
        ∫ x in triadicCube d (n + r), euclideanSq (gradient (fun x => ∑ k, w k x) x - g x) ≤
        2 * (Δ + δ) := by linarith
    calc ∫ x in triadicCube d (n + r), euclideanSq (gradient (fun x => ∑ k, w k x) x - g x)
        = volume.real (triadicCube d (n + r)) * ((volume.real (triadicCube d (n + r)))⁻¹ *
          ∫ x in triadicCube d (n + r), euclideanSq (gradient (fun x => ∑ k, w k x) x - g x)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hVmpos.ne', one_mul]
      _ ≤ volume.real (triadicCube d (n + r)) * (2 * (Δ + δ)) :=
          mul_le_mul_of_nonneg_left h1 hVmpos.le
      _ = 2 * volume.real (triadicCube d (n + r)) * (Δ + δ) := by ring
  have hsumk : ∑ k, ∫ x in partitionCube n r k, w k x ^ 2 ≤
      testPoincareConstant d * ((3 : ℝ) ^ n) ^ 2 *
        (volume.real (triadicCube d (n + r)) * ((2 * Λ + 2) * euclideanSq e + 4 * δ)) := by
    calc ∑ k, ∫ x in partitionCube n r k, w k x ^ 2
        ≤ ∑ _k : Fin d → Fin (3 ^ r), testPoincareConstant d * ((3 : ℝ) ^ n) ^ 2 *
            (Vn * (4 * ((1 / 2 : ℝ) * Λ * euclideanSq e + δ) + 2 * euclideanSq e)) :=
          Finset.sum_le_sum fun k _ => (hDk k).trans (by
            have := hμk k
            gcongr)
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard, hVm]
          ring
  have hA' : ∫ x in triadicCube d (n + r), (u x - ∑ k, w k x) ^ 2 ≤
      testPoincareConstant d * ((3 : ℝ) ^ (n + r)) ^ 2 *
        (2 * volume.real (triadicCube d (n + r)) * (Δ + δ)) :=
    hA.trans (mul_le_mul_of_nonneg_left hgrad (by positivity))
  rw [hwW2] at hF
  have htotal : ∫ x in triadicCube d (n + r), u x ^ 2 ≤
      2 * (testPoincareConstant d * ((3 : ℝ) ^ (n + r)) ^ 2 *
        (2 * volume.real (triadicCube d (n + r)) * (Δ + δ))) +
      2 * (testPoincareConstant d * ((3 : ℝ) ^ n) ^ 2 *
        (volume.real (triadicCube d (n + r)) * ((2 * Λ + 2) * euclideanSq e + 4 * δ))) := by
    linarith
  rw [setAverage_eq, smul_eq_mul]
  have hR2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htotal
    (inv_nonneg.mpr hVmpos.le)) (sq_nonneg ((3 : ℝ) ^ (n + r))⁻¹)
  have hsimp : ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ((volume.real (triadicCube d (n + r)))⁻¹ *
      (2 * (testPoincareConstant d * ((3 : ℝ) ^ (n + r)) ^ 2 *
        (2 * volume.real (triadicCube d (n + r)) * (Δ + δ))) +
      2 * (testPoincareConstant d * ((3 : ℝ) ^ n) ^ 2 *
        (volume.real (triadicCube d (n + r)) * ((2 * Λ + 2) * euclideanSq e + 4 * δ))))) =
      4 * testPoincareConstant d * Δ + 2 * testPoincareConstant d * ρ ^ 2 *
        ((2 * Λ + 2) * euclideanSq e) +
      δ * (4 * testPoincareConstant d + 8 * testPoincareConstant d * ρ ^ 2) := by
    rw [hρ_def]
    field_simp
    ring
  rw [hsimp] at hR2
  linarith

end QSH
