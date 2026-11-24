import QuantitativeStochasticHomogenization.Ch01.Sec03.MinimizerOscillation

/-!
# Proposition 1.8: convergence of the minimizers to the affine function

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3, Proposition 1.8, (1.33): for `p ∈ B₁`,
`E[3^{-2m} ⨍_{□_m} |v(·, □_m, p) - ℓ_p|²] ≤ C 3^{-m/4} + C ω(⌈m/2⌉)`.

The minimizer is `v(·, □_m, p) = ℓ_p + u`, for a pair `(u, g)` with `IsDirichletMinimizer`; the
statement holds for every choice of minimizers `a ↦ (u a, g a)`, the quantity being independent of
the choice (`IsDirichletMinimizer.ae_eq`). Its measurability, which the book does not discuss, is
`measurable_setIntegral_sq_minimizer`: `⨍_U (u a)²` is the limit of `⨍_U t²` along tests `t` chosen
measurably from a countable family with energies within `1/(k+1)` of `μ(U, p)`, by the quadratic
response and the Poincaré inequality.

The proof is Step 2 of the book: the expectation of (1.35) at `n = ⌈m/2⌉`, with
`E[3^{-dr} Σ_k μ(z_k + □_n, p) - μ(□_m, p)] = E μ(□_n, p) - E μ(□_m, p) ≤ ω(n)` by stationarity.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- A countable family of tests of `U` whose gradients are dense, in `L²(U)`, among the gradients
of the tests of `U`. -/
theorem exists_dense_tests (U : Set (Vec d)) :
    ∃ t : ℕ → Vec d → ℝ, (∀ j, IsSpatialTest U (t j)) ∧ ∀ v, IsSpatialTest U v → ∀ ε > 0,
      ∃ j, ∫ x in U, euclideanSq (gradient (t j) x - gradient v x) < ε := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  set S : Set (Lp (Vec d) 2 (volume.restrict U)) :=
    {F | ∃ v, ∃ hv : IsSpatialTest U v, F = (hv.memLp_gradient _).toLp (gradient v)}
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have h0 : ((isSpatialTest_zero U).memLp_gradient (volume.restrict U)).toLp
      (gradient fun _ => (0 : ℝ)) ∈ S := ⟨_, isSpatialTest_zero U, rfl⟩
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    have := hST h0
    rw [hT, closure_empty] at this
    exact this
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  have hfS : ∀ j, f j ∈ S := fun j => hTS (hf ▸ Set.mem_range_self j)
  choose t ht htf using hfS
  refine ⟨t, ht, fun v hv ε hε => ?_⟩
  have hvS : (hv.memLp_gradient (volume.restrict U)).toLp (gradient v) ∈ S := ⟨v, hv, rfl⟩
  set δ := Real.sqrt (ε / (d + 1))
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨F, hFT, hdist⟩ := Metric.mem_closure_iff.mp (hST hvS) δ hδ
  rw [hf] at hFT
  obtain ⟨j, rfl⟩ := hFT
  refine ⟨j, ?_⟩
  have hle := integral_euclideanSq_le_card_mul_norm_sq
    (f j - (hv.memLp_gradient (volume.restrict U)).toLp (gradient v))
  have heq : ∫ x in U, euclideanSq ((f j - (hv.memLp_gradient (volume.restrict U)).toLp
      (gradient v) : Lp (Vec d) 2 (volume.restrict U)) x) =
      ∫ x in U, euclideanSq (gradient (t j) x - gradient v x) := by
    refine integral_congr_ae ?_
    rw [htf j]
    filter_upwards [Lp.coeFn_sub ((ht j).memLp_gradient (volume.restrict U)).toLp
      (hv.memLp_gradient (volume.restrict U)).toLp, ((ht j).memLp_gradient _).coeFn_toLp,
      (hv.memLp_gradient (volume.restrict U)).coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [heq] at hle
  have hn : ‖f j - (hv.memLp_gradient (volume.restrict U)).toLp (gradient v)‖ < δ := by
    rw [← dist_eq_norm, dist_comm]
    exact hdist
  have hn2 : ‖f j - (hv.memLp_gradient (volume.restrict U)).toLp (gradient v)‖ ^ 2 < ε / (d + 1) := by
    have h0' := norm_nonneg (f j - (hv.memLp_gradient (volume.restrict U)).toLp (gradient v))
    have : δ ^ 2 = ε / (d + 1) := Real.sq_sqrt (by positivity)
    nlinarith
  have hd : (d : ℝ) * (ε / (d + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  calc ∫ x in U, euclideanSq (gradient (t j) x - gradient v x)
      ≤ d * ‖f j - (hv.memLp_gradient (volume.restrict U)).toLp (gradient v)‖ ^ 2 := hle
    _ ≤ d * (ε / (d + 1)) := mul_le_mul_of_nonneg_left hn2.le (Nat.cast_nonneg d)
    _ < ε := hd

/-- **Measurability of the mean square of the minimizer**: for a family of minimizers
`a ↦ (u a, g a)` of `μ(U, p)`, `a ↦ ∫_U (u a)²` is measurable. -/
theorem measurable_setIntegral_sq_minimizer [NeZero d] {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (hU0 : volume U ≠ 0) (hΛ : 0 ≤ Λ) (e : Vec d)
    {u : CoefficientField d Λ → Vec d → ℝ} {g : CoefficientField d Λ → Vec d → Vec d}
    (hmin : ∀ a, IsDirichletMinimizer a U e (u a) (g a)) :
    Measurable fun a => ∫ x in U, u a x ^ 2 := by
  have hUt : volume U ≠ ⊤ := hU.measure_lt_top.ne
  have := isFiniteMeasure_restrict.mpr hUt
  have hV : 0 < volume.real U := ENNReal.toReal_pos hU0 hUt
  obtain ⟨R, hR, hUR⟩ := exists_subset_cube_of_isBounded hU
  obtain ⟨t, ht, hdense⟩ := exists_dense_tests U
  -- every coefficient field has an almost minimizing element of the family
  have hex : ∀ (a : CoefficientField d Λ) (k : ℕ), ∃ j,
      trialEnergy a U e (gradient (t j)) < dirichletEnergy a U e + 1 / ((k : ℝ) + 1) := by
    intro a k
    set η : ℝ := 1 / (2 * ((k : ℝ) + 1))
    have hη : 0 < η := by positivity
    have hη2 : 1 / ((k : ℝ) + 1) = 2 * η := by simp only [η]; field_simp
    obtain ⟨v, hv, hvE⟩ := exists_test_trialEnergy_lt a hUt e hη
    set M := dirichletEnergy a U e
    have hM : 0 ≤ M := dirichletEnergy_nonneg a U e
    set s : ℝ := η / (2 * (M + η + 1))
    have hs : 0 < s := by positivity
    have hsM : s * (M + η) ≤ η / 2 := by
      simp only [s]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set K : ℝ := (1 + s⁻¹) * ((1 / 2) * Λ * (volume.real U)⁻¹)
    have hK : 0 ≤ K := by
      have : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr hV.le
      positivity
    obtain ⟨j, hj⟩ := hdense v hv (η / 2 / (K + 1)) (by positivity)
    refine ⟨j, ?_⟩
    have hle := trialEnergy_le_of_sub a hUt e (hv.memLp_gradient _) ((ht j).memLp_gradient _) hs
    have hKj : K * ∫ x in U, euclideanSq (gradient (t j) x - gradient v x) < η / 2 := by
      have hnn : 0 ≤ ∫ x in U, euclideanSq (gradient (t j) x - gradient v x) :=
        integral_nonneg fun x => euclideanSq_nonneg _
      calc K * ∫ x in U, euclideanSq (gradient (t j) x - gradient v x)
          ≤ (K + 1) * ∫ x in U, euclideanSq (gradient (t j) x - gradient v x) := by nlinarith
        _ < (K + 1) * (η / 2 / (K + 1)) := mul_lt_mul_of_pos_left hj (by positivity)
        _ = η / 2 := by field_simp
    have hexp : (1 + s⁻¹) * ((1 / 2) * Λ * ((volume.real U)⁻¹ *
        ∫ x in U, euclideanSq (gradient (t j) x - gradient v x))) =
        K * ∫ x in U, euclideanSq (gradient (t j) x - gradient v x) := by
      simp only [K]; ring
    rw [hexp] at hle
    have h1 : (1 + s) * trialEnergy a U e (gradient v) ≤ (1 + s) * (M + η) :=
      mul_le_mul_of_nonneg_left hvE.le (by positivity)
    rw [hη2]
    nlinarith
  classical
  set N : ℕ → CoefficientField d Λ → ℕ := fun k a => Nat.find (hex a k)
  have hEm : ∀ j, Measurable fun a : CoefficientField d Λ => trialEnergy a U e (gradient (t j)) := by
    intro j
    have hfun : (fun a : CoefficientField d Λ => trialEnergy a U e (gradient (t j))) =
        fun a => lpTrialEnergy a U e (((ht j).memLp_gradient (volume.restrict U)).toLp
          (gradient (t j))) := by
      funext a
      rw [lpTrialEnergy_toLp]
      rfl
    rw [hfun]
    exact measurable_lpTrialEnergy U e _
  have hμm := measurable_dirichletEnergy (Λ := Λ) hUt hΛ e
  have hPm : ∀ k j, MeasurableSet {a : CoefficientField d Λ |
      trialEnergy a U e (gradient (t j)) < dirichletEnergy a U e + 1 / ((k : ℝ) + 1)} :=
    fun k j => measurableSet_lt (hEm j) (hμm.add_const _)
  have hNm : ∀ k, Measurable (N k) := by
    intro k
    refine measurable_to_countable' fun j => ?_
    have hset : N k ⁻¹' {j} = {a | trialEnergy a U e (gradient (t j)) <
        dirichletEnergy a U e + 1 / ((k : ℝ) + 1)} ∩
        ⋂ i ∈ Finset.range j, {a | ¬ (trialEnergy a U e (gradient (t i)) <
          dirichletEnergy a U e + 1 / ((k : ℝ) + 1))} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_range, Set.mem_ofPred_eq, N]
      rw [Nat.find_eq_iff]
    rw [hset]
    exact (hPm k j).inter (Finset.measurableSet_biInter _ fun i _ => (hPm k i).compl)
  set Φ : ℕ → CoefficientField d Λ → ℝ := fun k a => ∫ x in U, t (N k a) x ^ 2
  have hΦm : ∀ k, Measurable (Φ k) := fun k =>
    (measurable_from_nat (f := fun j => ∫ x in U, t j x ^ 2)).comp (hNm k)
  refine measurable_of_tendsto_metrizable hΦm (tendsto_pi_nhds.mpr fun a => ?_)
  -- convergence at a fixed coefficient field
  have hspec : ∀ k, trialEnergy a U e (gradient (t (N k a))) <
      dirichletEnergy a U e + 1 / ((k : ℝ) + 1) := fun k => Nat.find_spec (hex a k)
  have hgrad : ∀ k, ∫ x in U, euclideanSq (gradient (t (N k a)) x - g a x) ≤
      2 * volume.real U * (1 / ((k : ℝ) + 1)) := by
    intro k
    have hq := ((hmin a).quadraticResponse hUt (ht (N k a)).h01).1
    rw [setAverage_eq, smul_eq_mul] at hq
    have h1 := hspec k
    have h2 : (volume.real U)⁻¹ * ∫ x in U, euclideanSq (gradient (t (N k a)) x - g a x) ≤
        2 * (1 / ((k : ℝ) + 1)) := by linarith
    calc ∫ x in U, euclideanSq (gradient (t (N k a)) x - g a x)
        = volume.real U * ((volume.real U)⁻¹ *
          ∫ x in U, euclideanSq (gradient (t (N k a)) x - g a x)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
      _ ≤ volume.real U * (2 * (1 / ((k : ℝ) + 1))) := mul_le_mul_of_nonneg_left h2 hV.le
      _ = 2 * volume.real U * (1 / ((k : ℝ) + 1)) := by ring
  have hsq : ∀ k, ∫ x in U, (t (N k a) x - u a x) ^ 2 ≤
      testPoincareConstant d * R ^ 2 * (2 * volume.real U * (1 / ((k : ℝ) + 1))) := by
    intro k
    have hP := setIntegral_sq_le_of_H01 0 hR hUR ((ht (N k a)).h01.sub (hmin a).1)
    exact hP.trans (mul_le_mul_of_nonneg_left (hgrad k)
      (mul_nonneg (testPoincareConstant_nonneg d) (sq_nonneg R)))
  have hlim : Tendsto (fun k => ∫ x in U, (t (N k a) x - u a x) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) hsq ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul
      (testPoincareConstant d * R ^ 2 * (2 * volume.real U))
    rw [mul_zero] at this
    exact this.congr fun k => by ring
  exact tendsto_integral_sq_of_tendsto_integral_sq_sub (hmin a).1.1
    (fun k => (ht (N k a)).memLp_two _) hlim

theorem isBounded_triadicCube (m : ℕ) : Bornology.IsBounded (triadicCube d m) := by
  refine (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := (3 : ℝ) ^ m)).subset fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have := mem_triadicCube_iff.mp hx i
  rw [Real.norm_eq_abs]
  have h0 : (0 : ℝ) < 3 ^ m := by positivity
  linarith

/-- **The expectation of (1.35)** for a family of minimizers of `μ(□_{n+r}, p)`, `p ∈ B₁`. -/
theorem integral_minimizer_setAverage_sq_le [NeZero d] {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) (hΛ : 0 ≤ Λ) (n r : ℕ) {e : Vec d} (he : e ∈ originBall d 1)
    {u : CoefficientField d Λ → Vec d → ℝ} {g : CoefficientField d Λ → Vec d → Vec d}
    (hmin : ∀ a, IsDirichletMinimizer a (triadicCube d (n + r)) e (u a) (g a)) :
    Integrable (fun a => ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u a x ^ 2) P ∧
    ∫ a, ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * (⨍ x in triadicCube d (n + r), u a x ^ 2) ∂P ≤
      4 * testPoincareConstant d * omegaModulus P n +
        2 * testPoincareConstant d * ((3 : ℝ) ^ n / (3 : ℝ) ^ (n + r)) ^ 2 * (2 * Λ + 2) := by
  have := hP.1
  have hc := testPoincareConstant_nonneg d
  set N : ℝ := ((3 : ℝ) ^ r) ^ d with hN_def
  have hN : 0 < N := by positivity
  set K : ℝ := 2 * testPoincareConstant d * ((3 : ℝ) ^ n / (3 : ℝ) ^ (n + r)) ^ 2 *
    ((2 * Λ + 2) * euclideanSq e)
  have hQi : ∀ k, Integrable (fun a => dirichletEnergy a (partitionCube n r k) e) P := by
    intro k
    have h : Integrable (fun a => dirichletEnergy (translate (latticeShift (partitionCenter n r k)) a)
        (triadicCube d n) e) P :=
      (integrable_dirichletEnergy_triadicCube
        (P := Measure.map (translate (latticeShift (partitionCenter n r k))) P) hΛ n e).comp_measurable
        (measurable_translateCoefficient (latticeShift (partitionCenter n r k)))
    exact h.congr (Eventually.of_forall fun a => (dirichletEnergy_partitionCube a n r k e).symm)
  have hQE : ∀ k, ∫ a, dirichletEnergy a (partitionCube n r k) e ∂P =
      expectedDirichletEnergy P n e := by
    intro k
    simp_rw [dirichletEnergy_partitionCube]
    exact integral_comp_translate hP _ (measurable_dirichletEnergy_triadicCube hΛ n e)
  have hmi := integrable_dirichletEnergy_triadicCube (P := P) hΛ (n + r) e
  set G : CoefficientField d Λ → ℝ := fun a =>
    4 * testPoincareConstant d * (∑ k : Fin d → Fin (3 ^ r), (1 / N) *
      dirichletEnergy a (partitionCube n r k) e - dirichletEnergy a (triadicCube d (n + r)) e) + K
  have hsumi : Integrable (fun a => ∑ k : Fin d → Fin (3 ^ r), (1 / N) *
      dirichletEnergy a (partitionCube n r k) e) P :=
    integrable_finsetSum _ fun k _ => (hQi k).const_mul _
  have hGi : Integrable G P := ((hsumi.sub hmi).const_mul _).add (integrable_const K)
  have hle : ∀ a, ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u a x ^ 2 ≤ G a :=
    fun a => minimizer_setAverage_sq_le a n r e (hmin a)
  have hnn : ∀ a, 0 ≤ ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u a x ^ 2 :=
    fun a => mul_nonneg (sq_nonneg _) (setAverage_nonneg_of_nonneg fun x => sq_nonneg _)
  have hmeas : Measurable fun a =>
      ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u a x ^ 2 := by
    have hfun : (fun a => ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u a x ^ 2) =
        fun a => ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ((volume.real (triadicCube d (n + r)))⁻¹ *
          ∫ x in triadicCube d (n + r), u a x ^ 2) := by
      funext a
      rw [setAverage_eq, smul_eq_mul]
    rw [hfun]
    exact measurable_const.mul (measurable_const.mul (measurable_setIntegral_sq_minimizer
      (isBounded_triadicCube (n + r)) (volume_triadicCube_ne_zero d (n + r)) hΛ e hmin))
  have hint : Integrable (fun a =>
      ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * ⨍ x in triadicCube d (n + r), u a x ^ 2) P :=
    hGi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn a)]
      exact hle a)
  refine ⟨hint, ?_⟩
  have hGE : ∫ a, G a ∂P = 4 * testPoincareConstant d * (expectedDirichletEnergy P n e -
      expectedDirichletEnergy P (n + r) e) + K := by
    simp only [G]
    have i1 : Integrable (fun a => ∑ k : Fin d → Fin (3 ^ r), (1 / N) *
        dirichletEnergy a (partitionCube n r k) e - dirichletEnergy a (triadicCube d (n + r)) e) P :=
      hsumi.sub hmi
    rw [integral_add (i1.const_mul _) (integrable_const K), integral_const_mul,
      integral_sub hsumi hmi, integral_finsetSum _ fun k _ => (hQi k).const_mul _, integral_const,
      probReal_univ, one_smul]
    simp_rw [integral_const_mul, hQE]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_partitionIndex, ← hN_def]
    unfold expectedDirichletEnergy
    field_simp
  have hω := sub_le_omegaModulus hP hΛ n he
  have hLm := limitDirichletEnergy_le_expected P (n + r) e
  have hK : K ≤ 2 * testPoincareConstant d * ((3 : ℝ) ^ n / (3 : ℝ) ^ (n + r)) ^ 2 * (2 * Λ + 2) := by
    have he1 := euclideanSq_le_one_of_mem_originBall he
    have h0 : 0 ≤ 2 * testPoincareConstant d * ((3 : ℝ) ^ n / (3 : ℝ) ^ (n + r)) ^ 2 *
        (2 * Λ + 2) := by positivity
    simp only [K]
    nlinarith
  calc ∫ a, ((3 : ℝ) ^ (n + r))⁻¹ ^ 2 * (⨍ x in triadicCube d (n + r), u a x ^ 2) ∂P
      ≤ ∫ a, G a ∂P := integral_mono hint hGi hle
    _ ≤ _ := by
        rw [hGE]
        have : expectedDirichletEnergy P n e - expectedDirichletEnergy P (n + r) e ≤
            omegaModulus P n := by linarith
        nlinarith

theorem sq_div_three_pow_le (m : ℕ) :
    ((3 : ℝ) ^ ((m + 1) / 2) / (3 : ℝ) ^ ((m + 1) / 2 + m / 2)) ^ 2 ≤
      3 * (3 : ℝ) ^ (-(m : ℝ) / 4) := by
  have h3 : (0 : ℝ) < 3 ^ ((m + 1) / 2) := by positivity
  rw [pow_add, div_mul_cancel_left₀ h3.ne', inv_pow, ← pow_mul]
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  calc (3 : ℝ) ^ (-((m / 2 * 2 : ℕ) : ℝ)) ≤ (3 : ℝ) ^ ((1 : ℝ) + -(m : ℝ) / 4) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hm : (m : ℝ) ≤ ((m / 2 * 2 : ℕ) : ℝ) + 1 := by
          have : m ≤ m / 2 * 2 + 1 := by omega
          exact_mod_cast this
        have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
    _ = 3 * (3 : ℝ) ^ (-(m : ℝ) / 4) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]

/-- **Proposition 1.8**, (1.33): there is `C(d, Λ)` such that for every law satisfying
(0.10)–(0.11), every `m`, every `p ∈ B₁` and every choice of the minimizers
`v(·, □_m, p) = ℓ_p + u a`, `E[3^{-2m} ⨍_{□_m} |v(·, □_m, p) - ℓ_p|²] ≤ C 3^{-m/4} + C ω(⌈m/2⌉)`,
with `⌈m/2⌉ = (m + 1)/2`. -/
theorem proposition_1_8 [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ (m : ℕ) (p : Vec d),
      p ∈ originBall d 1 → ∀ (u : CoefficientField d Λ → Vec d → ℝ)
      (g : CoefficientField d Λ → Vec d → Vec d),
      (∀ a, IsDirichletMinimizer a (triadicCube d m) p (u a) (g a)) →
      Integrable (fun a => ((3 : ℝ) ^ m)⁻¹ ^ 2 * ⨍ x in triadicCube d m, u a x ^ 2) P ∧
      ∫ a, ((3 : ℝ) ^ m)⁻¹ ^ 2 * (⨍ x in triadicCube d m, u a x ^ 2) ∂P ≤
        C * (3 : ℝ) ^ (-(m : ℝ) / 4) + C * omegaModulus P ((m + 1) / 2) := by
  have hc := testPoincareConstant_nonneg d
  refine ⟨4 * testPoincareConstant d + 6 * testPoincareConstant d * (2 * |Λ| + 2), by positivity,
    fun P hP m p hp u g hmin => ?_⟩
  have := hP.1
  have hΛ : 0 ≤ Λ := by
    rcases isEmpty_or_nonempty (CoefficientField d Λ) with h | h
    · have h0 : P = 0 := Measure.eq_zero_of_isEmpty P
      have h1 := measure_univ (μ := P)
      rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
      exact absurd h1 zero_ne_one
    · obtain ⟨a⟩ := h
      exact zero_le_one.trans (one_le_of_coefficientField a)
  have hnr : (m + 1) / 2 + m / 2 = m := by omega
  have hmin' : ∀ a, IsDirichletMinimizer a (triadicCube d ((m + 1) / 2 + m / 2)) p (u a) (g a) := by
    rw [hnr]; exact hmin
  obtain ⟨hint, hbound⟩ := integral_minimizer_setAverage_sq_le hP hΛ ((m + 1) / 2) (m / 2) hp hmin'
  have hρ := sq_div_three_pow_le m
  rw [hnr] at hint hbound
  refine ⟨hint, hbound.trans ?_⟩
  rw [abs_of_nonneg hΛ]
  have hω := omegaModulus_nonneg hP hΛ ((m + 1) / 2)
  have h3 : 0 ≤ (3 : ℝ) ^ (-(m : ℝ) / 4) := by positivity
  have hρ' : ((3 : ℝ) ^ ((m + 1) / 2) / (3 : ℝ) ^ ((m + 1) / 2 + m / 2)) ^ 2 * (2 * Λ + 2) ≤
      3 * (3 : ℝ) ^ (-(m : ℝ) / 4) * (2 * Λ + 2) :=
    mul_le_mul_of_nonneg_right hρ (by positivity)
  rw [hnr] at hρ'
  have e1 : 0 ≤ 6 * testPoincareConstant d * (2 * Λ + 2) * omegaModulus P ((m + 1) / 2) := by
    positivity
  have e2 : 0 ≤ 4 * testPoincareConstant d * (3 : ℝ) ^ (-(m : ℝ) / 4) := by positivity
  have e3 := mul_le_mul_of_nonneg_left hρ' (by positivity : (0 : ℝ) ≤ 2 * testPoincareConstant d)
  nlinarith

end QSH
