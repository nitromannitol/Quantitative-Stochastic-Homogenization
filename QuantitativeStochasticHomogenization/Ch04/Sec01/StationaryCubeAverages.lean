import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedDensities
import QuantitativeStochasticHomogenization.Ch01.Sec03.SubadditiveLimit

/-!
# Cube averages of stationary densities

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.3: the expected average of a stationary density over a triadic cube is its mean over
the unit cell.

* `setIntegral_triadicCube_eq_of_periodic`: a lattice periodic function `g` satisfies
  `∫_{□_n} g = 3^{nd} ∫_{cell} g`, since `□_{n+1}` is, up to a null set, the union of `3^d`
  lattice translates of `□_n`;
* `setIntegral_cell_expectation_eq_of_tendsto`: if the Gaussian averages `∫ Φ_{0,n+1} H(a, ·)` of a
  stationary density converge almost surely to `c`, then the cell mean of `E[H]` is `c`;
* `integral_setAverage_triadicCube_eq`: `E[⨍_{□_n} H] = ∫_{cell} E[H]`.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Periodic functions on triadic cubes -/

theorem triadicCube_zero_ae_eq_latticeCell :
    triadicCube d 0 =ᵐ[volume] latticeCell 1 (0 : LatticeIndex d) := by
  have hsub : triadicCube d 0 ⊆ latticeCell 1 (0 : LatticeIndex d) := by
    intro x hx
    have hx' := mem_triadicCube_iff.mp hx
    intro i
    have h := abs_lt.mp (hx' i)
    simp only [pow_zero] at h
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_sub, zero_add]
    constructor <;> linarith [h.1, h.2]
  have hdiff : latticeCell 1 (0 : LatticeIndex d) \ triadicCube d 0 ⊆
      ⋃ i : Fin d, {x : Vec d | x i = -(1 / 2)} := by
    intro x ⟨hx, hxQ⟩
    by_contra hbad
    simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hbad
    apply hxQ
    refine mem_triadicCube_iff.mpr fun i => ?_
    have h := hx i
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_sub, zero_add] at h
    rw [pow_zero, abs_lt]
    have hne := hbad i
    constructor
    · rcases h.1.lt_or_eq with h1 | h1
      · linarith
      · exact absurd h1.symm (by simpa using hne)
    · linarith [h.2]
  refine Filter.EventuallyLE.antisymm (Eventually.of_forall fun x hx => hsub hx) ?_
  refine ae_le_set.mpr (measure_mono_null hdiff (measure_iUnion_null fun i => ?_))
  exact volume_coordinate_eq_null i _

theorem triadicCube_succ_ae_eq_iUnion (n : ℕ) :
    triadicCube d (n + 1) =ᵐ[volume] ⋃ k, triadicSubcube n k := by
  exact Filter.EventuallyLE.antisymm (ae_le_set.mpr (volume_triadicCube_diff n))
    (Eventually.of_forall fun x hx => (iUnion_subset fun k => triadicSubcube_subset n k) hx)

theorem setIntegral_triadicSubcube_eq {g : Vec d → ℝ}
    (hper : ∀ k : LatticeIndex d, ∀ᵐ x, g (x + latticeShift k) = g x) (n : ℕ)
    (k : Fin d → Fin 3) :
    ∫ x in triadicSubcube n k, g x = ∫ x in triadicCube d n, g x := by
  set s := latticeShift (subcubeOffset (d := d) n k) with hs
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) s
  have hpre : (fun x => x + s) ⁻¹' triadicSubcube n k = triadicCube d n := by
    ext x
    simp [triadicSubcube, hs]
  have h := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight s) g (triadicSubcube n k)
  rw [hpre] at h
  rw [← h]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hper (subcubeOffset n k)] with x hx
  exact hx

/-- **Periodic functions on triadic cubes**: `∫_{□_n} g = 3^{nd} ∫_{cell} g`. -/
theorem setIntegral_triadicCube_eq_of_periodic {g : Vec d → ℝ}
    (hper : ∀ k : LatticeIndex d, ∀ᵐ x, g (x + latticeShift k) = g x)
    (hint : ∀ n, IntegrableOn g (triadicCube d n)) (n : ℕ) :
    ∫ x in triadicCube d n, g x =
      ((3 : ℝ) ^ n) ^ d * ∫ x in latticeCell 1 (0 : LatticeIndex d), g x := by
  induction n with
  | zero =>
    rw [setIntegral_congr_set triadicCube_zero_ae_eq_latticeCell]
    simp
  | succ n ih =>
    have hU := triadicCube_succ_ae_eq_iUnion (d := d) n
    rw [setIntegral_congr_set hU]
    have hint' : IntegrableOn g (⋃ k, triadicSubcube n k) :=
      (hint (n + 1)).mono_set (iUnion_subset fun k => triadicSubcube_subset n k)
    rw [integral_iUnion (fun k => (isOpen_triadicSubcube n k).measurableSet)
      (pairwise_disjoint_triadicSubcube n) hint', tsum_fintype]
    simp only [setIntegral_triadicSubcube_eq hper n]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, ih]
    push_cast
    ring

/-! ## Cell means from Gaussian limits -/

variable {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]

/-- **The cell mean of a stationary density is the almost sure limit of its Gaussian
averages.** -/
theorem setIntegral_cell_expectation_eq_of_tendsto
    (hinv : ∀ n : LatticeIndex d, Measure.map (translate (latticeShift n)) P = P)
    {H : CoefficientField d Λ → Vec d → ℝ}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    (hper : ∀ n : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x,
      H a (x + latticeShift n) = H (translate (latticeShift n) a) x)
    {Y : CoefficientField d Λ → ℝ} (hY : Integrable Y P)
    (henv : ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      Integrable (fun x => heatKernel 0 r x * ‖H a x‖) ∧ ∫ x, heatKernel 0 r x * ‖H a x‖ ≤ Y a)
    {c : ℝ} (hlim : ∀ᵐ a ∂P, Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x)
      atTop (𝓝 c)) :
    ∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P = c := by
  have henvr : ∀ r : ℝ, 1 ≤ r → ∀ᵐ a ∂P,
      Integrable (fun x => heatKernel 0 r x * ‖H a x‖) ∧
        ∫ x, heatKernel 0 r x * ‖H a x‖ ≤ Y a := fun r hr => by
    filter_upwards [henv] with a ha
    exact ha r hr
  have hint : ∀ r : ℝ, 1 ≤ r → Integrable
      (fun p : CoefficientField d Λ × Vec d => heatKernel 0 r p.2 • H p.1 p.2) (P.prod volume) :=
    fun r hr => integrable_prod_heatKernel_smul hH hY (henvr r hr)
  obtain ⟨hcell, -⟩ := integrableOn_expectation_cell hH hY (henvr 1 le_rfl)
  have hmH : AEStronglyMeasurable (fun x => ∫ a, H a x ∂P) volume :=
    (hH.integral_prod_left' (μ := P)).aestronglyMeasurable
  have hper' := ae_expectation_add_latticeShift hinv hH hper
  have key : ∀ r : ℝ, 1 ≤ r →
      ‖(∫ a, (∫ x, heatKernel 0 r x • H a x) ∂P) -
          ∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P‖ ≤
        ((1 + thetaError (r ^ 2)) ^ d - 1) *
          ∫ x in latticeCell 1 (0 : LatticeIndex d), ‖∫ a, H a x ∂P‖ := fun r hr => by
    rw [integral_heatKernel_smul_expectation (hint r hr)]
    exact norm_integral_heatKernel_smul_sub_cell_le hmH hcell hper' 0 (zero_lt_one.trans_le hr)
  have hT1 := tendsto_expectation_average hH hY henv hlim
  have hT2 : Tendsto (fun n : ℕ => ∫ a, (∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x) ∂P) atTop
      (𝓝 (∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim0 := (tendsto_periodizationError (d := d)).mul_const
      (∫ x in latticeCell 1 (0 : LatticeIndex d), ‖∫ a, H a x ∂P‖)
    rw [zero_mul] at hlim0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun n => norm_nonneg _) fun n => key _ ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact tendsto_nhds_unique hT2 hT1

/-! ## Expected cube averages -/

/-- On `□_n` the mask `Φ_{0,3^n}` is at least `(4π 9^n)^{-d/2} e^{-d/16}`. -/
theorem heatKernel_ge_of_mem_triadicCube (n : ℕ) {x : Vec d} (hx : x ∈ triadicCube d n) :
    (4 * Real.pi * ((3 : ℝ) ^ n) ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) / 16) ≤
      heatKernel 0 ((3 : ℝ) ^ n) x := by
  unfold heatKernel euclideanHeatKernel
  have hR : 0 < (3 : ℝ) ^ n := by positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hx' := mem_triadicCube_iff.mp hx
  have hsq : euclideanSq (x - 0) ≤ d * (((3 : ℝ) ^ n) ^ 2 / 4) := by
    rw [sub_zero]
    unfold euclideanSq dot
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ((3 : ℝ) ^ n) ^ 2 / 4 :=
          Finset.sum_le_sum fun i _ => by
            have h := hx' i
            have h2 : x i ^ 2 ≤ ((3 : ℝ) ^ n / 2) ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
            nlinarith
      _ = d * (((3 : ℝ) ^ n) ^ 2 / 4) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

omit [IsProbabilityMeasure P] in
theorem integrable_prod_restrict_triadicCube {H : CoefficientField d Λ → Vec d → ℝ}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    {Y : CoefficientField d Λ → ℝ} (hY : Integrable Y P)
    (henv : ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      Integrable (fun x => heatKernel 0 r x * ‖H a x‖) ∧ ∫ x, heatKernel 0 r x * ‖H a x‖ ≤ Y a)
    (n : ℕ) :
    Integrable (fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
      (P.prod (volume.restrict (triadicCube d n))) := by
  set R : ℝ := (3 : ℝ) ^ n with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  set c : ℝ := (4 * Real.pi * R ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) / 16) with hc
  have hc0 : 0 < c := by positivity
  have hpt : ∀ a, ∀ x ∈ triadicCube d n, ‖H a x‖ ≤ c⁻¹ * (heatKernel 0 R x * ‖H a x‖) := by
    intro a x hx
    have h := heatKernel_ge_of_mem_triadicCube n hx
    have h1 : 1 ≤ c⁻¹ * heatKernel 0 R x := by
      rw [one_le_inv_mul₀ hc0]
      exact h
    calc ‖H a x‖ = 1 * ‖H a x‖ := (one_mul _).symm
      _ ≤ (c⁻¹ * heatKernel 0 R x) * ‖H a x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = c⁻¹ * (heatKernel 0 R x * ‖H a x‖) := mul_assoc _ _ _
  have hHa : ∀ᵐ a ∂P, Integrable (H a) (volume.restrict (triadicCube d n)) := by
    filter_upwards [henv] with a ha
    obtain ⟨hi, -⟩ := ha R hR1
    refine Integrable.mono' ((hi.const_mul c⁻¹).integrableOn (s := triadicCube d n))
      (hH.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    exact (ae_restrict_iff' (isOpen_triadicCube n).measurableSet).mpr
      (Eventually.of_forall fun x hx => hpt a x hx)
  rw [integrable_prod_iff hH.aestronglyMeasurable]
  refine ⟨hHa, ?_⟩
  refine Integrable.mono' (hY.const_mul c⁻¹) hH.norm.integral_prod_right'.aestronglyMeasurable ?_
  filter_upwards [henv, hHa] with a ha hHa'
  obtain ⟨hi, hle⟩ := ha R hR1
  rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  calc ∫ x in triadicCube d n, ‖H a x‖
      ≤ ∫ x in triadicCube d n, c⁻¹ * (heatKernel 0 R x * ‖H a x‖) :=
        setIntegral_mono_on hHa'.norm ((hi.const_mul c⁻¹).integrableOn)
          (isOpen_triadicCube n).measurableSet (fun x hx => hpt a x hx)
    _ ≤ ∫ x, c⁻¹ * (heatKernel 0 R x * ‖H a x‖) :=
        setIntegral_le_integral (hi.const_mul c⁻¹)
          (Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr hc0.le)
            (mul_nonneg (heatKernel_nonneg _ _ _) (norm_nonneg _)))
    _ = c⁻¹ * ∫ x, heatKernel 0 R x * ‖H a x‖ := integral_const_mul _ _
    _ ≤ c⁻¹ * Y a := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hc0.le)

/-- **Expected cube averages of stationary densities**: `E[∫_{□_n} H] = 3^{nd} ∫_cell E[H]`. -/
theorem integral_setIntegral_triadicCube_eq
    (hinv : ∀ n : LatticeIndex d, Measure.map (translate (latticeShift n)) P = P)
    {H : CoefficientField d Λ → Vec d → ℝ}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    (hper : ∀ n : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x,
      H a (x + latticeShift n) = H (translate (latticeShift n) a) x)
    {Y : CoefficientField d Λ → ℝ} (hY : Integrable Y P)
    (henv : ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      Integrable (fun x => heatKernel 0 r x * ‖H a x‖) ∧ ∫ x, heatKernel 0 r x * ‖H a x‖ ≤ Y a)
    (n : ℕ) :
    Integrable (fun a => ∫ x in triadicCube d n, H a x) P ∧
      ∫ a, (∫ x in triadicCube d n, H a x) ∂P =
        ((3 : ℝ) ^ n) ^ d * ∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P := by
  have hint := fun m => integrable_prod_restrict_triadicCube hH hY henv m
  refine ⟨(hint n).integral_prod_left, ?_⟩
  rw [integral_integral_swap (hint n)]
  refine setIntegral_triadicCube_eq_of_periodic (ae_expectation_add_latticeShift hinv hH hper)
    (fun m => (hint m).integral_prod_right) n

end QSH
