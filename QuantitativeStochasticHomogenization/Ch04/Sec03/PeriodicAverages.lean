import QuantitativeStochasticHomogenization.Ch04.Sec03.PeriodizedGaussian
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses

/-!
# Gaussian averages of lattice periodic functions

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10 (in the book, Lemma 3.23).

The cells `latticeCell 1 n` partition `ℝ^d`, so integrals over `ℝ^d` unfold into sums over the
cells of the translates (`lintegral_eq_tsum_latticeCell`, `hasSum_integral_latticeCell`). For a
function `m` that is `ℤ^d`-periodic up to null sets and integrable on one cell, the average
`∫ Φ_{z,r} m` is the cell integral of `m` against the periodized mask; since the periodized mask is
within `(1 + thetaError r²)^d - 1` of `1`, the average is within that multiple of `∫_cell |m|` of
the cell mean `∫_cell m` (`norm_integral_heatKernel_smul_sub_cell_le`).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Unfolding over the lattice cells -/

theorem pairwise_disjoint_latticeCell_one :
    Pairwise (Disjoint on fun n : LatticeIndex d => latticeCell 1 n) := by
  intro n m hnm
  refine Set.disjoint_left.mpr fun x hn hm => hnm ?_
  rw [mem_latticeCell_iff one_pos] at hn hm
  rw [← hn, ← hm]

theorem iUnion_latticeCell_one : ⋃ n : LatticeIndex d, latticeCell 1 n = univ :=
  eq_univ_of_forall fun x =>
    mem_iUnion.mpr ⟨cellIndex 1 x, (mem_latticeCell_iff one_pos).mpr rfl⟩

theorem preimage_add_latticeCell_one (n : LatticeIndex d) :
    (fun x => x + latticeShift n) ⁻¹' latticeCell 1 n = latticeCell 1 (0 : LatticeIndex d) := by
  ext x
  simp only [latticeCell, mem_preimage, Set.mem_ofPred_eq, Pi.add_apply, latticeShift, one_mul,
    Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem setLIntegral_latticeCell_one (f : Vec d → ℝ≥0∞) (n : LatticeIndex d) :
    ∫⁻ x in latticeCell 1 n, f x =
      ∫⁻ x in latticeCell 1 (0 : LatticeIndex d), f (x + latticeShift n) := by
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) (latticeShift n)
  rw [← preimage_add_latticeCell_one n]
  exact (hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _) f _).symm

theorem setIntegral_latticeCell_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) (n : LatticeIndex d) :
    ∫ x in latticeCell 1 n, f x =
      ∫ x in latticeCell 1 (0 : LatticeIndex d), f (x + latticeShift n) := by
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) (latticeShift n)
  rw [← preimage_add_latticeCell_one n]
  exact (hmp.setIntegral_preimage_emb (measurableEmbedding_addRight _) f _).symm

/-- **Unfolding a lower integral over the lattice cells.** -/
theorem lintegral_eq_tsum_latticeCell (f : Vec d → ℝ≥0∞) :
    ∫⁻ x, f x = ∑' n : LatticeIndex d,
      ∫⁻ x in latticeCell 1 (0 : LatticeIndex d), f (x + latticeShift n) := by
  rw [← setLIntegral_univ, ← iUnion_latticeCell_one,
    lintegral_iUnion (fun n => measurableSet_latticeCell 1 n) pairwise_disjoint_latticeCell_one]
  exact tsum_congr fun n => setLIntegral_latticeCell_one f n

/-- **Unfolding an integral over the lattice cells.** -/
theorem hasSum_integral_latticeCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec d → E} (hf : Integrable f) :
    HasSum (fun n : LatticeIndex d =>
      ∫ x in latticeCell 1 (0 : LatticeIndex d), f (x + latticeShift n)) (∫ x, f x) := by
  have h := hasSum_integral_iUnion (fun n => measurableSet_latticeCell 1 n)
    pairwise_disjoint_latticeCell_one (f := f) (μ := volume)
    (by rw [iUnion_latticeCell_one]; exact hf.integrableOn)
  rw [iUnion_latticeCell_one, Measure.restrict_univ] at h
  convert h using 1
  funext n
  exact (setIntegral_latticeCell_one f n).symm

/-! ## The periodized mask -/

/-- The periodized mask `∑_{n ∈ ℤ^d} Φ_{z,r}(x + n)`. -/
def periodizedHeatKernel (z : Vec d) (r : ℝ) (x : Vec d) : ℝ :=
  ∑' n : LatticeIndex d, heatKernel z r (x + latticeShift n)

theorem measurable_heatKernel_fixed (z : Vec d) (r : ℝ) : Measurable (heatKernel z r) := by
  unfold heatKernel euclideanHeatKernel euclideanSq dot
  fun_prop

theorem ofReal_periodizedHeatKernel (z : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    ENNReal.ofReal (periodizedHeatKernel z r x) =
      ∑' n : LatticeIndex d, ENNReal.ofReal (heatKernel z r (x + latticeShift n)) :=
  ENNReal.ofReal_tsum_of_nonneg (fun _ => heatKernel_nonneg _ _ _)
    (hasSum_heatKernel_add_latticeShift z x hr).summable

theorem measurable_periodizedHeatKernel (z : Vec d) (r : ℝ) :
    Measurable (periodizedHeatKernel z r) := by
  unfold periodizedHeatKernel
  exact Measurable.tsum fun n => (measurable_heatKernel_fixed z r).comp (measurable_add_const _)

theorem abs_periodizedHeatKernel_sub_one_le (z : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    |periodizedHeatKernel z r x - 1| ≤ (1 + thetaError (r ^ 2)) ^ d - 1 :=
  abs_tsum_heatKernel_add_latticeShift_sub_one_le z x hr

theorem periodizedHeatKernel_le (z : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    periodizedHeatKernel z r x ≤ (1 + thetaError (r ^ 2)) ^ d := by
  have h := abs_periodizedHeatKernel_sub_one_le z hr x
  rw [abs_le] at h
  linarith [h.2]

/-! ## Gaussian averages of periodic functions -/

section Periodic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The cell integral of the periodized mask against `|m|` as a sum over the cells. -/
theorem tsum_setLIntegral_heatKernel_mul {m : Vec d → E} (hm : AEStronglyMeasurable m volume)
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∑' n : LatticeIndex d, ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
        ENNReal.ofReal (heatKernel z r (x + latticeShift n)) * ‖m x‖ₑ =
      ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
        ENNReal.ofReal (periodizedHeatKernel z r x) * ‖m x‖ₑ := by
  have hmeas : ∀ n : LatticeIndex d, AEMeasurable (fun x =>
      ENNReal.ofReal (heatKernel z r (x + latticeShift n)) * ‖m x‖ₑ)
      (volume.restrict (latticeCell 1 (0 : LatticeIndex d))) := fun n =>
    (((measurable_heatKernel_fixed z r).comp (measurable_add_const _)).ennreal_ofReal.aemeasurable.mul
      hm.enorm).restrict
  rw [← lintegral_tsum hmeas]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.tsum_mul_right, ofReal_periodizedHeatKernel z hr x]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem setLIntegral_periodized_lt_top {m : Vec d → E}
    (hcell : IntegrableOn m (latticeCell 1 (0 : LatticeIndex d))) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
      ENNReal.ofReal (periodizedHeatKernel z r x) * ‖m x‖ₑ < ⊤ := by
  calc ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
        ENNReal.ofReal (periodizedHeatKernel z r x) * ‖m x‖ₑ
      ≤ ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
        ENNReal.ofReal ((1 + thetaError (r ^ 2)) ^ d) * ‖m x‖ₑ :=
        lintegral_mono fun x =>
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (periodizedHeatKernel_le z hr x)) _
    _ = ENNReal.ofReal ((1 + thetaError (r ^ 2)) ^ d) *
        ∫⁻ x in latticeCell 1 (0 : LatticeIndex d), ‖m x‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcell.2

omit [CompleteSpace E] in
theorem lintegral_enorm_heatKernel_smul_periodic {m : Vec d → E}
    (hm : AEStronglyMeasurable m volume)
    (hper : ∀ n : LatticeIndex d, ∀ᵐ x, m (x + latticeShift n) = m x) (z : Vec d) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ x, ‖heatKernel z r x • m x‖ₑ =
      ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
        ENNReal.ofReal (periodizedHeatKernel z r x) * ‖m x‖ₑ := by
  rw [lintegral_eq_tsum_latticeCell, ← tsum_setLIntegral_heatKernel_mul hm z hr]
  refine tsum_congr fun n => lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hper n] with x hx
  rw [hx, enorm_smul, Real.enorm_of_nonneg (heatKernel_nonneg _ _ _)]

theorem integrable_heatKernel_smul_periodic {m : Vec d → E} (hm : AEStronglyMeasurable m volume)
    (hcell : IntegrableOn m (latticeCell 1 (0 : LatticeIndex d)))
    (hper : ∀ n : LatticeIndex d, ∀ᵐ x, m (x + latticeShift n) = m x) (z : Vec d) {r : ℝ}
    (hr : 0 < r) :
    Integrable (fun x => heatKernel z r x • m x) := by
  refine ⟨(measurable_heatKernel_fixed z r).aestronglyMeasurable.smul hm, ?_⟩
  change ∫⁻ x, ‖heatKernel z r x • m x‖ₑ < ⊤
  rw [lintegral_enorm_heatKernel_smul_periodic hm hper z hr]
  exact setLIntegral_periodized_lt_top hcell z hr

/-- **The average of a periodic function** is the cell integral against the periodized mask. -/
theorem integral_heatKernel_smul_periodic {m : Vec d → E} (hm : AEStronglyMeasurable m volume)
    (hcell : IntegrableOn m (latticeCell 1 (0 : LatticeIndex d)))
    (hper : ∀ n : LatticeIndex d, ∀ᵐ x, m (x + latticeShift n) = m x) (z : Vec d) {r : ℝ}
    (hr : 0 < r) :
    ∫ x, heatKernel z r x • m x =
      ∫ x in latticeCell 1 (0 : LatticeIndex d), periodizedHeatKernel z r x • m x := by
  have h1 := hasSum_integral_latticeCell (integrable_heatKernel_smul_periodic hm hcell hper z hr)
  have hterm : ∀ n : LatticeIndex d,
      ∫ x in latticeCell 1 (0 : LatticeIndex d),
        heatKernel z r (x + latticeShift n) • m (x + latticeShift n) =
      ∫ x in latticeCell 1 (0 : LatticeIndex d), heatKernel z r (x + latticeShift n) • m x := by
    intro n
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hper n] with x hx
    rw [hx]
  rw [← h1.tsum_eq, tsum_congr hterm]
  have hfin : ∑' n : LatticeIndex d, ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
      ‖heatKernel z r (x + latticeShift n) • m x‖ₑ ≠ ⊤ := by
    have he : ∀ n : LatticeIndex d, ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
        ‖heatKernel z r (x + latticeShift n) • m x‖ₑ =
        ∫⁻ x in latticeCell 1 (0 : LatticeIndex d),
          ENNReal.ofReal (heatKernel z r (x + latticeShift n)) * ‖m x‖ₑ := fun n =>
      lintegral_congr fun x => by
        rw [enorm_smul, Real.enorm_of_nonneg (heatKernel_nonneg _ _ _)]
    rw [tsum_congr he, tsum_setLIntegral_heatKernel_mul hm z hr]
    exact (setLIntegral_periodized_lt_top hcell z hr).ne
  have hmeas : ∀ n : LatticeIndex d, AEStronglyMeasurable (fun x =>
      heatKernel z r (x + latticeShift n) • m x)
      (volume.restrict (latticeCell 1 (0 : LatticeIndex d))) := fun n =>
    (((measurable_heatKernel_fixed z r).comp (measurable_add_const _)).aestronglyMeasurable.smul
      hm).restrict
  rw [← integral_tsum hmeas hfin]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (hasSum_heatKernel_add_latticeShift z x hr).summable.tsum_smul_const (m x)

/-- **Gaussian averages of periodic functions**: for `m` periodic up to null sets and integrable
on the cell, `‖∫ Φ_{z,r} m - ∫_cell m‖ ≤ ((1 + thetaError r²)^d - 1) ∫_cell |m|`. -/
theorem norm_integral_heatKernel_smul_sub_cell_le {m : Vec d → E}
    (hm : AEStronglyMeasurable m volume)
    (hcell : IntegrableOn m (latticeCell 1 (0 : LatticeIndex d)))
    (hper : ∀ n : LatticeIndex d, ∀ᵐ x, m (x + latticeShift n) = m x) (z : Vec d) {r : ℝ}
    (hr : 0 < r) :
    ‖(∫ x, heatKernel z r x • m x) - ∫ x in latticeCell 1 (0 : LatticeIndex d), m x‖ ≤
      ((1 + thetaError (r ^ 2)) ^ d - 1) * ∫ x in latticeCell 1 (0 : LatticeIndex d), ‖m x‖ := by
  rw [integral_heatKernel_smul_periodic hm hcell hper z hr]
  have hb : ∀ x, ‖(periodizedHeatKernel z r x - 1) • m x‖ ≤
      ((1 + thetaError (r ^ 2)) ^ d - 1) * ‖m x‖ := fun x => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_periodizedHeatKernel_sub_one_le z hr x) (norm_nonneg _)
  have hI1 : IntegrableOn (fun x => (periodizedHeatKernel z r x - 1) • m x)
      (latticeCell 1 (0 : LatticeIndex d)) :=
    Integrable.mono' (hcell.norm.const_mul _)
      (((measurable_periodizedHeatKernel z r).sub measurable_const).aestronglyMeasurable.smul
        hm.restrict) (Eventually.of_forall hb)
  have heq : ∫ x in latticeCell 1 (0 : LatticeIndex d), periodizedHeatKernel z r x • m x =
      (∫ x in latticeCell 1 (0 : LatticeIndex d), (periodizedHeatKernel z r x - 1) • m x) +
        ∫ x in latticeCell 1 (0 : LatticeIndex d), m x := by
    rw [← integral_add hI1 hcell]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_smul, one_smul, sub_add_cancel]
  rw [heq, add_sub_cancel_right, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hcell.norm.const_mul _) (Eventually.of_forall hb)

end Periodic

end QSH
