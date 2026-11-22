import QuantitativeStochasticHomogenization.Ch04.Sec03.CellMeanTools
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma

/-!
# Expectations of Gaussian averages of stationary densities

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10 (in the book, Lemma 3.23 and
(3.92)–(3.93)).

Let `H(a, x)` be a jointly measurable density which is stationary under the lattice translations
(`H(a, x + n) = H(T_n a, x)`), for a law invariant under these translations, and whose Gaussian
averages `∫ Φ_{z,r} |H(a, ·)|` are dominated by integrable envelopes `Y z`. Then:

* the expectation `∫ Φ_{z,r} E[H(·, x)] dx` of the average is the average of the expected density
  (Fubini), which is lattice periodic (`ae_expectation_add_latticeShift`) and integrable on the
  unit cell, with `∫_cell |E H| ≤ (4π)^{d/2} e^{d/16} E[Y 0]` (`integrableOn_expectation_cell`);
* if the averages at the origin converge almost surely to a constant `c` as `r → ∞`, then the
  cell mean of `E H` is `c`, and the expectation of every average is within the periodization error
  `(1 + thetaError r²)^d - 1` times `(4π)^{d/2} e^{d/16} E[Y 0]` of `c`
  (`norm_expectation_average_sub_le`).
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

section Generic

variable {P : Measure (CoefficientField d Λ)} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [IsProbabilityMeasure P] in
theorem integrable_prod_heatKernel_smul {H : CoefficientField d Λ → Vec d → E}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    {Y : CoefficientField d Λ → ℝ} (hY : Integrable Y P) {z : Vec d} {r : ℝ}
    (henv : ∀ᵐ a ∂P, Integrable (fun x => heatKernel z r x * ‖H a x‖) ∧
      ∫ x, heatKernel z r x * ‖H a x‖ ≤ Y a) :
    Integrable (fun p : CoefficientField d Λ × Vec d => heatKernel z r p.2 • H p.1 p.2)
      (P.prod volume) := by
  have hm : StronglyMeasurable fun p : CoefficientField d Λ × Vec d =>
      heatKernel z r p.2 • H p.1 p.2 :=
    ((measurable_heatKernel_fixed z r).comp measurable_snd).stronglyMeasurable.smul hH
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  have hnorm : ∀ a x, ‖heatKernel z r x • H a x‖ = heatKernel z r x * ‖H a x‖ := fun a x => by
    rw [norm_smul, Real.norm_of_nonneg (heatKernel_nonneg _ _ _)]
  constructor
  · filter_upwards [henv] with a ha
    refine Integrable.mono' ha.1 ((measurable_heatKernel_fixed z r).stronglyMeasurable.smul
      (hH.comp_measurable (measurable_const.prodMk measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun x => (hnorm a x).le)
  · refine Integrable.mono' hY hm.norm.integral_prod_right'.aestronglyMeasurable ?_
    filter_upwards [henv] with a ha
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    simp only [hnorm]
    exact ha.2

theorem integral_heatKernel_smul_expectation {H : CoefficientField d Λ → Vec d → E} {z : Vec d}
    {r : ℝ} (hint : Integrable (fun p : CoefficientField d Λ × Vec d => heatKernel z r p.2 • H p.1 p.2)
      (P.prod volume)) :
    ∫ a, (∫ x, heatKernel z r x • H a x) ∂P = ∫ x, heatKernel z r x • ∫ a, H a x ∂P := by
  rw [integral_integral_swap (f := fun a x => heatKernel z r x • H a x) hint]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_smul _ _)

/-- **The expected density of a stationary density is lattice periodic.** -/
theorem ae_expectation_add_latticeShift
    (hinv : ∀ n : LatticeIndex d, Measure.map (translate (latticeShift n)) P = P)
    {H : CoefficientField d Λ → Vec d → E}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    (hper : ∀ n : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x,
      H a (x + latticeShift n) = H (translate (latticeShift n) a) x) (n : LatticeIndex d) :
    ∀ᵐ x, (∫ a, H a (x + latticeShift n) ∂P) = ∫ a, H a x ∂P := by
  have hT := measurable_translateCoefficient (d := d) (K := Λ) (latticeShift n)
  have h1 : StronglyMeasurable fun p : CoefficientField d Λ × Vec d =>
      H p.1 (p.2 + latticeShift n) :=
    hH.comp_measurable (measurable_fst.prodMk (measurable_snd.add_const _))
  have h2 : StronglyMeasurable fun p : CoefficientField d Λ × Vec d =>
      H (translate (latticeShift n) p.1) p.2 :=
    hH.comp_measurable ((hT.comp measurable_fst).prodMk measurable_snd)
  have hset : MeasurableSet {p : CoefficientField d Λ × Vec d |
      H p.1 (p.2 + latticeShift n) = H (translate (latticeShift n) p.1) p.2} :=
    h1.measurableSet_eq_fun h2
  have hswap := (Measure.ae_ae_comm hset).mp (hper n)
  filter_upwards [hswap] with x hx
  rw [integral_congr_ae hx]
  have hx' : StronglyMeasurable fun b : CoefficientField d Λ => H b x :=
    hH.comp_measurable (measurable_id.prodMk measurable_const)
  rw [← integral_map hT.aemeasurable hx'.aestronglyMeasurable, hinv n]

/-- **The expected density is integrable on the unit cell**, with
`∫_cell |E H| ≤ (4π)^{d/2} e^{d/16} E[Y]` when `∫ Φ_{0,1} |H(a, ·)| ≤ Y(a)`. -/
theorem integrableOn_expectation_cell {H : CoefficientField d Λ → Vec d → E}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    {Y : CoefficientField d Λ → ℝ} (hY : Integrable Y P)
    (henv : ∀ᵐ a ∂P, Integrable (fun x => heatKernel 0 1 x * ‖H a x‖) ∧
      ∫ x, heatKernel 0 1 x * ‖H a x‖ ≤ Y a) :
    IntegrableOn (fun x => ∫ a, H a x ∂P) (latticeCell 1 (0 : LatticeIndex d)) ∧
      ∫ x in latticeCell 1 (0 : LatticeIndex d), ‖∫ a, H a x ∂P‖ ≤
        (cellHeatLower d)⁻¹ * ∫ a, Y a ∂P := by
  have hN : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => ‖H p.1 p.2‖ := hH.norm
  have henvN : ∀ᵐ a ∂P, Integrable (fun x => heatKernel 0 1 x * ‖‖H a x‖‖) ∧
      ∫ x, heatKernel 0 1 x * ‖‖H a x‖‖ ≤ Y a := by
    filter_upwards [henv] with a ha
    simpa only [norm_norm] using ha
  have hint := integrable_prod_heatKernel_smul (H := fun a x => ‖H a x‖) hN hY henvN
  set g : Vec d → ℝ := fun x => ∫ a, heatKernel 0 1 x • ‖H a x‖ ∂P with hgdef
  have hg : Integrable g := hint.integral_prod_right
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    integral_nonneg fun a => smul_nonneg (heatKernel_nonneg _ _ _) (norm_nonneg _)
  have hgE : ∫ x, g x ≤ ∫ a, Y a ∂P := by
    rw [hgdef, ← integral_integral_swap (f := fun a x => heatKernel 0 1 x • ‖H a x‖) hint]
    refine integral_mono_ae hint.integral_prod_left hY ?_
    filter_upwards [henv] with a ha
    simpa only [smul_eq_mul] using ha.2
  have hc := cellHeatLower_pos d
  have hpt : ∀ x ∈ latticeCell 1 (0 : LatticeIndex d),
      ‖∫ a, H a x ∂P‖ ≤ (cellHeatLower d)⁻¹ * g x := by
    intro x hx
    have h1 := norm_integral_le_integral_norm (μ := P) (fun a => H a x)
    have h2 : g x = heatKernel 0 1 x * ∫ a, ‖H a x‖ ∂P := by
      rw [hgdef]; simp only [smul_eq_mul]; exact integral_const_mul _ _
    have h3 := heatKernel_zero_one_ge_of_mem_cell hx
    have h4 : 0 ≤ ∫ a, ‖H a x‖ ∂P := integral_nonneg fun a => norm_nonneg _
    rw [h2, le_inv_mul_iff₀ hc]
    calc cellHeatLower d * ‖∫ a, H a x ∂P‖ ≤ cellHeatLower d * ∫ a, ‖H a x‖ ∂P :=
          mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ heatKernel 0 1 x * ∫ a, ‖H a x‖ ∂P := mul_le_mul_of_nonneg_right h3 h4
  have hmH : StronglyMeasurable fun x => ∫ a, H a x ∂P := hH.integral_prod_left'
  have hcellm : MeasurableSet (latticeCell 1 (0 : LatticeIndex d)) := measurableSet_latticeCell 1 0
  have hgc : IntegrableOn (fun x => (cellHeatLower d)⁻¹ * g x) (latticeCell 1 (0 : LatticeIndex d)) :=
    (hg.const_mul _).integrableOn
  have hae : ∀ᵐ x ∂(volume.restrict (latticeCell 1 (0 : LatticeIndex d))),
      ‖∫ a, H a x ∂P‖ ≤ (cellHeatLower d)⁻¹ * g x :=
    (ae_restrict_iff' hcellm).mpr (Eventually.of_forall hpt)
  refine ⟨hgc.mono' hmH.aestronglyMeasurable hae, ?_⟩
  calc ∫ x in latticeCell 1 (0 : LatticeIndex d), ‖∫ a, H a x ∂P‖
      ≤ ∫ x in latticeCell 1 (0 : LatticeIndex d), (cellHeatLower d)⁻¹ * g x :=
        setIntegral_mono_ae_restrict (hgc.mono' hmH.aestronglyMeasurable hae).norm hgc hae
    _ ≤ ∫ x, (cellHeatLower d)⁻¹ * g x :=
        setIntegral_le_integral (hg.const_mul _)
          (Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr hc.le) (hg0 x))
    _ = (cellHeatLower d)⁻¹ * ∫ x, g x := integral_const_mul _ _
    _ ≤ (cellHeatLower d)⁻¹ * ∫ a, Y a ∂P := mul_le_mul_of_nonneg_left hgE (inv_nonneg.mpr hc.le)

/-- **The expected averages at the origin converge** to the almost sure limit of the averages,
by dominated convergence. -/
theorem tendsto_expectation_average [CompleteSpace E] {H : CoefficientField d Λ → Vec d → E}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    {Y : CoefficientField d Λ → ℝ} (hY : Integrable Y P)
    (henv : ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r → Integrable (fun x => heatKernel 0 r x * ‖H a x‖) ∧
      ∫ x, heatKernel 0 r x * ‖H a x‖ ≤ Y a) {c : E}
    (hlim : ∀ᵐ a ∂P, Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x) atTop
      (𝓝 c)) :
    Tendsto (fun n : ℕ => ∫ a, (∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x) ∂P) atTop (𝓝 c) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun a => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x) P := fun n =>
    (((measurable_heatKernel_fixed 0 ((n : ℝ) + 1)).comp measurable_snd).stronglyMeasurable.smul
      hH).integral_prod_right'.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ a ∂P, ‖∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x‖ ≤ Y a := by
    intro n
    filter_upwards [henv] with a ha
    have hr : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (ha _ hr).2)
    congr 1
    funext x
    rw [norm_smul, Real.norm_of_nonneg (heatKernel_nonneg _ _ _)]
  have h := tendsto_integral_of_dominated_convergence Y hmeas hY hbound hlim
  simpa using h

/-- **The expectation of a Gaussian average of a stationary density** is within
`((1 + thetaError r²)^d - 1) (4π)^{d/2} e^{d/16} E[Y 0]` of the almost sure limit `c` of the
averages at the origin. -/
theorem norm_expectation_average_sub_le [CompleteSpace E]
    (hinv : ∀ n : LatticeIndex d, Measure.map (translate (latticeShift n)) P = P)
    {H : CoefficientField d Λ → Vec d → E}
    (hH : StronglyMeasurable fun p : CoefficientField d Λ × Vec d => H p.1 p.2)
    (hper : ∀ n : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x,
      H a (x + latticeShift n) = H (translate (latticeShift n) a) x)
    (Y : Vec d → CoefficientField d Λ → ℝ) (hY : ∀ z, Integrable (Y z) P)
    (henv : ∀ z, ∀ᵐ a ∂P, ∀ r : ℝ, 1 ≤ r →
      Integrable (fun x => heatKernel z r x * ‖H a x‖) ∧ ∫ x, heatKernel z r x * ‖H a x‖ ≤ Y z a)
    {c : E} (hlim : ∀ᵐ a ∂P, Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x)
      atTop (𝓝 c))
    (z : Vec d) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun a => ∫ x, heatKernel z r x • H a x) P ∧
      ‖(∫ a, (∫ x, heatKernel z r x • H a x) ∂P) - c‖ ≤
        ((1 + thetaError (r ^ 2)) ^ d - 1) * ((cellHeatLower d)⁻¹ * ∫ a, Y 0 a ∂P) := by
  have henvr : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ᵐ a ∂P,
      Integrable (fun x => heatKernel z r x * ‖H a x‖) ∧
        ∫ x, heatKernel z r x * ‖H a x‖ ≤ Y z a := fun z r hr => by
    filter_upwards [henv z] with a ha
    exact ha r hr
  have hint : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → Integrable
      (fun p : CoefficientField d Λ × Vec d => heatKernel z r p.2 • H p.1 p.2) (P.prod volume) :=
    fun z r hr => integrable_prod_heatKernel_smul hH (hY z) (henvr z r hr)
  obtain ⟨hcell, hcellb⟩ := integrableOn_expectation_cell hH (hY 0) (henvr 0 1 le_rfl)
  have hmH : AEStronglyMeasurable (fun x => ∫ a, H a x ∂P) volume :=
    (hH.integral_prod_left' (μ := P)).aestronglyMeasurable
  have hper' := ae_expectation_add_latticeShift hinv hH hper
  have key : ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      ‖(∫ a, (∫ x, heatKernel z r x • H a x) ∂P) -
          ∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P‖ ≤
        ((1 + thetaError (r ^ 2)) ^ d - 1) *
          ∫ x in latticeCell 1 (0 : LatticeIndex d), ‖∫ a, H a x ∂P‖ := fun z r hr => by
    rw [integral_heatKernel_smul_expectation (hint z r hr)]
    exact norm_integral_heatKernel_smul_sub_cell_le hmH hcell hper' z (zero_lt_one.trans_le hr)
  have hT1 := tendsto_expectation_average hH (hY 0) (henv 0) hlim
  have hT2 : Tendsto (fun n : ℕ => ∫ a, (∫ x, heatKernel 0 ((n : ℝ) + 1) x • H a x) ∂P) atTop
      (𝓝 (∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim0 := (tendsto_periodizationError (d := d)).mul_const
      (∫ x in latticeCell 1 (0 : LatticeIndex d), ‖∫ a, H a x ∂P‖)
    rw [zero_mul] at hlim0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun n => norm_nonneg _) fun n => key 0 _ ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hc : ∫ x in latticeCell 1 (0 : LatticeIndex d), ∫ a, H a x ∂P = c :=
    tendsto_nhds_unique hT2 hT1
  refine ⟨(hint z r hr).integral_prod_left, ?_⟩
  have h := key z r hr
  rw [hc] at h
  exact h.trans (mul_le_mul_of_nonneg_left hcellb
    (periodizationError_nonneg (zero_lt_one.trans_le hr)))

end Generic

end QSH
