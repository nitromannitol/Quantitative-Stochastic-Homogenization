import QuantitativeStochasticHomogenization.Ch05.Sec03.CoarsenedCoefficientEstimatesCorrected
import QuantitativeStochasticHomogenization.Front.Assumptions.MeasurableVersion

/-!
# Measurability of the flux defect of (5.64)

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.3, (5.64): the supremum over `A₁` in (5.64) is almost surely measurable.

On the event where the gradients of `A₁` are the corrected fields `G ξ = ∑ᵢ ξᵢ Wᵢ`,
`Wᵢ = eᵢ + ∇φ_{eᵢ}`, with finite energy against `Φ_{z,r}`, the supremum is taken over the
ellipsoid `{ξ : ∑ ξᵢξⱼ Mᵢⱼ ≤ 1}`, `Mᵢⱼ = ∫ Φ Wᵢ·Wⱼ`, of
`|∑ ξᵢ ∫ Φ a Wᵢ - (ā + b) ∑ ξᵢ ∫ Φ Wᵢ|`. These averages are measurable in the coefficient field:
the flux is computed with the jointly measurable version of the coefficients. By continuity in
`ξ` the supremum is a supremum over a dense sequence, hence almost surely measurable
(`aemeasurable_coarseFluxDefect`).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Columns

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P) (z : Vec d) (r : ℝ)

theorem measurable_correctedCoordinate_uncurry (i : Fin d) :
    Measurable (fun p : CoefficientField d Λ × Vec d => correctedCoordinate S p.1 i p.2) :=
  measurable_const.add (S.corrector (unitVector i)).measurable_grad

/-- `∫ Φ_{z,r} Wᵢ`. -/
def columnAverage (a : CoefficientField d Λ) (i : Fin d) : Vec d :=
  ∫ x, heatKernel z r x • correctedCoordinate S a i x

/-- `∫ Φ_{z,r} ã Wᵢ`, with the jointly measurable version `ã` of the coefficients. -/
def columnFlux (a : CoefficientField d Λ) (i : Fin d) : Vec d :=
  ∫ x, heatKernel z r x • (coefficientVersion a x).mulVec (correctedCoordinate S a i x)

/-- `∫ Φ_{z,r} Wᵢ·Wⱼ`. -/
def columnGram (a : CoefficientField d Λ) (i j : Fin d) : ℝ :=
  ∫ x, heatKernel z r x * dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)

/-- The energy `∑ ξᵢξⱼ Mᵢⱼ` of `G ξ`. -/
def gramEnergyAt (a : CoefficientField d Λ) (ξ : Vec d) : ℝ :=
  ∑ i, ∑ j, ξ i * ξ j * columnGram S z r a i j

/-- The defect `|∑ ξᵢ ∫ Φ ã Wᵢ - (A + b) ∑ ξᵢ ∫ Φ Wᵢ|` of `G ξ`. -/
def defectAt (A : Mat d) (a : CoefficientField d Λ) (ξ : Vec d) : ℝ :=
  euclideanNorm ((∑ i, ξ i • columnFlux S z r a i) -
    (A + coarsenedCoefficient a A z r).mulVec (∑ i, ξ i • columnAverage S z r a i))

theorem measurable_mulVec_uncurry {α : Type*} [MeasurableSpace α] {M : α → Mat d}
    {v : α → Vec d} (hM : Measurable M) (hv : Measurable v) :
    Measurable (fun p => (M p).mulVec (v p)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_fun_sum _ fun j _ =>
    ((measurable_pi_iff.mp (measurable_pi_iff.mp hM i) j)).mul (measurable_pi_iff.mp hv j)

theorem measurable_columnAverage (i : Fin d) :
    Measurable (fun a : CoefficientField d Λ => columnAverage S z r a i) := by
  have hf : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (x : Vec d) =>
      heatKernel z r x • correctedCoordinate S a i x) :=
    (((measurable_heatKernel z r).comp measurable_snd).smul
      (measurable_correctedCoordinate_uncurry S i)).stronglyMeasurable
  exact (hf.integral_prod_right (ν := (volume : Measure (Vec d)))).measurable

theorem measurable_columnFlux (i : Fin d) :
    Measurable (fun a : CoefficientField d Λ => columnFlux S z r a i) := by
  have hf : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (x : Vec d) =>
      heatKernel z r x • (coefficientVersion a x).mulVec (correctedCoordinate S a i x)) :=
    (((measurable_heatKernel z r).comp measurable_snd).smul
      (measurable_mulVec_uncurry measurable_coefficientVersion
        (measurable_correctedCoordinate_uncurry S i))).stronglyMeasurable
  exact (hf.integral_prod_right (ν := (volume : Measure (Vec d)))).measurable

theorem measurable_columnGram (i j : Fin d) :
    Measurable (fun a : CoefficientField d Λ => columnGram S z r a i j) := by
  have hdot : Measurable (fun p : CoefficientField d Λ × Vec d =>
      dot (correctedCoordinate S p.1 i p.2) (correctedCoordinate S p.1 j p.2)) := by
    have hi := measurable_correctedCoordinate_uncurry S i
    have hj := measurable_correctedCoordinate_uncurry S j
    simp only [dot]
    exact Finset.measurable_fun_sum _ fun k _ =>
      (measurable_pi_iff.mp hi k).mul (measurable_pi_iff.mp hj k)
  have hf : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (x : Vec d) =>
      heatKernel z r x * dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)) :=
    (((measurable_heatKernel z r).comp measurable_snd).mul hdot).stronglyMeasurable
  exact (hf.integral_prod_right (ν := (volume : Measure (Vec d)))).measurable

theorem measurable_gramEnergyAt (ξ : Vec d) :
    Measurable (fun a : CoefficientField d Λ => gramEnergyAt S z r a ξ) := by
  unfold gramEnergyAt
  exact Finset.measurable_fun_sum _ fun i _ => Finset.measurable_fun_sum _ fun j _ =>
    (measurable_columnGram S z r i j).const_mul _

theorem aemeasurable_defectAt (A : Mat d)
    (hJm : ∀ p q : Vec d, AEMeasurable (fun a => J1Heat a z r p q) P) (ξ : Vec d) :
    AEMeasurable (fun a : CoefficientField d Λ => defectAt S z r A a ξ) P := by
  have hcc : AEMeasurable (fun a : CoefficientField d Λ => A + coarsenedCoefficient a A z r) P := by
    refine aemeasurable_pi_iff.mpr fun j => aemeasurable_pi_iff.mpr fun k => ?_
    exact aemeasurable_const.add (((hJm _ _).sub (hJm _ _)).div_const 2)
  have hV : Measurable (fun a : CoefficientField d Λ => ∑ i, ξ i • columnFlux S z r a i) :=
    Finset.measurable_fun_sum _ fun i _ => (measurable_columnFlux S z r i).const_smul (ξ i)
  have hU : Measurable (fun a : CoefficientField d Λ => ∑ i, ξ i • columnAverage S z r a i) :=
    Finset.measurable_fun_sum _ fun i _ => (measurable_columnAverage S z r i).const_smul (ξ i)
  have hM : AEMeasurable (fun a : CoefficientField d Λ =>
      (A + coarsenedCoefficient a A z r).mulVec (∑ i, ξ i • columnAverage S z r a i)) P := by
    have hcont : Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact hcont.measurable.comp_aemeasurable (hcc.prodMk hU.aemeasurable)
  unfold defectAt
  exact measurable_euclideanNorm.comp_aemeasurable (hV.aemeasurable.sub hM)

theorem continuous_gramEnergyAt (a : CoefficientField d Λ) :
    Continuous (gramEnergyAt S z r a) := by
  unfold gramEnergyAt
  fun_prop

theorem continuous_euclideanNorm' : Continuous (euclideanNorm (d := d)) := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem continuous_defectAt (A : Mat d) (a : CoefficientField d Λ) :
    Continuous (defectAt S z r A a) := by
  unfold defectAt
  refine continuous_euclideanNorm'.comp ?_
  refine (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const).sub ?_
  exact Continuous.matrix_mulVec continuous_const
    (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)

theorem gramEnergyAt_smul (a : CoefficientField d Λ) (t : ℝ) (ξ : Vec d) :
    gramEnergyAt S z r a (t • ξ) = t ^ 2 * gramEnergyAt S z r a ξ := by
  unfold gramEnergyAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem defectAt_smul (A : Mat d) (a : CoefficientField d Λ) (t : ℝ) (ξ : Vec d) :
    defectAt S z r A a (t • ξ) = |t| * defectAt S z r A a ξ := by
  unfold defectAt
  have h1 : (∑ i, (t • ξ) i • columnFlux S z r a i) = t • ∑ i, ξ i • columnFlux S z r a i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  have h2 : (∑ i, (t • ξ) i • columnAverage S z r a i) =
      t • ∑ i, ξ i • columnAverage S z r a i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [h1, h2, Matrix.mulVec_smul, ← smul_sub, euclideanNorm_smul_eq_abs_mul]

end Columns

/-! ## The defect on the event of (4.12) -/

section GoodEvent

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P) (A : Mat d) (z : Vec d)
  {r : ℝ} (hr : 0 < r) {a : CoefficientField d Λ}
  (hint : ∀ i : Fin d, Integrable (fun x => heatKernel z r x *
    euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x)))

include hr hint

omit hr hint in
theorem aemeasurable_correctedCoordinate (i : Fin d) :
    AEMeasurable (correctedCoordinate S a i) volume :=
  ((measurable_correctedCoordinate_uncurry S i).comp measurable_prodMk_left).aemeasurable

theorem integrable_heatKernel_smul_correctedCoordinate (i : Fin d) :
    Integrable (fun x => heatKernel z r x • correctedCoordinate S a i x) :=
  integrable_mask_smul (heatKernel_nonneg z r) (integrable_heatKernel z hr)
    (aemeasurable_correctedCoordinate S (a := a) i) (hint i)

theorem integrable_heatKernel_smul_flux_correctedCoordinate (i : Fin d) :
    Integrable (fun x => heatKernel z r x • (a x).mulVec (correctedCoordinate S a i x)) :=
  integrable_mask_smul (heatKernel_nonneg z r) (integrable_heatKernel z hr)
    (aemeasurable_mulVec a (aemeasurable_correctedCoordinate S (a := a) i))
    (integrable_mask_mul_euclideanSq_mulVec a (heatKernel_nonneg z r) (integrable_heatKernel z hr)
      (aemeasurable_correctedCoordinate S (a := a) i) (hint i))

theorem integrable_heatKernel_mul_dot_correctedCoordinate (i j : Fin d) :
    Integrable (fun x => heatKernel z r x *
      dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)) := by
  have hmi := aemeasurable_correctedCoordinate S (a := a) i
  have hmj := aemeasurable_correctedCoordinate S (a := a) j
  refine Integrable.mono' (((hint i).add (hint j)).div_const 2)
    (((integrable_heatKernel z hr).aestronglyMeasurable.aemeasurable.mul
      (aemeasurable_dot hmi hmj)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  have hk := heatKernel_nonneg z r x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  have h1 := abs_dot_le (correctedCoordinate S a i x) (correctedCoordinate S a j x)
  have h2 := euclideanNorm_sq (correctedCoordinate S a i x)
  have h3 := euclideanNorm_sq (correctedCoordinate S a j x)
  have h4 := euclideanNorm_nonneg (correctedCoordinate S a i x)
  have h5 := euclideanNorm_nonneg (correctedCoordinate S a j x)
  change heatKernel z r x * |dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)| ≤
    (heatKernel z r x * euclideanSq (correctedCoordinate S a i x) +
      heatKernel z r x * euclideanSq (correctedCoordinate S a j x)) / 2
  have h6 : |dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)| ≤
      (euclideanSq (correctedCoordinate S a i x) + euclideanSq (correctedCoordinate S a j x)) / 2 := by
    rw [← h2, ← h3]
    nlinarith [sq_nonneg (euclideanNorm (correctedCoordinate S a i x) -
      euclideanNorm (correctedCoordinate S a j x))]
  calc heatKernel z r x * |dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)|
      ≤ heatKernel z r x * ((euclideanSq (correctedCoordinate S a i x) +
          euclideanSq (correctedCoordinate S a j x)) / 2) := mul_le_mul_of_nonneg_left h6 hk
    _ = _ := by ring

theorem integral_heatKernel_smul_correctedField (ξ : Vec d) :
    ∫ x, heatKernel z r x • correctedField S a ξ x = ∑ i, ξ i • columnAverage S z r a i := by
  have hi : ∀ i, Integrable (fun x => ξ i • (heatKernel z r x • correctedCoordinate S a i x)) :=
    fun i => (integrable_heatKernel_smul_correctedCoordinate S z hr hint i).smul (ξ i)
  have heq : (fun x => heatKernel z r x • correctedField S a ξ x) =
      fun x => ∑ i, ξ i • (heatKernel z r x • correctedCoordinate S a i x) := by
    funext x
    rw [correctedField, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [heq, integral_finsetSum _ fun i _ => hi i]
  exact Finset.sum_congr rfl fun i _ => integral_smul _ _

theorem integral_heatKernel_smul_flux_correctedField (ξ : Vec d) :
    ∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x) =
      ∑ i, ξ i • columnFlux S z r a i := by
  have hi : ∀ i, Integrable (fun x => ξ i • (heatKernel z r x •
      (a x).mulVec (correctedCoordinate S a i x))) :=
    fun i => (integrable_heatKernel_smul_flux_correctedCoordinate S z hr hint i).smul (ξ i)
  have heq : (fun x => heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) =
      fun x => ∑ i, ξ i • (heatKernel z r x • (a x).mulVec (correctedCoordinate S a i x)) := by
    funext x
    rw [correctedField, Matrix.mulVec_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_smul, smul_comm]
  rw [heq, integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul, columnFlux]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_coefficientVersion_eq a] with x hx
  rw [hx]

omit hr hint in
theorem euclideanSq_correctedField (ξ x : Vec d) :
    euclideanSq (correctedField S a ξ x) = ∑ i, ∑ j, ξ i * ξ j *
      dot (correctedCoordinate S a i x) (correctedCoordinate S a j x) := by
  simp only [correctedField, euclideanSq, dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun k _ => by ring

theorem integrable_heatKernel_mul_euclideanSq_correctedField (ξ : Vec d) :
    Integrable (fun x => heatKernel z r x * euclideanSq (correctedField S a ξ x)) := by
  simp only [euclideanSq_correctedField, Finset.mul_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integrable_heatKernel_mul_dot_correctedCoordinate S z hr hint i j).const_mul (ξ i * ξ j)

theorem integral_heatKernel_mul_euclideanSq_correctedField (ξ : Vec d) :
    ∫ x, heatKernel z r x * euclideanSq (correctedField S a ξ x) = gramEnergyAt S z r a ξ := by
  have hij : ∀ i j, Integrable (fun x => ξ i * ξ j * (heatKernel z r x *
      dot (correctedCoordinate S a i x) (correctedCoordinate S a j x))) := fun i j =>
    (integrable_heatKernel_mul_dot_correctedCoordinate S z hr hint i j).const_mul _
  have heq : (fun x => heatKernel z r x * euclideanSq (correctedField S a ξ x)) =
      fun x => ∑ i, ∑ j, ξ i * ξ j * (heatKernel z r x *
        dot (correctedCoordinate S a i x) (correctedCoordinate S a j x)) := by
    funext x
    rw [euclideanSq_correctedField, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hij i j]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]; rfl

end GoodEvent

/-! ## The supremum over the ellipsoid -/

section Supremum

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P) (A : Mat d) (z : Vec d)
  {r : ℝ} (hr : 0 < r) {a : CoefficientField d Λ}
  (hint : ∀ i : Fin d, Integrable (fun x => heatKernel z r x *
    euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x)))

include hr hint

theorem coarseFluxDefect_eq_sSup_image (hcorr : GradientsOfA1AreCorrected S a) :
    coarseFluxDefect a A z r =
      sSup (defectAt S z r A a '' {ξ | gramEnergyAt S z r a ξ ≤ 1}) := by
  have hval : ∀ (w : HarmonicA1 a) (ξ : Vec d), w.grad =ᵐ[volume] correctedField S a ξ →
      euclideanNorm ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec (∫ x, heatKernel z r x • w.grad x)) =
      defectAt S z r A a ξ := fun w ξ hξ => by
    unfold defectAt
    rw [← integral_heatKernel_smul_correctedField S z hr hint ξ,
      ← integral_heatKernel_smul_flux_correctedField S z hr hint ξ]
    have h1 : (∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) =
        ∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x) :=
      integral_congr_ae (hξ.mono fun x hx => by simp only; rw [hx])
    have h2 : (∫ x, heatKernel z r x • w.grad x) =
        ∫ x, heatKernel z r x • correctedField S a ξ x :=
      integral_congr_ae (hξ.mono fun x hx => by simp only; rw [hx])
    rw [h1, h2]
  have hen : ∀ (w : HarmonicA1 a) (ξ : Vec d), w.grad =ᵐ[volume] correctedField S a ξ →
      (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2) =ᵐ[volume]
        fun x => heatKernel z r x * euclideanSq (correctedField S a ξ x) := fun w ξ hξ =>
    hξ.mono fun x hx => by simp only; rw [hx, euclideanNorm_sq]
  unfold coarseFluxDefect
  congr 1
  ext e
  constructor
  · rintro ⟨w, -, hwnorm, rfl⟩
    obtain ⟨ξ, hξ⟩ := hcorr.1 w
    refine ⟨ξ, ?_, (hval w ξ hξ).symm⟩
    show gramEnergyAt S z r a ξ ≤ 1
    rw [← integral_heatKernel_mul_euclideanSq_correctedField S z hr hint ξ,
      ← integral_congr_ae (hen w ξ hξ)]
    exact Real.sqrt_le_one.mp hwnorm
  · rintro ⟨ξ, hξK, rfl⟩
    obtain ⟨w, hw⟩ := hcorr.2 ξ
    refine ⟨w, (integrable_heatKernel_mul_euclideanSq_correctedField S z hr hint ξ).congr
      (hen w ξ hw).symm, ?_, (hval w ξ hw).symm⟩
    rw [integral_congr_ae (hen w ξ hw), integral_heatKernel_mul_euclideanSq_correctedField
      S z hr hint ξ]
    exact Real.sqrt_le_one.mpr hξK

theorem defectAt_le_of_gramEnergyAt_le (ξ : Vec d) (hξ : gramEnergyAt S z r a ξ ≤ 1) :
    defectAt S z r A a ξ ≤
      |Λ| + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A + coarsenedCoefficient a A z r)‖ := by
  have hm : AEMeasurable (correctedField S a ξ) volume :=
    (measurable_correctedField S a ξ).aemeasurable
  have hG2 := integrable_heatKernel_mul_euclideanSq_correctedField S z hr hint ξ
  have hE := integral_heatKernel_mul_euclideanSq_correctedField S z hr hint ξ
  have hu : euclideanSq (∑ i, ξ i • columnAverage S z r a i) ≤ 1 := by
    rw [← integral_heatKernel_smul_correctedField S z hr hint ξ]
    refine (euclideanSq_integral_le (heatKernel_nonneg z r) (integrable_heatKernel z hr)
      (integral_heatKernel z hr).le hm hG2).trans ?_
    rw [hE]; exact hξ
  have hv : euclideanSq (∑ i, ξ i • columnFlux S z r a i) ≤ Λ ^ 2 := by
    rw [← integral_heatKernel_smul_flux_correctedField S z hr hint ξ]
    refine (euclideanSq_integral_le (heatKernel_nonneg z r) (integrable_heatKernel z hr)
      (integral_heatKernel z hr).le (aemeasurable_mulVec a hm)
      (integrable_mask_mul_euclideanSq_mulVec a (heatKernel_nonneg z r)
        (integrable_heatKernel z hr) hm hG2)).trans ?_
    calc ∫ x, heatKernel z r x * euclideanSq ((a x).mulVec (correctedField S a ξ x))
        ≤ ∫ x, Λ ^ 2 * (heatKernel z r x * euclideanSq (correctedField S a ξ x)) :=
          integral_mono (integrable_mask_mul_euclideanSq_mulVec a (heatKernel_nonneg z r)
            (integrable_heatKernel z hr) hm hG2) (hG2.const_mul _) fun x => by
            have := mul_le_mul_of_nonneg_left (euclideanSq_mulVec_le a x
              (correctedField S a ξ x)) (heatKernel_nonneg z r x)
            linarith
      _ = Λ ^ 2 * gramEnergyAt S z r a ξ := by rw [integral_const_mul, hE]
      _ ≤ Λ ^ 2 * 1 := mul_le_mul_of_nonneg_left hξ (sq_nonneg Λ)
      _ = Λ ^ 2 := mul_one _
  have hun : euclideanNorm (∑ i, ξ i • columnAverage S z r a i) ≤ 1 := by
    rw [euclideanNorm, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hu
  have hvn : euclideanNorm (∑ i, ξ i • columnFlux S z r a i) ≤ |Λ| := by
    rw [euclideanNorm, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hv
  set M := A + coarsenedCoefficient a A z r
  set u := ∑ i, ξ i • columnAverage S z r a i
  have hMu : euclideanNorm (M.mulVec u) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ := by
    rw [← norm_toLp, ← Matrix.toEuclideanCLM_toLp]
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 u)‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * 1 := by
          rw [norm_toLp]; exact mul_le_mul_of_nonneg_left hun (norm_nonneg _)
      _ = _ := mul_one _
  unfold defectAt
  exact (euclideanNorm_sub_le _ _).trans (add_le_add hvn hMu)

omit hr hint in
theorem defectAt_zero : defectAt S z r A a 0 = 0 := by
  simp [defectAt, euclideanNorm, euclideanSq, dot]

omit hr hint in
theorem gramEnergyAt_zero : gramEnergyAt S z r a 0 = 0 := by
  simp [gramEnergyAt]

omit hr hint in
theorem defectAt_nonneg (ξ : Vec d) : 0 ≤ defectAt S z r A a ξ :=
  euclideanNorm_nonneg _

end Supremum

/-! ## The supremum over a dense sequence -/

section Dense

variable {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P) (A : Mat d) (z : Vec d)
  (r : ℝ)

/-- The supremum of the defect over the points of a dense sequence of `ℝ^d` in the open
ellipsoid of the Gram energy. -/
def defectSup (a : CoefficientField d Λ) : ℝ :=
  ⨆ n : ℕ, if gramEnergyAt S z r a (TopologicalSpace.denseSeq (Vec d) n) < 1 then
    defectAt S z r A a (TopologicalSpace.denseSeq (Vec d) n) else 0

theorem aemeasurable_defectSup
    (hJm : ∀ p q : Vec d, AEMeasurable (fun a => J1Heat a z r p q) P) :
    AEMeasurable (defectSup S A z r) P := by
  refine AEMeasurable.iSup fun n => ?_
  have hset : MeasurableSet {a : CoefficientField d Λ |
      gramEnergyAt S z r a (TopologicalSpace.denseSeq (Vec d) n) < 1} :=
    measurableSet_lt (measurable_gramEnergyAt S z r _) measurable_const
  refine ((aemeasurable_defectAt S z r A hJm (TopologicalSpace.denseSeq (Vec d) n)).indicator
    hset).congr
    (Eventually.of_forall fun a => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

theorem sSup_image_eq_defectSup {a : CoefficientField d Λ} (hr : 0 < r)
    (hint : ∀ i : Fin d, Integrable (fun x => heatKernel z r x *
      euclideanSq (unitVector i + (S.corrector (unitVector i)).grad a x))) :
    sSup (defectAt S z r A a '' {ξ | gramEnergyAt S z r a ξ ≤ 1}) = defectSup S A z r a := by
  unfold defectSup
  set f := defectAt S z r A a with hf
  set E := gramEnergyAt S z r a with hE
  set s := TopologicalSpace.denseSeq (Vec d) with hs
  set B := |Λ| + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A + coarsenedCoefficient a A z r)‖ with hB
  have hfB : ∀ ξ, E ξ ≤ 1 → f ξ ≤ B := fun ξ hξ =>
    defectAt_le_of_gramEnergyAt_le S A z hr hint ξ hξ
  have hf0 : f 0 = 0 := defectAt_zero S A z
  have hE0 : E 0 = 0 := gramEnergyAt_zero S z
  have hB0 : 0 ≤ B := by
    have := hfB 0 (by rw [hE0]; norm_num)
    rwa [hf0] at this
  have hgB : ∀ n, (if E (s n) < 1 then f (s n) else 0) ≤ B := fun n => by
    split_ifs with h
    · exact hfB _ h.le
    · exact hB0
  have bddImg : BddAbove (f '' {ξ | E ξ ≤ 1}) := ⟨B, by rintro _ ⟨ξ, hξ, rfl⟩; exact hfB ξ hξ⟩
  have bddRng : BddAbove (Set.range fun n => if E (s n) < 1 then f (s n) else 0) :=
    ⟨B, by rintro _ ⟨n, rfl⟩; exact hgB n⟩
  have mem0 : (0 : ℝ) ∈ f '' {ξ | E ξ ≤ 1} := ⟨0, by simp [hE0], hf0⟩
  have hsup0 : (0 : ℝ) ≤ ⨆ n, if E (s n) < 1 then f (s n) else 0 := by
    refine le_ciSup_of_le bddRng 0 ?_
    split_ifs
    · exact defectAt_nonneg S A z _
    · exact le_rfl
  refine le_antisymm (csSup_le ⟨0, mem0⟩ ?_) (ciSup_le fun n => ?_)
  · rintro _ ⟨ξ, hξ, rfl⟩
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have hfξ : 0 ≤ f ξ := defectAt_nonneg S A z ξ
    set c := δ / (2 * (f ξ + δ)) with hc
    have hc0 : 0 < c := by positivity
    have hc1 : c ≤ 1 / 2 := by
      rw [hc, div_le_iff₀ (by positivity)]
      linarith
    have hcf : c * f ξ < δ / 2 := by
      rw [hc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    set t := 1 - c with ht
    have ht0 : 0 < t := by linarith
    have ht1 : t < 1 := by linarith
    have hEt : E (t • ξ) < 1 := by
      rw [hE, gramEnergyAt_smul, ← hE]
      have ht2 : t ^ 2 < 1 := by nlinarith
      have hEξ : t ^ 2 * E ξ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left hξ (sq_nonneg t)
      linarith
    have hft : f (t • ξ) = t * f ξ := by
      rw [hf, defectAt_smul, abs_of_pos ht0]
    have hU : IsOpen ({η | E η < 1} ∩ {η | f (t • ξ) - δ / 2 < f η}) :=
      (isOpen_lt (continuous_gramEnergyAt S z r a) continuous_const).inter
        (isOpen_lt continuous_const (continuous_defectAt S z r A a))
    have hmem : f (t • ξ) - δ / 2 < f (t • ξ) := by linarith
    obtain ⟨n, hn1, hn2⟩ := (TopologicalSpace.denseRange_denseSeq (Vec d)).exists_mem_open hU
      ⟨t • ξ, hEt, hmem⟩
    have hn1' : E (s n) < 1 := hn1
    have hg : (if E (s n) < 1 then f (s n) else 0) = f (s n) := by simp [hn1']
    have hle := le_ciSup bddRng n
    simp only [hg] at hle
    have : f ξ - δ < f (s n) := by
      have h1 : f (t • ξ) - δ / 2 < f (s n) := hn2
      rw [hft] at h1
      have h2 : t * f ξ = f ξ - c * f ξ := by rw [ht]; ring
      linarith
    linarith
  · split_ifs with h
    · exact le_csSup bddImg ⟨s n, h.le, rfl⟩
    · exact le_csSup bddImg mem0

end Dense

/-- **The flux defect of (5.64) is almost surely measurable** on the event of (4.12) by the
corrected fields with finite Gaussian energy. -/
theorem aemeasurable_coarseFluxDefect {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hJm : ∀ p q : Vec d, AEMeasurable (fun a => J1Heat a z r p q) P)
    (hcorr : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) (hen : HasGaussianCorrectorEnergy S) :
    AEMeasurable (fun a => coarseFluxDefect a A z r) P := by
  refine (aemeasurable_defectSup S A z r hJm).congr ?_
  filter_upwards [hcorr, hen] with a h1 h2
  have hint := fun i => h2 i z r hr
  rw [coarseFluxDefect_eq_sSup_image S A z hr hint h1, sSup_image_eq_defectSup S A z r hr hint]

/-- **`QSH.Frozen.coarsenedCoefficientEstimates`** from (5.58) with a constant `C₀(d, Λ)`, the
measurability of `J₁`, (4.12) by the corrected fields and the finite Gaussian energy of the
corrected coordinates. -/
theorem coarsenedCoefficientEstimates_of_corrected_energy
    (h558 : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P → ∀ S : HomogenizationData P,
        EnergyEstimate P S.homogenized C₀)
    (hJm : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
        AEMeasurable (fun a => J1Heat a z r p q) P)
    (hcorr : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ S : HomogenizationData P, ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (hen : ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 1 < Λ → ∀ P : Measure (CoefficientField d Λ),
      LawHypotheses P → ∀ S : HomogenizationData P, HasGaussianCorrectorEnergy S) :
    QSH.Frozen.coarsenedCoefficientEstimates :=
  coarsenedCoefficientEstimates_of_corrected h558 hJm hcorr hen
    fun d hd Λ hΛ P hP S z r hr => aemeasurable_coarseFluxDefect S S.homogenized z
      (by linarith) (hJm d hd Λ hΛ P hP z r hr) (hcorr d hd Λ hΛ P hP S) (hen d hd Λ hΛ P hP S)

end QSH
