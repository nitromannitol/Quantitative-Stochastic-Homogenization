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

end QSH
