import QuantitativeStochasticHomogenization.Ch03.Sec04FirstOrderCorrectors

/-!
# Linear combinations of first-order correctors

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4, Definitions 3.14–3.15: if `φᵢ` are correctors in the directions `uᵢ`, then
`∑ᵢ cᵢ φᵢ` is a corrector in the direction `∑ᵢ cᵢ uᵢ` (`Corrector.linearCombination`). In
particular homogenization data can be replaced by data whose correctors are the combinations of
the correctors in the coordinate directions (`HomogenizationData.linearize`), with the same
homogenized matrix.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Weak derivatives of finite linear combinations -/

theorem isSpatialTest_continuous_coordinateDerivative {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) (j : Fin d) : Continuous (coordinateDerivative j φ) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem isSpatialTest_hasCompactSupport_coordinateDerivative {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) (j : Fin d) : HasCompactSupport (coordinateDerivative j φ) :=
  hφ.2.1.fderiv_apply (𝕜 := ℝ) (unitVector j)

theorem integrable_mul_coordinateDerivative {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest Set.univ φ) (j : Fin d) :
    Integrable (fun x => f x * coordinateDerivative j φ x) :=
  hf.integrable_smul_right_of_hasCompactSupport
    (isSpatialTest_continuous_coordinateDerivative hφ j)
    (isSpatialTest_hasCompactSupport_coordinateDerivative hφ j)

theorem integrable_mul_test {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) : Integrable (fun x => f x * φ x) :=
  hf.integrable_smul_right_of_hasCompactSupport hφ.1.continuous hφ.2.1

theorem HasWeakPartialDerivative.finsetSum {ι : Type*} (s : Finset ι) {j : Fin d}
    {f g : ι → Vec d → ℝ} (c : ι → ℝ)
    (h : ∀ i ∈ s, HasWeakPartialDerivative Set.univ j (f i) (g i)) :
    HasWeakPartialDerivative Set.univ j (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * g i x) := by
  have hf : ∀ i ∈ s, LocallyIntegrable (f i) volume := fun i hi =>
    locallyIntegrableOn_univ.mp (h i hi).1
  have hg : ∀ i ∈ s, LocallyIntegrable (g i) volume := fun i hi =>
    locallyIntegrableOn_univ.mp (h i hi).2.1
  refine ⟨locallyIntegrableOn_univ.mpr (locallyIntegrable_finsetSum s fun i hi =>
      (hf i hi).smul (c i)), locallyIntegrableOn_univ.mpr (locallyIntegrable_finsetSum s
      fun i hi => (hg i hi).smul (c i)), fun φ hφ => ?_⟩
  have h1 := fun i hi => (h i hi).2.2 φ hφ
  simp only [Measure.restrict_univ] at h1 ⊢
  have hint1 : ∀ i ∈ s, Integrable (fun x => c i * (f i x * coordinateDerivative j φ x)) :=
    fun i hi => (integrable_mul_coordinateDerivative (hf i hi) hφ j).const_mul (c i)
  have hint2 : ∀ i ∈ s, Integrable (fun x => c i * (g i x * φ x)) :=
    fun i hi => (integrable_mul_test (hg i hi) hφ).const_mul (c i)
  calc (∫ x, (∑ i ∈ s, c i * f i x) * coordinateDerivative j φ x)
      = ∫ x, ∑ i ∈ s, c i * (f i x * coordinateDerivative j φ x) := by
        congr 1; funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ s, c i * ∫ x, f i x * coordinateDerivative j φ x := by
        rw [integral_finsetSum s hint1]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i ∈ s, c i * -(∫ x, g i x * φ x) :=
        Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
    _ = -(∫ x, (∑ i ∈ s, c i * g i x) * φ x) := by
        rw [show (fun x => (∑ i ∈ s, c i * g i x) * φ x) =
            fun x => ∑ i ∈ s, c i * (g i x * φ x) by
          funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
          integral_finsetSum s hint2, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring

theorem HasWeakGradient.finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ}
    {g : ι → Vec d → Vec d} (c : ι → ℝ) (h : ∀ i ∈ s, HasWeakGradient Set.univ (f i) (g i)) :
    HasWeakGradient Set.univ (fun x => ∑ i ∈ s, c i * f i x) (fun x => ∑ i ∈ s, c i • g i x) :=
  fun j => by
    have := HasWeakPartialDerivative.finsetSum s (j := j) (f := f) (g := fun i x => g i x j) c
      fun i hi => h i hi j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

theorem integrable_dot_gradient {F : Vec d → Vec d}
    (hF : ∀ k : Fin d, LocallyIntegrable (fun x => F x k) volume) {φ : Vec d → ℝ}
    (hφ : IsSpatialTest Set.univ φ) : Integrable (fun x => dot (F x) (gradient φ x)) := by
  unfold dot
  exact integrable_finsetSum _ fun k _ => integrable_mul_coordinateDerivative (hF k) hφ k

theorem HasWeakDivergence.finsetSum_zero {ι : Type*} (s : Finset ι) {F : ι → Vec d → Vec d}
    (c : ι → ℝ) (h : ∀ i ∈ s, HasWeakDivergence Set.univ (F i) (fun _ => 0)) :
    HasWeakDivergence Set.univ (fun x => ∑ i ∈ s, c i • F i x) (fun _ => 0) := by
  have hF : ∀ i ∈ s, ∀ k : Fin d, LocallyIntegrable (fun x => F i x k) volume := fun i hi k =>
    locallyIntegrableOn_univ.mp ((h i hi).1 k)
  refine ⟨fun k => ?_, locallyIntegrableOn_zero, fun φ hφ => ?_⟩
  · refine locallyIntegrableOn_univ.mpr ?_
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      locallyIntegrable_finsetSum s fun i hi => (hF i hi k).smul (c i)
  · have h1 := fun i hi => (h i hi).2.2 φ hφ
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at h1 ⊢
    have hint : ∀ i ∈ s, Integrable (fun x => c i * dot (F i x) (gradient φ x)) := fun i hi =>
      (integrable_dot_gradient (hF i hi) hφ).const_mul (c i)
    calc (∫ x, dot (∑ i ∈ s, c i • F i x) (gradient φ x))
        = ∫ x, ∑ i ∈ s, c i * dot (F i x) (gradient φ x) := by
          congr 1; funext x
          simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ i ∈ s, c i * ∫ x, dot (F i x) (gradient φ x) := by
          rw [integral_finsetSum s hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ = 0 := Finset.sum_eq_zero fun i hi => by rw [h1 i hi, mul_zero]

/-! ## Sublinearity of finite linear combinations -/

private theorem abs_apply_le_norm (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem measure_ball_zero_lt_top (R : ℝ) : volume (ball (0 : Vec d) R) < ⊤ := by
  have hsub : ball (0 : Vec d) R ⊆ Set.pi Set.univ (fun _ => Set.Ioo (-R) R) := fun x hx i _ => by
    have h1 := abs_apply_le_norm x i
    have h2 : euclideanNorm x < R := by simpa [ball] using hx
    exact abs_lt.mp (h1.trans_lt h2)
  refine (measure_mono hsub).trans_lt ?_
  rw [Real.volume_pi_Ioo]
  exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top

instance isFiniteMeasure_restrict_ball_zero (R : ℝ) :
    IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
  isFiniteMeasure_restrict.mpr (measure_ball_zero_lt_top R).ne

/-- The centered oscillation `⨍_{B_R} |f - (f)_R|²`. -/
def ballOscillation (f : Vec d → ℝ) (R : ℝ) : ℝ :=
  ⨍ x in ball 0 R, (f x - ⨍ y in ball 0 R, f y ∂volume) ^ 2 ∂volume

theorem ballOscillation_nonneg (f : Vec d → ℝ) (R : ℝ) : 0 ≤ ballOscillation f R := by
  unfold ballOscillation
  rw [setAverage_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun x => sq_nonneg _)

theorem ballOscillation_finsetSum_le {ι : Type*} [Fintype ι] {f : ι → Vec d → ℝ} (c : ι → ℝ)
    {R : ℝ} (hf : ∀ i, MemLp (f i) 2 (volume.restrict (ball 0 R))) :
    ballOscillation (fun x => ∑ i, c i * f i x) R ≤
      Fintype.card ι * ∑ i, c i ^ 2 * ballOscillation (f i) R := by
  have hint : ∀ i, Integrable (f i) (volume.restrict (ball 0 R)) := fun i =>
    (hf i).integrable one_le_two
  obtain ⟨m, hm⟩ : ∃ m : ι → ℝ, ∀ i, m i = ⨍ y in ball 0 R, f i y ∂volume := ⟨_, fun _ => rfl⟩
  have hmean : (⨍ y in ball 0 R, (∑ i, c i * f i y) ∂volume) = ∑ i, c i * m i := by
    rw [setAverage_eq, integral_finsetSum _ fun i _ => (hint i).const_mul (c i), smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hm i, setAverage_eq, smul_eq_mul]
    ring
  have hsq : ∀ i, Integrable (fun x => (f i x - m i) ^ 2) (volume.restrict (ball 0 R)) := fun i =>
    ((hf i).sub (memLp_const (m i))).integrable_sq
  unfold ballOscillation
  rw [hmean]
  simp only [← hm]
  have hpt : ∀ x, (∑ i, c i * f i x - ∑ i, c i * m i) ^ 2 ≤
      Fintype.card ι * ∑ i, c i ^ 2 * (f i x - m i) ^ 2 := fun x => by
    rw [← Finset.sum_sub_distrib]
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => c i * f i x - c i * m i)
    simp only [Finset.card_univ] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : Integrable (fun x => (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * (f i x - m i) ^ 2)
      (volume.restrict (ball 0 R)) :=
    (integrable_finsetSum _ fun i _ => (hsq i).const_mul _).const_mul _
  simp only [setAverage_eq, smul_eq_mul]
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hbound
    (Eventually.of_forall hpt)
  have hlin : ∫ x in ball 0 R, (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * (f i x - m i) ^ 2 =
      Fintype.card ι * ∑ i, c i ^ 2 * ∫ x in ball 0 R, (f i x - m i) ^ 2 := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hsq i).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [hlin] at hmono
  have hv := inv_nonneg.mpr (measureReal_nonneg (μ := volume) (s := ball (0 : Vec d) R))
  calc ((volume : Measure (Vec d)).real (ball 0 R))⁻¹ *
        ∫ x in ball 0 R, (∑ i, c i * f i x - ∑ i, c i * m i) ^ 2
      ≤ ((volume : Measure (Vec d)).real (ball 0 R))⁻¹ *
        ((Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * ∫ x in ball 0 R, (f i x - m i) ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hv
    _ = (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 *
        (((volume : Measure (Vec d)).real (ball 0 R))⁻¹ * ∫ x in ball 0 R, (f i x - m i) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Finite linear combinations of functions of sublinear oscillation have sublinear
oscillation. -/
theorem tendsto_sublinear_finsetSum {ι : Type*} [Fintype ι] {f : ι → Vec d → ℝ} (c : ι → ℝ)
    (hf : ∀ i, ∀ R : ℝ, 0 < R → MemLp (f i) 2 (volume.restrict (ball 0 R)))
    (hs : ∀ i, Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (ballOscillation (f i) R)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (ballOscillation (fun x => ∑ i, c i * f i x) R))
      atTop (𝓝 0) := by
  have hsq : ∀ i, Tendsto (fun R : ℝ => (R⁻¹ * Real.sqrt (ballOscillation (f i) R)) ^ 2) atTop
      (𝓝 0) := fun i => by simpa using (hs i).pow 2
  have hsum : Tendsto (fun R : ℝ => (Fintype.card ι : ℝ) *
      ∑ i, c i ^ 2 * (R⁻¹ * Real.sqrt (ballOscillation (f i) R)) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => (hsq i).const_mul (c i ^ 2))
      |>.const_mul (Fintype.card ι : ℝ)
    simpa using this
  have hup : Tendsto (fun R : ℝ => Real.sqrt ((Fintype.card ι : ℝ) *
      ∑ i, c i ^ 2 * (R⁻¹ * Real.sqrt (ballOscillation (f i) R)) ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsum
    rw [Real.sqrt_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact mul_nonneg (inv_nonneg.mpr hR.le) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hle := ballOscillation_finsetSum_le c (fun i => hf i R hR) (R := R)
    have hR' : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    have heq : (Fintype.card ι : ℝ) *
        ∑ i, c i ^ 2 * (R⁻¹ * Real.sqrt (ballOscillation (f i) R)) ^ 2 =
        (R⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * ballOscillation (f i) R) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (ballOscillation_nonneg _ _)]
      ring
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR']
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hR'

/-! ## The corrector of a linear combination of directions -/

/-- **`∑ᵢ cᵢ φᵢ` is a corrector in the direction `∑ᵢ cᵢ uᵢ`.** -/
def Corrector.linearCombination {ι : Type*} [Fintype ι] {P : Measure (CoefficientField d Λ)}
    {u : ι → Vec d} (φ : (i : ι) → Corrector P (u i)) (c : ι → ℝ) :
    Corrector P (∑ i, c i • u i) where
  potential a x := ∑ i, c i * (φ i).potential a x
  grad a x := ∑ i, c i • (φ i).grad a x
  measurable_grad := Finset.measurable_fun_sum _ fun i _ => ((φ i).measurable_grad).const_smul (c i)
  weak_gradient := by
    filter_upwards [ae_all_iff.mpr fun i => (φ i).weak_gradient] with a ha
    exact HasWeakGradient.finsetSum _ c fun i _ => ha i
  locally_square_integrable := by
    filter_upwards [ae_all_iff.mpr fun i => (φ i).locally_square_integrable] with a ha R hR
    exact ⟨memLp_finsetSum _ fun i _ => ((ha i R hR).1.const_mul (c i)),
      memLp_finsetSum _ fun i _ => ((ha i R hR).2.const_smul (c i))⟩
  stationary z := by
    filter_upwards [ae_all_iff.mpr fun i => (φ i).stationary z] with a ha
    filter_upwards [ae_all_iff.mpr ha] with x hx
    exact Finset.sum_congr rfl fun i _ => by rw [hx i]
  harmonic := by
    filter_upwards [ae_all_iff.mpr fun i => (φ i).harmonic] with a ha
    have heq : (fun x => (a x).mulVec ((∑ i, c i • u i) + ∑ i, c i • (φ i).grad a x)) =
        fun x => ∑ i, c i • (a x).mulVec (u i + (φ i).grad a x) := by
      funext x
      rw [← Finset.sum_add_distrib, Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← smul_add, Matrix.mulVec_smul]
    rw [heq]
    exact HasWeakDivergence.finsetSum_zero _ c fun i _ => ha i
  sublinear := by
    filter_upwards [ae_all_iff.mpr fun i => (φ i).sublinear,
      ae_all_iff.mpr fun i => (φ i).locally_square_integrable] with a hs hl
    exact tendsto_sublinear_finsetSum c (fun i R hR => (hl i R hR).1) hs

/-- A corrector in the direction `u` as a corrector in an equal direction `e`. -/
def Corrector.ofEq {P : Measure (CoefficientField d Λ)} {u e : Vec d} (φ : Corrector P u)
    (h : u = e) : Corrector P e where
  potential := φ.potential
  grad := φ.grad
  measurable_grad := φ.measurable_grad
  weak_gradient := φ.weak_gradient
  locally_square_integrable := φ.locally_square_integrable
  stationary := φ.stationary
  harmonic := h ▸ φ.harmonic
  sublinear := φ.sublinear

theorem sum_smul_unitVector_eq (e : Vec d) : ∑ i, e i • unitVector i = e := by
  funext k
  simp [unitVector, Pi.single_apply]

/-- Homogenization data whose correctors are the combinations `∑ᵢ eᵢ φ_{eᵢ}` of the correctors of
`S` in the coordinate directions, with the homogenized matrix of `S`. -/
def HomogenizationData.linearize {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) : HomogenizationData P where
  corrector e := (Corrector.linearCombination (fun i : Fin d => S.corrector (unitVector i))
    (fun i => e i)).ofEq (sum_smul_unitVector_eq e)
  homogenized := S.homogenized
  symmetric := S.symmetric
  variational_limit := S.variational_limit

theorem HomogenizationData.linearize_grad {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (e : Vec d) (a : CoefficientField d Λ) (x : Vec d) :
    (S.linearize.corrector e).grad a x = ∑ i, e i • (S.corrector (unitVector i)).grad a x :=
  rfl

theorem HomogenizationData.linearize_grad_unitVector {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (j : Fin d) (a : CoefficientField d Λ) (x : Vec d) :
    (S.linearize.corrector (unitVector j)).grad a x = (S.corrector (unitVector j)).grad a x := by
  rw [linearize_grad]
  simp [unitVector, Pi.single_apply]

end QSH
