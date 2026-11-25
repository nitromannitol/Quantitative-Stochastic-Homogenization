import QuantitativeStochasticHomogenization.Ch01.Sec05.TwoScaleSteps

/-!
# The constants of the proof of Theorem 1.17

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, the bounds of the quantities entering `K₁` of (1.64):

* the boundary layer term (1.63), by Hölder's inequality:
  `‖(1 - η)(a(·/ε) - ā)∇u‖_{L²(U)} ≤ 2Λ ‖∇u‖_{L^q(U)} |{x ∈ U : η(x) ≠ 1}|^{1/2 - 1/q}`
  (`l2_boundaryLayer_le`);
* the derivatives of the multipliers `G_j = η ∂_j ũ` from the bounds of the cutoff and of the
  interior estimates (1.61), as in (1.65) (`abs_multiplier_le`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ} {Λ : ℝ}

theorem coordinateDerivative_add_of_contDiff {f h : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : Fin d) (x : Vec d) :
    coordinateDerivative k (fun y => f y + h y) x =
      coordinateDerivative k f x + coordinateDerivative k h x := by
  unfold coordinateDerivative
  rw [fderiv_fun_add ((hf.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  rfl

theorem coordinateDerivative_eq_zero_of_notMem_tsupport' {f : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport f) (k : Fin d) : coordinateDerivative k f x = 0 :=
  coordinateDerivative_eq_zero_of_notMem_tsupport hx k

theorem tsupport_coordinateDerivative_subset (f : Vec d → ℝ) (k : Fin d) :
    tsupport (coordinateDerivative k f) ⊆ tsupport f := by
  have : coordinateDerivative k f = fun x => fderiv ℝ f x (unitVector k) := rfl
  rw [this]
  exact (tsupport_comp_subset (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) (by simp)
    (fderiv ℝ f)).trans (tsupport_fderiv_subset ℝ)

/-- **The bounds of the multipliers** `G = η f`, `f = ∂_j ũ`. -/
theorem abs_multiplier_le {η f : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {E₁ E₂ B₀ B₁ B₂ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hη1 : ∀ x, |η x| ≤ 1)
    (hηd : ∀ i x, |coordinateDerivative i η x| ≤ E₁)
    (hηdd : ∀ i k x, |coordinateDerivative k (coordinateDerivative i η) x| ≤ E₂)
    (hf0 : ∀ x ∈ tsupport η, |f x| ≤ B₀)
    (hf1 : ∀ x ∈ tsupport η, ∀ i, |coordinateDerivative i f x| ≤ B₁)
    (hf2 : ∀ x ∈ tsupport η, ∀ i k, |coordinateDerivative k (coordinateDerivative i f) x| ≤ B₂) :
    (∀ x, |η x * f x| ≤ B₀) ∧
      (∀ i x, |coordinateDerivative i (fun y => η y * f y) x| ≤ E₁ * B₀ + B₁) ∧
      (∀ i k x, |coordinateDerivative k (coordinateDerivative i (fun y => η y * f y)) x| ≤
        E₂ * B₀ + 2 * (E₁ * B₁) + B₂) := by
  have hsupp : tsupport (fun y => η y * f y) ⊆ tsupport η := tsupport_mul_subset_left
  have hd1 : ∀ i, coordinateDerivative i (fun y => η y * f y) =
      fun y => coordinateDerivative i η y * f y + η y * coordinateDerivative i f y := fun i =>
    funext fun y => coordinateDerivative_mul_of_contDiff hη hf i y
  refine ⟨fun x => ?_, fun i x => ?_, fun i k x => ?_⟩
  · by_cases hx : x ∈ tsupport η
    · rw [abs_mul]
      exact (mul_le_mul (hη1 x) (hf0 x hx) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, abs_zero]; exact hB₀
  · by_cases hx : x ∈ tsupport η
    · rw [hd1 i]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul (hηd i x) (hf0 x hx) (abs_nonneg _) hE₁
      · rw [abs_mul]
        exact (mul_le_mul (hη1 x) (hf1 x hx i) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [coordinateDerivative_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h)) i, abs_zero]
      positivity
  · by_cases hx : x ∈ tsupport η
    · have hηi := contDiff_coordinateDerivative_top hη i
      have hfi := contDiff_coordinateDerivative_top hf i
      rw [hd1 i, coordinateDerivative_add_of_contDiff (hηi.mul hf) (hη.mul hfi),
        coordinateDerivative_mul_of_contDiff hηi hf, coordinateDerivative_mul_of_contDiff hη hfi]
      have t1 : |coordinateDerivative k (coordinateDerivative i η) x * f x| ≤ E₂ * B₀ := by
        rw [abs_mul]; exact mul_le_mul (hηdd i k x) (hf0 x hx) (abs_nonneg _) hE₂
      have t2 : |coordinateDerivative i η x * coordinateDerivative k f x| ≤ E₁ * B₁ := by
        rw [abs_mul]; exact mul_le_mul (hηd i x) (hf1 x hx k) (abs_nonneg _) hE₁
      have t3 : |coordinateDerivative k η x * coordinateDerivative i f x| ≤ E₁ * B₁ := by
        rw [abs_mul]; exact mul_le_mul (hηd k x) (hf1 x hx i) (abs_nonneg _) hE₁
      have t4 : |η x * coordinateDerivative k (coordinateDerivative i f) x| ≤ B₂ := by
        rw [abs_mul]
        exact (mul_le_mul (hη1 x) (hf2 x hx i k) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      calc |coordinateDerivative k (coordinateDerivative i η) x * f x +
            coordinateDerivative i η x * coordinateDerivative k f x +
            (coordinateDerivative k η x * coordinateDerivative i f x +
              η x * coordinateDerivative k (coordinateDerivative i f) x)|
          ≤ |coordinateDerivative k (coordinateDerivative i η) x * f x| +
            |coordinateDerivative i η x * coordinateDerivative k f x| +
            (|coordinateDerivative k η x * coordinateDerivative i f x| +
              |η x * coordinateDerivative k (coordinateDerivative i f) x|) :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
        _ ≤ _ := by linarith
    · have hx' : x ∉ tsupport (coordinateDerivative i (fun y => η y * f y)) := fun h =>
        hx (hsupp (tsupport_coordinateDerivative_subset _ i h))
      rw [coordinateDerivative_eq_zero_of_notMem_tsupport hx' k, abs_zero]
      positivity

theorem euclideanNorm_mulVec_le_of_dot_le {B : Mat d} (hBt : B.transpose = B)
    (hB0 : ∀ ξ, 0 ≤ dot ξ (B.mulVec ξ)) (hΛ : 0 ≤ Λ)
    (hB1 : ∀ ξ, dot ξ (B.mulVec ξ) ≤ Λ * euclideanSq ξ) (v : Vec d) :
    euclideanNorm (B.mulVec v) ≤ Λ * euclideanNorm v := by
  have h := euclideanSq_mulVec_le_of_dot_le hBt hB0 hB1 v
  unfold euclideanNorm
  rw [← Real.sqrt_sq hΛ, ← Real.sqrt_mul (sq_nonneg Λ)]
  exact Real.sqrt_le_sqrt h

theorem euclideanNorm_sub_le' (x y : Vec d) :
    euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y := by
  have h := PDE.vecEuclideanNorm_add_le x (-y)
  rw [← sub_eq_add_neg, PDE.vecEuclideanNorm_neg] at h
  exact h

/-- **The boundary layer term (1.63)** by Hölder's inequality. -/
theorem l2_boundaryLayer_le (hΛ : 1 ≤ Λ) {U : Set (Vec d)} (hUt : volume U ≠ ⊤)
    (b : CoefficientField d Λ) {A : Mat d} (hAt : A.transpose = A)
    (hA0 : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ)) (hA1 : ∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ)
    {η : Vec d → ℝ} (hη : Continuous η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    {g : Vec d → Vec d} (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    {q : ℝ≥0∞} (hq2 : 2 ≤ q) (hgq : MemLp (fun x => euclideanNorm (g x)) q (volume.restrict U))
    (k : Fin d) :
    l2 U (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k) ≤
      2 * Λ * (eLpNorm (fun x => euclideanNorm (g x)) q (volume.restrict U)).toReal *
        (volume.real {x ∈ U | η x ≠ 1}) ^ (1 / 2 - 1 / q.toReal) := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUt
  have hΛ0 : 0 ≤ Λ := by linarith
  set S : Set (Vec d) := {x | η x ≠ 1} with hS
  have hSm : MeasurableSet S := (measurableSet_singleton (1 : ℝ)).compl.preimage hη.measurable
  set F : Vec d → ℝ := fun x => euclideanNorm (g x) with hF
  have hF2 : MemLp F 2 (volume.restrict U) := hgq.mono_exponent hq2
  have hFS : MemLp (S.indicator F) 2 (volume.restrict U) := hF2.indicator hSm
  have hbM : ∀ i, MemLp (fun x => (b x).mulVec (g x) i) 2 (volume.restrict U) := fun i =>
    memLp_coefficient_mulVec_apply b (memLp_pi_iff.2 hg) i
  have hΨ : AEStronglyMeasurable (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k)
      (volume.restrict U) := by
    have h1 := ((hbM k).sub (memLp_const_mulVec A hg k)).aestronglyMeasurable
    have hc : Continuous (fun x => (1 : ℝ) - η x) := continuous_const.sub hη
    exact (hc.aestronglyMeasurable.mul h1).congr
      (Eventually.of_forall fun x => by simp [smul_eq_mul])
  -- the pointwise bound
  have hpt : ∀ x, |((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k| ≤
      (2 * Λ) * |S.indicator F x| := by
    intro x
    by_cases hx : η x = 1
    · simp only [hx, sub_self, zero_smul, Pi.zero_apply, abs_zero]
      exact mul_nonneg (by linarith) (abs_nonneg _)
    · have hxS : x ∈ S := hx
      rw [Set.indicator_of_mem hxS, abs_of_nonneg (show 0 ≤ F x from Real.sqrt_nonneg _)]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      have h1 : |1 - η x| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hη01 x]
      have h2 : |((b x).mulVec (g x) - A.mulVec (g x)) k| ≤ 2 * Λ * euclideanNorm (g x) := by
        refine (abs_apply_le_sqrt_euclideanSq _ k).trans ?_
        refine (euclideanNorm_sub_le' _ _).trans ?_
        have hb := euclideanNorm_mulVec_le_of_dot_le (b.symmetric x) (fun ξ => by
          have := (b.elliptic x ξ).1
          have h0 : 0 ≤ euclideanSq ξ := by
            unfold euclideanSq dot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
          linarith) hΛ0 (fun ξ => (b.elliptic x ξ).2) (g x)
        have hA := euclideanNorm_mulVec_le_of_dot_le hAt hA0 hΛ0 hA1 (g x)
        change euclideanNorm _ + euclideanNorm _ ≤ _
        linarith
      calc |1 - η x| * |((b x).mulVec (g x) - A.mulVec (g x)) k|
          ≤ 1 * (2 * Λ * euclideanNorm (g x)) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 2 * Λ * euclideanNorm (g x) := one_mul _
  have hstep1 := l2_le_mul hΨ hFS (by positivity) hpt
  -- Hölder on `S ∩ U`
  have hres : eLpNorm (S.indicator F) 2 (volume.restrict U) =
      eLpNorm F 2 (volume.restrict (S ∩ U)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hSm, Measure.restrict_restrict hSm]
  have hhold := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (S ∩ U)) hq2
    (hF2.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
  have hmono : eLpNorm F q (volume.restrict (S ∩ U)) ≤ eLpNorm F q (volume.restrict U) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_right le_rfl)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hhold
  have hSU : volume (S ∩ U) ≠ ⊤ := measure_ne_top_of_subset inter_subset_right hUt
  have he : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / q.toReal := by
    rcases eq_or_ne q ⊤ with hqt | hqt
    · simp [hqt]
    · have hq2' : (2 : ℝ) ≤ q.toReal := by
        have := ENNReal.toReal_mono hqt hq2
        simpa using this
      have : (0 : ℝ) < 2 := by norm_num
      simp only [ENNReal.toReal_ofNat]
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le this hq2'
  have hfin : volume (S ∩ U) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / q.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg he hSU
  have hall : l2 U (S.indicator F) ≤
      (eLpNorm F q (volume.restrict U)).toReal *
        (volume (S ∩ U)).toReal ^ (1 / 2 - 1 / q.toReal) := by
    unfold l2
    rw [hres]
    have h1 := hhold.trans (mul_le_mul_left hmono _ |>.trans_eq (mul_comm _ _) |>.trans_eq
      (mul_comm _ _))
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hgq.eLpNorm_ne_top hfin) h1
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at h2
    simpa using h2
  have hvol : volume.real {x ∈ U | η x ≠ 1} = (volume (S ∩ U)).toReal := by
    have : {x ∈ U | η x ≠ 1} = S ∩ U := by
      ext x; simp [hS, and_comm]
    rw [this, measureReal_def]
  rw [hvol]
  calc l2 U (fun x => ((1 - η x) • ((b x).mulVec (g x) - A.mulVec (g x))) k)
      ≤ 2 * Λ * l2 U (S.indicator F) := hstep1
    _ ≤ 2 * Λ * ((eLpNorm F q (volume.restrict U)).toReal *
          (volume (S ∩ U)).toReal ^ (1 / 2 - 1 / q.toReal)) :=
        mul_le_mul_of_nonneg_left hall (by positivity)
    _ = _ := by ring

end TwoScale

end QSH
