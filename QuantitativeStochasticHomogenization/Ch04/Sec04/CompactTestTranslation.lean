import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestProfile
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakCongruence
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct
import QuantitativeStochasticHomogenization.Ch04.Sec04.HarmonicPairSpace
import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification

/-!
# The translation estimate for functions with a weak gradient on a ball

The segment translation inequality of the finite-ball estimate of the
proof of Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*: if `v` has the weak gradient `g` on `B_R` with `v, g ∈ L²(B_R)` and
`t + |h| ≤ R`, then
`∫_{B_t} (v(x - h) - v(x))² ≤ |h|² ∫_{B_{t+|h|}} |g|²`.

The proof identifies `v(x - h) - v(x)` with `-∫₀¹ h · g(x - θh) dθ` almost everywhere on `B_t`:
both have the same integral against every smooth test `φ` in `B_t`, since
`θ ↦ ∫ v(y) φ(y + θh) dy` has derivative `-∫ h · g(y) φ(y + θh) dy` by the definition of the weak
gradient. Jensen's inequality on `[0, 1]` and Fubini's theorem give the bound.
-/

open MeasureTheory Filter Set
open scoped ContDiff Interval

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The segment average `W(x) = -∫₀¹ h · G(x - θh) dθ`. -/
def translationSegmentAverage (G : Vec d → Vec d) (h x : Vec d) : ℝ :=
  -∫ θ in (0 : ℝ)..1, dot h (G (x - θ • h))

theorem setIntegral_ball_comp_sub' (F : Vec d → ℝ) (z y : Vec d) (r : ℝ) :
    ∫ x in ball z r, F (x - y) = ∫ u in ball (z - y) r, F u := by
  rw [← integral_indicator (measurableSet_ball z r),
    ← integral_indicator (measurableSet_ball (z - y) r)]
  have h := integral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun u => (ball (z - y) r).indicator F u) y
  rw [← h]
  congr 1
  funext x
  have hmem : x - y ∈ ball (z - y) r ↔ x ∈ ball z r := by
    show euclideanNorm (x - y - (z - y)) < r ↔ euclideanNorm (x - z) < r
    rw [sub_sub_sub_cancel_right]
  by_cases hx : x ∈ ball z r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]

theorem coordinateDerivative_comp_add_right' (i : Fin d) (ψ : Vec d → ℝ) (y u : Vec d) :
    coordinateDerivative i (fun u => ψ (u + y)) u = coordinateDerivative i ψ (u + y) := by
  unfold coordinateDerivative
  rw [fderiv_comp_add_right]

theorem euclideanNorm_sub_smul_le (x h : Vec d) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    euclideanNorm (x - θ • h) ≤ euclideanNorm x + euclideanNorm h := by
  have h1 := euclideanNorm_add_le x ((-θ) • h)
  rw [euclideanNorm_smul_abs, abs_neg, abs_of_nonneg hθ.1] at h1
  have e : x + (-θ) • h = x - θ • h := by rw [neg_smul, sub_eq_add_neg]
  rw [e] at h1
  have : θ * euclideanNorm h ≤ euclideanNorm h :=
    mul_le_of_le_one_left (Real.sqrt_nonneg _) hθ.2
  linarith

theorem memLp_mono_set' {U V : Set (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict V))
    (hUV : U ⊆ V) : MemLp f 2 (volume.restrict U) :=
  hf.mono_measure (Measure.restrict_mono hUV le_rfl)

theorem sq_dot_le' (x y : Vec d) : dot x y ^ 2 ≤ euclideanSq x * euclideanSq y :=
  calc dot x y ^ 2 = (∑ i, x i * y i) ^ 2 := rfl
    _ ≤ (∑ i, x i ^ 2) * ∑ i, y i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = euclideanSq x * euclideanSq y := by simp only [euclideanSq, dot, sq]

theorem abs_dot_le_sum (h y : Vec d) : |dot h y| ≤ euclideanNorm h * ∑ i, |y i| := by
  unfold dot
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_apply_le_euclideanNorm h i) (abs_nonneg _) |>.trans_eq
    (mul_comm _ _) |>.trans_eq (by ring)

/-- The test shifted by `θ h` is a test in `B_R`. -/
theorem isSpatialTest_comp_add_smul {t R : ℝ} {h : Vec d} (htR : t + euclideanNorm h ≤ R)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball 0 t) φ) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    IsSpatialTest (ball 0 R) (fun y => φ (y + θ • h)) := by
  refine ⟨hφ.1.comp (contDiff_id.add contDiff_const),
    hφ.2.1.comp_homeomorph (Homeomorph.addRight (θ • h)), ?_⟩
  have e := tsupport_comp_eq_preimage φ (Homeomorph.addRight (θ • h))
  change tsupport (φ ∘ (Homeomorph.addRight (θ • h))) ⊆ _
  rw [e]
  intro y hy
  have hy' : y + θ • h ∈ ball (0 : Vec d) t := hφ.2.2 hy
  have h1 : euclideanNorm (y + θ • h) < t := by simpa [ball] using hy'
  have h2 := euclideanNorm_sub_smul_le (y + θ • h) h hθ
  rw [add_sub_cancel_right] at h2
  show euclideanNorm (y - 0) < R
  rw [sub_zero]
  linarith

/-- The translated gradient paired with `h` and a bounded continuous function is integrable in
`(θ, x)` over `(0, 1] × ℝ^d`. -/
theorem integrable_dot_translate_mul {G : Vec d → Vec d} (hGm : Measurable G)
    (hGi : ∀ i, Integrable (fun x => G x i)) (h : Vec d) {φ : Vec d → ℝ} (hφ : Continuous φ)
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    Integrable (fun q : ℝ × Vec d => dot h (G (q.2 - q.1 • h)) * φ q.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
  have hmap : Measurable fun q : ℝ × Vec d => q.2 - q.1 • h :=
    (measurable_snd.sub (measurable_fst.smul measurable_const))
  have hm : AEStronglyMeasurable (fun q : ℝ × Vec d => dot h (G (q.2 - q.1 • h)) * φ q.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
    refine (Measurable.mul ?_ (hφ.measurable.comp measurable_snd)).aestronglyMeasurable
    unfold dot
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      ((measurable_pi_apply i).comp (hGm.comp hmap))
  set B : ℝ × Vec d → ℝ := fun q => euclideanNorm h * C * ∑ i, |G (q.2 - q.1 • h) i| with hB
  have hBint : Integrable B ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
    have hBm : AEStronglyMeasurable B ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) :=
      (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp (hGm.comp hmap)).abs)).aestronglyMeasurable
    refine (integrable_prod_iff hBm).mpr ⟨Eventually.of_forall fun θ => ?_, ?_⟩
    · exact (integrable_finsetSum _ fun i _ => ((hGi i).comp_sub_right (θ • h)).abs).const_mul _
    · have e : ∀ θ : ℝ, ∫ x, ‖B (θ, x)‖ = euclideanNorm h * |C| * ∑ i, ∫ x, |G x i| := fun θ => by
        have hint : ∀ i, Integrable (fun x => |G (x - θ • h) i|) := fun i =>
          ((hGi i).comp_sub_right (θ • h)).abs
        have hpt : ∀ x, ‖B (θ, x)‖ = euclideanNorm h * |C| * ∑ i, |G (x - θ • h) i| := fun x => by
          simp only [hB]
          rw [Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ euclideanNorm h from Real.sqrt_nonneg _),
            abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (G (x - θ • h) i) :
              (0 : ℝ) ≤ ∑ i, |G (x - θ • h) i|)]
        rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
          integral_finsetSum Finset.univ fun i _ => hint i]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_sub_right_eq_self (fun x => |G x i|) (θ • h)
      simp only [e]
      exact integrable_const _
  refine Integrable.mono' hBint hm (Eventually.of_forall fun q => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  calc |dot h (G (q.2 - q.1 • h))| * ‖φ q.2‖
      ≤ (euclideanNorm h * ∑ i, |G (q.2 - q.1 • h) i|) * C :=
        mul_le_mul (abs_dot_le_sum _ _) (hC _) (norm_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    _ = B q := by simp only [hB]; ring

/-- **The test identity** for the translation: for a test `φ` in `B_t`,
`∫ (F(x - h) - F(x)) φ(x) = ∫ W(x) φ(x)` with the segment average `W` of the zero extension of
the gradient. -/
theorem integral_translate_sub_mul_eq {R t : ℝ} {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : IntegrableOn v (ball 0 R)) (hGm : Measurable G)
    (hG : ∀ i, IntegrableOn (fun x => G x i) (ball 0 R))
    (hw : HasWeakGradient (ball 0 R) v G) {h : Vec d} (htR : t + euclideanNorm h ≤ R)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball 0 t) φ) :
    ∫ x, ((ball 0 R).indicator v (x - h) - (ball 0 R).indicator v x) * φ x =
      ∫ x, translationSegmentAverage ((ball 0 R).indicator G) h x * φ x := by
  set F := (ball (0 : Vec d) R).indicator v with hFdef
  set G' := (ball (0 : Vec d) R).indicator G with hG'def
  have hF : Integrable F := (integrable_indicator_iff (measurableSet_ball _ _)).mpr hv
  have hG'm : Measurable G' := hGm.indicator (measurableSet_ball _ _)
  have hG'i : ∀ i, Integrable (fun x => G' x i) := fun i => by
    have : (fun x => G' x i) = (ball (0 : Vec d) R).indicator (fun x => G x i) := by
      funext x
      by_cases hx : x ∈ ball (0 : Vec d) R <;> simp [hG'def, hx]
    rw [this]
    exact (integrable_indicator_iff (measurableSet_ball _ _)).mpr (hG i)
  have hφc : Continuous φ := hφ.1.continuous
  obtain ⟨Mφ, hMφ⟩ := hφc.bounded_above_of_compact_support hφ.2.1
  have hdφ : ∀ i, Continuous (coordinateDerivative i φ) := fun i =>
    (contDiff_coordinateDerivative hφ.1 i).continuous
  have hdφc : ∀ i, HasCompactSupport (coordinateDerivative i φ) := fun i =>
    hasCompactSupport_coordinateDerivative hφ.2.1 i
  choose Md hMd using fun i => (hdφ i).bounded_above_of_compact_support (hdφc i)
  -- the function ψ(θ) = ∫ F(y) φ(y + θh) dy and its derivative
  set ψ : ℝ → ℝ := fun θ => ∫ y, F y * φ (y + θ • h) with hψ
  set ψ' : ℝ → ℝ := fun θ => ∫ y, F y * ∑ i, h i * coordinateDerivative i φ (y + θ • h)
    with hψ'
  have hMd0 : 0 ≤ ∑ i, |h i| * Md i := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) ((norm_nonneg _).trans (hMd i 0))
  have hderiv : ∀ θ, HasDerivAt ψ (ψ' θ) θ := by
    intro θ
    have hmeas : ∀ θ : ℝ, AEStronglyMeasurable (fun y => F y * φ (y + θ • h)) volume := fun θ =>
      hF.aestronglyMeasurable.mul (hφc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    have hint : Integrable (fun y => F y * φ (y + θ • h)) := by
      refine Integrable.mono' (hF.norm.mul_const Mφ) (hmeas θ) (Eventually.of_forall fun y => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMφ _) (norm_nonneg _)
    have hm' : AEStronglyMeasurable (fun y => F y * ∑ i, h i * coordinateDerivative i φ
        (y + θ • h)) volume :=
      hF.aestronglyMeasurable.mul (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((hdφ i).comp (continuous_id.add continuous_const))).aestronglyMeasurable
    have hbound : ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ θ' ∈ (Set.univ : Set ℝ),
        ‖F y * ∑ i, h i * coordinateDerivative i φ (y + θ' • h)‖ ≤
          ‖F y‖ * ∑ i, |h i| * Md i := by
      refine Eventually.of_forall fun y θ' _ => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMd i _) (abs_nonneg _)
    have hdiff : ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ θ' ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun θ => F y * φ (y + θ • h))
          (F y * ∑ i, h i * coordinateDerivative i φ (y + θ' • h)) θ' := by
      refine Eventually.of_forall fun y θ' _ => ?_
      have h1 : HasDerivAt (fun θ : ℝ => y + θ • h) h θ' := by
        simpa using ((hasDerivAt_id θ').smul_const h).const_add y
      have h2 := ((hφ.1.differentiable (by simp)) (y + θ' • h)).hasFDerivAt.comp_hasDerivAt θ' h1
      rw [fderiv_apply_eq_sum_coordinateDerivative] at h2
      exact h2.const_mul (F y)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le Filter.univ_mem
      (Eventually.of_forall hmeas) hint hm' hbound (hF.norm.mul_const _) hdiff).2
  have hcont : Continuous ψ' := by
    refine continuous_of_dominated (bound := fun y => ‖F y‖ * ∑ i, |h i| * Md i)
      (fun θ => hF.aestronglyMeasurable.mul (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((hdφ i).comp (continuous_id.add continuous_const))).aestronglyMeasurable)
      (fun θ => Eventually.of_forall fun y => ?_) (hF.norm.mul_const _)
      (Eventually.of_forall fun y => ?_)
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMd i _) (abs_nonneg _)
    · exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((hdφ i).comp (continuous_const.add (continuous_id.smul continuous_const))))
  have hftc : ψ 1 - ψ 0 = ∫ θ in (0 : ℝ)..1, ψ' θ :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      (hcont.intervalIntegrable 0 1)).symm
  -- the left side
  have hL : ∫ x, (F (x - h) - F x) * φ x = ψ 1 - ψ 0 := by
    have i1 : Integrable (fun x => F (x - h) * φ x) := by
      refine Integrable.mono' ((hF.comp_sub_right h).norm.mul_const Mφ)
        ((hF.comp_sub_right h).aestronglyMeasurable.mul hφc.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMφ _) (norm_nonneg _)
    have i2 : Integrable (fun x => F x * φ x) := by
      refine Integrable.mono' (hF.norm.mul_const Mφ)
        (hF.aestronglyMeasurable.mul hφc.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMφ _) (norm_nonneg _)
    have e1 : ψ 1 = ∫ x, F (x - h) * φ x := by
      simp only [hψ, one_smul]
      rw [← integral_add_right_eq_self (fun x => F (x - h) * φ x) h]
      simp only [add_sub_cancel_right]
    have e0 : ψ 0 = ∫ x, F x * φ x := by simp [hψ]
    rw [e1, e0, ← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  -- the derivative through the weak gradient
  have hψ'eq : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ψ' θ = -∫ y, ∑ i, h i * (G' y i * φ (y + θ • h)) := by
    intro θ hθ
    have htest := isSpatialTest_comp_add_smul htR hφ hθ
    have hw' : ∀ i, ∫ y, F y * coordinateDerivative i φ (y + θ • h) =
        -∫ y, G' y i * φ (y + θ • h) := fun i => by
      have h1 := (hw i).2.2 _ htest
      simp only [coordinateDerivative_comp_add_right'] at h1
      have e1 : ∫ y in ball 0 R, v y * coordinateDerivative i φ (y + θ • h) =
          ∫ y, F y * coordinateDerivative i φ (y + θ • h) := by
        rw [← integral_indicator (measurableSet_ball _ _)]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ ball (0 : Vec d) R <;> simp [hFdef, hy]
      have e2 : ∫ y in ball 0 R, G y i * φ (y + θ • h) = ∫ y, G' y i * φ (y + θ • h) := by
        rw [← integral_indicator (measurableSet_ball _ _)]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ ball (0 : Vec d) R <;> simp [hG'def, hy]
      rw [← e1, ← e2]
      exact h1
    have hint : ∀ i, Integrable (fun y => F y * (h i * coordinateDerivative i φ (y + θ • h))) :=
      fun i => by
        refine Integrable.mono' (hF.norm.mul_const (|h i| * Md i))
          (hF.aestronglyMeasurable.mul (continuous_const.mul ((hdφ i).comp
            (continuous_id.add continuous_const))).aestronglyMeasurable)
          (Eventually.of_forall fun y => ?_)
        rw [norm_mul, norm_mul, Real.norm_eq_abs (h i)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMd i _) (abs_nonneg _))
          (norm_nonneg _)
    have hint2 : ∀ i, Integrable (fun y => h i * (G' y i * φ (y + θ • h))) := fun i => by
      refine Integrable.mono' (((hG'i i).norm.mul_const Mφ).const_mul |h i|)
        (aestronglyMeasurable_const.mul ((hG'i i).aestronglyMeasurable.mul
          (hφc.comp (continuous_id.add continuous_const)).aestronglyMeasurable))
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, norm_mul, Real.norm_eq_abs (h i)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMφ _) (norm_nonneg _))
        (abs_nonneg _)
    simp only [hψ', Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hint i, integral_finsetSum _ fun i _ => hint2 i,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun y => F y * (h i * coordinateDerivative i φ (y + θ • h))) =
        fun y => h i * (F y * coordinateDerivative i φ (y + θ • h)) := by funext y; ring
    rw [e, integral_const_mul, hw' i, integral_const_mul]
    ring
  -- the right side by translation and Fubini
  set P : ℝ × Vec d → ℝ := fun q => dot h (G' (q.2 - q.1 • h)) * φ q.2 with hPdef
  have hPint := integrable_dot_translate_mul hG'm hG'i h hφc (C := Mφ) hMφ
  have hR : ∫ θ in (0 : ℝ)..1, ψ' θ = ∫ x, translationSegmentAverage G' h x * φ x := by
    have e1 : ∫ θ in (0 : ℝ)..1, ψ' θ = ∫ θ in (0 : ℝ)..1, -∫ x, P (θ, x) := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [Set.uIcc_of_le zero_le_one] at hθ
      rw [hψ'eq θ hθ]
      congr 1
      rw [← integral_sub_right_eq_self (fun y => ∑ i, h i * (G' y i * φ (y + θ • h))) (θ • h)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hPdef, sub_add_cancel, dot]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, intervalIntegral.integral_neg, intervalIntegral.integral_of_le zero_le_one,
      integral_integral_swap hPint]
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hPdef, translationSegmentAverage, intervalIntegral.integral_of_le zero_le_one]
    rw [integral_mul_const]
    ring
  rw [hL, hftc, hR]

/-- The squared translated gradient is integrable in `(θ, x)` over `(0, 1] × ℝ^d`. -/
theorem integrable_euclideanSq_translate {G : Vec d → Vec d} (hGm : Measurable G)
    (hG2 : ∀ i, Integrable (fun x => G x i ^ 2)) (h : Vec d) :
    Integrable (fun q : ℝ × Vec d => euclideanSq (G (q.2 - q.1 • h)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
  have hmap : Measurable fun q : ℝ × Vec d => q.2 - q.1 • h :=
    (measurable_snd.sub (measurable_fst.smul measurable_const))
  have hm : AEStronglyMeasurable (fun q : ℝ × Vec d => euclideanSq (G (q.2 - q.1 • h)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold euclideanSq dot
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hGm.comp hmap)).mul ((measurable_pi_apply i).comp (hGm.comp hmap))
  refine (integrable_prod_iff hm).mpr ⟨Eventually.of_forall fun θ => ?_, ?_⟩
  · have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      (hG2 i).comp_sub_right (θ • h)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [euclideanSq, dot, sq]
  · have e : ∀ θ : ℝ, ∫ x, ‖euclideanSq (G (x - θ • h))‖ = ∑ i, ∫ x, G x i ^ 2 := fun θ => by
      have hint : ∀ i, Integrable (fun x => G (x - θ • h) i ^ 2) := fun i =>
        (hG2 i).comp_sub_right (θ • h)
      have e1 : (fun x => ‖euclideanSq (G (x - θ • h))‖) = fun x => ∑ i, G (x - θ • h) i ^ 2 := by
        funext x
        rw [Real.norm_of_nonneg (zero_le_euclideanSq _)]
        simp [euclideanSq, dot, sq]
      rw [e1, integral_finsetSum _ fun i _ => hint i]
      exact Finset.sum_congr rfl fun i _ => integral_sub_right_eq_self (fun x => G x i ^ 2) (θ • h)
    simp only [e]
    exact integrable_const _

/-- Jensen's inequality on `(0, 1]`: `(∫ f)² ≤ ∫ f²`. -/
theorem sq_setIntegral_Ioc_le {f : ℝ → ℝ} (hf : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hf2 : Integrable (fun θ => f θ ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (∫ θ in Set.Ioc (0 : ℝ) 1, f θ) ^ 2 ≤ ∫ θ in Set.Ioc (0 : ℝ) 1, f θ ^ 2 := by
  have h1 : ∫ _θ in Set.Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by simp
  have hi1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    integrable_const _
  have h := sq_integral_mul_le (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)) (g := f)
    (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) h1 hi1 (by simpa using hf) (by simpa using hf2)
  simpa using h

/-- **Almost everywhere identity of the translation** with the segment average. -/
theorem ae_translate_sub_eq {R t : ℝ} {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : IntegrableOn v (ball 0 R)) (hGm : Measurable G)
    (hG : ∀ i, IntegrableOn (fun x => G x i) (ball 0 R))
    (hw : HasWeakGradient (ball 0 R) v G) {h : Vec d} (htR : t + euclideanNorm h ≤ R) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ ball 0 t →
      (ball 0 R).indicator v (x - h) - (ball 0 R).indicator v x =
        translationSegmentAverage ((ball 0 R).indicator G) h x := by
  set F := (ball (0 : Vec d) R).indicator v with hFdef
  set G' := (ball (0 : Vec d) R).indicator G with hG'def
  have hF : Integrable F := (integrable_indicator_iff (measurableSet_ball _ _)).mpr hv
  have hG'm : Measurable G' := hGm.indicator (measurableSet_ball _ _)
  have hG'i : ∀ i, Integrable (fun x => G' x i) := fun i => by
    have : (fun x => G' x i) = (ball (0 : Vec d) R).indicator (fun x => G x i) := by
      funext x
      by_cases hx : x ∈ ball (0 : Vec d) R <;> simp [hG'def, hx]
    rw [this]
    exact (integrable_indicator_iff (measurableSet_ball _ _)).mpr (hG i)
  have hP1 := integrable_dot_translate_mul hG'm hG'i h (φ := fun _ => (1 : ℝ)) continuous_const
    (C := 1) (fun _ => by simp)
  have hW : Integrable (translationSegmentAverage G' h) := by
    have := hP1.integral_prod_right.neg
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [translationSegmentAverage, intervalIntegral.integral_of_le zero_le_one]
  set f : Vec d → ℝ := fun x => F (x - h) - F x - translationSegmentAverage G' h x with hf
  have hfi : Integrable f := ((hF.comp_sub_right h).sub hF).sub hW
  have h0 := (isOpen_ball (0 : Vec d) t).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := f) (hfi.locallyIntegrable.locallyIntegrableOn _) fun g hg hgc hgs => by
      have htest : IsSpatialTest (ball 0 t) g := ⟨hg, hgc, hgs⟩
      have hid := integral_translate_sub_mul_eq hv hGm hG hw htR htest
      obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
      have i1 : Integrable (fun x => (F (x - h) - F x) * g x) :=
        Integrable.mono' (((hF.comp_sub_right h).sub hF).norm.mul_const Mg)
          (((hF.comp_sub_right h).sub hF).aestronglyMeasurable.mul hg.continuous.aestronglyMeasurable)
          (Eventually.of_forall fun x => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMg x) (norm_nonneg _))
      have i2 : Integrable (fun x => translationSegmentAverage G' h x * g x) :=
        Integrable.mono' (hW.norm.mul_const Mg)
          (hW.aestronglyMeasurable.mul hg.continuous.aestronglyMeasurable)
          (Eventually.of_forall fun x => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMg x) (norm_nonneg _))
      have e : (fun x => g x • f x) = fun x => (F (x - h) - F x) * g x -
          translationSegmentAverage G' h x * g x := by
        funext x; simp only [hf, smul_eq_mul]; ring
      rw [e, integral_sub i1 i2, hid, sub_self]
  filter_upwards [h0] with x hx hxt
  have := hx hxt
  simp only [hf] at this
  linarith

/-- **The translation estimate** for a function with a weak gradient on `B_R`:
`∫_{B_t} (v(x - h) - v(x))² ≤ |h|² ∫_{B_{t+|h|}} |g|²` for `t + |h| ≤ R`. -/
theorem integral_sq_translate_sub_le {R t : ℝ} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (ball 0 R)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R)))
    (hw : HasWeakGradient (ball 0 R) v g) {h : Vec d} (htR : t + euclideanNorm h ≤ R) :
    ∫ x in ball 0 t, (v (x - h) - v x) ^ 2 ≤
      euclideanSq h * ∫ x in ball 0 (t + euclideanNorm h), euclideanSq (g x) := by
  classical
  -- a measurable version of the gradient
  choose G₀ hG₀m hG₀e using fun i => (hg i).aestronglyMeasurable
  set G : Vec d → Vec d := fun x i => G₀ i x with hGdef
  have hGm : Measurable G := measurable_pi_iff.mpr fun i => (hG₀m i).measurable
  have hGg : G =ᵐ[volume.restrict (ball 0 R)] g := by
    filter_upwards [ae_all_iff.2 hG₀e] with x hx
    funext i
    exact (hx i).symm
  have hwG : HasWeakGradient (ball 0 R) v G :=
    hasWeakGradient_congr_ae (isOpen_ball 0 R) hw (ae_eq_refl _) hGg.symm
  have hGL2 : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict (ball 0 R)) := fun i =>
    (hg i).ae_eq (hGg.mono fun x hx => (congrFun hx i).symm)
  have hvi : IntegrableOn v (ball 0 R) := hv.integrable one_le_two
  have hGi : ∀ i, IntegrableOn (fun x => G x i) (ball 0 R) := fun i =>
    (hGL2 i).integrable one_le_two
  set F := (ball (0 : Vec d) R).indicator v with hFdef
  set G' := (ball (0 : Vec d) R).indicator G with hG'def
  have hG'm : Measurable G' := hGm.indicator (measurableSet_ball _ _)
  have hG'comp : ∀ i, (fun x => G' x i) = (ball (0 : Vec d) R).indicator (fun x => G x i) :=
    fun i => by
      funext x
      by_cases hx : x ∈ ball (0 : Vec d) R <;> simp [hG'def, hx]
  have hG'i : ∀ i, Integrable (fun x => G' x i) := fun i => by
    rw [hG'comp i]
    exact (integrable_indicator_iff (measurableSet_ball _ _)).mpr (hGi i)
  have hG'2 : ∀ i, Integrable (fun x => G' x i ^ 2) := fun i => by
    have e : (fun x => G' x i ^ 2) = (ball (0 : Vec d) R).indicator (fun x => G x i ^ 2) := by
      funext x
      by_cases hx : x ∈ ball (0 : Vec d) R <;> simp [hG'def, hx]
    rw [e]
    exact (integrable_indicator_iff (measurableSet_ball _ _)).mpr (hGL2 i).integrable_sq
  -- the identity on `B_t`
  have hae := ae_translate_sub_eq hvi hGm hGi hwG htR
  have hxR : ∀ x ∈ ball (0 : Vec d) t, x ∈ ball (0 : Vec d) R ∧ x - h ∈ ball (0 : Vec d) R :=
    fun x hx => by
      have hx' : euclideanNorm x < t := by simpa [ball] using hx
      have h1 := euclideanNorm_sub_smul_le x h (θ := 1) ⟨zero_le_one, le_rfl⟩
      rw [one_smul] at h1
      have hn : 0 ≤ euclideanNorm h := Real.sqrt_nonneg _
      refine ⟨?_, ?_⟩ <;> simp only [ball, Set.mem_ofPred_eq, sub_zero]
      · linarith
      · linarith
  have heq : ∫ x in ball 0 t, (v (x - h) - v x) ^ 2 =
      ∫ x in ball 0 t, translationSegmentAverage G' h x ^ 2 := by
    refine setIntegral_congr_ae (measurableSet_ball _ _) ?_
    filter_upwards [hae] with x hx hxt
    rw [← hx hxt, Set.indicator_of_mem (hxR x hxt).2, Set.indicator_of_mem (hxR x hxt).1]
  rw [heq]
  -- Jensen on the segment
  set Q : ℝ × Vec d → ℝ := fun q => euclideanSq (G' (q.2 - q.1 • h)) with hQdef
  have hQint : Integrable Q ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) :=
    integrable_euclideanSq_translate hG'm hG'2 h
  have hP1 := integrable_dot_translate_mul hG'm hG'i h (φ := fun _ => (1 : ℝ)) continuous_const
    (C := 1) (fun _ => by simp)
  have hpt : ∀ᵐ x ∂(volume : Measure (Vec d)),
      translationSegmentAverage G' h x ^ 2 ≤ euclideanSq h * ∫ θ in Set.Ioc (0 : ℝ) 1, Q (θ, x) := by
    filter_upwards [hQint.prod_left_ae, hP1.prod_left_ae] with x hQx hPx
    have hPx' : Integrable (fun θ : ℝ => dot h (G' (x - θ • h)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      simpa using hPx
    have hP2 : Integrable (fun θ : ℝ => dot h (G' (x - θ • h)) ^ 2)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      refine Integrable.mono' (hQx.const_mul (euclideanSq h)) (hPx'.aestronglyMeasurable.pow 2)
        (Eventually.of_forall fun θ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_dot_le' _ _
    have hS : translationSegmentAverage G' h x = -∫ θ in Set.Ioc (0 : ℝ) 1, dot h (G' (x - θ • h)) := by
      simp [translationSegmentAverage, intervalIntegral.integral_of_le zero_le_one]
    rw [hS, neg_sq]
    refine (sq_setIntegral_Ioc_le hPx' hP2).trans ?_
    rw [← integral_const_mul]
    exact integral_mono hP2 (hQx.const_mul _) fun θ => sq_dot_le' _ _
  -- Fubini and the translation of the ball
  have hQt : ∀ θ ∈ Set.Ioc (0 : ℝ) 1, ∫ x in ball 0 t, Q (θ, x) ≤
      ∫ x in ball 0 (t + euclideanNorm h), euclideanSq (g x) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2⟩
    have hint : Integrable (fun x => euclideanSq (G' x)) := by
      have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hG'2 i
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [euclideanSq, dot, sq]
    rw [show (fun x => Q (θ, x)) = fun x => euclideanSq (G' (x - θ • h)) from rfl,
      setIntegral_ball_comp_sub' (fun u => euclideanSq (G' u)) 0 (θ • h) t]
    have hsub : ball (0 - θ • h) t ⊆ ball (0 : Vec d) (t + euclideanNorm h) := by
      intro y hy
      have hy' : euclideanNorm (y - (0 - θ • h)) < t := hy
      have h1 := euclideanNorm_sub_smul_le (y - (0 - θ • h)) h hθ'
      have e : y - (0 - θ • h) - θ • h = y := by abel
      rw [e] at h1
      change euclideanNorm (y - 0) < _
      rw [sub_zero]
      linarith
    have hRsub : ball (0 : Vec d) (t + euclideanNorm h) ⊆ ball 0 R := fun y hy =>
      lt_of_lt_of_le hy htR
    refine (setIntegral_mono_set hint.integrableOn (Eventually.of_forall fun _ =>
      zero_le_euclideanSq _) hsub.eventuallyLE).trans (le_of_eq ?_)
    refine setIntegral_congr_ae (measurableSet_ball _ _) ?_
    filter_upwards [ae_imp_of_ae_restrict hGg] with x hx hxB
    rw [hG'def, Set.indicator_of_mem (hRsub hxB), hx (hRsub hxB)]
  have hIQ : Integrable (fun x => ∫ θ in Set.Ioc (0 : ℝ) 1, Q (θ, x)) := hQint.integral_prod_right
  have hWm : AEStronglyMeasurable (translationSegmentAverage G' h) volume := by
    refine hP1.integral_prod_right.neg.aestronglyMeasurable.congr (Eventually.of_forall fun x => ?_)
    simp [translationSegmentAverage, intervalIntegral.integral_of_le zero_le_one]
  have hW2 : IntegrableOn (fun x => translationSegmentAverage G' h x ^ 2) (ball 0 t) :=
    Integrable.mono' (hIQ.const_mul (euclideanSq h)).integrableOn (hWm.pow 2).restrict
      (ae_restrict_of_ae (hpt.mono fun x hx => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hx))
  set Qt : ℝ × Vec d → ℝ := fun q => (ball (0 : Vec d) t).indicator (fun x => Q (q.1, x)) q.2
    with hQtdef
  have hQtint : Integrable Qt ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
    have hmeas : AEStronglyMeasurable Qt ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
      have : Qt = (Prod.snd ⁻¹' ball (0 : Vec d) t).indicator Q := by
        funext q
        by_cases hq : q.2 ∈ ball (0 : Vec d) t <;> simp [hQtdef, hq, Set.indicator]
      rw [this]
      exact hQint.aestronglyMeasurable.indicator ((measurableSet_ball _ _).preimage measurable_snd)
    refine Integrable.mono' hQint hmeas (Eventually.of_forall fun q => ?_)
    by_cases hq : q.2 ∈ ball (0 : Vec d) t
    · simp [hQtdef, hq, Real.norm_of_nonneg (zero_le_euclideanSq _), hQdef]
    · simp [hQtdef, hq, hQdef, zero_le_euclideanSq]
  have hswap : ∫ x in ball 0 t, ∫ θ in Set.Ioc (0 : ℝ) 1, Q (θ, x) =
      ∫ θ in Set.Ioc (0 : ℝ) 1, ∫ x in ball 0 t, Q (θ, x) := by
    rw [← integral_indicator (measurableSet_ball _ _)]
    have e : (ball (0 : Vec d) t).indicator (fun x => ∫ θ in Set.Ioc (0 : ℝ) 1, Q (θ, x)) =
        fun x => ∫ θ in Set.Ioc (0 : ℝ) 1, Qt (θ, x) := by
      funext x
      by_cases hx : x ∈ ball (0 : Vec d) t <;> simp [hQtdef, hx]
    rw [e, ← integral_integral_swap (f := fun θ x => Qt (θ, x)) hQtint]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hQtdef]
    rw [integral_indicator (measurableSet_ball _ _)]
  have hθint : IntegrableOn (fun θ => ∫ x in ball 0 t, Q (θ, x)) (Set.Ioc (0 : ℝ) 1) := by
    refine hQtint.integral_prod_left.congr (Eventually.of_forall fun θ => ?_)
    simp only [hQtdef]
    rw [integral_indicator (measurableSet_ball _ _)]
  calc ∫ x in ball 0 t, translationSegmentAverage G' h x ^ 2
      ≤ ∫ x in ball 0 t, euclideanSq h * ∫ θ in Set.Ioc (0 : ℝ) 1, Q (θ, x) :=
        setIntegral_mono_ae_restrict hW2 (hIQ.const_mul _).integrableOn (ae_restrict_of_ae hpt)
    _ = euclideanSq h * ∫ θ in Set.Ioc (0 : ℝ) 1, ∫ x in ball 0 t, Q (θ, x) := by
        rw [integral_const_mul, hswap]
    _ ≤ euclideanSq h * ∫ θ in Set.Ioc (0 : ℝ) 1,
          ∫ x in ball 0 (t + euclideanNorm h), euclideanSq (g x) :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hθint
          (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioc hQt) (zero_le_euclideanSq _)
    _ = euclideanSq h * ∫ x in ball 0 (t + euclideanNorm h), euclideanSq (g x) := by
        simp

set_option maxHeartbeats 400000 in
/-- **The averaged translation estimate**: for a nonnegative continuous kernel `κ` with
`∫ κ = 1` vanishing outside `B_δ`, the average `κ * F` of the zero extension `F` of `v` satisfies
`∫_{B_t} (v - κ * F)² ≤ δ² ∫_{B_{t+δ}} |g|²` for `t + δ ≤ R`. -/
theorem integral_sq_sub_kernelPairing_le {R t δ : ℝ} (hδ : 0 ≤ δ) (htR : t + δ ≤ R)
    {v : Vec d → ℝ} {g : Vec d → Vec d}
    (hv : MemLp v 2 (volume.restrict (ball 0 R)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (ball 0 R)))
    (hw : HasWeakGradient (ball 0 R) v g) {κ : Vec d → ℝ} (hκ : Continuous κ)
    (hκ0 : ∀ z, 0 ≤ κ z) (hκs : ∀ z, δ ≤ euclideanNorm z → κ z = 0) (hκ1 : ∫ z, κ z = 1) :
    ∫ x in ball 0 t, (v x - kernelPairing κ ((ball 0 R).indicator v) x) ^ 2 ≤
      δ ^ 2 * ∫ x in ball 0 (t + δ), euclideanSq (g x) := by
  classical
  -- a measurable version of `v`
  obtain ⟨v₀, hv₀m, hv₀e⟩ := hv.aestronglyMeasurable
  have hv₀ : MemLp v₀ 2 (volume.restrict (ball 0 R)) := hv.ae_eq hv₀e
  have hw₀ : HasWeakGradient (ball 0 R) v₀ g :=
    hasWeakGradient_congr_ae (isOpen_ball 0 R) hw hv₀e (ae_eq_refl _)
  set F := (ball (0 : Vec d) R).indicator v with hFdef
  set F₀ := (ball (0 : Vec d) R).indicator v₀ with hF₀def
  have hFF₀ : F =ᵐ[volume] F₀ := by
    have := (ae_restrict_iff' (measurableSet_ball (0 : Vec d) R)).mp hv₀e
    filter_upwards [this] with x hx
    by_cases hxR : x ∈ ball (0 : Vec d) R
    · simp [hFdef, hF₀def, hxR, hx hxR]
    · simp [hFdef, hF₀def, hxR]
  have hF₀m : Measurable F₀ := hv₀m.measurable.indicator (measurableSet_ball _ _)
  have hF₀2 : MemLp F₀ 2 volume := (memLp_indicator_iff_restrict (measurableSet_ball _ _)).mpr hv₀
  have hκc : HasCompactSupport κ := HasCompactSupport.intro (isCompact_euclideanSq_le (δ ^ 2))
    fun z hz => hκs z (by
      have h1 : δ ^ 2 < euclideanSq z := not_le.mp hz
      have h2 : δ ^ 2 < euclideanNorm z ^ 2 := by
        rw [euclideanNorm, Real.sq_sqrt (zero_le_euclideanSq z)]; exact h1
      exact (lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) h2).le)
  have hκi : Integrable κ := hκ.integrable_of_hasCompactSupport hκc
  obtain ⟨Mκ, hMκ⟩ := hκ.bounded_above_of_compact_support hκc
  have hκ2 : MemLp κ 2 volume := hκ.memLp_of_hasCompactSupport hκc
  have hFx : ∀ x : Vec d, MemLp (fun z => F₀ (x - z)) 2 volume := fun x =>
    hF₀2.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hgκ : ∀ x, Integrable fun z => (v₀ x - F₀ (x - z)) * κ z := fun x => by
    have := (hκi.const_mul (v₀ x)).sub ((hFx x).integrable_mul hκ2)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hg2κ : ∀ x, Integrable fun z => (v₀ x - F₀ (x - z)) ^ 2 * κ z := fun x => by
    refine Integrable.mono' (((hκi.const_mul (2 * v₀ x ^ 2))).add
      ((hFx x).integrable_sq.const_mul (2 * Mκ))) ?_ (Eventually.of_forall fun z => ?_)
    · exact (((hv₀m.measurable.aestronglyMeasurable.comp_measurable measurable_const).sub
        (hFx x).aestronglyMeasurable).pow 2).mul hκ.aestronglyMeasurable
    · have hk := hκ0 z
      have hkM : κ z ≤ Mκ := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMκ z)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hk)]
      have h1 : (v₀ x - F₀ (x - z)) ^ 2 ≤ 2 * v₀ x ^ 2 + 2 * F₀ (x - z) ^ 2 := by
        nlinarith [sq_nonneg (v₀ x + F₀ (x - z))]
      calc (v₀ x - F₀ (x - z)) ^ 2 * κ z ≤ (2 * v₀ x ^ 2 + 2 * F₀ (x - z) ^ 2) * κ z :=
            mul_le_mul_of_nonneg_right h1 hk
        _ ≤ 2 * v₀ x ^ 2 * κ z + 2 * Mκ * F₀ (x - z) ^ 2 := by
            nlinarith [sq_nonneg (F₀ (x - z)), mul_le_mul_of_nonneg_left hkM
              (sq_nonneg (F₀ (x - z)))]
  -- the pointwise representation and Jensen
  have hrep : ∀ x : Vec d, v₀ x - kernelPairing κ F₀ x = ∫ z, (v₀ x - F₀ (x - z)) * κ z := by
    intro x
    have e1 : kernelPairing κ F₀ x = ∫ z, F₀ (x - z) * κ z := by
      unfold kernelPairing
      rw [← integral_sub_left_eq_self (fun w => F₀ w * κ (x - w)) volume x]
      simp only [sub_sub_cancel]
    have i2 : Integrable fun z => F₀ (x - z) * κ z := (hFx x).integrable_mul hκ2
    rw [e1, show (fun z => (v₀ x - F₀ (x - z)) * κ z) =
      fun z => v₀ x * κ z - F₀ (x - z) * κ z by funext z; ring,
      integral_sub (hκi.const_mul _) i2, integral_const_mul, hκ1, mul_one]
  have hjen : ∀ x : Vec d, (v₀ x - kernelPairing κ F₀ x) ^ 2 ≤
      ∫ z, (v₀ x - F₀ (x - z)) ^ 2 * κ z := fun x => by
    rw [hrep x]
    exact sq_integral_mul_le hκ0 hκ1 hκi (hgκ x) (hg2κ x)
  -- the bound for each shift
  set C := ∫ x in ball 0 (t + δ), euclideanSq (g x) with hC
  have hshift : ∀ z, κ z ≠ 0 → ∫ x in ball 0 t, (v₀ x - F₀ (x - z)) ^ 2 ≤ δ ^ 2 * C := by
    intro z hz
    have hzδ : euclideanNorm z < δ := by
      by_contra hc
      exact hz (hκs z (not_lt.mp hc))
    have hz0 := Real.sqrt_nonneg (euclideanSq z)
    have htz : t + euclideanNorm z ≤ R := by linarith
    have hT := integral_sq_translate_sub_le hv₀ hg hw₀ htz
    have e : ∫ x in ball 0 t, (v₀ x - F₀ (x - z)) ^ 2 =
        ∫ x in ball 0 t, (v₀ (x - z) - v₀ x) ^ 2 := by
      refine setIntegral_congr_fun (measurableSet_ball _ _) fun x hx => ?_
      have hx' : euclideanNorm x < t := by simpa [ball] using hx
      have h1 := euclideanNorm_sub_smul_le x z (θ := 1) ⟨zero_le_one, le_rfl⟩
      rw [one_smul] at h1
      have hxz : x - z ∈ ball (0 : Vec d) R := by
        show euclideanNorm (x - z - 0) < R
        rw [sub_zero]; linarith
      simp only [hF₀def, Set.indicator_of_mem hxz]
      ring
    rw [e]
    refine hT.trans ?_
    have hsq : euclideanSq z ≤ δ ^ 2 := by
      rw [← Real.sq_sqrt (zero_le_euclideanSq z)]
      exact pow_le_pow_left₀ hz0 hzδ.le 2
    have hint : IntegrableOn (fun x => euclideanSq (g x)) (ball 0 (t + δ)) := by
      have hsub : ball (0 : Vec d) (t + δ) ⊆ ball 0 R := fun y hy => lt_of_lt_of_le hy htR
      have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
        (memLp_mono_set' (hg i) hsub).integrable_sq
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [euclideanSq, dot, sq]
    have hmono : ∫ x in ball 0 (t + euclideanNorm z), euclideanSq (g x) ≤ C :=
      setIntegral_mono_set hint (Eventually.of_forall fun _ => zero_le_euclideanSq _)
        (Eventually.of_forall fun y (hy : y ∈ ball (0 : Vec d) (t + euclideanNorm z)) =>
          show euclideanNorm (y - 0) < t + δ from lt_of_lt_of_le hy (by linarith))
    have hC0 : 0 ≤ ∫ x in ball 0 (t + euclideanNorm z), euclideanSq (g x) :=
      integral_nonneg fun _ => zero_le_euclideanSq _
    exact mul_le_mul hsq hmono hC0 (sq_nonneg _)
  -- Fubini
  set f : Vec d × Vec d → ℝ := (Prod.snd ⁻¹' ball (0 : Vec d) t).indicator
    (fun q => κ q.1 * (v₀ q.2 - F₀ (q.2 - q.1)) ^ 2) with hfdef
  have hfm : AEStronglyMeasurable f (volume.prod volume) := by
    refine (Measurable.indicator ?_ ((measurableSet_ball _ _).preimage measurable_snd)).aestronglyMeasurable
    exact (hκ.measurable.comp measurable_fst).mul
      (((hv₀m.measurable.comp measurable_snd).sub (hF₀m.comp (measurable_snd.sub measurable_fst))).pow_const 2)
  have hslice : ∀ z : Vec d, ∫ x, f (z, x) = κ z * ∫ x in ball 0 t, (v₀ x - F₀ (x - z)) ^ 2 := by
    intro z
    rw [← integral_const_mul, ← integral_indicator (measurableSet_ball _ _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ball (0 : Vec d) t <;> simp [hfdef, hx, Set.indicator]
  have hsliceint : ∀ z : Vec d, Integrable fun x => f (z, x) := by
    intro z
    have hm2 : MemLp (fun x => v₀ x - F₀ (x - z)) 2 (volume.restrict (ball 0 t)) :=
      (memLp_mono_set' hv₀ fun y (hy : y ∈ ball (0 : Vec d) t) =>
        show euclideanNorm (y - 0) < R from lt_of_lt_of_le hy (by linarith)).sub
        ((hF₀2.comp_measurePreserving (measurePreserving_sub_right volume z)).restrict _)
    have hi : IntegrableOn (fun x => κ z * (v₀ x - F₀ (x - z)) ^ 2) (ball 0 t) :=
      hm2.integrable_sq.const_mul _
    refine ((integrable_indicator_iff (measurableSet_ball _ _)).mpr hi).congr
      (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ball (0 : Vec d) t <;> simp [hfdef, hx, Set.indicator]
  have hfint : Integrable f (volume.prod volume) := by
    refine (integrable_prod_iff hfm).mpr ⟨Eventually.of_forall hsliceint, ?_⟩
    refine Integrable.mono' (hκi.mul_const (δ ^ 2 * C)) hfm.norm.integral_prod_right'
      (Eventually.of_forall fun z => ?_)
    have hn : ∫ x, ‖f (z, x)‖ = ∫ x, f (z, x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      refine Real.norm_of_nonneg ?_
      simp only [hfdef, Set.indicator]
      split_ifs
      · exact mul_nonneg (hκ0 z) (sq_nonneg _)
      · exact le_rfl
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), hn, hslice]
    by_cases hz : κ z = 0
    · rw [hz, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hshift z hz) (hκ0 z)
  -- assembly
  have hLHS : ∫ x in ball 0 t, (v x - kernelPairing κ F x) ^ 2 =
      ∫ x in ball 0 t, (v₀ x - kernelPairing κ F₀ x) ^ 2 := by
    have hkp : ∀ x, kernelPairing κ F x = kernelPairing κ F₀ x := fun x => by
      unfold kernelPairing
      refine integral_congr_ae ?_
      filter_upwards [hFF₀] with w hw
      rw [hw]
    have hvv : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) t)), v x = v₀ x := by
      have := ae_restrict_of_ae_restrict_of_subset (fun y (hy : y ∈ ball (0 : Vec d) t) =>
        lt_of_lt_of_le hy (by linarith : t ≤ R)) hv₀e
      exact this
    refine integral_congr_ae ?_
    filter_upwards [hvv] with x hx
    rw [hx, hkp x]
  rw [hLHS]
  calc ∫ x in ball 0 t, (v₀ x - kernelPairing κ F₀ x) ^ 2
      ≤ ∫ x in ball 0 t, ∫ z, (v₀ x - F₀ (x - z)) ^ 2 * κ z := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) ?_
          (Eventually.of_forall hjen)
        refine (hfint.integral_prod_right.integrableOn).congr_fun (fun x hx => ?_)
          (measurableSet_ball _ _)
        simp only [hfdef, Set.indicator, Set.mem_preimage, hx, ↓reduceIte]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    _ = ∫ z, ∫ x, f (z, x) := by
        rw [integral_integral_swap (f := fun z x => f (z, x)) hfint,
          ← integral_indicator (measurableSet_ball _ _)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ ball (0 : Vec d) t
        · simp only [hfdef, Set.indicator, Set.mem_preimage, hx, ↓reduceIte]
          exact integral_congr_ae (Eventually.of_forall fun z => by ring)
        · simp [hx, hfdef, Set.indicator]
    _ ≤ ∫ z, κ z * (δ ^ 2 * C) := by
        refine integral_mono hfint.integral_prod_left (hκi.mul_const _) fun z => ?_
        simp only
        rw [hslice]
        by_cases hz : κ z = 0
        · rw [hz, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hshift z hz) (hκ0 z)
    _ = δ ^ 2 * C := by rw [integral_mul_const, hκ1, one_mul]

end QSH
