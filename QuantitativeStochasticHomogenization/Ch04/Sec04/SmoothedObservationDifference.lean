import QuantitativeStochasticHomogenization.Ch04.Sec04.ObservationEstimateProof
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatGradientWindow
import QuantitativeStochasticHomogenization.Ch03.Sec04.HeatKernelScaling
import QuantitativeStochasticHomogenization.Ch03.Sec04.ReferenceSpatialCutoff
import QuantitativeStochasticHomogenization.Ch03.Sec04.RescaledSpatialCutoff

/-!
# Differences of cut-off Gaussian observations of a function with a weak gradient

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21, prepared for the
observation of the smoothed correctors. For a smooth compactly supported cutoff `χ` and a function
`φ` with weak gradient `g` on `ℝ^d`, the Gaussian observations `F(p) = ∫ χ Φ_{p,ρ} φ` at two
centers `z` and `z + h` differ by
`F(z + h) - F(z) = ∫_0^1 ∑_j h_j (∫ χ Φ_{p_t,ρ} g_j + ∫ φ Φ_{p_t,ρ} ∂_jχ) dt`, `p_t = z + t h`.
The proof applies the fundamental theorem of calculus to `t ↦ Φ_{p_t,ρ}(x)`, exchanges the two
integrals, and tests the weak gradient against the compactly supported `χ Φ_{p_t,ρ}`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem heatKernel_eq_comp_sub (p : Vec d) (ρ : ℝ) :
    heatKernel p ρ = fun x => euclideanHeatKernel (ρ ^ 2) (x - p) := rfl

theorem hasFDerivAt_heatKernel (p : Vec d) (ρ : ℝ) (x : Vec d) :
    HasFDerivAt (heatKernel p ρ) (fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - p)) x := by
  have hE : HasFDerivAt (euclideanHeatKernel (d := d) (ρ ^ 2))
      (fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - p)) (x - p) :=
    ((contDiff_euclideanHeatKernel_top (ρ ^ 2)).differentiable (by simp) _).hasFDerivAt
  have hl : HasFDerivAt (fun x : Vec d => x - p) (ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).sub_const p
  have := hE.comp x hl
  rw [ContinuousLinearMap.comp_id] at this
  exact this

theorem coordinateDerivative_heatKernel (p : Vec d) (ρ : ℝ) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (heatKernel p ρ) x =
      fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - p) (unitVector j) := by
  simp only [coordinateDerivative, (hasFDerivAt_heatKernel p ρ x).fderiv]

theorem contDiff_heatKernel (p : Vec d) (ρ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (heatKernel p ρ) := by
  rw [heatKernel_eq_comp_sub]
  exact (contDiff_euclideanHeatKernel_top (ρ ^ 2)).comp (contDiff_id.sub contDiff_const)

theorem hasDerivAt_heatKernel_line (ρ : ℝ) (p h x : Vec d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => heatKernel (p + t • h) ρ x)
      (-(fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - (p + t • h)) h)) t := by
  have hE : HasFDerivAt (euclideanHeatKernel (d := d) (ρ ^ 2))
      (fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - (p + t • h))) (x - (p + t • h)) :=
    ((contDiff_euclideanHeatKernel_top (ρ ^ 2)).differentiable (by simp) _).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x - (p + t • h)) (-h) t := by
    have h1 := (((hasDerivAt_id t).smul_const h).const_add p).const_sub x
    simpa using h1
  have := hE.comp_hasDerivAt t hl
  rw [map_neg] at this
  exact this

theorem clm_apply_eq_sum_unitVector (L : Vec d →L[ℝ] ℝ) (h : Vec d) :
    L h = ∑ j, h j * L (unitVector j) := by
  have hh : h = ∑ j, h j • unitVector j := by
    funext k
    simp [unitVector, Pi.single_apply]
  conv_lhs => rw [hh]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- `|∂_j Φ_{p,ρ}| ≤ 2^{d/2} (2/ρ) (8πρ²)^{-d/2}`. -/
theorem abs_coordinateDerivative_heatKernel_le {ρ : ℝ} (hρ : 0 < ρ) (p : Vec d) (j : Fin d)
    (x : Vec d) :
    |coordinateDerivative j (heatKernel p ρ) x| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [coordinateDerivative_heatKernel]
  have h := abs_heatGrad_le hρ2 j (x - p)
  have hs : Real.sqrt (ρ ^ 2) = ρ := Real.sqrt_sq hρ.le
  rw [hs] at h
  refine h.trans ?_
  have hE : euclideanHeatKernel (2 * ρ ^ 2) (x - p) ≤ (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) := by
    unfold euclideanHeatKernel
    have h1 : Real.exp (-euclideanSq (x - p) / (4 * (2 * ρ ^ 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (zero_le_euclideanSq _)) (by positivity)
    have h2 : 0 ≤ (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    calc (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanSq (x - p) / (4 * (2 * ρ ^ 2)))
        ≤ (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := mul_one _
  have h0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) := by positivity
  exact mul_le_mul_of_nonneg_left hE h0

theorem coordinateDerivative_mul_fun {f k : Vec d → ℝ} (hf : Differentiable ℝ f)
    (hk : Differentiable ℝ k) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (fun y => f y * k y) x =
      f x * coordinateDerivative j k x + k x * coordinateDerivative j f x := by
  simp only [coordinateDerivative]
  rw [fderiv_fun_mul (hf x) (hk x)]
  simp [smul_eq_mul]

theorem integrable_mul_of_compact {φ ψ : Vec d → ℝ} (hφ : LocallyIntegrable φ volume)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) : Integrable (fun x => ψ x * φ x) := by
  simpa [smul_eq_mul] using hφ.integrable_smul_left_of_hasCompactSupport hψ hψc

/-- **The weak gradient against a cut-off Gaussian**:
`-∫ χ φ ∂_jΦ_p = ∫ χ Φ_p g_j + ∫ ∂_jχ Φ_p φ`. -/
theorem neg_integral_cutoff_mul_coordinateDerivative_heatKernel {χ φ : Vec d → ℝ}
    {g : Vec d → Vec d} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hφg : HasWeakGradient Set.univ φ g) (ρ : ℝ) (p : Vec d) (j : Fin d) :
    -∫ x, χ x * φ x * coordinateDerivative j (heatKernel p ρ) x =
      (∫ x, χ x * heatKernel p ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel p ρ x * φ x := by
  have hΦ := contDiff_heatKernel p ρ
  have hψ : IsSpatialTest Set.univ (fun x => χ x * heatKernel p ρ x) :=
    ⟨hχ.mul hΦ, hχc.mul_right, Set.subset_univ _⟩
  have h := (hφg j).2.2 _ hψ
  rw [setIntegral_univ, setIntegral_univ] at h
  have hd : ∀ x, coordinateDerivative j (fun x => χ x * heatKernel p ρ x) x =
      χ x * coordinateDerivative j (heatKernel p ρ) x +
        heatKernel p ρ x * coordinateDerivative j χ x :=
    coordinateDerivative_mul_fun (hχ.differentiable (by simp)) (hΦ.differentiable (by simp)) j
  simp only [hd, mul_add] at h
  have hφl : LocallyIntegrable φ volume := by
    have := (hφg j).1; rwa [locallyIntegrableOn_univ] at this
  have hgl : LocallyIntegrable (fun x => g x j) volume := by
    have := (hφg j).2.1; rwa [locallyIntegrableOn_univ] at this
  have hcd : ∀ (f : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → Continuous (coordinateDerivative j f) :=
    fun f hf => (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs1 : HasCompactSupport (fun x => χ x * coordinateDerivative j (heatKernel p ρ) x) :=
    hχc.mul_right
  have hcs2 : HasCompactSupport (fun x => heatKernel p ρ x * coordinateDerivative j χ x) :=
    (hχc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector j))
      (by simp) |>.mul_left
  have hi1 := integrable_mul_of_compact hφl (hχ.continuous.mul (hcd _ hΦ)) hcs1
  have hi2 := integrable_mul_of_compact hφl (hΦ.continuous.mul (hcd _ hχ)) hcs2
  have hi3 := integrable_mul_of_compact hgl (hχ.continuous.mul hΦ.continuous) hχc.mul_right
  have e1 : ∫ x, φ x * (χ x * coordinateDerivative j (heatKernel p ρ) x) +
      φ x * (heatKernel p ρ x * coordinateDerivative j χ x) =
      (∫ x, χ x * φ x * coordinateDerivative j (heatKernel p ρ) x) +
        ∫ x, coordinateDerivative j χ x * heatKernel p ρ x * φ x := by
    rw [integral_add (hi1.congr (Eventually.of_forall fun x =>
        (by ring : χ x * coordinateDerivative j (heatKernel p ρ) x * φ x =
          φ x * (χ x * coordinateDerivative j (heatKernel p ρ) x))))
      (hi2.congr (Eventually.of_forall fun x =>
        (by ring : heatKernel p ρ x * coordinateDerivative j χ x * φ x =
          φ x * (heatKernel p ρ x * coordinateDerivative j χ x))))]
    congr 1
    · exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    · exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have e2 : ∫ x, g x j * (χ x * heatKernel p ρ x) = ∫ x, χ x * heatKernel p ρ x * g x j :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e1, e2] at h
  linarith

theorem continuous_fderiv_heatKernel_line (ρ : ℝ) (p h : Vec d) :
    Continuous (fun q : Vec d × ℝ =>
      fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (q.1 - (p + q.2 • h)) h) := by
  have hc : Continuous (fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2))) :=
    (contDiff_euclideanHeatKernel_top (ρ ^ 2)).continuous_fderiv (by simp)
  exact (hc.comp (continuous_fst.sub (continuous_const.add
    (continuous_snd.smul continuous_const)))).clm_apply continuous_const

/-- **The pointwise difference of two Gaussians along a segment.** -/
theorem heatKernel_add_sub_eq_integral (ρ : ℝ) (z h x : Vec d) :
    heatKernel (z + h) ρ x - heatKernel z ρ x =
      ∫ t in (0 : ℝ)..1, -(fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - (z + t • h)) h) := by
  have hcont : Continuous (fun t : ℝ =>
      -(fderiv ℝ (euclideanHeatKernel (d := d) (ρ ^ 2)) (x - (z + t • h)) h)) :=
    ((continuous_fderiv_heatKernel_line ρ z h).comp
      (continuous_const.prodMk continuous_id)).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_heatKernel_line ρ z h x t) (hcont.intervalIntegrable 0 1)]
  simp

/-- **The difference of the cut-off Gaussian observations at `z + h` and `z`.** -/
theorem integral_cutoff_heatKernel_add_sub {χ φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hφl : LocallyIntegrable φ volume)
    (hφg : HasWeakGradient Set.univ φ g) {ρ : ℝ} (hρ : 0 < ρ) (z h : Vec d) :
    (∫ x, χ x * heatKernel (z + h) ρ x * φ x) - ∫ x, χ x * heatKernel z ρ x * φ x =
      ∫ t in (0 : ℝ)..1, ∑ j, h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * φ x) := by
  set E := euclideanHeatKernel (d := d) (ρ ^ 2) with hE
  set D : Vec d → ℝ → ℝ := fun x t => fderiv ℝ E (x - (z + t • h)) h with hD
  have hχφ : Integrable (fun x => χ x * φ x) := integrable_mul_of_compact hφl hχ.continuous hχc
  -- the bound of the line derivative
  set K := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ρ) * (4 * Real.pi * (2 * ρ ^ 2)) ^ (-(d : ℝ) / 2)
    with hK
  have hDsum : ∀ x t, D x t = ∑ j, h j * coordinateDerivative j (heatKernel (z + t • h) ρ) x :=
    fun x t => by
      simp only [hD, coordinateDerivative_heatKernel]
      exact clm_apply_eq_sum_unitVector _ h
  have hDb : ∀ x t, |D x t| ≤ ∑ j, |h j| * K := fun x t => by
    rw [hDsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_coordinateDerivative_heatKernel_le hρ _ j x)
      (abs_nonneg _)
  -- step 1: the difference under one integral
  have hint : ∀ p : Vec d, Integrable (fun x => χ x * heatKernel p ρ x * φ x) := fun p =>
    (integrable_mul_of_compact hφl (hχ.continuous.mul (contDiff_heatKernel p ρ).continuous)
      hχc.mul_right)
  have h1 : (∫ x, χ x * heatKernel (z + h) ρ x * φ x) - ∫ x, χ x * heatKernel z ρ x * φ x =
      ∫ x, ∫ t in (0 : ℝ)..1, -(χ x * φ x * D x t) := by
    rw [← integral_sub (hint _) (hint _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, ← mul_neg,
      ← intervalIntegral.integral_neg]
    have := heatKernel_add_sub_eq_integral ρ z h x
    rw [← this]
    ring
  -- step 2: exchange the integrals
  have hF : Integrable (Function.uncurry fun x t => -(χ x * φ x * D x t))
      ((volume : Measure (Vec d)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hb : Integrable (fun q : Vec d × ℝ => |χ q.1 * φ q.1| * (∑ j, |h j| * K))
        ((volume : Measure (Vec d)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      MeasureTheory.Integrable.mul_prod hχφ.abs (integrable_const _)
    refine hb.mono' ?_ (Eventually.of_forall fun q => ?_)
    · have hc : Continuous (fun q : Vec d × ℝ => D q.1 q.2) :=
        continuous_fderiv_heatKernel_line ρ z h
      exact ((hχφ.aestronglyMeasurable.comp_fst).mul hc.aestronglyMeasurable).neg
    · simp only [Function.uncurry, norm_neg, Real.norm_eq_abs, abs_mul]
      rw [← abs_mul]
      exact mul_le_mul_of_nonneg_left (hDb _ _) (abs_nonneg _)
  have h2 : ∫ x, ∫ t in (0 : ℝ)..1, -(χ x * φ x * D x t) =
      ∫ t in (0 : ℝ)..1, ∫ x, -(χ x * φ x * D x t) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_integral_swap hF
  -- step 3: the weak gradient at each time
  have h3 : ∀ t : ℝ, ∫ x, -(χ x * φ x * D x t) =
      ∑ j, h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * φ x) := by
    intro t
    have hij : ∀ j, Integrable (fun x => χ x * φ x *
        coordinateDerivative j (heatKernel (z + t • h) ρ) x) := fun j => by
      have hcd : Continuous (coordinateDerivative j (heatKernel (z + t • h) ρ)) :=
        ((contDiff_heatKernel _ ρ).continuous_fderiv (by simp)).clm_apply continuous_const
      exact (integrable_mul_of_compact hφl (hχ.continuous.mul hcd) hχc.mul_right).congr
        (Eventually.of_forall fun x =>
          (by ring : χ x * coordinateDerivative j (heatKernel (z + t • h) ρ) x * φ x =
            χ x * φ x * coordinateDerivative j (heatKernel (z + t • h) ρ) x))
    have e : (fun x => -(χ x * φ x * D x t)) = fun x => ∑ j, h j *
        (-(χ x * φ x * coordinateDerivative j (heatKernel (z + t • h) ρ) x)) := by
      funext x
      rw [hDsum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (((hij j).neg).const_mul (h j) :
      Integrable (fun x => h j *
        -(χ x * φ x * coordinateDerivative j (heatKernel (z + t • h) ρ) x)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_neg]
    rw [neg_integral_cutoff_mul_coordinateDerivative_heatKernel hχ hχc hφg ρ (z + t • h) j]
  rw [h1, h2]
  exact intervalIntegral.integral_congr fun t _ => h3 t

/-- **A cutoff for the ball `B_T(z)`**: smooth, compactly supported, between `0` and `1`, equal to
one on `B_{T/2}(z)`, zero outside `B_T(z)`, with gradient at most `D/T`. -/
theorem exists_ball_cutoff (d : ℕ) : ∃ D : ℝ, 0 < D ∧ ∀ (z : Vec d) (T : ℝ), 0 < T →
    ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ ball z (T / 2), χ x = 1) ∧ (∀ x, x ∉ ball z T → χ x = 0) ∧
      ∀ x, euclideanSq (gradient χ x) ≤ (D / T) ^ 2 := by
  obtain ⟨χ₀, D, hD, hχ₀, hχ₀b, hχ₀1, hχ₀D⟩ := exists_nonnegative_reference_spatial_cutoff d
  refine ⟨4 * D, by positivity, fun z T hT => ?_⟩
  have hR : 0 < T / 4 := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := rescale_reference_spatial_cutoff hR hχ₀ hχ₀b hχ₀1 hχ₀D
  set c : Vec d → ℝ := fun x => χ₀ ((2 * (T / 4))⁻¹ • x) with hc
  refine ⟨fun x => c (x + -z), h1.1.comp (contDiff_id.add contDiff_const),
    h1.2.1.comp_homeomorph (Homeomorph.addRight (-z)), fun x => h2 _, fun x hx => ?_,
    fun x hx => ?_, fun x => ?_⟩
  · apply h3
    show euclideanNorm (x + -z) < 2 * (T / 4)
    have : euclideanNorm (x - z) < T / 2 := hx
    rw [← sub_eq_add_neg]
    linarith
  · have hn : x + -z ∉ tsupport c := by
      intro hmem
      have := h1.2.2 hmem
      have h' : euclideanNorm (x + -z) < 4 * (T / 4) := this
      rw [← sub_eq_add_neg] at h'
      exact hx (show euclideanNorm (x - z) < T by linarith)
    exact image_eq_zero_of_notMem_tsupport hn
  · have e : gradient (fun x => c (x + -z)) x = gradient c (x + -z) := by
      funext i
      exact coordinateDerivative_comp_add i c (-z) x
    rw [e]
    have h4' := h4 (x + -z)
    rw [div_div_eq_mul_div, mul_comm D 4] at h4'
    exact h4'

end QSH
