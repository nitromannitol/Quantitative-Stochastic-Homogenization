import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedObservationDifference

/-!
# The truncated Gaussian observation of a function by its Gaussian gradient averages

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (SCOTT-localization (5)). Let `χ` be a cutoff vanishing outside `B_T(z)` and
choose the constant `c` with `∫ χ Φ_{z,ρ} (φ - c) = 0`. For `y = z + h` the truncated observation
`∫_{B_T(z)} Φ_{y,ρ} (φ - c)` is the cut-off observation plus the term with `1 - χ`, and the cut-off
observation is the difference of the cut-off observations at `y` and `z`. With
`G(p)_j = ∫ Φ_{p,ρ} ∂_jφ` and the two cut-off error terms bounded by `τ` along the segment, this
gives `|∫_{B_T(z)} Φ_{y,ρ} (φ - c)| ≤ |h| √d (∫_0^1 |G(z + t h)|² dt)^{1/2} + |h| d τ + τ'`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem ball_subset_metric_closedBall (z : Vec d) (T : ℝ) :
    ball z T ⊆ Metric.closedBall z T := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (le_of_lt (lt_of_le_of_lt (zero_le_euclideanNorm _) hx))).2
    fun i => ?_
  rw [Real.norm_eq_abs]
  exact (abs_coord_le_euclideanNorm (x - z) i).trans (le_of_lt hx)

theorem integrableOn_ball_heatKernel_mul {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    (p z : Vec d) (ρ T : ℝ) :
    IntegrableOn (fun x => heatKernel p ρ x * f x) (ball z T) := by
  have hK : IsCompact (Metric.closedBall z T) := isCompact_closedBall z T
  have h := (hf.integrableOn_isCompact hK).continuousOn_mul
    (contDiff_heatKernel p ρ).continuous.continuousOn hK
  exact h.mono_set (ball_subset_metric_closedBall z T)

/-- **The truncated observation at `z + h` by the Gaussian gradient averages along the segment.** -/
theorem abs_truncated_observation_le {φ : Vec d → ℝ} {g : Vec d → Vec d}
    (hφl : LocallyIntegrable φ volume) (hφg : HasWeakGradient Set.univ φ g)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    {z h : Vec d} {T ρ c τ₁ τ₂ τ₃ : ℝ} (hρ : 0 < ρ)
    (hχT : ∀ x, x ∉ ball z T → χ x = 0)
    (hc : ∫ x, χ x * heatKernel z ρ x * (φ x - c) = 0)
    (G : ℝ → Vec d) (hGi : IntervalIntegrable (fun t => euclideanNorm (G t)) volume 0 1)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      |∫ x, χ x * heatKernel (z + t • h) ρ x * g x j| ≤ |G t j| + τ₁)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      |∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c)| ≤ τ₂)
    (h3 : |∫ x in ball z T, (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c)| ≤ τ₃) :
    |∫ x in ball z T, heatKernel (z + h) ρ x * (φ x - c)| ≤
      euclideanNorm h * (Real.sqrt d * ∫ t in (0 : ℝ)..1, euclideanNorm (G t)) +
        euclideanNorm h * (d * (τ₁ + τ₂)) + τ₃ := by
  have hfl : LocallyIntegrable (fun x => φ x - c) volume := hφl.sub (locallyIntegrable_const c)
  have hfg : HasWeakGradient Set.univ (fun x => φ x - c) g := hφg.sub_const c
  -- the split with the cutoff
  have hint1 : IntegrableOn (fun x => heatKernel (z + h) ρ x * (φ x - c)) (ball z T) :=
    integrableOn_ball_heatKernel_mul hfl _ z ρ T
  have hcont : IntegrableOn (fun x => χ x * heatKernel (z + h) ρ x * (φ x - c)) (ball z T) :=
    (integrable_mul_of_compact hfl (hχ.continuous.mul (contDiff_heatKernel _ ρ).continuous)
      hχc.mul_right).integrableOn
  have hsplit : ∫ x in ball z T, heatKernel (z + h) ρ x * (φ x - c) =
      (∫ x in ball z T, χ x * heatKernel (z + h) ρ x * (φ x - c)) +
        ∫ x in ball z T, (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c) := by
    have hrest : IntegrableOn (fun x => (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c))
        (ball z T) :=
      (hint1.sub hcont).congr_fun (fun x _ => by simp only [Pi.sub_apply]; ring)
        (measurableSet_ball z T)
    rw [← integral_add hcont hrest]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      (by ring : heatKernel (z + h) ρ x * (φ x - c) =
        χ x * heatKernel (z + h) ρ x * (φ x - c) +
          (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c)))
  have hχint : ∫ x in ball z T, χ x * heatKernel (z + h) ρ x * (φ x - c) =
      ∫ x, χ x * heatKernel (z + h) ρ x * (φ x - c) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hχT x hx]; ring
  -- the difference formula
  have hdiff := integral_cutoff_heatKernel_add_sub hχ hχc hfl hfg hρ z h
  rw [hc, sub_zero] at hdiff
  -- the bound of the time integrand
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖∑ j, h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c))‖ ≤
      euclideanNorm h * (Real.sqrt d * euclideanNorm (G t)) +
        euclideanNorm h * (d * (τ₁ + τ₂)) := by
    intro t ht
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ j, |h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c))| ≤
        euclideanNorm h * (|G t j| + (τ₁ + τ₂)) := fun j => by
      rw [abs_mul]
      refine mul_le_mul (abs_coord_le_euclideanNorm h j) ?_ (abs_nonneg _)
        (zero_le_euclideanNorm h)
      refine (abs_add_le _ _).trans ?_
      linarith [hA t ht j, hB t ht j]
    refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have := sum_abs_le_sqrt_mul_euclideanNorm (G t)
    have hn := zero_le_euclideanNorm h
    nlinarith
  have hbound : ‖∫ t in (0 : ℝ)..1, ∑ j, h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
      ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c))‖ ≤
      ∫ t in (0 : ℝ)..1, (euclideanNorm h * (Real.sqrt d * euclideanNorm (G t)) +
        euclideanNorm h * (d * (τ₁ + τ₂))) :=
    intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall fun t ht => hpt t (Set.Ioc_subset_Icc_self ht))
      (((hGi.const_mul (Real.sqrt d)).const_mul (euclideanNorm h)).add intervalIntegrable_const)
  rw [intervalIntegral.integral_add ((hGi.const_mul (Real.sqrt d)).const_mul (euclideanNorm h))
    intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero, one_smul]
    at hbound
  rw [hsplit, hχint, hdiff]
  rw [Real.norm_eq_abs] at hbound
  calc |(∫ t in (0 : ℝ)..1, ∑ j, h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c))) +
        ∫ x in ball z T, (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c)|
      ≤ |∫ t in (0 : ℝ)..1, ∑ j, h j * ((∫ x, χ x * heatKernel (z + t • h) ρ x * g x j) +
        ∫ x, coordinateDerivative j χ x * heatKernel (z + t • h) ρ x * (φ x - c))| +
        |∫ x in ball z T, (1 - χ x) * heatKernel (z + h) ρ x * (φ x - c)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **The centering constant**: the cut-off Gaussian mean of `φ` at `z`. -/
theorem integral_cutoff_heatKernel_sub_mean {φ χ : Vec d → ℝ} (hφl : LocallyIntegrable φ volume)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (z : Vec d) {ρ : ℝ}
    (hm : ∫ x, χ x * heatKernel z ρ x ≠ 0) :
    ∫ x, χ x * heatKernel z ρ x *
      (φ x - (∫ y, χ y * heatKernel z ρ y * φ y) / ∫ y, χ y * heatKernel z ρ y) = 0 := by
  have hc1 : Integrable (fun x => χ x * heatKernel z ρ x * φ x) :=
    integrable_mul_of_compact hφl (hχ.mul (contDiff_heatKernel z ρ).continuous) hχc.mul_right
  have hc2 : Integrable (fun x => χ x * heatKernel z ρ x) :=
    (hχ.mul (contDiff_heatKernel z ρ).continuous).integrable_of_hasCompactSupport hχc.mul_right
  set c := (∫ y, χ y * heatKernel z ρ y * φ y) / ∫ y, χ y * heatKernel z ρ y with hcdef
  have e : (fun x => χ x * heatKernel z ρ x * (φ x - c)) =
      fun x => χ x * heatKernel z ρ x * φ x - c * (χ x * heatKernel z ρ x) := by
    funext x; ring
  rw [e, integral_sub hc1 (hc2.const_mul c), integral_const_mul, hcdef, div_mul_cancel₀ _ hm,
    sub_self]

theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ l : ℝ, 0 ≤ A - 2 * l * B + l ^ 2 * C) : B ^ 2 ≤ A * C := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · rw [← hC0] at h ⊢
    simp only [mul_zero, add_zero] at h
    by_cases hB : B = 0
    · rw [hB]; simp
    · have h1 := h ((A + 1) / (2 * B))
      have e : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by field_simp
      rw [e] at h1
      linarith
  · have h1 := h (B / C)
    have e : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hCpos] at h1
    exact h1

/-- **Cauchy–Schwarz with a nonnegative weight**: `(∫ w f)² ≤ (∫ w f²) (∫ w)`. -/
theorem sq_integral_weight_mul_le {w f : Vec d → ℝ} {μ : Measure (Vec d)} (hw : ∀ x, 0 ≤ w x)
    (hwi : Integrable w μ) (hwf : Integrable (fun x => w x * f x) μ)
    (hwf2 : Integrable (fun x => w x * f x ^ 2) μ) :
    (∫ x, w x * f x ∂μ) ^ 2 ≤ (∫ x, w x * f x ^ 2 ∂μ) * ∫ x, w x ∂μ := by
  refine sq_le_mul_of_quadratic_nonneg (integral_nonneg hw) fun l => ?_
  have i1 : Integrable (fun x => w x * f x ^ 2 - 2 * l * (w x * f x)) μ :=
    hwf2.sub (hwf.const_mul (2 * l))
  have i2 : Integrable (fun x => 2 * l * (w x * f x)) μ := hwf.const_mul (2 * l)
  have i3 : Integrable (fun x => l ^ 2 * w x) μ := hwi.const_mul (l ^ 2)
  have e : (∫ x, w x * f x ^ 2 ∂μ) - 2 * l * (∫ x, w x * f x ∂μ) + l ^ 2 * ∫ x, w x ∂μ =
      ∫ x, (w x * f x ^ 2 - 2 * l * (w x * f x) + l ^ 2 * w x) ∂μ := by
    rw [integral_add i1 i3, integral_sub hwf2 i2, integral_const_mul, integral_const_mul]
  rw [e]
  refine integral_nonneg fun x => ?_
  have e2 : w x * f x ^ 2 - 2 * l * (w x * f x) + l ^ 2 * w x = w x * (f x - l) ^ 2 := by ring
  simp only
  rw [e2]
  exact mul_nonneg (hw x) (sq_nonneg _)

end QSH
