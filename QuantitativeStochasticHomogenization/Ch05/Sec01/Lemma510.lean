import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouvilleReduction

/-!
# Lemma 5.10: compactly supported functions of mean zero are divergences

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 5.1, Lemma 5.10: for every `f ∈ C_c^∞(ℝ^d)` with `∫ f = 0` there is
`F ∈ C_c^∞(ℝ^d; ℝ^d)` with `∇·F = f` (`lemma_5_10`).

The proof is the book's: with a bump `h` of unit mass, `g₀ = f`,
`g_{k+1}(x) = h(x_k) ∫ g_k(x + s e_k) ds`, and
`F_k(x) = ∫_{-∞}^0 (g_k - g_{k+1})(x + s e_k) ds`, so that `∂_k F_k = g_k - g_{k+1}` and
`∇·F = g₀ - g_d = f`. The smoothness of the line integrals `x ↦ ∫_S ψ(x + s v) ds` of smooth
compactly supported `ψ` is `contDiff_setIntegral_add_smul`; that `g_d = 0` follows from
`g_d(x) = c ∏ h(x_j)` and `∫ g_d = ∫ f - ∫ ∇·F = 0`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

universe u

variable {d : ℕ}

section LineIntegral

/-- Where `ψ(x + s v) ≠ 0` with `x` near `x₀`, `|s|` is bounded. -/
theorem abs_le_of_add_smul_mem {R : ℝ} {v x₀ x : Vec d} (hv : v ≠ 0) {s : ℝ}
    (hx : x ∈ Metric.ball x₀ 1) (hxs : x + s • v ∈ Metric.closedBall (0 : Vec d) R) :
    |s| ≤ (R + ‖x₀‖ + 1) / ‖v‖ := by
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [le_div_iff₀ hv0]
  have h1 : ‖x + s • v‖ ≤ R := by simpa using hxs
  have h2 : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have h3 : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
    calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ ≤ ‖x₀‖ + 1 := by linarith
  have h4 : ‖s • v‖ ≤ ‖x + s • v‖ + ‖x‖ := by
    calc ‖s • v‖ = ‖(x + s • v) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + s • v‖ + ‖x‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs] at h4
  linarith

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise bound `‖φ(x + s v)‖ ≤ C 1_{|s| ≤ M}` for a bounded `φ` supported in a ball, uniform
for `x` near `x₀`. -/
theorem norm_le_indicator_of_tsupport {φ : Vec d → E} {R C : ℝ}
    (hR : tsupport φ ⊆ Metric.closedBall (0 : Vec d) R) (hC : ∀ y, ‖φ y‖ ≤ C) {v x₀ : Vec d}
    (hv : v ≠ 0) {x : Vec d} (hx : x ∈ Metric.ball x₀ 1) (s : ℝ) :
    ‖φ (x + s • v)‖ ≤ C * (Icc (-((R + ‖x₀‖ + 1) / ‖v‖)) ((R + ‖x₀‖ + 1) / ‖v‖)).indicator
      (fun _ => (1 : ℝ)) s := by
  by_cases h : φ (x + s • v) = 0
  · rw [h, norm_zero]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    exact mul_nonneg hC0 (indicator_nonneg (fun _ _ => zero_le_one) _)
  · have hmem : x + s • v ∈ Metric.closedBall (0 : Vec d) R := hR (subset_tsupport _ h)
    have hs := abs_le_of_add_smul_mem hv hx hmem
    rw [indicator_of_mem (show s ∈ Icc _ _ from abs_le.mp hs), mul_one]
    exact hC _

theorem integrable_indicator_Icc_const (C a b : ℝ) (S : Set ℝ) :
    Integrable (fun s : ℝ => C * (Icc a b).indicator (fun _ => (1 : ℝ)) s)
      (volume.restrict S) := by
  have h : Integrable ((Icc a b).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  exact (h.mono_measure Measure.restrict_le_self).const_mul C

theorem exists_tsupport_subset_closedBall {φ : Vec d → E} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, tsupport φ ⊆ Metric.closedBall (0 : Vec d) R :=
  hφ.isCompact.isBounded.subset_closedBall 0

/-- **Differentiation of line integrals**: for `ψ ∈ C¹_c`, `v ≠ 0` and a set `S ⊆ ℝ`, the map
`x ↦ ∫_S ψ(x + s v) ds` has derivative `∫_S Dψ(x + s v) ds`. -/
theorem hasFDerivAt_setIntegral_add_smul [CompleteSpace E] {ψ : Vec d → E}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {v : Vec d} (hv : v ≠ 0) (S : Set ℝ)
    (x₀ : Vec d) :
    HasFDerivAt (fun x => ∫ s in S, ψ (x + s • v)) (∫ s in S, fderiv ℝ ψ (x₀ + s • v)) x₀ := by
  obtain ⟨R, hR⟩ := exists_tsupport_subset_closedBall hψc
  have hR' : tsupport (fderiv ℝ ψ) ⊆ Metric.closedBall (0 : Vec d) R :=
    (tsupport_fderiv_subset ℝ).trans hR
  have hcont : Continuous ψ := hψ.continuous
  have hcont' : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨C₀, hC₀⟩ := hcont.bounded_above_of_compact_support hψc
  obtain ⟨C₁, hC₁⟩ := hcont'.bounded_above_of_compact_support (hψc.fderiv (𝕜 := ℝ))
  have hline : ∀ x : Vec d, Continuous fun s : ℝ => x + s • v := fun x =>
    continuous_const.add (continuous_id.smul continuous_const)
  have hx₀ : x₀ ∈ Metric.ball x₀ 1 := Metric.mem_ball_self one_pos
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x₀ one_pos)
    (F' := fun x s => fderiv ℝ ψ (x + s • v))
    (bound := fun s => C₁ * (Icc (-((R + ‖x₀‖ + 1) / ‖v‖)) ((R + ‖x₀‖ + 1) / ‖v‖)).indicator
      (fun _ => (1 : ℝ)) s)
    (Eventually.of_forall fun x => (hcont.comp (hline x)).aestronglyMeasurable) ?_
    (hcont'.comp (hline x₀)).aestronglyMeasurable
    (Eventually.of_forall fun s x hx => norm_le_indicator_of_tsupport hR' hC₁ hv hx s)
    (integrable_indicator_Icc_const _ _ _ S) ?_
  · refine (integrable_indicator_Icc_const C₀ (-((R + ‖x₀‖ + 1) / ‖v‖))
      ((R + ‖x₀‖ + 1) / ‖v‖) S).mono' (hcont.comp (hline x₀)).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    exact norm_le_indicator_of_tsupport hR hC₀ hv hx₀ s
  · refine Eventually.of_forall fun s x _ => ?_
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x + s • v)) (x + s • v) :=
      ((hψ.differentiable one_ne_zero) (x + s • v)).hasFDerivAt
    have h2 : HasFDerivAt (fun y : Vec d => y + s • v) (ContinuousLinearMap.id ℝ (Vec d)) x :=
      (hasFDerivAt_id x).add_const (s • v)
    have h3 := h1.comp x h2
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3

theorem contDiff_setIntegral_add_smul_aux (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ψ : Vec d → E},
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → ∀ {v : Vec d}, v ≠ 0 → ∀ S : Set ℝ,
      ContDiff ℝ n (fun x => ∫ s in S, ψ (x + s • v)) := by
  induction n with
  | zero =>
    intro E _ _ _ ψ hψ hψc v hv S
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_setIntegral_add_smul (hψ.of_le (by simp)) hψc hv S x).continuousAt
  | succ n ih =>
    intro E _ _ _ ψ hψ hψc v hv S
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ s in S, fderiv ℝ ψ (x + s • v),
      ih (hψ.fderiv_right (by simp)) (hψc.fderiv (𝕜 := ℝ)) hv S, fun x => ?_⟩
    exact hasFDerivAt_setIntegral_add_smul (hψ.of_le (by simp)) hψc hv S x

/-- **Smoothness of line integrals**: for `ψ ∈ C_c^∞`, `v ≠ 0` and a set `S ⊆ ℝ`, the map
`x ↦ ∫_S ψ(x + s v) ds` is smooth. -/
theorem contDiff_setIntegral_add_smul [CompleteSpace E] {ψ : Vec d → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) {v : Vec d} (hv : v ≠ 0) (S : Set ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ s in S, ψ (x + s • v)) :=
  contDiff_infty.2 fun n => contDiff_setIntegral_add_smul_aux n hψ hψc hv S

end LineIntegral

end QSH
