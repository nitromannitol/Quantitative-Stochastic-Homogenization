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

section Construction

/-- The `k`-th coordinate direction `e_k` (zero for `k ≥ d`). -/
def coordDir (d k : ℕ) : Vec d := if h : k < d then unitVector ⟨k, h⟩ else 0

theorem coordDir_of_lt {k : ℕ} (hk : k < d) : coordDir d k = unitVector ⟨k, hk⟩ := dif_pos hk

theorem unitVector_ne_zero (i : Fin d) : (unitVector i : Vec d) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unitVector] at this

theorem add_smul_unitVector_apply_ne (x : Vec d) (s : ℝ) {i j : Fin d} (hij : j ≠ i) :
    (x + s • unitVector i) j = x j := by
  simp [unitVector, Pi.single_apply, hij]

theorem add_smul_unitVector_apply_self (x : Vec d) (s : ℝ) (i : Fin d) :
    (x + s • unitVector i) i = x i + s := by
  simp [unitVector]

/-- The functions `g_k` of the proof of Lemma 5.10: `g₀ = f` and
`g_{k+1}(x) = h(x_k) ∫ g_k(x + s e_k) ds`. -/
def bumpLineSeq (h : ℝ → ℝ) (f : Vec d → ℝ) : ℕ → Vec d → ℝ
  | 0 => f
  | k + 1 => fun x => (if hk : k < d then h (x ⟨k, hk⟩) else 0) *
      ∫ s : ℝ, bumpLineSeq h f k (x + s • coordDir d k)

theorem bumpLineSeq_succ_of_lt (h : ℝ → ℝ) (f : Vec d → ℝ) {k : ℕ} (hk : k < d) (x : Vec d) :
    bumpLineSeq h f (k + 1) x =
      h (x ⟨k, hk⟩) * ∫ s : ℝ, bumpLineSeq h f k (x + s • unitVector ⟨k, hk⟩) := by
  simp only [bumpLineSeq, dif_pos hk, coordDir_of_lt hk]

theorem exists_lt_abs_of_lt_norm {R : ℝ} (hR : 0 ≤ R) {x : Vec d} (hx : R < ‖x‖) :
    ∃ j, R < |x j| := by
  by_contra hcon
  push Not at hcon
  have : ‖x‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).2 fun j => by
    rw [Real.norm_eq_abs]; exact hcon j
  linarith

theorem hasCompactSupport_of_vanish {E : Type*} [NormedAddCommGroup E] {φ : Vec d → E} {R : ℝ}
    (hφ : ∀ x, R < ‖x‖ → φ x = 0) : HasCompactSupport φ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) R) fun x hx => hφ x (by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx)

/-- The functions `g_k` are smooth and vanish outside the box `‖x‖ ≤ R`. -/
theorem bumpLineSeq_spec {h : ℝ → ℝ} {f : Vec d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhR : ∀ t, R < |t| → h t = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfR : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ k ≤ d, ContDiff ℝ (⊤ : ℕ∞) (bumpLineSeq h f k) ∧
      ∀ x, R < ‖x‖ → bumpLineSeq h f k x = 0 := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hf, hfR⟩
  | succ k ih =>
    intro hk
    have hk' : k < d := hk
    obtain ⟨hg, hgR⟩ := ih (by omega)
    have hfun : bumpLineSeq h f (k + 1) = fun x =>
        h (x ⟨k, hk'⟩) * ∫ s : ℝ in univ, bumpLineSeq h f k (x + s • unitVector ⟨k, hk'⟩) := by
      funext x
      rw [bumpLineSeq_succ_of_lt h f hk', Measure.restrict_univ]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hfun]
      exact (hh.comp (contDiff_apply ℝ ℝ (⟨k, hk'⟩ : Fin d))).mul
        (contDiff_setIntegral_add_smul hg (hasCompactSupport_of_vanish hgR)
          (unitVector_ne_zero _) univ)
    · rw [bumpLineSeq_succ_of_lt h f hk']
      obtain ⟨j, hj⟩ := exists_lt_abs_of_lt_norm hR hx
      by_cases hjk : j = ⟨k, hk'⟩
      · rw [← hjk, hhR _ hj, zero_mul]
      · have hz : ∀ s : ℝ, bumpLineSeq h f k (x + s • unitVector ⟨k, hk'⟩) = 0 := by
          intro s
          refine hgR _ ?_
          have h1 := norm_le_pi_norm (x + s • unitVector ⟨k, hk'⟩) j
          rw [add_smul_unitVector_apply_ne x s hjk, Real.norm_eq_abs] at h1
          linarith
        simp only [hz, integral_zero, mul_zero]

/-- **The line integrals of `g_{k+1}` and `g_k` along `e_k` agree** (`∫ h = 1`). -/
theorem integral_bumpLineSeq_succ {h : ℝ → ℝ} (hh1 : ∫ t : ℝ, h t = 1) (f : Vec d → ℝ) {k : ℕ}
    (hk : k < d) (x : Vec d) :
    ∫ s : ℝ, bumpLineSeq h f (k + 1) (x + s • unitVector ⟨k, hk⟩) =
      ∫ s : ℝ, bumpLineSeq h f k (x + s • unitVector ⟨k, hk⟩) := by
  have e1 : ∀ s : ℝ, bumpLineSeq h f (k + 1) (x + s • unitVector ⟨k, hk⟩) =
      h (x ⟨k, hk⟩ + s) * ∫ t : ℝ, bumpLineSeq h f k (x + t • unitVector ⟨k, hk⟩) := by
    intro s
    rw [bumpLineSeq_succ_of_lt h f hk, add_smul_unitVector_apply_self]
    congr 1
    have e2 : ∀ t : ℝ, x + s • unitVector ⟨k, hk⟩ + t • unitVector ⟨k, hk⟩ =
        x + (t + s) • unitVector ⟨k, hk⟩ := fun t => by rw [add_smul]; abel
    simp only [e2]
    exact integral_add_right_eq_self (fun t => bumpLineSeq h f k (x + t • unitVector ⟨k, hk⟩)) s
  simp only [e1]
  rw [integral_mul_const, integral_add_left_eq_self (fun t => h t) (x ⟨k, hk⟩), hh1, one_mul]

end Construction

end QSH
