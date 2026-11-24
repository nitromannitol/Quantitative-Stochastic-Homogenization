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

omit [NormedSpace ℝ E] in
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

omit [NormedSpace ℝ E] in
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

theorem coordDir_of_lt {k : ℕ} (hk : k < d) : coordDir d k = unitVector ⟨k, hk⟩ := by
  simp only [coordDir, hk, ↓reduceDIte]

theorem unitVector_ne_zero (i : Fin d) : (unitVector i : Vec d) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unitVector] at this

theorem add_smul_unitVector_apply_ne (x : Vec d) (s : ℝ) {i j : Fin d} (hij : j ≠ i) :
    (x + s • unitVector i) j = x j := by
  simp [unitVector, hij]

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
  simp only [bumpLineSeq, hk, ↓reduceDIte, coordDir_of_lt hk]

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

section Assembly

/-- Integrability of `s ↦ φ(x + s v)` for continuous compactly supported `φ`. -/
theorem integrable_comp_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : Vec d → E} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {v : Vec d} (hv : v ≠ 0)
    (x : Vec d) (S : Set ℝ) : Integrable (fun s : ℝ => φ (x + s • v)) (volume.restrict S) := by
  obtain ⟨R, hR⟩ := exists_tsupport_subset_closedBall hφc
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hline : Continuous fun s : ℝ => x + s • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact (integrable_indicator_Icc_const C _ _ S).mono' (hφ.comp hline).aestronglyMeasurable
    (Eventually.of_forall fun s => norm_le_indicator_of_tsupport hR hC hv
      (Metric.mem_ball_self one_pos) s)

/-- The product `∏_{j < k} h(x_j)`. -/
def bumpPrefix (h : ℝ → ℝ) (k : ℕ) (x : Vec d) : ℝ := ∏ j : Fin d, if j.val < k then h (x j) else 1

theorem bumpPrefix_succ (h : ℝ → ℝ) {k : ℕ} (hk : k < d) (x : Vec d) :
    bumpPrefix h (k + 1) x = h (x ⟨k, hk⟩) * bumpPrefix h k x := by
  unfold bumpPrefix
  have hpt : ∀ j : Fin d, (if j.val < k + 1 then h (x j) else 1) =
      (if j = ⟨k, hk⟩ then h (x j) else 1) * (if j.val < k then h (x j) else 1) := by
    intro j
    by_cases hj : j = ⟨k, hk⟩
    · subst hj; simp
    · have hjv : j.val ≠ k := fun h' => hj (Fin.ext h')
      by_cases hlt : j.val < k
      · simp [hj, hlt, show j.val < k + 1 by omega]
      · simp [hj, hlt, show ¬ j.val < k + 1 by omega]
  rw [Finset.prod_congr rfl fun j _ => hpt j, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem bumpPrefix_add_smul (h : ℝ → ℝ) {k : ℕ} (hk : k < d) (x : Vec d) (s : ℝ) :
    bumpPrefix h k (x + s • unitVector ⟨k, hk⟩) = bumpPrefix h k x := by
  unfold bumpPrefix
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hlt : j.val < k
  · have hj : j ≠ ⟨k, hk⟩ := fun h' => by rw [h'] at hlt; exact lt_irrefl _ hlt
    simp only [hlt, ↓reduceIte, add_smul_unitVector_apply_ne x s hj]
  · simp only [hlt, ↓reduceIte]

/-- **The product form**: `g_k(x) = ∏_{j<k} h(x_j) Φ_k(x)` with `Φ_k` invariant along `e_j`,
`j < k`. -/
theorem bumpLineSeq_eq_prefix_mul (h : ℝ → ℝ) (f : Vec d → ℝ) :
    ∀ k ≤ d, ∃ Φ : Vec d → ℝ, (∀ x, bumpLineSeq h f k x = bumpPrefix h k x * Φ x) ∧
      ∀ (j : Fin d), j.val < k → ∀ (x : Vec d) (t : ℝ), Φ (x + t • unitVector j) = Φ x := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨f, fun x => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    simp [bumpLineSeq, bumpPrefix]
  | succ k ih =>
    intro hk
    have hk' : k < d := hk
    obtain ⟨Φ, hΦ, hinv⟩ := ih (by omega)
    refine ⟨fun x => ∫ s : ℝ, Φ (x + s • unitVector ⟨k, hk'⟩), fun x => ?_, ?_⟩
    · rw [bumpLineSeq_succ_of_lt h f hk', bumpPrefix_succ h hk']
      simp only [hΦ, bumpPrefix_add_smul h hk']
      rw [integral_const_mul]
      ring
    · intro j hj x t
      by_cases hjk : j = ⟨k, hk'⟩
      · subst hjk
        have e : ∀ s : ℝ, x + t • unitVector ⟨k, hk'⟩ + s • unitVector ⟨k, hk'⟩ =
            x + (s + t) • unitVector ⟨k, hk'⟩ := fun s => by rw [add_smul]; abel
        simp only [e]
        exact integral_add_right_eq_self (fun s => Φ (x + s • unitVector ⟨k, hk'⟩)) t
      · have hj' : j.val < k := by
          have : j.val ≠ k := fun h' => hjk (Fin.ext h')
          omega
        have e : ∀ s : ℝ, x + t • unitVector j + s • unitVector ⟨k, hk'⟩ =
            (x + s • unitVector ⟨k, hk'⟩) + t • unitVector j := fun s => by abel
        simp only [e, hinv j hj']

/-- A function invariant along every coordinate direction is constant. -/
theorem eq_of_invariant {Φ : Vec d → ℝ}
    (hinv : ∀ (j : Fin d) (x : Vec d) (t : ℝ), Φ (x + t • unitVector j) = Φ x) (x : Vec d) :
    Φ x = Φ 0 := by
  have hsum : ∀ s : Finset (Fin d), ∀ y : Vec d, Φ (y + ∑ j ∈ s, x j • unitVector j) = Φ y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      have e : y + (x a • unitVector a + ∑ j ∈ s, x j • unitVector j) =
          (y + ∑ j ∈ s, x j • unitVector j) + x a • unitVector a := by abel
      rw [Finset.sum_insert ha, e, hinv a, ih]
  have hx : x = (0 : Vec d) + ∑ j, x j • unitVector j := by
    funext i
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  rw [hx, hsum]

end Assembly

section Lemma510

/-- **The derivative of the half-line primitive**: `∂_v ∫_{-∞}^0 φ(x + s v) ds = φ(x)`. -/
theorem fderiv_setIntegral_Iic_apply {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {v : Vec d} (hv : v ≠ 0) (x : Vec d) :
    fderiv ℝ (fun y => ∫ s in Iic (0 : ℝ), φ (y + s • v)) x v = φ x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  rw [(hasFDerivAt_setIntegral_add_smul hφ1 hφc hv (Iic 0) x).fderiv]
  have hD : Integrable (fun s : ℝ => fderiv ℝ φ (x + s • v)) (volume.restrict (Iic 0)) :=
    integrable_comp_add_smul (hφ.continuous_fderiv (by simp)) (hφc.fderiv (𝕜 := ℝ)) hv x _
  rw [ContinuousLinearMap.integral_apply hD]
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => φ (x + s • v)) (fderiv ℝ φ (x + s • v) v) s := fun s =>
    ((hφ.differentiable (by simp)) (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hcont : Continuous (fun s : ℝ => φ (x + s • v)) :=
    hφ.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hint : IntegrableOn (fun s : ℝ => fderiv ℝ φ (x + s • v) v) (Iic 0) := by
    have hψ : Continuous fun y => fderiv ℝ φ y v :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψc : HasCompactSupport fun y => fderiv ℝ φ y v :=
      (hφc.fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by
        show (fderiv ℝ φ y) v = 0
        rw [h0]
        rfl)
    exact integrable_comp_add_smul hψ hψc hv x _
  have htend : Tendsto (fun s : ℝ => φ (x + s • v)) atBot (𝓝 0) := by
    obtain ⟨R, hR⟩ := exists_tsupport_subset_closedBall hφc
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atBot]
    refine ⟨-((R + ‖x‖ + 1) / ‖v‖) - 1, fun s hs => ?_⟩
    by_contra hne
    have hmem : x + s • v ∈ Metric.closedBall (0 : Vec d) R := hR (subset_tsupport _ (Ne.symm hne))
    have h1 := (abs_le.mp (abs_le_of_add_smul_mem hv (Metric.mem_ball_self one_pos) hmem)).1
    linarith
  rw [integral_Iic_of_hasDerivAt_of_tendsto hcont.continuousWithinAt (fun s _ => hderiv s) hint
    htend]
  simp

/-- **Lemma 5.10.** For every `f ∈ C_c^∞(ℝ^d)` with `∫ f = 0` there is `F ∈ C_c^∞(ℝ^d; ℝ^d)` with
`∇·F = f`. -/
theorem lemma_5_10 {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hmean : ∫ x, f x = 0) :
    ∃ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      ∀ x, ∑ i, coordinateDerivative i (fun y => F y i) x = f x := by
  obtain ⟨R₀, hR₀⟩ := exists_tsupport_subset_closedBall hfc
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max R₀ 1 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfR : ∀ x, R < ‖x‖ → f x = 0 := fun x hx => by
    by_contra hne
    have h1 := hR₀ (subset_tsupport _ hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have : R₀ ≤ R := by rw [hRdef]; exact le_max_left _ _
    linarith
  let b : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ → ℝ, h = b.normed volume := ⟨_, rfl⟩
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := by rw [hhdef]; exact b.contDiff_normed
  have hh1 : ∫ t : ℝ, h t = 1 := by rw [hhdef]; exact b.integral_normed
  have hhR : ∀ t, R < |t| → h t = 0 := fun t ht => by
    have hns : t ∉ Function.support h := by
      rw [hhdef, b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
      exact not_lt.2 ht.le
    simpa using hns
  have hspec := bumpLineSeq_spec hR.le hh hhR hf hfR
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → Vec d → ℝ, g = bumpLineSeq h f := ⟨_, rfl⟩
  rw [← hgdef] at hspec
  have hg0 : g 0 = f := by rw [hgdef]; rfl
  -- the functions `φᵢ = gᵢ - g_{i+1}`
  have hφ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun y => g i.val y - g (i.val + 1) y) ∧
      ∀ y, R < ‖y‖ → g i.val y - g (i.val + 1) y = 0 := by
    intro i
    obtain ⟨h1, h1R⟩ := hspec i.val i.isLt.le
    obtain ⟨h2, h2R⟩ := hspec (i.val + 1) i.isLt
    exact ⟨h1.sub h2, fun y hy => by rw [h1R y hy, h2R y hy, sub_zero]⟩
  have hφc : ∀ i : Fin d, HasCompactSupport (fun y => g i.val y - g (i.val + 1) y) :=
    fun i => hasCompactSupport_of_vanish (hφ i).2
  obtain ⟨F, hFdef⟩ : ∃ F : Vec d → Vec d, F = fun x i =>
      ∫ s in Iic (0 : ℝ), (g i.val (x + s • unitVector i) - g (i.val + 1) (x + s • unitVector i)) :=
    ⟨_, rfl⟩
  have hFi : ∀ i : Fin d, (fun x => F x i) = fun x => ∫ s in Iic (0 : ℝ),
      (fun y => g i.val y - g (i.val + 1) y) (x + s • unitVector i) := fun i => by
    rw [hFdef]
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    refine contDiff_pi.2 fun i => ?_
    rw [hFi i]
    exact contDiff_setIntegral_add_smul (hφ i).1 (hφc i) (unitVector_ne_zero i) (Iic 0)
  -- `F` vanishes outside the box
  have hFR : ∀ x, R < ‖x‖ → F x = 0 := by
    intro x hx
    funext i
    show F x i = 0
    have hFxi : F x i = ∫ s in Iic (0 : ℝ),
        (g i.val (x + s • unitVector i) - g (i.val + 1) (x + s • unitVector i)) := by
      rw [hFdef]
    rw [hFxi]
    obtain ⟨j, hj⟩ := exists_lt_abs_of_lt_norm hR.le hx
    have hzero : ∀ y : Vec d, R < |y j| → g i.val y - g (i.val + 1) y = 0 := fun y hy =>
      (hφ i).2 y (lt_of_lt_of_le hy (by
        have := norm_le_pi_norm y j; rwa [Real.norm_eq_abs] at this))
    by_cases hji : j = i
    · subst hji
      rcases lt_or_gt_of_ne (show x j ≠ 0 by intro h0; rw [h0, abs_zero] at hj; linarith)
        with hneg | hpos
      · have hxj : x j < -R := by
          rw [abs_of_neg hneg] at hj; linarith
        refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => hzero _ ?_
        rw [add_smul_unitVector_apply_self]
        have : s ≤ 0 := hs
        rw [abs_of_neg (by linarith)]
        linarith
      · have hxj : R < x j := by rw [abs_of_pos hpos] at hj; exact hj
        have hint := integrable_comp_add_smul ((hφ j).1.continuous) (hφc j)
          (unitVector_ne_zero j) x univ
        rw [Measure.restrict_univ] at hint
        have hsplit := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hint
        rw [compl_Iic] at hsplit
        have hIoi : ∫ s in Ioi (0 : ℝ),
            (g j.val (x + s • unitVector j) - g (j.val + 1) (x + s • unitVector j)) = 0 := by
          refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => hzero _ ?_
          rw [add_smul_unitVector_apply_self]
          have : 0 < s := hs
          rw [abs_of_pos (by linarith)]
          linarith
        have hline := integral_bumpLineSeq_succ hh1 f j.isLt x
        rw [← hgdef] at hline
        have hfull : ∫ s : ℝ,
            (g j.val (x + s • unitVector j) - g (j.val + 1) (x + s • unitVector j)) = 0 := by
          have i1 := integrable_comp_add_smul ((hspec j.val j.isLt.le).1.continuous)
            (hasCompactSupport_of_vanish (hspec j.val j.isLt.le).2) (unitVector_ne_zero j) x univ
          have i2 := integrable_comp_add_smul ((hspec (j.val + 1) j.isLt).1.continuous)
            (hasCompactSupport_of_vanish (hspec (j.val + 1) j.isLt).2) (unitVector_ne_zero j) x univ
          rw [Measure.restrict_univ] at i1 i2
          rw [integral_sub i1 i2, hline, sub_self]
        rw [hIoi, add_zero] at hsplit
        rw [hsplit, hfull]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun s _ => hzero _ ?_
      rw [add_smul_unitVector_apply_ne x s hji]
      exact hj
  have hFc : HasCompactSupport F := hasCompactSupport_of_vanish hFR
  -- the divergence telescopes
  have hdiv : ∀ x, ∑ i, coordinateDerivative i (fun y => F y i) x = f x - g d x := by
    intro x
    have hi : ∀ i : Fin d, coordinateDerivative i (fun y => F y i) x =
        g i.val x - g (i.val + 1) x := by
      intro i
      unfold coordinateDerivative
      rw [hFi i]
      exact fderiv_setIntegral_Iic_apply (hφ i).1 (hφc i) (unitVector_ne_zero i) x
    rw [Finset.sum_congr rfl fun i _ => hi i,
      Fin.sum_univ_eq_sum_range (fun k => g k x - g (k + 1) x) d, Finset.sum_range_sub', hg0]
  -- `g_d = 0`
  obtain ⟨Φ, hΦ, hinv⟩ := bumpLineSeq_eq_prefix_mul h f d le_rfl
  rw [← hgdef] at hΦ
  have hconst : ∀ x, Φ x = Φ 0 := eq_of_invariant fun j => hinv j j.isLt
  have hgd : ∀ x, g d x = (∏ j : Fin d, h (x j)) * Φ 0 := by
    intro x
    rw [hΦ x, hconst x]
    congr 1
    unfold bumpPrefix
    exact Finset.prod_congr rfl fun j _ => by simp only [j.isLt, ↓reduceIte]
  have hH : ∫ x : Vec d, ∏ j : Fin d, h (x j) = 1 := by
    have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ : Fin d => h)
      (μ := fun _ => (volume : Measure ℝ))
    rw [← volume_pi] at this
    rw [this, hh1, Finset.prod_const_one]
  have hint_g : ∫ x, g d x = 0 := by
    have hfint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
    have hspat : ∀ i : Fin d, IsSpatialTest Set.univ (fun y => F y i) := fun i =>
      ⟨(contDiff_pi.1 hFsmooth) i, hFc.comp_left (g := fun v : Vec d => v i) rfl, subset_univ _⟩
    have hdint : ∀ i : Fin d, Integrable (coordinateDerivative i (fun y => F y i)) := fun i =>
      (isSpatialTest_coordinateDerivative (hspat i) i).1.continuous.integrable_of_hasCompactSupport
        (isSpatialTest_coordinateDerivative (hspat i) i).2.1
    have e : (fun x => g d x) = fun x => f x - ∑ i, coordinateDerivative i (fun y => F y i) x :=
      funext fun x => by rw [hdiv x]; ring
    rw [e, integral_sub hfint (integrable_finsetSum _ fun i _ => hdint i),
      integral_finsetSum _ fun i _ => hdint i, hmean]
    simp only [fun i => integral_coordinateDerivative_univ_eq_zero (hspat i) i,
      Finset.sum_const_zero, sub_zero]
  have hΦ0 : Φ 0 = 0 := by
    have : ∫ x, g d x = Φ 0 := by
      simp only [hgd]
      rw [integral_mul_const, hH, one_mul]
    rw [← this, hint_g]
  refine ⟨F, hFsmooth, hFc, fun x => ?_⟩
  rw [hdiv x, hgd x, hΦ0, mul_zero, sub_zero]

end Lemma510

end QSH
