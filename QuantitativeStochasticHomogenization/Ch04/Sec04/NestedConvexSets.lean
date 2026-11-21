import Mathlib

/-!
# Nested closed convex sets and lexicographic minimizers

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, pp. 155-156: the existence of the coordinate minimizers of the objective `I` and of the
minimizer of smallest `L²` norm.

In a Banach space carrying a quadratic gauge `Q` (a nonnegative function satisfying the
parallelogram identity and dominating the square of the norm), a decreasing sequence of nonempty
closed convex sets on which `Q` is bounded has a nonempty intersection: points that almost minimize
`Q` on the successive sets form a Cauchy sequence. This replaces weak compactness. As a consequence,
a continuous convex function `f ≥ 0` on a closed convex set `K` with `Q`-bounded sublevel sets has a
minimizer which, among all minimizers, minimizes a second continuous convex function `g ≥ 0`.
-/

open Filter Topology

noncomputable section

namespace QSH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic gauge on `E`: nonnegative, satisfying the parallelogram identity and dominating the
square of the norm. -/
structure IsQuadraticGauge (Q : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ Q x
  parallelogram : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y
  norm_sq_le : ∀ x, ‖x‖ ^ 2 ≤ Q x

namespace IsQuadraticGauge

variable {Q : E → ℝ}

omit [NormedSpace ℝ E] in
theorem map_zero (hQ : IsQuadraticGauge Q) : Q 0 = 0 := by
  have h := hQ.parallelogram 0 0
  simp only [add_zero, sub_zero] at h
  linarith

omit [NormedSpace ℝ E] in
theorem map_add_self (hQ : IsQuadraticGauge Q) (x : E) : Q (x + x) = 4 * Q x := by
  have h := hQ.parallelogram x x
  rw [sub_self, hQ.map_zero] at h
  linarith

/-- The parallelogram identity with the midpoint. -/
theorem sub_eq_midpoint (hQ : IsQuadraticGauge Q) (x y : E) :
    Q (x - y) = 2 * Q x + 2 * Q y - 4 * Q ((1 / 2 : ℝ) • (x + y)) := by
  have hmid : (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x + y) = x + y := by
    rw [← add_smul]; norm_num
  have h1 := hQ.map_add_self ((1 / 2 : ℝ) • (x + y))
  rw [hmid] at h1
  have h2 := hQ.parallelogram x y
  linarith

end IsQuadraticGauge

variable [CompleteSpace E]

/-- **Nested closed convex sets.** A decreasing sequence of nonempty closed convex sets on which a
quadratic gauge is bounded has a nonempty intersection. -/
theorem nonempty_iInter_of_isQuadraticGauge {Q : E → ℝ} (hQ : IsQuadraticGauge Q)
    (A : ℕ → Set E) (hanti : Antitone A) (hne : ∀ n, (A n).Nonempty)
    (hclosed : ∀ n, IsClosed (A n)) (hconv : ∀ n, Convex ℝ (A n))
    (hbdd : BddAbove (Q '' A 0)) : (⋂ n, A n).Nonempty := by
  obtain ⟨M, hM⟩ := hbdd
  have hbelow : ∀ n, BddBelow (Q '' A n) := fun n =>
    ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hQ.nonneg x⟩
  have hne' : ∀ n, (Q '' A n).Nonempty := fun n => (hne n).image Q
  set q : ℕ → ℝ := fun n => sInf (Q '' A n) with hq_def
  have hq_le : ∀ n, ∀ x ∈ A n, q n ≤ Q x := fun n x hx =>
    csInf_le (hbelow n) ⟨x, hx, rfl⟩
  have hq_mono : Monotone q := fun n m hnm =>
    csInf_le_csInf (hbelow n) (hne' m) (Set.image_mono (hanti hnm))
  have hq_bdd : ∀ n, q n ≤ M := fun n => by
    obtain ⟨x, hx⟩ := hne n
    exact (hq_le n x hx).trans (hM ⟨x, hanti (Nat.zero_le n) hx, rfl⟩)
  have hx_ex : ∀ n, ∃ x ∈ A n, Q x < q n + 1 / ((n : ℝ) + 1) := fun n => by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne' n) (lt_add_of_pos_right (q n) hpos)
    exact ⟨x, hx, hlt⟩
  choose x hxA hxQ using hx_ex
  have hL : Tendsto q atTop (𝓝 (⨆ n, q n)) :=
    tendsto_atTop_ciSup hq_mono ⟨M, by rintro _ ⟨n, rfl⟩; exact hq_bdd n⟩
  set L := ⨆ n, q n
  have hqL : ∀ n, q n ≤ L := fun n =>
    le_ciSup ⟨M, by rintro _ ⟨k, rfl⟩; exact hq_bdd k⟩ n
  -- the key estimate
  have hkey : ∀ n m, n ≤ m →
      ‖x n - x m‖ ^ 2 ≤ 2 * (L - q n) + 4 / ((n : ℝ) + 1) := by
    intro n m hnm
    have hmA : x m ∈ A n := hanti hnm (hxA m)
    have hmid : (1 / 2 : ℝ) • (x n + x m) ∈ A n := by
      have := (hconv n) (hxA n) hmA (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using this
    have h1 := hQ.sub_eq_midpoint (x n) (x m)
    have h2 := hq_le n _ hmid
    have h3 := hxQ n
    have h4 := hxQ m
    have h5 : q m ≤ L := hqL m
    have h6 : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    have h7 := hQ.norm_sq_le (x n - x m)
    have h8 : (4 : ℝ) / ((n : ℝ) + 1) = 4 * (1 / ((n : ℝ) + 1)) := by ring
    nlinarith
  set b : ℕ → ℝ := fun N => 2 * Real.sqrt (2 * (L - q N) + 4 / ((N : ℝ) + 1)) with hb_def
  have hb : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => L - q N) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := L)).sub hL
    have h2 : Tendsto (fun N : ℕ => 4 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 : ℝ)
      rw [mul_zero] at h
      refine h.congr fun N => ?_
      ring
    have h3 : Tendsto (fun N : ℕ => 2 * (L - q N) + 4 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (h1.const_mul 2).add h2
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h3
    simpa [hb_def, Function.comp_def] using h4.const_mul 2
  have hdist : ∀ n m N, N ≤ n → N ≤ m → dist (x n) (x m) ≤ b N := by
    intro n m N hn hm
    have hle : ∀ k, N ≤ k → dist (x N) (x k) ≤ Real.sqrt (2 * (L - q N) + 4 / ((N : ℝ) + 1)) :=
      fun k hk => by
        rw [dist_eq_norm]
        exact Real.le_sqrt_of_sq_le (hkey N k hk)
    calc dist (x n) (x m) ≤ dist (x N) (x n) + dist (x N) (x m) := dist_triangle_left _ _ _
      _ ≤ b N := by rw [hb_def]; linarith [hle n hn, hle m hm]
  have hcauchy : CauchySeq x := cauchySeq_of_le_tendsto_0 b hdist hb
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, Set.mem_iInter.2 fun k => ?_⟩
  refine (hclosed k).mem_of_tendsto hy ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  exact hanti hn (hxA n)

/-- **Lexicographic minimizer.** A continuous convex function `f ≥ 0` on a nonempty closed convex
set `K`, whose sublevel sets in `K` are bounded for a quadratic gauge, has a minimizer on `K`
which minimizes a second continuous convex function `g ≥ 0` among all minimizers of `f`. -/
theorem exists_lexicographic_minimizer {Q : E → ℝ} (hQ : IsQuadraticGauge Q) {K : Set E}
    (hK : IsClosed K) (hKne : K.Nonempty) {f g : E → ℝ}
    (hf : Continuous f) (hfc : ConvexOn ℝ K f) (hf0 : ∀ x ∈ K, 0 ≤ f x)
    (hg : Continuous g) (hgc : ConvexOn ℝ K g) (hg0 : ∀ x ∈ K, 0 ≤ g x)
    (hcoer : ∀ t : ℝ, BddAbove (Q '' {x | x ∈ K ∧ f x ≤ t})) :
    ∃ x ∈ K, (∀ y ∈ K, f x ≤ f y) ∧ ∀ y ∈ K, f y ≤ f x → g x ≤ g y := by
  have hclosed_sub : ∀ {S : Set E} {h : E → ℝ}, IsClosed S → Continuous h → ∀ t : ℝ,
      IsClosed {x | x ∈ S ∧ h x ≤ t} := fun hS hh t =>
    hS.inter (isClosed_le hh continuous_const)
  -- first stage: minimize `f`
  set m := sInf (f '' K) with hm_def
  have hfb : BddBelow (f '' K) := ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact hf0 x hx⟩
  set A : ℕ → Set E := fun n => {x | x ∈ K ∧ f x ≤ m + 1 / ((n : ℝ) + 1)}
  have hAanti : Antitone A := by
    intro n k hnk x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1)
    linarith
  have hAne : ∀ n, (A n).Nonempty := fun n => by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hKne.image f) (lt_add_of_pos_right m hpos)
    exact ⟨x, hx, hlt.le⟩
  have hA0 : BddAbove (Q '' A 0) := by
    refine (hcoer (m + 1)).mono (Set.image_mono ?_)
    intro x hx
    exact ⟨hx.1, by simpa using hx.2⟩
  obtain ⟨x₀, hx₀⟩ := nonempty_iInter_of_isQuadraticGauge hQ A hAanti hAne
    (fun n => hclosed_sub hK hf _) (fun n => hfc.convex_le _) hA0
  have hx₀' : ∀ n, x₀ ∈ A n := Set.mem_iInter.1 hx₀
  have hx₀K : x₀ ∈ K := (hx₀' 0).1
  have hm_le : ∀ y ∈ K, m ≤ f y := fun y hy => csInf_le hfb ⟨y, hy, rfl⟩
  have hfx₀ : f x₀ ≤ m := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    linarith [(hx₀' n).2]
  -- second stage: minimize `g` on the minimizers
  set Mset : Set E := {x | x ∈ K ∧ f x ≤ m}
  have hMclosed : IsClosed Mset := hclosed_sub hK hf m
  have hMconv : Convex ℝ Mset := hfc.convex_le m
  have hMK : Mset ⊆ K := fun x hx => hx.1
  have hMne : Mset.Nonempty := ⟨x₀, hx₀K, hfx₀⟩
  set N := sInf (g '' Mset) with hN_def
  have hgb : BddBelow (g '' Mset) := ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact hg0 x hx.1⟩
  set B : ℕ → Set E := fun n => {x | x ∈ Mset ∧ g x ≤ N + 1 / ((n : ℝ) + 1)}
  have hBanti : Antitone B := by
    intro n k hnk x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1)
    linarith
  have hBne : ∀ n, (B n).Nonempty := fun n => by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hMne.image g) (lt_add_of_pos_right N hpos)
    exact ⟨x, hx, hlt.le⟩
  have hB0 : BddAbove (Q '' B 0) := by
    refine (hcoer m).mono (Set.image_mono ?_)
    intro x hx
    exact hx.1
  obtain ⟨x, hx⟩ := nonempty_iInter_of_isQuadraticGauge hQ B hBanti hBne
    (fun n => hclosed_sub hMclosed hg _) (fun n => (hgc.subset hMK hMconv).convex_le _) hB0
  have hx' : ∀ n, x ∈ B n := Set.mem_iInter.1 hx
  have hxM : x ∈ Mset := (hx' 0).1
  have hgx : g x ≤ N := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    linarith [(hx' n).2]
  refine ⟨x, hxM.1, fun y hy => hxM.2.trans (hm_le y hy), fun y hy hyx => ?_⟩
  have hyM : y ∈ Mset := ⟨hy, hyx.trans hxM.2⟩
  exact hgx.trans (csInf_le hgb ⟨y, hyM, rfl⟩)

end QSH
