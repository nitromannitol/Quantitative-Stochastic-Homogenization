import QuantitativeStochasticHomogenization.Ch04.Sec04.NestedConvexSets

/-!
# Measurable dependence of lexicographic minimizers

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 156: the measurability of the least-norm coordinate minimizers.

Let `K ω` be closed convex sets depending on a parameter `ω`, on which a continuous convex
function `f ≥ 0` has `Q`-bounded sublevel sets, and let `x ω` be the unique minimizer of `f` on
`K ω` which minimizes a second continuous convex function `g ≥ 0` among the minimizers. If the
sets `K ω` contain measurable sequences `h n ω` which are dense in `K ω`, then `x` is measurable:
the infima of `f`, of `g` on the almost minimizers of `f`, and of `Q` on the almost lexicographic
minimizers are countable infima over the dense sequence, and the members of the sequence that
almost minimize `Q` there converge to `x ω` (the parallelogram argument of
`nonempty_iInter_of_isQuadraticGauge`).
-/

open Filter Topology

noncomputable section

namespace QSH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Almost minimizers of a quadratic gauge on nested convex sets form a Cauchy sequence.** -/
theorem cauchySeq_of_almost_minimizers {Q : E → ℝ} (hQ : IsQuadraticGauge Q)
    (B : ℕ → Set E) (hanti : Antitone B) (hconv : ∀ n, Convex ℝ (B n))
    (hbdd : BddAbove (Q '' B 0)) (ε : ℕ → ℝ) (hεanti : Antitone ε)
    (hε : Tendsto ε atTop (𝓝 0)) (x : ℕ → E) (hxB : ∀ n, x n ∈ B n)
    (hxQ : ∀ n, ∀ y ∈ B n, Q (x n) ≤ Q y + ε n) : CauchySeq x := by
  obtain ⟨M, hM⟩ := hbdd
  have hbelow : ∀ n, BddBelow (Q '' B n) := fun n =>
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact hQ.nonneg y⟩
  have hne' : ∀ n, (Q '' B n).Nonempty := fun n => ⟨_, x n, hxB n, rfl⟩
  set q : ℕ → ℝ := fun n => sInf (Q '' B n) with hq_def
  have hq_le : ∀ n, ∀ y ∈ B n, q n ≤ Q y := fun n y hy => csInf_le (hbelow n) ⟨y, hy, rfl⟩
  have hq_mono : Monotone q := fun n m hnm =>
    csInf_le_csInf (hbelow n) (hne' m) (Set.image_mono (hanti hnm))
  have hq_bdd : ∀ n, q n ≤ M := fun n =>
    (hq_le n (x n) (hxB n)).trans (hM ⟨x n, hanti (Nat.zero_le n) (hxB n), rfl⟩)
  have hxq : ∀ n, Q (x n) ≤ q n + ε n := fun n => by
    have : Q (x n) - ε n ≤ q n :=
      le_csInf (hne' n) (by rintro _ ⟨y, hy, rfl⟩; linarith [hxQ n y hy])
    linarith
  have hL : Tendsto q atTop (𝓝 (⨆ n, q n)) :=
    tendsto_atTop_ciSup hq_mono ⟨M, by rintro _ ⟨n, rfl⟩; exact hq_bdd n⟩
  set L := ⨆ n, q n
  have hqL : ∀ n, q n ≤ L := fun n =>
    le_ciSup ⟨M, by rintro _ ⟨k, rfl⟩; exact hq_bdd k⟩ n
  have hkey : ∀ n m, n ≤ m → ‖x n - x m‖ ^ 2 ≤ 2 * (L - q n) + 4 * ε n := by
    intro n m hnm
    have hmB : x m ∈ B n := hanti hnm (hxB m)
    have hmid : (1 / 2 : ℝ) • (x n + x m) ∈ B n := by
      have := (hconv n) (hxB n) hmB (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using this
    have h1 := hQ.sub_eq_midpoint (x n) (x m)
    have h2 := hq_le n _ hmid
    have h3 := hxQ n _ hmid
    have h4 := hxq m
    have h5 := hqL m
    have h6 := hεanti hnm
    have h7 := hQ.norm_sq_le (x n - x m)
    nlinarith
  set b : ℕ → ℝ := fun N => 2 * Real.sqrt (2 * (L - q N) + 4 * ε N) with hb_def
  have hb : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => L - q N) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := L)).sub hL
    have h3 : Tendsto (fun N : ℕ => 2 * (L - q N) + 4 * ε N) atTop (𝓝 0) := by
      simpa using (h1.const_mul 2).add (hε.const_mul 4)
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h3
    simpa [hb_def, Function.comp_def] using h4.const_mul 2
  refine cauchySeq_of_le_tendsto_0 b (fun n m N hn hm => ?_) hb
  have hle : ∀ k, N ≤ k → dist (x N) (x k) ≤ Real.sqrt (2 * (L - q N) + 4 * ε N) :=
    fun k hk => by
      rw [dist_eq_norm]
      exact Real.le_sqrt_of_sq_le (hkey N k hk)
  calc dist (x n) (x m) ≤ dist (x N) (x n) + dist (x N) (x m) := dist_triangle_left _ _ _
    _ ≤ b N := by rw [hb_def]; linarith [hle n hn, hle m hm]

/-! ## Countable infima with a fallback index -/

/-- The infimum of `v n` over the indices `n` with `P n`, as a countable infimum: the other
indices take the value at the first index with `P`. -/
def condInf (P : ℕ → Prop) [DecidablePred P] (v : ℕ → ℝ) (hP : ∃ n, P n) : ℝ :=
  ⨅ n, if P n then v n else v (Nat.find hP)

theorem condInf_le {P : ℕ → Prop} [DecidablePred P] {v : ℕ → ℝ} (hP : ∃ n, P n)
    (hv : ∀ n, 0 ≤ v n) {n : ℕ} (hn : P n) : condInf P v hP ≤ v n := by
  refine (ciInf_le ⟨0, ?_⟩ n).trans (by simp [hn])
  rintro _ ⟨k, rfl⟩
  dsimp only
  split_ifs <;> exact hv _

theorem le_condInf {P : ℕ → Prop} [DecidablePred P] {v : ℕ → ℝ} (hP : ∃ n, P n) {c : ℝ}
    (hc : ∀ n, P n → c ≤ v n) : c ≤ condInf P v hP := by
  refine le_ciInf fun n => ?_
  split_ifs with h
  · exact hc n h
  · exact hc _ (Nat.find_spec hP)

theorem exists_lt_of_condInf_lt {P : ℕ → Prop} [DecidablePred P] {v : ℕ → ℝ}
    (hP : ∃ n, P n) {c : ℝ} (hc : condInf P v hP < c) : ∃ n, P n ∧ v n < c := by
  by_contra hcon
  exact absurd (le_condInf hP fun n hn => le_of_not_gt fun h' => hcon ⟨n, hn, h'⟩) (not_le.2 hc)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem measurable_nat_index {β : Type*} [MeasurableSpace β] {k : Ω → ℕ} (hk : Measurable k)
    {u : ℕ → Ω → β} (hu : ∀ n, Measurable (u n)) : Measurable fun ω => u (k ω) ω := by
  intro s hs
  have : (fun ω => u (k ω) ω) ⁻¹' s = ⋃ n, k ⁻¹' {n} ∩ u n ⁻¹' s := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun n => (hk (measurableSet_singleton n)).inter (hu n hs)

theorem measurable_condInf {P : Ω → ℕ → Prop} [∀ ω, DecidablePred (P ω)] {v : Ω → ℕ → ℝ}
    (hP : ∀ ω, ∃ n, P ω n) (hPm : ∀ n, MeasurableSet {ω | P ω n})
    (hv : ∀ n, Measurable fun ω => v ω n) :
    Measurable fun ω => condInf (P ω) (v ω) (hP ω) := by
  unfold condInf
  refine Measurable.iInf fun n => Measurable.ite (hPm n) (hv n) ?_
  exact measurable_nat_index (measurable_find hP hPm) hv

/-! ## Measurable lexicographic minimizers -/

variable [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- A point of the closure of a sequence lying in an open set is approximated by members of the
sequence in that set, with a continuous function almost not larger. -/
theorem exists_index_of_mem_closure {h : ℕ → E} {y : E} (hy : y ∈ closure (Set.range h))
    {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) {φ : E → ℝ} (hφ : Continuous φ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ n, h n ∈ U ∧ φ (h n) < φ y + δ := by
  have hO : IsOpen (U ∩ φ ⁻¹' Set.Iio (φ y + δ)) := hU.inter (isOpen_Iio.preimage hφ)
  obtain ⟨_, ⟨hzU, hzφ⟩, ⟨n, rfl⟩⟩ :=
    mem_closure_iff.1 hy _ hO ⟨hyU, by simp [hδ]⟩
  exact ⟨n, hzU, hzφ⟩

/-- **Measurability of lexicographic minimizers** from a measurable dense sequence, for functions
depending on the parameter. -/
theorem measurable_lexicographic_minimizer_param {Q : E → ℝ} (hQ : IsQuadraticGauge Q)
    (hQc : Continuous Q) {K : Ω → Set E} (hK : ∀ ω, IsClosed (K ω))
    {F G : Ω → E → ℝ} (hF : ∀ ω, Continuous (F ω)) (hfc : ∀ ω, ConvexOn ℝ (K ω) (F ω))
    (hf0 : ∀ ω, ∀ y ∈ K ω, 0 ≤ F ω y) (hG : ∀ ω, Continuous (G ω))
    (hgc : ∀ ω, ConvexOn ℝ (K ω) (G ω)) (hg0 : ∀ ω, ∀ y ∈ K ω, 0 ≤ G ω y)
    (hcoer : ∀ ω t, BddAbove (Q '' {y | y ∈ K ω ∧ F ω y ≤ t}))
    (h : ℕ → Ω → E) (hh : ∀ n, Measurable (h n)) (hmem : ∀ n ω, h n ω ∈ K ω)
    (hFm : ∀ n, Measurable fun ω => F ω (h n ω)) (hGm : ∀ n, Measurable fun ω => G ω (h n ω))
    (hdense : ∀ ω, K ω ⊆ closure (Set.range fun n => h n ω))
    (x : Ω → E) (hxK : ∀ ω, x ω ∈ K ω) (hxf : ∀ ω, ∀ y ∈ K ω, F ω (x ω) ≤ F ω y)
    (hxg : ∀ ω, ∀ y ∈ K ω, F ω y ≤ F ω (x ω) → G ω (x ω) ≤ G ω y)
    (huniq : ∀ ω, ∀ y ∈ K ω, (∀ z ∈ K ω, F ω y ≤ F ω z) →
      (∀ z ∈ K ω, F ω z ≤ F ω y → G ω y ≤ G ω z) → y = x ω) :
    Measurable x := by
  classical
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hε_def
  have hεpos : ∀ j, 0 < ε j := fun j => by positivity
  have hεanti : Antitone ε := fun j k hjk =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hfh : ∀ n, Measurable fun ω => F ω (h n ω) := hFm
  have hgh : ∀ n, Measurable fun ω => G ω (h n ω) := hGm
  have hQh : ∀ n, Measurable fun ω => Q (h n ω) := fun n => hQc.measurable.comp (hh n)
  -- the infimum of `f`
  set m : Ω → ℝ := fun ω => ⨅ n, F ω (h n ω) with hm_def
  have hm_meas : Measurable m := Measurable.iInf hfh
  have hm_eq : ∀ ω, m ω = F ω (x ω) := by
    intro ω
    have hbdd : BddBelow (Set.range fun n => F ω (h n ω)) :=
      ⟨0, by rintro _ ⟨n, rfl⟩; exact hf0 ω _ (hmem n ω)⟩
    refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_)
      (le_ciInf fun n => hxf ω _ (hmem n ω))
    obtain ⟨n, -, hn⟩ := exists_index_of_mem_closure (hdense ω (hxK ω)) isOpen_univ
      (Set.mem_univ _) (hF ω) hδ
    exact (ciInf_le hbdd n).trans_lt hn
  -- the existence of members of the dense sequence in open sets around `x ω`
  have hex : ∀ ω (U : Set E), IsOpen U → x ω ∈ U → ∃ n, h n ω ∈ U := fun ω U hU hxU => by
    obtain ⟨n, hn, -⟩ := exists_index_of_mem_closure (hdense ω (hxK ω)) hU hxU (hF ω) one_pos
    exact ⟨n, hn⟩
  -- the infimum of `g` on the almost minimizers of `f`
  set PA : ℕ → Ω → ℕ → Prop := fun j ω n => F ω (h n ω) < m ω + ε j
  have hPA : ∀ j ω, ∃ n, PA j ω n := fun j ω => by
    obtain ⟨n, hn⟩ := hex ω {y | F ω y < m ω + ε j} (isOpen_lt (hF ω) continuous_const)
      (by simp [hm_eq, hεpos j])
    exact ⟨n, hn⟩
  have hPA_meas : ∀ j n, MeasurableSet {ω | PA j ω n} := fun j n =>
    measurableSet_lt (hfh n) (hm_meas.add_const _)
  set Nj : ℕ → Ω → ℝ := fun j ω => condInf (PA j ω) (fun n => G ω (h n ω)) (hPA j ω)
  have hNj_meas : ∀ j, Measurable (Nj j) := fun j =>
    measurable_condInf (hPA j) (hPA_meas j) hgh
  have hNj_le : ∀ j ω, Nj j ω ≤ G ω (x ω) := by
    intro j ω
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨n, hn, hgn⟩ := exists_index_of_mem_closure (hdense ω (hxK ω))
      (isOpen_lt (hF ω) continuous_const) (show F ω (x ω) < m ω + ε j by simp [hm_eq, hεpos j]) (hG ω) hδ
    exact (condInf_le (hPA j ω) (fun k => hg0 ω _ (hmem k ω)) hn).trans_lt hgn
  set N : Ω → ℝ := fun ω => ⨆ j, Nj j ω
  have hN_meas : Measurable N := Measurable.iSup hNj_meas
  have hN_eq : ∀ ω, N ω = G ω (x ω) := by
    intro ω
    have hbdd : BddAbove (Set.range fun j => Nj j ω) :=
      ⟨G ω (x ω), by rintro _ ⟨j, rfl⟩; exact hNj_le j ω⟩
    refine le_antisymm (ciSup_le fun j => hNj_le j ω) ?_
    set L := N ω
    have hNL : ∀ j, Nj j ω ≤ L := fun j => le_ciSup hbdd j
    set D : ℕ → Set E := fun j => {y | y ∈ {y | y ∈ K ω ∧ F ω y ≤ m ω + ε j} ∧ G ω y ≤ L + ε j}
    have hDanti : Antitone D := by
      intro j k hjk y hy
      exact ⟨⟨hy.1.1, hy.1.2.trans (by linarith [hεanti hjk])⟩, hy.2.trans
        (by linarith [hεanti hjk])⟩
    have hDne : ∀ j, (D j).Nonempty := by
      intro j
      obtain ⟨n, hn, hgn⟩ := exists_lt_of_condInf_lt (hPA j ω)
        (show Nj j ω < L + ε j by linarith [hNL j, hεpos j])
      exact ⟨h n ω, ⟨hmem n ω, hn.le⟩, hgn.le⟩
    have hDclosed : ∀ j, IsClosed (D j) := fun j =>
      ((hK ω).inter (isClosed_le (hF ω) continuous_const)).inter (isClosed_le (hG ω) continuous_const)
    have hDconv : ∀ j, Convex ℝ (D j) := fun j =>
      ((hgc ω).subset (fun y hy => hy.1) ((hfc ω).convex_le _)).convex_le _
    have hD0 : BddAbove (Q '' D 0) :=
      (hcoer ω (m ω + ε 0)).mono (Set.image_mono fun y hy => hy.1)
    obtain ⟨y, hy⟩ := nonempty_iInter_of_isQuadraticGauge hQ D hDanti hDne hDclosed hDconv hD0
    have hy' : ∀ j, y ∈ D j := Set.mem_iInter.1 hy
    have hyK : y ∈ K ω := (hy' 0).1.1
    have hfy : F ω y ≤ F ω (x ω) := by
      rw [← hm_eq]
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact lt_of_le_of_lt (hy' j).1.2 (by simp only [hε_def]; linarith)
    have hgy : G ω y ≤ L := by
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact lt_of_le_of_lt (hy' j).2 (by simp only [hε_def]; linarith)
    exact (hxg ω y hyK hfy).trans hgy
  -- the infimum of `Q` on the almost lexicographic minimizers
  set PB : ℕ → Ω → ℕ → Prop := fun j ω n => F ω (h n ω) < m ω + ε j ∧ G ω (h n ω) < N ω + ε j
  have hBopen : ∀ j ω, IsOpen {y : E | F ω y < m ω + ε j ∧ G ω y < N ω + ε j} := fun j ω =>
    (isOpen_lt (hF ω) continuous_const).inter (isOpen_lt (hG ω) continuous_const)
  have hxB : ∀ j ω, x ω ∈ {y : E | F ω y < m ω + ε j ∧ G ω y < N ω + ε j} := fun j ω =>
    ⟨by simp [hm_eq, hεpos j], by simp [hN_eq, hεpos j]⟩
  have hPB : ∀ j ω, ∃ n, PB j ω n := fun j ω => hex ω _ (hBopen j ω) (hxB j ω)
  have hPB_meas : ∀ j n, MeasurableSet {ω | PB j ω n} := fun j n =>
    (measurableSet_lt (hfh n) (hm_meas.add_const _)).inter
      (measurableSet_lt (hgh n) (hN_meas.add_const _))
  set β : ℕ → Ω → ℝ := fun j ω => condInf (PB j ω) (fun n => Q (h n ω)) (hPB j ω)
  have hβ_meas : ∀ j, Measurable (β j) := fun j => measurable_condInf (hPB j) (hPB_meas j) hQh
  have hβ_le : ∀ j ω, ∀ y ∈ K ω, F ω y < m ω + ε j → G ω y < N ω + ε j → β j ω ≤ Q y := by
    intro j ω y hyK hfy hgy
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨n, hn, hQn⟩ := exists_index_of_mem_closure (hdense ω hyK) (hBopen j ω) ⟨hfy, hgy⟩
      hQc hδ
    exact (condInf_le (hPB j ω) (fun k => hQ.nonneg _) hn).trans_lt hQn
  -- the selected members
  set PC : ℕ → Ω → ℕ → Prop := fun j ω n => PB j ω n ∧ Q (h n ω) < β j ω + ε j
  have hPC : ∀ j ω, ∃ n, PC j ω n := fun j ω => by
    obtain ⟨n, hn, hQn⟩ := exists_lt_of_condInf_lt (hPB j ω)
      (show β j ω < β j ω + ε j by linarith [hεpos j])
    exact ⟨n, hn, hQn⟩
  have hPC_meas : ∀ j n, MeasurableSet {ω | PC j ω n} := fun j n =>
    (hPB_meas j n).inter (measurableSet_lt (hQh n) ((hβ_meas j).add_const _))
  set k : ℕ → Ω → ℕ := fun j ω => Nat.find (hPC j ω)
  have hk_meas : ∀ j, Measurable (k j) := fun j => measurable_find (hPC j) (hPC_meas j)
  set xs : ℕ → Ω → E := fun j ω => h (k j ω) ω
  have hxs_meas : ∀ j, Measurable (xs j) := fun j => measurable_nat_index (hk_meas j) hh
  have hxs_spec : ∀ j ω, PC j ω (k j ω) := fun j ω => Nat.find_spec (hPC j ω)
  -- convergence to `x`
  have hlim : ∀ ω, Tendsto (fun j => xs j ω) atTop (𝓝 (x ω)) := by
    intro ω
    set B : ℕ → Set E := fun j => {y | y ∈ K ω ∧ (F ω y < m ω + ε j ∧ G ω y < N ω + ε j)}
    have hBanti : Antitone B := by
      intro j l hjl y hy
      exact ⟨hy.1, hy.2.1.trans_le (by linarith [hεanti hjl]),
        hy.2.2.trans_le (by linarith [hεanti hjl])⟩
    have hBconv : ∀ j, Convex ℝ (B j) := by
      intro j y hy z hz s t hs ht hst
      have a1 := (hfc ω).convex_lt (m ω + ε j) ⟨hy.1, hy.2.1⟩ ⟨hz.1, hz.2.1⟩ hs ht hst
      have a2 := (hgc ω).convex_lt (N ω + ε j) ⟨hy.1, hy.2.2⟩ ⟨hz.1, hz.2.2⟩ hs ht hst
      exact ⟨a1.1, a1.2, a2.2⟩
    have hB0 : BddAbove (Q '' B 0) :=
      (hcoer ω (m ω + ε 0)).mono (Set.image_mono fun y (hy : y ∈ B 0) =>
        (⟨hy.1, hy.2.1.le⟩ : y ∈ {y | y ∈ K ω ∧ F ω y ≤ m ω + ε 0}))
    have hxsB : ∀ j, xs j ω ∈ B j := fun j => ⟨hmem _ ω, (hxs_spec j ω).1⟩
    have hxsQ : ∀ j, ∀ y ∈ B j, Q (xs j ω) ≤ Q y + ε j := fun j y hy =>
      ((hxs_spec j ω).2.trans_le (by linarith [hβ_le j ω y hy.1 hy.2.1 hy.2.2])).le
    have hcauchy := cauchySeq_of_almost_minimizers hQ B hBanti hBconv hB0 ε hεanti hεlim
      (fun j => xs j ω) hxsB hxsQ
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hyC : ∀ j, y ∈ {y | y ∈ K ω ∧ F ω y ≤ m ω + ε j ∧ G ω y ≤ N ω + ε j} := by
      intro j
      have hC : IsClosed {y | y ∈ K ω ∧ F ω y ≤ m ω + ε j ∧ G ω y ≤ N ω + ε j} :=
        (hK ω).inter ((isClosed_le (hF ω) continuous_const).inter (isClosed_le (hG ω) continuous_const))
      refine hC.mem_of_tendsto hy ?_
      filter_upwards [eventually_ge_atTop j] with l hl
      have hl' := hBanti hl (hxsB l)
      exact ⟨hl'.1, hl'.2.1.le, hl'.2.2.le⟩
    have hyK : y ∈ K ω := (hyC 0).1
    have hfy : F ω y ≤ m ω := by
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact lt_of_le_of_lt (hyC j).2.1 (by simp only [hε_def]; linarith)
    have hgy : G ω y ≤ N ω := by
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact lt_of_le_of_lt (hyC j).2.2 (by simp only [hε_def]; linarith)
    rw [hm_eq] at hfy
    rw [hN_eq] at hgy
    have hyx : y = x ω := by
      refine huniq ω y hyK (fun z hz => hfy.trans (hxf ω z hz)) fun z hz hzy => ?_
      exact hgy.trans (hxg ω z hz (hzy.trans hfy))
    rw [← hyx]
    exact hy
  exact measurable_of_tendsto_metrizable hxs_meas (tendsto_pi_nhds.2 hlim)

/-- **Measurability of lexicographic minimizers** from a measurable dense sequence. -/
theorem measurable_lexicographic_minimizer {Q : E → ℝ} (hQ : IsQuadraticGauge Q)
    (hQc : Continuous Q) {K : Ω → Set E} (hK : ∀ ω, IsClosed (K ω))
    {f g : E → ℝ} (hf : Continuous f) (hfc : ∀ ω, ConvexOn ℝ (K ω) f)
    (hf0 : ∀ ω, ∀ y ∈ K ω, 0 ≤ f y) (hg : Continuous g) (hgc : ∀ ω, ConvexOn ℝ (K ω) g)
    (hg0 : ∀ ω, ∀ y ∈ K ω, 0 ≤ g y)
    (hcoer : ∀ ω t, BddAbove (Q '' {y | y ∈ K ω ∧ f y ≤ t}))
    (h : ℕ → Ω → E) (hh : ∀ n, Measurable (h n)) (hmem : ∀ n ω, h n ω ∈ K ω)
    (hdense : ∀ ω, K ω ⊆ closure (Set.range fun n => h n ω))
    (x : Ω → E) (hxK : ∀ ω, x ω ∈ K ω) (hxf : ∀ ω, ∀ y ∈ K ω, f (x ω) ≤ f y)
    (hxg : ∀ ω, ∀ y ∈ K ω, f y ≤ f (x ω) → g (x ω) ≤ g y)
    (huniq : ∀ ω, ∀ y ∈ K ω, (∀ z ∈ K ω, f y ≤ f z) →
      (∀ z ∈ K ω, f z ≤ f y → g y ≤ g z) → y = x ω) :
    Measurable x :=
  measurable_lexicographic_minimizer_param hQ hQc hK (F := fun _ => f) (G := fun _ => g)
    (fun _ => hf) hfc hf0 (fun _ => hg) hgc hg0 hcoer h hh hmem
    (fun n => hf.measurable.comp (hh n)) (fun n => hg.measurable.comp (hh n)) hdense x hxK hxf
    hxg huniq

end QSH
