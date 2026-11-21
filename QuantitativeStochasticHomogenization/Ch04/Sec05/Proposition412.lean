import QuantitativeStochasticHomogenization.Ch04.Sec05.Proposition412Fields

/-!
# Proposition 4.12: the fluctuation estimates

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Proposition 4.12: for `s ∈ (1, 2]`, `β ∈ (0, d/2]` and `α, δ > 0` with
`α > β(1+δ)`, `Add(s, α)` and `Loc(s, δ, α)` imply `Fluc(s, β)`.

The statement is proved for a bounded jointly measurable field `J` and the localization by
measurable fields `LocFieldEstimate` (`fluctuationEstimatesFor_locFieldEstimate`), with local
σ-algebras of unit range of dependence. The book integrates the localized quantities
`x ↦ J₁^{(δ)}(x, r)` over cubes and uses the independence of integrals over cubes far apart; this
needs the localized quantities as a jointly measurable family, which `LocFieldEstimate` provides
(Definition 4.9 gives one random variable per center). Integrals over cubes at distance larger than
one are independent, and those over nearby cells are handled by a colouring of the cells (Lemma
A.12), with the same proof as the book's.

For fixed `p, q` the localized fields are truncated at the bound of `J` and centered
(`truncatedField`); these are centered local fields (`CenteredLocalFields`), with the additivity
(4.116) deduced from `Add(s, α)` and the localization. The bound (4.115) for them follows from
(4.117) (Step 3), and `Fluc(s, β)` for `J` follows since `J` is within `|J - J^{(δ)}|` of the
truncation.
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Vec d) → MeasurableSpace Ω}

omit [MeasurableSpace Ω] in
theorem measurable_prod_of_le {m m' : MeasurableSpace Ω} (h : m ≤ m') {f : Ω × Vec d → ℝ}
    (hf : @Measurable (Ω × Vec d) ℝ (@Prod.instMeasurableSpace Ω (Vec d) m _) _ f) :
    @Measurable (Ω × Vec d) ℝ (@Prod.instMeasurableSpace Ω (Vec d) m' _) _ f := by
  have h1 : @Measurable (Ω × Vec d) Ω (@Prod.instMeasurableSpace Ω (Vec d) m' _) m Prod.fst :=
    (@measurable_fst Ω (Vec d) m' _).mono le_rfl h
  have h2 : @Measurable (Ω × Vec d) (Vec d) (@Prod.instMeasurableSpace Ω (Vec d) m' _) _
      Prod.snd := @measurable_snd Ω (Vec d) m' _
  have hid := @Measurable.prodMk (Ω × Vec d) (@Prod.instMeasurableSpace Ω (Vec d) m' _) Ω
    (Vec d) m _ Prod.fst Prod.snd h1 h2
  exact hf.comp hid

variable (P) in
/-- The truncated and centered localized fields: for `r ≥ 1`,
`[J^{(δ)}(r)]_M - E[[J^{(δ)}(r)]_M]`, and `0` for `r < 1`. -/
noncomputable def truncatedField (M : ℝ) (Jδ : ℝ → Ω → Vec d → ℝ) (r : ℝ) (a : Ω) (x : Vec d) :
    ℝ :=
  if 1 ≤ r then clampAt M (Jδ r a x) - ∫ a', clampAt M (Jδ r a' x) ∂P else 0

theorem truncatedField_of_one_le {M : ℝ} {Jδ : ℝ → Ω → Vec d → ℝ} {r : ℝ} (hr : 1 ≤ r) (a : Ω)
    (x : Vec d) :
    truncatedField P M Jδ r a x = clampAt M (Jδ r a x) - ∫ a', clampAt M (Jδ r a' x) ∂P := by
  simp only [truncatedField, hr, ↓reduceIte]

theorem abs_truncatedField_le [IsProbabilityMeasure P] {M : ℝ} (hM : 0 ≤ M)
    (Jδ : ℝ → Ω → Vec d → ℝ) (r : ℝ) (a : Ω) (x : Vec d) :
    |truncatedField P M Jδ r a x| ≤ 2 * M := by
  unfold truncatedField
  split_ifs
  · have h1 := abs_clampAt_le hM (Jδ r a x)
    have h2 : |∫ a', clampAt M (Jδ r a' x) ∂P| ≤ M := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ a', |clampAt M (Jδ r a' x)| ∂P ≤ ∫ _a', M ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const M) (Filter.Eventually.of_forall fun a' => abs_clampAt_le hM _)
        _ = M := by simp
    exact (abs_sub _ _).trans (by linarith)
  · simp only [abs_zero]
    linarith

theorem measurable_truncatedField [IsProbabilityMeasure P] {M : ℝ} {Jδ : ℝ → Ω → Vec d → ℝ}
    (hJδ : ∀ r, 1 ≤ r → Measurable fun w : Ω × Vec d => Jδ r w.1 w.2) (r : ℝ) :
    Measurable fun w : Ω × Vec d => truncatedField P M Jδ r w.1 w.2 := by
  unfold truncatedField
  by_cases hr : 1 ≤ r
  · simp only [hr, ↓reduceIte]
    have hc : Measurable fun w : Ω × Vec d => clampAt M (Jδ r w.1 w.2) :=
      (continuous_clampAt M).measurable.comp (hJδ r hr)
    have hm : Measurable fun x : Vec d => ∫ a', clampAt M (Jδ r a' x) ∂P :=
      hc.stronglyMeasurable.integral_prod_left'.measurable
    exact hc.sub (hm.comp measurable_snd)
  · simp only [hr, ↓reduceIte]
    exact measurable_const

theorem integral_truncatedField [IsProbabilityMeasure P] {M : ℝ} (hM : 0 ≤ M)
    {Jδ : ℝ → Ω → Vec d → ℝ} (hJδ : ∀ r, 1 ≤ r → Measurable fun w : Ω × Vec d => Jδ r w.1 w.2)
    (r : ℝ) (x : Vec d) : ∫ a, truncatedField P M Jδ r a x ∂P = 0 := by
  unfold truncatedField
  by_cases hr : 1 ≤ r
  · simp only [hr, ↓reduceIte]
    have hc : Measurable fun a => clampAt M (Jδ r a x) :=
      (continuous_clampAt M).measurable.comp ((hJδ r hr).comp measurable_prodMk_right)
    have hi : Integrable (fun a => clampAt M (Jδ r a x)) P :=
      Integrable.of_bound hc.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact abs_clampAt_le hM _)
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  · simp only [hr, ↓reduceIte, integral_zero]

theorem isLocal_truncatedField [IsProbabilityMeasure P] {M : ℝ} (hM : 0 ≤ M) {Jδ : ℝ → Ω → Vec d → ℝ} {δ : ℝ}
    (hJδ : ∀ r, 1 ≤ r → ∀ U : Set (Vec d), MeasurableSet U →
      @Measurable (Ω × Vec d) ℝ
        (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
        (fun w => U.indicator (Jδ r w.1) w.2))
    (hJδm : ∀ r, 1 ≤ r → Measurable fun w : Ω × Vec d => Jδ r w.1 w.2)
    (r : ℝ) (hr : 1 ≤ r) (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (Ω × Vec d) ℝ
      (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
      (fun w => U.indicator (truncatedField P M Jδ r w.1) w.2) := by
  have e : (fun w : Ω × Vec d => U.indicator (truncatedField P M Jδ r w.1) w.2) = fun w =>
      clampAt M (U.indicator (Jδ r w.1) w.2) -
        U.indicator (fun x => ∫ a', clampAt M (Jδ r a' x) ∂P) w.2 := by
    funext w
    by_cases hx : w.2 ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        truncatedField_of_one_le hr]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
        clampAt_zero hM, sub_zero]
  rw [e]
  have hmean : Measurable fun x : Vec d => ∫ a', clampAt M (Jδ r a' x) ∂P :=
    ((continuous_clampAt M).measurable.comp (hJδm r hr)).stronglyMeasurable.integral_prod_left'.measurable
  have h1 := (continuous_clampAt M).measurable.comp (hJδ r hr U hU)
  have h2 : @Measurable (Ω × Vec d) ℝ
      (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
      (fun w => U.indicator (fun x => ∫ a', clampAt M (Jδ r a' x) ∂P) w.2) :=
    (hmean.indicator hU).comp
      (@measurable_snd Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _)
  exact Measurable.sub
    (m := @Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) h1 h2

theorem integrable_of_abs_le_of_measurable [IsProbabilityMeasure P] {G : Ω → ℝ} {B : ℝ}
    (hG : Measurable G) (hGB : ∀ a, |G a| ≤ B) : Integrable G P :=
  Integrable.of_bound hG.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hGB a)

/-- **The additivity (4.116) of the truncated localized fields**, from `Add(s, α)`, the closeness
of the localized fields and Lemmas A.9 and A.10. -/
theorem exists_additive_truncatedField [IsProbabilityMeasure P] {s : ℝ} (hs1 : 1 < s)
    (hs2 : s ≤ 2) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ) {M : ℝ}, 0 ≤ M → ∀ (p q : Vec d)
        (Jδ : ℝ → Ω → Vec d → ℝ) {α CA CL : ℝ}, 0 ≤ α → 0 < CL → 0 < CA →
      (∀ a z r, |J a z r p q| ≤ M) →
      (∀ r, Measurable fun w : Ω × Vec d => J w.1 w.2 r p q) →
      (∀ r, 1 ≤ r → Measurable fun w : Ω × Vec d => Jδ r w.1 w.2) →
      (∀ r, 1 ≤ r → ∀ z, OsBound P (fun a => |J a z r p q - Jδ r a z|) s (CL * r ^ (-α))) →
      (∀ (z : Vec d) (r₁ r : ℝ), 1 ≤ r₁ → r₁ < r → OsBound P (fun a => |J a z r p q -
        ∫ y, heatKernel z (Real.sqrt (r ^ 2 - r₁ ^ 2)) y * J a y r₁ p q|) s (CA * r₁ ^ (-α))) →
      ∀ (r₁ r : ℝ), 1 ≤ r₁ → r₁ < r → ∀ x : Vec d,
        CenteredOsBound P (fun a => truncatedField P M Jδ r a x -
          ∫ y, heatKernel x (Real.sqrt (r ^ 2 - r₁ ^ 2)) y * truncatedField P M Jδ r₁ a y) s
          ((C₁ * (CL + CA) + C₂ * CL) * r₁ ^ (-α)) := by
  obtain ⟨C₁, hC₁, hcen1⟩ := exists_centeredOsBound_sub_integral hs1 hs2
  obtain ⟨C₂, hC₂, hcen2⟩ := exists_centeredOsBound_heatAverage_sub (P := P) (d := d) hs1 hs2
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro J M hM p q Jδ α CA CL hα hCL hCA hJb hJm hJδm hloc hadd r₁ r hr₁ hr x
  have hr1 : 1 ≤ r := hr₁.trans hr.le
  have hr₁0 : 0 < r₁ := zero_lt_one.trans_le hr₁
  have hr₁sq : r₁ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr hr₁0.le two_ne_zero
  set ρ : ℝ := Real.sqrt (r ^ 2 - r₁ ^ 2) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (by linarith)
  have hΦm : Measurable (heatKernel x ρ) := measurable_heatKernel_right x ρ
  have hΦi : Integrable (heatKernel x ρ) := integrable_heatKernel x hρ
  have hΦ1 : ∫ y, |heatKernel x ρ y| = 1 := by
    simp_rw [abs_of_nonneg (heatKernel_nonneg x ρ _)]
    exact integral_heatKernel x hρ
  have hJcm : ∀ t, 1 ≤ t → Measurable fun w : Ω × Vec d => clampAt M (Jδ t w.1 w.2) :=
    fun t ht => (continuous_clampAt M).measurable.comp (hJδm t ht)
  set H : Ω → ℝ := fun a => ∫ y, heatKernel x ρ y * J a y r₁ p q with hHdef
  have hHm : Measurable H := measurable_integral_mul hΦm (hJm r₁)
  have hHb : ∀ a, |H a| ≤ M := by
    intro a
    have := abs_integral_mul_le (X := fun a y => J a y r₁ p q) (fun a y => hJb a y r₁) hΦi a
    rwa [hΦ1, mul_one] at this
  set Hc : Ω → ℝ := fun a => ∫ y, heatKernel x ρ y * clampAt M (Jδ r₁ a y) with hHcdef
  have hHcm : Measurable Hc := measurable_integral_mul hΦm (hJcm r₁ hr₁)
  have hHcb : ∀ a, |Hc a| ≤ M := by
    intro a
    have := abs_integral_mul_le (X := fun a y => clampAt M (Jδ r₁ a y))
      (fun a y => abs_clampAt_le hM _) hΦi a
    rwa [hΦ1, mul_one] at this
  set T : Ω → ℝ := fun a => clampAt M (Jδ r a x) - H a with hTdef
  have hTm : Measurable T :=
    ((hJcm r hr1).comp (measurable_id.prodMk measurable_const)).sub hHm
  have hTabs : OsBound P (fun a => |T a|) s ((CL + CA) * r₁ ^ (-α)) := by
    have h1 := hloc r hr1 x
    have h2 := hadd x r₁ r hr₁ hr
    have hsum := osBound_add h1 h2 hs1.le
    have hrα : r ^ (-α) ≤ r₁ ^ (-α) := Real.rpow_le_rpow_of_nonpos hr₁0 hr.le (by linarith)
    refine (hsum.mono_scale (by nlinarith [Real.rpow_nonneg hr₁0.le (-α)])).of_le
      (continuous_abs.measurable.comp hTm) fun a => ?_
    have hc := abs_clampAt_sub_le (v := Jδ r a x) (hJb a x r)
    rw [abs_sub_comm (Jδ r a x)] at hc
    calc |T a| = |(clampAt M (Jδ r a x) - J a x r p q) + (J a x r p q - H a)| := by
          rw [hTdef]; ring_nf
      _ ≤ |clampAt M (Jδ r a x) - J a x r p q| + |J a x r p q - H a| := abs_add_le _ _
      _ ≤ |J a x r p q - Jδ r a x| + |J a x r p q - H a| := by linarith
  have hT := hcen1 P T _ hTm hTabs
  set V : Vec d → Ω → ℝ := fun y a => J a y r₁ p q - clampAt M (Jδ r₁ a y) with hVdef
  have hVm : Measurable (Function.uncurry V) :=
    ((hJm r₁).comp measurable_swap).sub ((hJcm r₁ hr₁).comp measurable_swap)
  have hVB : ∀ y a, |V y a| ≤ 2 * M := fun y a =>
    (abs_sub _ _).trans (by linarith [hJb a y r₁, abs_clampAt_le hM (Jδ r₁ a y)])
  have hVθ : ∀ y, OsBound P (fun a => |V y a|) s (CL * r₁ ^ (-α)) := by
    intro y
    refine (hloc r₁ hr₁ y).of_le (continuous_abs.measurable.comp
      (hVm.comp (measurable_const.prodMk measurable_id))) fun a => ?_
    have hc := abs_clampAt_sub_le (v := Jδ r₁ a y) (hJb a y r₁)
    rw [abs_sub_comm (clampAt M _), abs_sub_comm (Jδ r₁ a y)] at hc
    exact hc
  have hT3 := hcen2 V (CL * r₁ ^ (-α)) (2 * M) x ρ hρ hVm hVB hVθ
  have hsum := hT.add hT3
  refine (hsum.mono_scale (le_of_eq (by ring))).congr_ae ?_
    (Filter.Eventually.of_forall fun a => ?_)
  · have hmt : ∀ t, 1 ≤ t → Measurable fun w : Ω × Vec d => truncatedField P M Jδ t w.1 w.2 :=
      fun t _ => measurable_truncatedField (P := P) hJδm t
    exact ((hmt r hr1).comp (measurable_id.prodMk measurable_const)).sub
      (measurable_integral_mul hΦm (measurable_truncatedField (P := P) hJδm r₁))
  · set mt : Vec d → ℝ := fun y => ∫ a', clampAt M (Jδ r₁ a' y) ∂P with hmtdef
    have hmtm : Measurable mt := (hJcm r₁ hr₁).stronglyMeasurable.integral_prod_left'.measurable
    have hmtb : ∀ y, |mt y| ≤ M := by
      intro y
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ a', |clampAt M (Jδ r₁ a' y)| ∂P ≤ ∫ _a', M ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const M) (Filter.Eventually.of_forall fun a' => abs_clampAt_le hM _)
        _ = M := by simp
    have hi1 : ∀ a', Integrable fun y => heatKernel x ρ y * clampAt M (Jδ r₁ a' y) := fun a' =>
      hΦi.mul_bdd ((hJcm r₁ hr₁).comp measurable_prodMk_left).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact abs_clampAt_le hM _)
    have hint2 : Integrable fun y => heatKernel x ρ y * mt y :=
      hΦi.mul_bdd hmtm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hmtb y)
    have hi3 : ∀ a', Integrable fun y => heatKernel x ρ y * J a' y r₁ p q := fun a' =>
      hΦi.mul_bdd ((hJm r₁).comp measurable_prodMk_left).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hJb a' y r₁)
    have f1 : ∫ y, heatKernel x ρ y * truncatedField P M Jδ r₁ a y =
        Hc a - ∫ y, heatKernel x ρ y * mt y := by
      rw [hHcdef, ← integral_sub (hi1 a) hint2]
      congr 1
      funext y
      rw [truncatedField_of_one_le hr₁, mul_sub]
    have f2 : ∀ a', ∫ y, heatKernel x ρ y * V y a' = H a' - Hc a' := by
      intro a'
      rw [hHdef, hHcdef]
      beta_reduce
      rw [← integral_sub (hi3 a') (hi1 a')]
      congr 1
      funext y
      rw [hVdef, mul_sub]
    have hIH := integrable_of_abs_le_of_measurable (P := P) hHm hHb
    have hIHc := integrable_of_abs_le_of_measurable (P := P) hHcm hHcb
    have hIJc : Integrable (fun a => clampAt M (Jδ r a x)) P :=
      integrable_of_abs_le_of_measurable
        ((hJcm r hr1).comp (measurable_id.prodMk measurable_const)) fun a => abs_clampAt_le hM _
    have f3 : ∫ a', T a' ∂P = (∫ a', clampAt M (Jδ r a' x) ∂P) - ∫ a', H a' ∂P :=
      integral_sub hIJc hIH
    have f4 : ∫ a', (∫ y, heatKernel x ρ y * V y a') ∂P = (∫ a', H a' ∂P) - ∫ a', Hc a' ∂P := by
      rw [← integral_sub hIH hIHc]
      congr 1
      funext a'
      exact f2 a'
    have f5 : ∫ a', Hc a' ∂P = ∫ y, heatKernel x ρ y * mt y := by
      have hprod : Integrable (fun w : Ω × Vec d =>
          heatKernel x ρ w.2 * clampAt M (Jδ r₁ w.1 w.2)) (P.prod volume) := by
        have hg : Integrable (fun w : Ω × Vec d => (1 : ℝ) * (M * heatKernel x ρ w.2))
            (P.prod volume) := (integrable_const (μ := P) (1 : ℝ)).mul_prod (hΦi.const_mul M)
        refine hg.mono' ((hΦm.comp measurable_snd).mul (hJcm r₁ hr₁)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun w => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg x ρ _), one_mul,
          mul_comm M]
        exact mul_le_mul_of_nonneg_left (abs_clampAt_le hM _) (heatKernel_nonneg x ρ _)
      rw [hHcdef, integral_integral_swap (f := fun a y => heatKernel x ρ y *
        clampAt M (Jδ r₁ a y)) hprod]
      congr 1
      funext y
      rw [hmtdef, integral_const_mul]
    show _ = truncatedField P M Jδ r a x -
      ∫ y, heatKernel x ρ y * truncatedField P M Jδ r₁ a y
    beta_reduce
    rw [f1, f2 a, f3, f4, f5, truncatedField_of_one_le hr1, hTdef]
    ring

/-- **Proposition 4.12** (fluctuation estimates): for a jointly measurable field `J` bounded on
the unit balls of `p, q`, local σ-algebras of unit range of dependence and the localization by
measurable fields, for `s ∈ (1, 2]`, `β ∈ (0, d/2]` and `α, δ > 0` with `α > β(1+δ)`,
`Add(s, α)` and `Loc(s, δ, α)` imply `Fluc(s, β)`. -/
theorem fluctuationEstimatesFor_locFieldEstimate [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (hF : HasUnitRange P F) (hmono : Monotone F) (hFle : ∀ U, F U ≤ (inferInstance : MeasurableSpace Ω))
    {J : Ω → Vec d → ℝ → Vec d → Vec d → ℝ} {M : ℝ}
    (hJb : ∀ a z r p q, euclideanNorm p < 1 → euclideanNorm q < 1 → |J a z r p q| ≤ M)
    (hJm : ∀ r p q, Measurable fun w : Ω × Vec d => J w.1 w.2 r p q) :
    FluctuationEstimatesFor P J (LocFieldEstimate P F J) := by
  intro s β α δ hs1 hs2 hβ0 hβd hδ hβα hAdd hLoc
  obtain ⟨CA, hCA, hA⟩ := hAdd
  obtain ⟨CL, hCL, hL⟩ := hLoc
  set M' : ℝ := max M 1 with hM'def
  have hM' : 0 < M' := lt_max_of_lt_right one_pos
  have hJb' : ∀ a z r p q, euclideanNorm p < 1 → euclideanNorm q < 1 → |J a z r p q| ≤ M' :=
    fun a z r p q hp hq => (hJb a z r p q hp hq).trans (le_max_left _ _)
  have hβδ : 0 < β * (1 + δ) := mul_pos hβ0 (by linarith)
  have hα0 : 0 < α := by linarith
  have hβα' : β ≤ α := by nlinarith
  set c : ℝ := (1 + δ)⁻¹ with hcdef
  have hc0 : 0 < c := by positivity
  have hcα : β / α < c := by
    rw [div_lt_iff₀ hα0, hcdef, ← div_eq_inv_mul, lt_div_iff₀ (by linarith)]
    exact hβα
  set η₁ : ℝ := (β / α + c) / 2 with hη₁def
  set η₂ : ℝ := (η₁ + c) / 2 with hη₂def
  have hβα0 : 0 < β / α := div_pos hβ0 hα0
  have hη₁ : 0 < η₁ := by positivity
  have hη₁c : η₁ < c := by linarith
  have hη₁₂ : η₁ < η₂ := by linarith
  have hη₂c : η₂ < c := by linarith
  have hη₂ : η₂ * (1 + δ) < 1 := by
    have h := mul_lt_mul_of_pos_right hη₂c (by linarith : (0 : ℝ) < 1 + δ)
    rwa [hcdef, inv_mul_cancel₀ (by linarith)] at h
  have hβη : β < η₁ * α := by
    have h1 : β / α < η₁ := by linarith
    rwa [div_lt_iff₀ hα0] at h1
  obtain ⟨C₁, C₂, hC₁, hC₂, hadd⟩ := exists_additive_truncatedField (P := P) (d := d) hs1 hs2
  set A : ℝ := C₁ * (CL + CA) + C₂ * CL with hAdef
  have hA0 : 0 < A := by positivity
  obtain ⟨Cf, hCf, hfield⟩ := exists_centeredOsBound_field (Ω := Ω) (F := F) (δ := δ) (α := α)
    (B := 2 * M') (A := A) hd hmono hs1 hs2 (by positivity) hA0 hβ0 hβd hδ hη₁ hη₁₂ hη₂ hβη
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  set C' : ℝ := CL + (8 : ℝ) ^ s⁻¹ * (4 * Cf) + 2 * CL / Real.log 2 ^ s⁻¹ with hC'def
  refine ⟨C', by positivity, fun z R hR p q hp hq => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hsel : ∀ r : ℝ, ∃ Jδ : Ω → Vec d → ℝ, 1 ≤ r →
      (∀ U : Set (Vec d), MeasurableSet U →
        @Measurable (Ω × Vec d) ℝ
          (@Prod.instMeasurableSpace Ω (Vec d) (F (euclideanThickening (r ^ (1 + δ)) U)) _) _
          (fun w => U.indicator (Jδ w.1) w.2)) ∧
      ∀ z : Vec d, OsBound P (fun a => |J a z r p q - Jδ a z|) s (CL * r ^ (-α)) := by
    intro r
    by_cases hr : 1 ≤ r
    · obtain ⟨Jδ, h1, h2⟩ := hL r hr p q hp hq
      exact ⟨Jδ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hr⟩
  choose Jδ hJδ using hsel
  have hJδm : ∀ r, 1 ≤ r → Measurable fun w : Ω × Vec d => Jδ r w.1 w.2 := by
    intro r hr
    have h := (hJδ r hr).1 Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ] at h
    exact measurable_prod_of_le (hFle _) h
  let X : CenteredLocalFields P F s δ α (2 * M') A :=
    { field := truncatedField P M' Jδ
      abs_le := abs_truncatedField_le hM'.le Jδ
      measurable := measurable_truncatedField hJδm
      isLocal := isLocal_truncatedField hM'.le (fun r hr => (hJδ r hr).1) hJδm
      centered := integral_truncatedField hM'.le hJδm
      additive := hadd J hM'.le p q Jδ hα0.le hCL hCA (fun a z r => hJb' a z r p q hp hq)
        (fun r => hJm r p q) hJδm (fun r hr z => (hJδ r hr).2 z)
        (fun z r₁ r hr₁ hr => (hA z r₁ r hr₁ hr p q hp hq).2) }
  have hX := hfield P hF X R hR z
  have hJzm : Measurable fun a => J a z R p q :=
    (hJm R p q).comp (measurable_id.prodMk measurable_const)
  have hJzi : Integrable (fun a => J a z R p q) P :=
    integrable_of_abs_le_of_measurable hJzm fun a => hJb' a z R p q hp hq
  refine ⟨hJzi, ?_⟩
  have O1 := (hJδ R hR).2 z
  obtain ⟨hInt, he⟩ := O1.integrable_and_integral_le hs1.le fun a => abs_nonneg _
  set e : ℝ := ∫ a, |J a z R p q - Jδ R a z| ∂P with hedef
  have O2 := hX.osBound_abs
  have hc2 : 0 < 2 * (CL * R ^ (-α)) := by positivity
  have O3 : OsBound P (fun _ : Ω => e) s (2 * (CL * R ^ (-α)) / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const (by linarith) hc2 (Filter.Eventually.of_forall
      fun _ => he)
  have hsum := osBound_add (osBound_add O1 O2 hs1.le) O3 hs1.le
  have hRαβ : R ^ (-α) ≤ R ^ (-β) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hRβ : 0 ≤ R ^ (-β) := Real.rpow_nonneg hR0.le _
  refine (hsum.mono_scale ?_).of_le
    (continuous_abs.measurable.comp (hJzm.sub measurable_const)) fun a => ?_
  · have h1 : CL * R ^ (-α) ≤ CL * R ^ (-β) := mul_le_mul_of_nonneg_left hRαβ hCL.le
    have h3 : 2 * (CL * R ^ (-α)) / Real.log 2 ^ s⁻¹ ≤ 2 * CL / Real.log 2 ^ s⁻¹ * R ^ (-β) := by
      rw [div_mul_eq_mul_div, mul_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hl2.le
    calc CL * R ^ (-α) + (8 : ℝ) ^ s⁻¹ * (4 * (Cf * R ^ (-β))) +
          2 * (CL * R ^ (-α)) / Real.log 2 ^ s⁻¹
        ≤ CL * R ^ (-β) + (8 : ℝ) ^ s⁻¹ * (4 * (Cf * R ^ (-β))) +
          2 * CL / Real.log 2 ^ s⁻¹ * R ^ (-β) := by linarith
      _ = C' * R ^ (-β) := by rw [hC'def]; ring
  · show |J a z R p q - ∫ a', J a' z R p q ∂P| ≤
      |J a z R p q - Jδ R a z| + |X.field R a z| + e
    have hXa : X.field R a z = clampAt M' (Jδ R a z) - ∫ a', clampAt M' (Jδ R a' z) ∂P :=
      truncatedField_of_one_le hR a z
    have hcm : Measurable fun a' => clampAt M' (Jδ R a' z) :=
      (continuous_clampAt M').measurable.comp ((hJδm R hR).comp measurable_prodMk_right)
    have hci : Integrable (fun a' => clampAt M' (Jδ R a' z)) P :=
      integrable_of_abs_le_of_measurable hcm fun a' => abs_clampAt_le hM'.le _
    have hmean : |(∫ a', clampAt M' (Jδ R a' z) ∂P) - ∫ a', J a' z R p q ∂P| ≤ e := by
      rw [← integral_sub hci hJzi]
      refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hInt
        (Filter.Eventually.of_forall fun a' => ?_))
      have := abs_clampAt_sub_le (v := Jδ R a' z) (hJb' a' z R p q hp hq)
      rw [abs_sub_comm (Jδ R a' z)] at this
      exact this
    have hpt := abs_clampAt_sub_le (v := Jδ R a z) (hJb' a z R p q hp hq)
    rw [abs_sub_comm (Jδ R a z)] at hpt
    rw [hXa]
    calc |J a z R p q - ∫ a', J a' z R p q ∂P|
        = |(J a z R p q - clampAt M' (Jδ R a z)) +
            (clampAt M' (Jδ R a z) - ∫ a', clampAt M' (Jδ R a' z) ∂P) +
            ((∫ a', clampAt M' (Jδ R a' z) ∂P) - ∫ a', J a' z R p q ∂P)| := by ring_nf
      _ ≤ |J a z R p q - clampAt M' (Jδ R a z)| +
            |clampAt M' (Jδ R a z) - ∫ a', clampAt M' (Jδ R a' z) ∂P| +
            |(∫ a', clampAt M' (Jδ R a' z) ∂P) - ∫ a', J a' z R p q ∂P| := abs_add_three _ _ _
      _ ≤ |J a z R p q - Jδ R a z| +
            |clampAt M' (Jδ R a z) - ∫ a', clampAt M' (Jδ R a' z) ∂P| + e := by
          rw [abs_sub_comm (J a z R p q)]
          linarith

end QSH
