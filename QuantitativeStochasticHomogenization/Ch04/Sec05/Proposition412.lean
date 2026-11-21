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

end QSH
