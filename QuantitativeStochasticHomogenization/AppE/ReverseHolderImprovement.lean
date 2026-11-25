import QuantitativeStochasticHomogenization.AppC.IterationLemma
import QuantitativeStochasticHomogenization.Front.Notation
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Reverse Hölder inequalities improve themselves

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix E, Lemma E.6: let `0 < p < q < r ≤ ∞` and `A, a > 0`. If `μ` is a Borel measure on
`ℝⁿ`, `U` a Borel set, `{σU}_{σ ∈ (0, 1]}` Borel subsets of `U`, and `f ∈ L^p(U; μ) ∩ L^r(U; μ)`
satisfies `‖f‖_{L^r(σ'U; μ)} ≤ A (σ - σ')^{-a} ‖f‖_{L^q(σU; μ)}` for all `1/2 ≤ σ' < σ ≤ 1`, then
`‖f‖_{L^r(⅔U; μ)} ≤ C ‖f‖_{L^p(U; μ)}` with `C(a, A, p, q, r)`.

The proof is the book's. With `h ∈ (0, 1)` defined by `1/q = h/p + (1 - h)/r`, Hölder's
inequality gives `‖f‖_{L^q} ≤ ‖f‖_{L^p}^h ‖f‖_{L^r}^{1-h}`
(`eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`), and Young's inequality, here the weighted
arithmetic-geometric mean inequality (`mul_rpow_mul_rpow_le_half_add`), turns the hypothesis into
`ρ(σ') ≤ ρ(σ)/2 + (σ - σ')^{-a/h} K ‖f‖_{L^p(U)}` for `ρ(σ) = ‖f‖_{L^r(σU)}`. Lemma C.6
(`lemma_C_6`), applied to `t ↦ ρ((2t + 1)/3)` on `[1/2, 1)`, bounds `ρ(2/3)`.

The general form `reverseHolder_improvement` holds on any measurable space and does not use the
measurability of `U` and of the sets `σU`; `lemma_E_6` is the statement on `ℝⁿ`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace QSH

/-- **Hölder interpolation of `L^q` between `L^p` and `L^r`**: if
`h p⁻¹ + (1 - h) r⁻¹ = q⁻¹` with `h ∈ (0, 1)`, then `‖f‖_q ≤ ‖f‖_p^h ‖f‖_r^{1-h}`. -/
theorem eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {p q r : ℝ≥0∞} {h : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (hpqr : ENNReal.ofReal h * p⁻¹ + ENNReal.ofReal (1 - h) * r⁻¹ = q⁻¹) :
    eLpNorm f q μ ≤ eLpNorm f p μ ^ h * eLpNorm f r μ ^ (1 - h) := by
  have h1' : 0 < 1 - h := by linarith
  have hF : AEStronglyMeasurable (fun x => ‖f x‖ ^ h) μ :=
    (hf.norm.aemeasurable.pow_const h).aestronglyMeasurable
  have hG : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 - h)) μ :=
    (hf.norm.aemeasurable.pow_const (1 - h)).aestronglyMeasurable
  have hh0 : ENNReal.ofReal h ≠ 0 := by simpa using h0
  have hh1 : ENNReal.ofReal (1 - h) ≠ 0 := by simpa using h1'
  have : ENNReal.HolderTriple (p / ENNReal.ofReal h) (r / ENNReal.ofReal (1 - h)) q := by
    refine ⟨?_⟩
    rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hh0),
      ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hh1), div_eq_mul_inv,
      div_eq_mul_inv, hpqr]
  have hprod : (fun x => ‖f x‖) = fun x => ‖f x‖ ^ h * ‖f x‖ ^ (1 - h) := by
    funext x
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num), add_sub_cancel, Real.rpow_one]
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := p / ENNReal.ofReal h)
    (q := r / ENNReal.ofReal (1 - h)) (r := q) (μ := μ) (fun a b : ℝ => a * b) 1
    (continuous_fst.mul continuous_snd) hF hG
    (Eventually.of_forall fun x => by simp [norm_mul])
  rw [← hprod, eLpNorm_norm, ENNReal.coe_one, one_mul, eLpNorm_norm_rpow f hf h0,
    eLpNorm_norm_rpow f hf h1', ENNReal.div_mul_cancel hh0 ENNReal.ofReal_ne_top,
    ENNReal.div_mul_cancel hh1 ENNReal.ofReal_ne_top] at hH
  · exact hH
  · exact hf

/-- **Young's inequality in the form used for Lemma E.6**: for `h ∈ (0, 1)` and `B, X, Y ≥ 0`,
`B X^h Y^{1-h} ≤ Y/2 + h (2(1 - h))^{(1-h)/h} B^{1/h} X`. -/
theorem mul_rpow_mul_rpow_le_half_add {h B X Y : ℝ} (h0 : 0 < h) (h1 : h < 1) (hB : 0 ≤ B)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    B * (X ^ h * Y ^ (1 - h)) ≤
      1 / 2 * Y + h * (2 * (1 - h)) ^ ((1 - h) / h) * B ^ (1 / h) * X := by
  have hc : 0 < 2 * (1 - h) := by linarith
  have hh1 : 1 - h ≠ 0 := by linarith
  set c := 2 * (1 - h) with hcdef
  set κ := c ^ ((1 - h) / h) with hκdef
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg hc.le _
  have hBh : 0 ≤ B ^ (1 / h) := Real.rpow_nonneg hB _
  have hκ : κ ^ h = c ^ (1 - h) := by
    rw [hκdef, ← Real.rpow_mul hc.le]
    congr 1
    field_simp
  have hc' : c ^ (1 - h) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := h) (w₂ := 1 - h)
    (p₁ := κ * B ^ (1 / h) * X) (p₂ := Y / c) h0.le (by linarith)
    (mul_nonneg (mul_nonneg hκ0 hBh) hX) (div_nonneg hY hc.le) (by ring)
  have lhs : (κ * B ^ (1 / h) * X) ^ h * (Y / c) ^ (1 - h) = B * (X ^ h * Y ^ (1 - h)) := by
    rw [Real.mul_rpow (mul_nonneg hκ0 hBh) hX, Real.mul_rpow hκ0 hBh, hκ, ← Real.rpow_mul hB,
      one_div_mul_cancel h0.ne', Real.rpow_one, Real.div_rpow hY hc.le]
    field_simp
  have rhs : h * (κ * B ^ (1 / h) * X) + (1 - h) * (Y / c) =
      1 / 2 * Y + h * κ * B ^ (1 / h) * X := by
    rw [hcdef]
    field_simp
    ring
  rw [lhs, rhs] at hamgm
  exact hamgm

/-- **Lemma E.6 on a measurable space**: a reverse Hölder inequality between `L^q` and `L^r` on a
family of subsets `σU`, `σ ∈ [1/2, 1]`, of `U` gives `‖f‖_{L^r(⅔U)} ≤ C ‖f‖_{L^p(U)}` for
`0 < p < q < r ≤ ∞`, with `C(a, A, p, q, r)`. -/
theorem reverseHolder_improvement {p q r : ℝ≥0∞} (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    {A a : ℝ} (hA : 0 < A) (ha : 0 < a) :
    ∃ C : ℝ≥0, ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (U : Set α) (S : ℝ → Set α)
      (f : α → ℝ), (∀ σ ∈ Ioc (0 : ℝ) 1, S σ ⊆ U) → MemLp f p (μ.restrict U) →
      MemLp f r (μ.restrict U) →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
        eLpNorm f r (μ.restrict (S σ')) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-a)) * eLpNorm f q (μ.restrict (S σ))) →
      eLpNorm f r (μ.restrict (S (2 / 3))) ≤ C * eLpNorm f p (μ.restrict U) := by
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := (hp.trans hpq).ne'
  have hr0 : r ≠ 0 := (hp.trans (hpq.trans hqr)).ne'
  have hpi : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp0
  have hqi : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hq0
  have hri : r⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hr0
  set x := p⁻¹.toReal with hx
  set y := q⁻¹.toReal with hy
  set z := r⁻¹.toReal with hz
  have hxy : y < x := (ENNReal.toReal_lt_toReal hqi hpi).2 (ENNReal.inv_lt_inv.2 hpq)
  have hyz : z < y := (ENNReal.toReal_lt_toReal hri hqi).2 (ENNReal.inv_lt_inv.2 hqr)
  set h := (y - z) / (x - z) with hhdef
  have hxz : 0 < x - z := by linarith
  have h0 : 0 < h := div_pos (by linarith) hxz
  have h1 : h < 1 := (div_lt_one hxz).2 (by linarith)
  have h1' : 0 < 1 - h := by linarith
  have hpqr : ENNReal.ofReal h * p⁻¹ + ENNReal.ofReal (1 - h) * r⁻¹ = q⁻¹ := by
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpi, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hri⟩)
      hqi, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpi)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hri), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal h0.le, ENNReal.toReal_ofReal h1'.le, ← hx, ← hy, ← hz, hhdef]
    field_simp
    ring
  set ξ := a / h with hξ
  have hξ0 : 0 ≤ ξ := (div_pos ha h0).le
  set κ := (2 * (1 - h)) ^ ((1 - h) / h) with hκdef
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg (by linarith) _
  set K := h * κ * A ^ (1 / h) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg h0.le hκ0) (Real.rpow_nonneg hA.le _)
  obtain ⟨C₆, hC₆⟩ := lemma_C_6 ξ
  refine ⟨Real.toNNReal (max C₆ 0 * ((2 / 3 : ℝ) ^ (-ξ) * K)), ?_⟩
  intro α _ μ U S f hSU hfp hfr hRH
  set X := (eLpNorm f p (μ.restrict U)).toReal with hXdef
  set ρ : ℝ → ℝ := fun σ => (eLpNorm f r (μ.restrict (S σ))).toReal with hρdef
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hle : ∀ σ ∈ Ioc (0 : ℝ) 1, μ.restrict (S σ) ≤ μ.restrict U :=
    fun σ hσ => Measure.restrict_mono (hSU σ hσ) le_rfl
  have hfinr : ∀ σ ∈ Ioc (0 : ℝ) 1, eLpNorm f r (μ.restrict (S σ)) ≠ ∞ := fun σ hσ =>
    ne_top_of_le_ne_top hfr.eLpNorm_ne_top (eLpNorm_mono_measure _ (hle σ hσ))
  have hfinp : ∀ σ ∈ Ioc (0 : ℝ) 1, eLpNorm f p (μ.restrict (S σ)) ≠ ∞ := fun σ hσ =>
    ne_top_of_le_ne_top hfp.eLpNorm_ne_top (eLpNorm_mono_measure _ (hle σ hσ))
  have step : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ρ σ' ≤ 1 / 2 * ρ σ + (σ - σ') ^ (-ξ) * (K * X) := by
    intro σ' σ hσ'1 hσσ' hσ1
    have hσ : σ ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, hσ1⟩
    have hs : 0 < σ - σ' := sub_pos.2 hσσ'
    have hB : 0 ≤ A * (σ - σ') ^ (-a) := mul_nonneg hA.le (Real.rpow_nonneg hs.le _)
    have hint := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow
      (hfr.aestronglyMeasurable.mono_measure (hle σ hσ)) h0 h1 hpqr
    have hR := (hRH σ' σ hσ'1 hσσ' hσ1).trans (mul_le_mul_right hint _)
    have hfin : ENNReal.ofReal (A * (σ - σ') ^ (-a)) *
        (eLpNorm f p (μ.restrict (S σ)) ^ h * eLpNorm f r (μ.restrict (S σ)) ^ (1 - h)) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg h0.le (hfinp σ hσ))
        (ENNReal.rpow_ne_top_of_nonneg h1'.le (hfinr σ hσ)))
    have hreal := ENNReal.toReal_mono hfin hR
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, ← ENNReal.toReal_rpow,
      ← ENNReal.toReal_rpow] at hreal
    set Xσ := (eLpNorm f p (μ.restrict (S σ))).toReal with hXσ
    have hXσ0 : 0 ≤ Xσ := ENNReal.toReal_nonneg
    have hXσX : Xσ ≤ X :=
      ENNReal.toReal_mono hfp.eLpNorm_ne_top (eLpNorm_mono_measure _ (hle σ hσ))
    have hyoung := mul_rpow_mul_rpow_le_half_add h0 h1 hB hXσ0
      (ENNReal.toReal_nonneg : 0 ≤ ρ σ)
    have hBpow : (A * (σ - σ') ^ (-a)) ^ (1 / h) = A ^ (1 / h) * (σ - σ') ^ (-ξ) := by
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le, hξ]
      congr 2
      ring
    have hlast : h * κ * (A * (σ - σ') ^ (-a)) ^ (1 / h) * Xσ ≤ (σ - σ') ^ (-ξ) * (K * X) := by
      rw [hBpow, hKdef]
      have hsξ : 0 ≤ (σ - σ') ^ (-ξ) := Real.rpow_nonneg hs.le _
      calc h * κ * (A ^ (1 / h) * (σ - σ') ^ (-ξ)) * Xσ
          = (σ - σ') ^ (-ξ) * (h * κ * A ^ (1 / h) * Xσ) := by ring
        _ ≤ (σ - σ') ^ (-ξ) * (h * κ * A ^ (1 / h) * X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXσX hK0) hsξ
    change ρ σ' ≤ _ at hreal
    rw [← hκdef] at hyoung
    linarith
  set A' := (2 / 3 : ℝ) ^ (-ξ) * (K * X) with hA'
  have hA'0 : 0 ≤ A' := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg hK0 hX0)
  have hmem : ∀ t ∈ Ico (1 / 2 : ℝ) 1, (2 * t + 1) / 3 ∈ Ioc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbdd : BddAbove ((fun t => (1 - t) ^ ξ * ρ ((2 * t + 1) / 3)) '' Ico (1 / 2 : ℝ) 1) := by
    refine ⟨(eLpNorm f r (μ.restrict U)).toReal, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1t : (1 - t) ^ ξ ≤ 1 := Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) hξ0
    have hρt : ρ ((2 * t + 1) / 3) ≤ (eLpNorm f r (μ.restrict U)).toReal :=
      ENNReal.toReal_mono hfr.eLpNorm_ne_top (eLpNorm_mono_measure _ (hle _ (hmem t ht)))
    calc (1 - t) ^ ξ * ρ ((2 * t + 1) / 3) ≤ 1 * (eLpNorm f r (μ.restrict U)).toReal :=
          mul_le_mul h1t hρt ENNReal.toReal_nonneg zero_le_one
      _ = _ := one_mul _
  have hstep : ∀ s t : ℝ, 1 / 2 ≤ s → s < t → t < 1 →
      ρ ((2 * s + 1) / 3) ≤ 1 / 2 * ρ ((2 * t + 1) / 3) + (t - s) ^ (-ξ) * A' := by
    intro s t hs hst ht
    have hts : 0 < t - s := sub_pos.2 hst
    have h := step ((2 * s + 1) / 3) ((2 * t + 1) / 3) (by linarith) (by linarith) (by linarith)
    have heq : (2 * t + 1) / 3 - (2 * s + 1) / 3 = 2 / 3 * (t - s) := by ring
    rw [heq, Real.mul_rpow (by norm_num) hts.le] at h
    calc ρ ((2 * s + 1) / 3) ≤ 1 / 2 * ρ ((2 * t + 1) / 3) +
          (2 / 3 : ℝ) ^ (-ξ) * (t - s) ^ (-ξ) * (K * X) := h
      _ = 1 / 2 * ρ ((2 * t + 1) / 3) + (t - s) ^ (-ξ) * A' := by rw [hA']; ring
  have hC := hC₆ A' hA'0 (fun t => ρ ((2 * t + 1) / 3))
    (fun t _ => ENNReal.toReal_nonneg) hbdd hstep
  have h23 : ρ (2 / 3) ≤ C₆ * A' := by
    have e : (2 * (1 / 2 : ℝ) + 1) / 3 = 2 / 3 := by norm_num
    have hC' : ρ ((2 * (1 / 2 : ℝ) + 1) / 3) ≤ C₆ * A' := hC
    rwa [e] at hC'
  have h23' : ρ (2 / 3) ≤ max C₆ 0 * ((2 / 3 : ℝ) ^ (-ξ) * K) * X := by
    calc ρ (2 / 3) ≤ C₆ * A' := h23
      _ ≤ max C₆ 0 * A' := mul_le_mul_of_nonneg_right (le_max_left _ _) hA'0
      _ = max C₆ 0 * ((2 / 3 : ℝ) ^ (-ξ) * K) * X := by rw [hA']; ring
  have hfin23 := hfinr (2 / 3) ⟨by norm_num, by norm_num⟩
  have hc0 : 0 ≤ max C₆ 0 * ((2 / 3 : ℝ) ^ (-ξ) * K) :=
    mul_nonneg (le_max_right _ _) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hK0)
  calc eLpNorm f r (μ.restrict (S (2 / 3))) = ENNReal.ofReal (ρ (2 / 3)) :=
        (ENNReal.ofReal_toReal hfin23).symm
    _ ≤ ENNReal.ofReal (max C₆ 0 * ((2 / 3 : ℝ) ^ (-ξ) * K) * X) := ENNReal.ofReal_le_ofReal h23'
    _ = ENNReal.ofReal (max C₆ 0 * ((2 / 3 : ℝ) ^ (-ξ) * K)) * ENNReal.ofReal X :=
        ENNReal.ofReal_mul hc0
    _ = _ := by rw [hXdef, ENNReal.ofReal_toReal hfp.eLpNorm_ne_top]; rfl

/-- **Lemma E.6.** Fix `0 < p < q < r ≤ ∞` and `A, a > 0`. There is `C(a, A, p, q, r) < ∞` such
that, for every Borel measure `μ` on `ℝⁿ`, every Borel set `U`, every family `{σU}_{σ ∈ (0, 1]}`
of Borel subsets of `U` and every `f ∈ L^p(U; μ) ∩ L^r(U; μ)` with the reverse Hölder inequality
`‖f‖_{L^r(σ'U; μ)} ≤ A (σ - σ')^{-a} ‖f‖_{L^q(σU; μ)}` for all `σ' < σ` in `[1/2, 1]` (E.18),
`‖f‖_{L^r(⅔U; μ)} ≤ C ‖f‖_{L^p(U; μ)}`. -/
theorem lemma_E_6 {p q r : ℝ≥0∞} (hp : 0 < p) (hpq : p < q) (hqr : q < r) {A a : ℝ}
    (hA : 0 < A) (ha : 0 < a) :
    ∃ C : ℝ≥0, ∀ (n : ℕ) (μ : Measure (Vec n)) (U : Set (Vec n)) (S : ℝ → Set (Vec n))
      (f : Vec n → ℝ), MeasurableSet U → (∀ σ ∈ Ioc (0 : ℝ) 1, MeasurableSet (S σ) ∧ S σ ⊆ U) →
      MemLp f p (μ.restrict U) → MemLp f r (μ.restrict U) →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
        eLpNorm f r (μ.restrict (S σ')) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-a)) * eLpNorm f q (μ.restrict (S σ))) →
      eLpNorm f r (μ.restrict (S (2 / 3))) ≤ C * eLpNorm f p (μ.restrict U) := by
  obtain ⟨C, hC⟩ := reverseHolder_improvement hp hpq hqr hA ha
  exact ⟨C, fun n μ U S f _ hS hfp hfr hRH =>
    hC μ U S f (fun σ hσ => (hS σ hσ).2) hfp hfr hRH⟩

end QSH
