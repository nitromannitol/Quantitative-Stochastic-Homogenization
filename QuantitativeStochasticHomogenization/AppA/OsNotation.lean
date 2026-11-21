/-
Moved from einstein-relation-lean (https://github.com/nitromannitol/einstein-relation-lean):
commit 9ff210bd4ddf435139a6c8db07a1547e2bcb7eb6, files
`EinsteinFull/Homogenization/OsBoundMax.lean`, `EinsteinFull/Homogenization/AKMOsCalculus.lean`,
`EinsteinFull/Homogenization/StretchedExponentialTail.lean`,
`EinsteinFull/Homogenization/AKMCenteredOsBound.lean` and
`EinsteinFull/Homogenization/AKMFiniteRangeSums.lean`; commit
3c88f7631ee1ec7d82adfc66c504c3f4d95f004c, file
`EinsteinFull/Homogenization/AKMCenteredOsBoundCalculus.lean`.
Changes: the namespace is `QSH` and the docstrings cite the book directly; the statements of
Lemmas A.1, A.3, A.9 and A.12 in the form of the book, and the passage between `|X| ≤ O_s(θ)` and
`X = O_s(θ)`, are added.
The layer-cake bound `lintegral_ofReal_exp_le_two_of_tail` and `osBound_of_tail` are adapted,
through the file `StretchedExponentialTail.lean` above, from subdiffusive-process
(https://github.com/nitromannitol/subdiffusive-process), commit
4c6b8fa60357a07fd5713e5104a6cc70f8e432dc, file
`SubdiffusiveProcess/Probability/Orlicz/TailConverse.lean` (`integrable_exp_le_two_of_tail` and
`ogammaLE_of_all_level_tail`), licensed under the Apache License 2.0.
-/
import QuantitativeStochasticHomogenization.Front.Notation
import QuantitativeStochasticHomogenization.Front.Assumptions
import SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound
import SubdiffusiveProcess.Paper.app_a_orlicz_tail_converse
import SubdiffusiveProcess.Probability.Orlicz.FiniteTriangle
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit
import SubdiffusiveProcess.Assumptions.OGammaBridge
import Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.FiniteSums

/-!
# Appendix A: The O_s Notation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix A. Numbered results of this appendix: Lemmas A.1, A.3–A.5, A.7–A.12.

Defined here: `X ≤ O_s(θ)`, (A.1).

Also defined: the centered bound `X = 𝒪_s(θ)` of (A.12) (`CenteredOsBound`), and, for an
abstract family `F` of local σ-algebras, the unit range of dependence (`HasUnitRange`).

Proved here:

* the rules of `O_s`: monotonicity in the scale and in the variable, homogeneity, the triangle
  inequality for `s ≥ 1` (the remark after (A.2), and Lemma A.4 for finite sums with `C_s = 1`),
  the passage to a smaller exponent, powers, the indicator of a minimal scale ((4.24)),
  deterministic bounds, maxima, transport by measure-preserving maps, and the mean of a bound;
* Lemma A.1 (both implications, through subdiffusive-process), and the variant of Remark A.2 in
  which the tail is assumed at the levels `x ≥ 1` only (`osBound_of_tail`);
* Lemma A.3 (i) and (ii);
* the rules of `𝒪_s`: symmetry, monotonicity, homogeneity, the triangle inequality, Lemma A.9
  (both implications, with explicit constants in the first), Lemma A.10 for a constant scale on a
  finite measure, Lemma A.11 (with `C = √2`, and `C = 1` for equal scales) and Lemma A.12 (with
  `C = (2 · 4^d)^{1/2}`).

The identification of `OsBound` with the predicate `SubdiffusiveProcess.OGammaLE` of the library
subdiffusive-process (`osBound_iff_ogammaLE`) gives access to its triangle inequalities and tail
bounds; Lemma A.9 uses the one-variable moment generating function bounds of the library
CoarseGraining.
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- **`X ≤ O_s(θ)`**, (A.1): `E[exp((θ⁻¹ X₊)^s)] ≤ 2`. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

open ProbabilityTheory
open scoped ENNReal

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## The stochastic bound of a maximum -/

section Maximum

theorem exp_max_half_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.exp (max u v / 2) ≤ (Real.exp u + Real.exp v) / 2 := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → b ≤ a →
      Real.exp (a / 2) ≤ (Real.exp a + Real.exp b) / 2 := by
    intro a b ha hb hba
    have h1 : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [sq, ← Real.exp_add]
      ring_nf
    have h2 : 1 ≤ Real.exp b := Real.one_le_exp hb
    nlinarith [sq_nonneg (Real.exp (a / 2) - 1)]
  rcases le_total u v with h | h
  · rw [max_eq_right h, add_comm]
    exact key v u hv hu h
  · rw [max_eq_left h]
    exact key u v hu hv h

theorem rpow_inv_mul_max_le {θ θ₁ s m : ℝ} (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ) (hs : 0 < s)
    (hm : 0 ≤ m) : (θ⁻¹ * m) ^ s ≤ (θ₁⁻¹ * m) ^ s := by
  have h1 : θ⁻¹ * m ≤ θ₁⁻¹ * m :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hθ₁ hθ) hm
  exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr (hθ₁.le.trans hθ)) hm) h1 hs.le

/-- **The stochastic bound of a maximum.** -/
theorem osBound_max {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {s θ₁ θ₂ : ℝ} (hX : OsBound P X s θ₁) (hY : OsBound P Y s θ₂) :
    OsBound P (fun ω => max (X ω) (Y ω)) s ((2 : ℝ) ^ s⁻¹ * max θ₁ θ₂) := by
  obtain ⟨hXm, hs, hθ₁, hXi⟩ := hX
  obtain ⟨hYm, -, hθ₂, hYi⟩ := hY
  set θ := max θ₁ θ₂ with hθdef
  have hθ : 0 < θ := lt_max_of_lt_left hθ₁
  have h2s : 0 < (2 : ℝ) ^ s⁻¹ := Real.rpow_pos_of_pos two_pos _
  refine ⟨hXm.max hYm, hs, mul_pos h2s hθ, ?_⟩
  have hpt : ∀ ω, Real.exp ((((2 : ℝ) ^ s⁻¹ * θ)⁻¹ * max (max (X ω) (Y ω)) 0) ^ s) ≤
      (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s) + Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s)) / 2 := by
    intro ω
    set a := max (X ω) 0
    set b := max (Y ω) 0
    have ha : 0 ≤ a := le_max_right _ _
    have hb : 0 ≤ b := le_max_right _ _
    have hmax : max (max (X ω) (Y ω)) 0 = max a b := by
      simp only [a, b]
      rcases le_total (X ω) (Y ω) with h | h
      · rw [max_eq_right h, max_eq_right (max_le_max h le_rfl)]
      · rw [max_eq_left h, max_eq_left (max_le_max h le_rfl)]
    have hscale : (((2 : ℝ) ^ s⁻¹ * θ)⁻¹ * max a b) ^ s = (θ⁻¹ * max a b) ^ s / 2 := by
      rw [mul_inv, mul_assoc, Real.mul_rpow (inv_nonneg.mpr h2s.le)
        (mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_of_le_left ha)), Real.inv_rpow h2s.le,
        ← Real.rpow_mul two_pos.le, inv_mul_cancel₀ hs.ne', Real.rpow_one]
      ring
    have hmaxs : (θ⁻¹ * max a b) ^ s = max ((θ⁻¹ * a) ^ s) ((θ⁻¹ * b) ^ s) := by
      rcases le_total a b with h | h
      · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hθ.le) ha)
          (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hθ.le)) hs.le)]
      · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hθ.le) hb)
          (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hθ.le)) hs.le)]
    rw [hmax, hscale, hmaxs]
    have hu := rpow_inv_mul_max_le hθ₁ (le_max_left θ₁ θ₂) hs ha
    have hv := rpow_inv_mul_max_le hθ₂ (le_max_right θ₁ θ₂) hs hb
    have hu0 : 0 ≤ (θ⁻¹ * a) ^ s := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) ha) _
    have hv0 : 0 ≤ (θ⁻¹ * b) ^ s := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) hb) _
    refine (exp_max_half_le hu0 hv0).trans ?_
    gcongr
  have hmX : Measurable (fun ω => ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s))) := by
    fun_prop
  have hmY : Measurable (fun ω => ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s))) := by
    fun_prop
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((((2 : ℝ) ^ s⁻¹ * θ)⁻¹ *
        max (max (X ω) (Y ω)) 0) ^ s)) ∂P
      ≤ ∫⁻ ω, (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s)) +
          ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
          ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ((hpt ω).trans (le_of_eq ?_))
        ring
    _ = (2 : ℝ≥0∞)⁻¹ * ((∫⁻ ω, ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s)) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s)) ∂P) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hmX]
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (2 + 2) := by gcongr
    _ = 2 := by
        rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_mul]

end Maximum

/-! ## The rules of the stochastic bound `O_s` -/

section Rules

theorem measurable_osIntegrand {X : Ω → ℝ} (hX : Measurable X) (s θ : ℝ) :
    Measurable (fun ω => Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) :=
  ((measurable_const.mul (hX.max measurable_const)).pow_const s).exp

/-- `OsBound` is the predicate `OGammaLE` of subdiffusive-process together with the
measurability of the variable and the positivity of the exponent and of the scale. -/
theorem osBound_iff_ogammaLE {X : Ω → ℝ} {s θ : ℝ} :
    OsBound P X s θ ↔
      Measurable X ∧ 0 < s ∧ 0 < θ ∧ SubdiffusiveProcess.OGammaLE P s θ X := by
  have hnn : ∀ ω, 0 ≤ Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) := fun ω => (Real.exp_pos _).le
  constructor
  · rintro ⟨hX, hs, hθ, hint⟩
    refine ⟨hX, hs, hθ, ?_⟩
    have hm := measurable_osIntegrand hX s θ
    have hnn' : 0 ≤ᵐ[P] fun ω => Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) :=
      Filter.Eventually.of_forall hnn
    have hfin : HasFiniteIntegral (fun ω => Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) P := by
      rw [hasFiniteIntegral_iff_ofReal hnn']
      exact hint.trans_lt (by simp)
    refine ⟨⟨hm.aestronglyMeasurable, hfin⟩, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae hnn' hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_two (by rw [ENNReal.ofReal_ofNat]; exact hint)
  · rintro ⟨hX, hs, hθ, hint, hle⟩
    refine ⟨hX, hs, hθ, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
    calc ENNReal.ofReal (∫ ω, Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) ∂P)
        ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
      _ = 2 := ENNReal.ofReal_ofNat 2

theorem rpow_le_one_add_rpow {y s s' : ℝ} (hy : 0 ≤ y) (hs' : 0 ≤ s') (hss : s' ≤ s) :
    y ^ s' ≤ 1 + y ^ s := by
  rcases le_total y 1 with h | h
  · exact (Real.rpow_le_one hy h hs').trans (le_add_of_nonneg_right (Real.rpow_nonneg hy s))
  · exact (Real.rpow_le_rpow_of_exponent_le h hss).trans (le_add_of_nonneg_left zero_le_one)

theorem rpow_inv_rpow_mul_inv_mul {κ θ m s' : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hm : 0 ≤ m)
    (hs' : 0 < s') : ((κ ^ s'⁻¹ * θ)⁻¹ * m) ^ s' = κ⁻¹ * (θ⁻¹ * m) ^ s' := by
  have hκs : 0 < κ ^ s'⁻¹ := Real.rpow_pos_of_pos hκ _
  rw [mul_inv, mul_assoc, Real.mul_rpow (inv_nonneg.mpr hκs.le)
    (mul_nonneg (inv_nonneg.mpr hθ.le) hm), Real.inv_rpow hκs.le, ← Real.rpow_mul hκ.le,
    inv_mul_cancel₀ hs'.ne', Real.rpow_one]

theorem OsBound.exponent_pos {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ) : 0 < s := h.2.1

theorem OsBound.scale_pos {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ) : 0 < θ := h.2.2.1

/-- A larger scale is admissible. -/
theorem OsBound.mono_scale {X : Ω → ℝ} {s θ θ' : ℝ} (h : OsBound P X s θ) (hθ : θ ≤ θ') :
    OsBound P X s θ' := by
  obtain ⟨hX, hs, hθ0, hint⟩ := h
  refine ⟨hX, hs, hθ0.trans_le hθ, le_trans (lintegral_mono fun ω => ?_) hint⟩
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (rpow_inv_mul_max_le hθ0 hθ hs (le_max_right _ _)))

/-- A measurable variable that is almost surely smaller satisfies the same bound. -/
theorem OsBound.of_le_ae {X Y : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ) (hY : Measurable Y)
    (hle : ∀ᵐ ω ∂P, Y ω ≤ X ω) : OsBound P Y s θ := by
  obtain ⟨-, hs, hθ, hint⟩ := h
  refine ⟨hY, hs, hθ, le_trans (lintegral_mono_ae ?_) hint⟩
  filter_upwards [hle] with ω hω
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_right _ _))
    (mul_le_mul_of_nonneg_left (max_le_max hω le_rfl) (inv_nonneg.mpr hθ.le)) hs.le

/-- A measurable variable that is everywhere smaller satisfies the same bound. -/
theorem OsBound.of_le {X Y : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ) (hY : Measurable Y)
    (hle : ∀ ω, Y ω ≤ X ω) : OsBound P Y s θ :=
  h.of_le_ae hY (Filter.Eventually.of_forall hle)

/-- Homogeneity: `c X ≤ O_s(c θ)` for `c > 0`. -/
theorem OsBound.const_mul {X : Ω → ℝ} {s θ c : ℝ} (h : OsBound P X s θ) (hc : 0 < c) :
    OsBound P (fun ω => c * X ω) s (c * θ) := by
  obtain ⟨hX, hs, hθ, hint⟩ := h
  have key : ∀ ω, (c * θ)⁻¹ * max (c * X ω) 0 = θ⁻¹ * max (X ω) 0 := by
    intro ω
    rw [show max (c * X ω) 0 = c * max (X ω) 0 by rw [mul_max_of_nonneg _ _ hc.le, mul_zero]]
    field_simp
  refine ⟨measurable_const.mul hX, hs, mul_pos hc hθ, ?_⟩
  simpa only [key] using hint

/-- **A smaller exponent.** If `X ≤ O_s(θ)` and `0 < s' ≤ s`, then
`X ≤ O_{s'}((2e - 1)^(1/s') θ)`. The proof is `y^{s'} ≤ 1 + y^s` and the convexity of `exp`. -/
theorem OsBound.mono_exponent [IsProbabilityMeasure P] {X : Ω → ℝ} {s s' θ : ℝ}
    (h : OsBound P X s θ) (hs' : 0 < s') (hss : s' ≤ s) :
    OsBound P X s' ((2 * Real.exp 1 - 1) ^ s'⁻¹ * θ) := by
  obtain ⟨hX, hs, hθ, hfi, hfle⟩ := osBound_iff_ogammaLE.1 h
  set κ : ℝ := 2 * Real.exp 1 - 1 with hκdef
  have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hκ : 1 < κ := by rw [hκdef]; linarith
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  have ht0 : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ0.le
  have ht1 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ.le
  set f : Ω → ℝ := fun ω => Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) with hf
  set g : Ω → ℝ := fun ω => Real.exp (((κ ^ s'⁻¹ * θ)⁻¹ * max (X ω) 0) ^ s') with hg
  have hpt : ∀ ω, g ω ≤ (1 - κ⁻¹) + κ⁻¹ * Real.exp 1 * f ω := by
    intro ω
    set y : ℝ := θ⁻¹ * max (X ω) 0 with hy
    have hy0 : 0 ≤ y := mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_right _ _)
    have hgω : g ω = Real.exp (κ⁻¹ * y ^ s') := by
      simp only [hg, hy]
      rw [rpow_inv_rpow_mul_inv_mul hκ0 hθ (le_max_right _ _) hs']
    rw [hgω]
    have h1 : κ⁻¹ * y ^ s' ≤ κ⁻¹ * (1 + y ^ s) :=
      mul_le_mul_of_nonneg_left (rpow_le_one_add_rpow hy0 hs'.le hss) ht0
    have h2 : Real.exp (κ⁻¹ * (1 + y ^ s) + (1 - κ⁻¹) * 0) ≤
        κ⁻¹ * Real.exp (1 + y ^ s) + (1 - κ⁻¹) * Real.exp 0 :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ht0 (by linarith) (by ring)
    rw [mul_zero, add_zero, Real.exp_zero, mul_one, Real.exp_add] at h2
    calc Real.exp (κ⁻¹ * y ^ s') ≤ Real.exp (κ⁻¹ * (1 + y ^ s)) := Real.exp_le_exp.mpr h1
      _ ≤ κ⁻¹ * (Real.exp 1 * Real.exp (y ^ s)) + (1 - κ⁻¹) := h2
      _ = (1 - κ⁻¹) + κ⁻¹ * Real.exp 1 * f ω := by simp only [hf, hy]; ring
  have hbi : Integrable (fun ω => (1 - κ⁻¹) + κ⁻¹ * Real.exp 1 * f ω) P :=
    (integrable_const _).add (hfi.const_mul _)
  have hgi : Integrable g P :=
    Integrable.mono' hbi (measurable_osIntegrand hX s' _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpt ω)
  refine osBound_iff_ogammaLE.2 ⟨hX, hs', mul_pos (Real.rpow_pos_of_pos hκ0 _) hθ, hgi, ?_⟩
  calc ∫ ω, g ω ∂P ≤ ∫ ω, ((1 - κ⁻¹) + κ⁻¹ * Real.exp 1 * f ω) ∂P :=
        integral_mono hgi hbi hpt
    _ = (1 - κ⁻¹) + κ⁻¹ * Real.exp 1 * ∫ ω, f ω ∂P := by
        rw [integral_add (integrable_const _) (hfi.const_mul _), integral_const_mul]
        simp
    _ ≤ (1 - κ⁻¹) + κ⁻¹ * Real.exp 1 * 2 := by
        gcongr
    _ = 2 := by
        have hκκ : κ⁻¹ * (2 * Real.exp 1 - 1) = 1 := by
          rw [← hκdef]
          exact inv_mul_cancel₀ hκ0.ne'
        linear_combination hκκ

/-- **Powers.** For a nonnegative `X ≤ O_s(θ)` and `t > 0`, `X^t ≤ O_{s/t}(θ^t)`. -/
theorem OsBound.rpow {X : Ω → ℝ} {s θ t : ℝ} (h : OsBound P X s θ) (hX0 : ∀ ω, 0 ≤ X ω)
    (ht : 0 < t) : OsBound P (fun ω => X ω ^ t) (s / t) (θ ^ t) := by
  obtain ⟨hX, hs, hθ, hint⟩ := h
  have key : ∀ ω, ((θ ^ t)⁻¹ * max (X ω ^ t) 0) ^ (s / t) = (θ⁻¹ * max (X ω) 0) ^ s := by
    intro ω
    rw [max_eq_left (Real.rpow_nonneg (hX0 ω) t), max_eq_left (hX0 ω),
      ← Real.inv_rpow hθ.le, ← Real.mul_rpow (inv_nonneg.mpr hθ.le) (hX0 ω),
      ← Real.rpow_mul (mul_nonneg (inv_nonneg.mpr hθ.le) (hX0 ω))]
    congr 1
    field_simp
  refine ⟨hX.pow_const t, div_pos hs ht, Real.rpow_pos_of_pos hθ t, ?_⟩
  simpa only [key] using hint

/-- **The indicator of a minimal scale**, (4.24) of Chapter 4: if `0 ≤ Y ≤ O_s(θ)`, `r > 0` and
`t > 0`, then `1{Y ≥ r} ≤ (Y/r)^t ≤ O_{s/t}((θ/r)^t)`. -/
theorem OsBound.indicator_le_of {Y : Ω → ℝ} {s θ r t : ℝ} (h : OsBound P Y s θ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hr : 0 < r) (ht : 0 < t) :
    OsBound P (Set.indicator {ω | r ≤ Y ω} (fun _ => (1 : ℝ))) (s / t) ((θ / r) ^ t) := by
  have hc : 0 < r⁻¹ := inv_pos.mpr hr
  have h1 : OsBound P (fun ω => (r⁻¹ * Y ω) ^ t) (s / t) ((r⁻¹ * θ) ^ t) :=
    (h.const_mul hc).rpow (fun ω => mul_nonneg hc.le (hY0 ω)) ht
  rw [show θ / r = r⁻¹ * θ from div_eq_inv_mul θ r]
  refine h1.of_le (measurable_const.indicator (measurableSet_le measurable_const h.1)) ?_
  intro ω
  by_cases hω : r ≤ Y ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | r ≤ Y ω} from hω)]
    refine Real.one_le_rpow ?_ ht.le
    rw [← div_eq_inv_mul, one_le_div hr]
    exact hω
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | r ≤ Y ω} from hω)]
    exact Real.rpow_nonneg (mul_nonneg hc.le (hY0 ω)) t

/-- **Transport by a measure-preserving map**, used with the stationarity of the law. -/
theorem OsBound.comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T P P)
    {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ) :
    OsBound P (fun ω => X (T ω)) s θ := by
  obtain ⟨hX, hs, hθ, hint⟩ := h
  refine ⟨hX.comp hT.measurable, hs, hθ, ?_⟩
  exact (hT.lintegral_comp (ENNReal.measurable_ofReal.comp (measurable_osIntegrand hX s θ))).trans_le
    hint

/-- **Triangle inequality** for `s ≥ 1`: the scales add. -/
theorem osBound_add {X Y : Ω → ℝ} {s θ₁ θ₂ : ℝ} (hX : OsBound P X s θ₁)
    (hY : OsBound P Y s θ₂) (hs : 1 ≤ s) :
    OsBound P (fun ω => X ω + Y ω) s (θ₁ + θ₂) := by
  obtain ⟨hXm, hs0, hθ₁, hXo⟩ := osBound_iff_ogammaLE.1 hX
  obtain ⟨hYm, -, hθ₂, hYo⟩ := osBound_iff_ogammaLE.1 hY
  exact osBound_iff_ogammaLE.2 ⟨hXm.add hYm, hs0, add_pos hθ₁ hθ₂,
    SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_add hθ₁ hθ₂ hs
      hXm.aemeasurable hYm.aemeasurable hXo hYo⟩

/-- **Triangle inequality for finite sums** for `s ≥ 1`. -/
theorem osBound_finset_sum {ι : Type*} (I : Finset ι) (hI : I.Nonempty) {X : ι → Ω → ℝ}
    {s : ℝ} {θ : ι → ℝ} (hs : 1 ≤ s) (hX : ∀ i ∈ I, OsBound P (X i) s (θ i)) :
    OsBound P (fun ω => ∑ i ∈ I, X i ω) s (∑ i ∈ I, θ i) := by
  have hm : ∀ i ∈ I, Measurable (X i) := fun i hi => (hX i hi).1
  refine osBound_iff_ogammaLE.2 ⟨Finset.measurable_sum I hm, zero_lt_one.trans_le hs,
    Finset.sum_pos (fun i hi => (hX i hi).2.2.1) hI, ?_⟩
  exact SubdiffusiveProcess.Probability.Orlicz.ogammaLE_finset_sum hs I hI
    (fun i hi => (hX i hi).2.2.1) (fun i hi => (hm i hi).aemeasurable)
    (fun i hi => (osBound_iff_ogammaLE.1 (hX i hi)).2.2.2)

/-- **Deterministic bounds.** On a probability space, a measurable `X ≤ c` with `c > 0` satisfies
`X ≤ O_s(c / (log 2)^(1/s))`. -/
theorem osBound_of_le_const [IsProbabilityMeasure P] {X : Ω → ℝ} {s c : ℝ}
    (hX : Measurable X) (hs : 0 < s) (hc : 0 < c) (hle : ∀ᵐ ω ∂P, X ω ≤ c) :
    OsBound P X s (c / Real.log 2 ^ s⁻¹) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hls : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos hl _
  refine ⟨hX, hs, div_pos hc hls, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (((c / Real.log 2 ^ s⁻¹)⁻¹ * max (X ω) 0) ^ s)) ∂P
      ≤ ∫⁻ _, (2 : ℝ≥0∞) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle] with ω hω
        rw [← ENNReal.ofReal_ofNat 2]
        refine ENNReal.ofReal_le_ofReal ?_
        refine (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log two_pos)
        have hm : max (X ω) 0 ≤ c := max_le hω hc.le
        calc ((c / Real.log 2 ^ s⁻¹)⁻¹ * max (X ω) 0) ^ s
            ≤ ((c / Real.log 2 ^ s⁻¹)⁻¹ * c) ^ s := by
              refine Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr (div_pos hc hls).le)
                (le_max_right _ _)) ?_ hs.le
              exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (div_pos hc hls).le)
          _ = Real.log 2 := by
              rw [inv_div, div_mul_cancel₀ _ hc.ne', ← Real.rpow_mul hl.le,
                inv_mul_cancel₀ hs.ne', Real.rpow_one]
    _ = 2 := by simp

end Rules

/-! ## Stochastic bounds from tail bounds -/

section TailBounds

open Set

variable {μ : Measure Ω}

/-- **Layer-cake bound.** A nonnegative random variable `Z` with `P[Z > r] ≤ exp(-3r)` for every
`r ≥ 1/8` satisfies `E[exp Z] ≤ 2`. -/
theorem lintegral_ofReal_exp_le_two_of_tail [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : ∀ ω, 0 ≤ Z ω) (hm : AEMeasurable Z μ)
    (ht : ∀ r : ℝ, 1 / 8 ≤ r → μ {ω | r < Z ω} ≤ ENNReal.ofReal (Real.exp (-3 * r))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂μ ≤ 2 := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (f := Z) (g := Real.exp) (Filter.Eventually.of_forall hZ) hm
    (fun r _ => Real.continuous_exp.intervalIntegrable 0 r)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  set c : ENNReal := ENNReal.ofReal (Real.exp (1 / 8)) with hc
  have hdom : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤
        (Iio (1 / 8 : ℝ)).indicator (fun _ => c) r + ENNReal.ofReal (Real.exp (-2 * r)) := by
    refine Filter.Eventually.of_forall fun r => ?_
    by_cases hr : r < 1 / 8
    · rw [indicator_of_mem (show r ∈ Iio (1 / 8 : ℝ) from hr)]
      calc μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤ 1 * c :=
            mul_le_mul' prob_le_one (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hr.le))
        _ = c := one_mul c
        _ ≤ _ := le_self_add
    · rw [indicator_of_notMem (show r ∉ Iio (1 / 8 : ℝ) from hr), zero_add]
      calc μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤
            ENNReal.ofReal (Real.exp (-3 * r)) * ENNReal.ofReal (Real.exp r) :=
            mul_le_mul' (ht r (not_lt.mp hr)) le_rfl
        _ = ENNReal.ofReal (Real.exp (-2 * r)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 2
            ring
  have hg : IntegrableOn (fun r : ℝ => Real.exp (-2 * r)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hgL : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * r)) = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      integral_exp_mul_Ioi (by norm_num) 0]
    norm_num
  have hind : ∫⁻ r in Ioi (0 : ℝ), (Iio (1 / 8 : ℝ)).indicator (fun _ => c) r =
      c * ENNReal.ofReal (1 / 8) := by
    rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
  have he : Real.exp (1 / 8) ≤ 4 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 8) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hsum : ∫⁻ r in Ioi (0 : ℝ), ((Iio (1 / 8 : ℝ)).indicator (fun _ => c) r +
      ENNReal.ofReal (Real.exp (-2 * r))) ≤ 1 := by
    rw [lintegral_add_left (measurable_const.indicator measurableSet_Iio), hind, hgL, hc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (by norm_num), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  have hL : ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ ≤ 1 := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..Z ω, Real.exp r) ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [integral_exp, Real.exp_zero]
      _ = _ := hlayer
      _ ≤ _ := lintegral_mono_ae hdom
      _ ≤ 1 := hsum
  have hpoint : ∀ ω, ENNReal.ofReal (Real.exp (Z ω)) =
      ENNReal.ofReal (Real.exp (Z ω) - 1) + 1 := by
    intro ω
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by linarith [Real.one_le_exp (hZ ω)]) (by norm_num)]
    congr 1
    ring
  simp_rw [hpoint]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ + 1 ≤ 1 + 1 := add_le_add hL le_rfl
    _ = 2 := one_add_one_eq_two

/-- **Stretched-exponential moments from a tail bound.** If `P[X ≥ t A] ≤ exp(-t^q)` for every
`t ≥ 1` and `0 < s ≤ q`, then `X ≤ O_s(8^(1/s) A)`. -/
theorem osBound_of_tail [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {s q A : ℝ} (hs : 0 < s) (hsq : s ≤ q) (hA : 0 < A)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {ω | t * A ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ q)))) :
    OsBound μ X s ((8 : ℝ) ^ s⁻¹ * A) := by
  have h8 : 0 < (8 : ℝ) ^ s⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  set θ := (8 : ℝ) ^ s⁻¹ * A with hθ
  have hθ0 : 0 < θ := mul_pos h8 hA
  refine ⟨hX, hs, hθ0, ?_⟩
  set Y : Ω → ℝ := fun ω => θ⁻¹ * max (X ω) 0 with hYdef
  have hY : ∀ ω, 0 ≤ Y ω := fun ω => mul_nonneg (inv_nonneg.mpr hθ0.le) (le_max_right _ _)
  refine lintegral_ofReal_exp_le_two_of_tail (Z := fun ω => Y ω ^ s)
    (fun ω => Real.rpow_nonneg (hY ω) _) ?_ ?_
  · exact (((hX.max measurable_const).const_mul _).pow_const _).aemeasurable
  · intro r hr
    have hr0 : 0 < r := by linarith
    have h8r : 1 ≤ 8 * r := by linarith
    set t := (8 * r) ^ s⁻¹ with ht
    have ht1 : 1 ≤ t := Real.one_le_rpow h8r (inv_nonneg.mpr hs.le)
    have htA : t * A = θ * r ^ s⁻¹ := by
      rw [ht, hθ, Real.mul_rpow (by norm_num) hr0.le]
      ring
    have hsub : {ω | r < Y ω ^ s} ⊆ {ω | t * A ≤ X ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h1 : r ^ s⁻¹ < Y ω := by
        by_contra hcon
        push Not at hcon
        have h := Real.rpow_le_rpow (hY ω) hcon hs.le
        rw [Real.rpow_inv_rpow hr0.le hs.ne'] at h
        linarith
      have h2 : θ * r ^ s⁻¹ < max (X ω) 0 := by
        have h := mul_lt_mul_of_pos_left h1 hθ0
        rwa [hYdef, ← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul] at h
      rcases lt_max_iff.mp h2 with h | h
      · rw [htA]
        exact h.le
      · exact absurd h (not_lt.mpr (by positivity))
    calc μ {ω | r < Y ω ^ s} ≤ μ {ω | t * A ≤ X ω} := measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ q))) := htail t ht1
      _ ≤ ENNReal.ofReal (Real.exp (-3 * r)) := by
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have hq : t ^ q = (8 * r) ^ (q / s) := by
            rw [ht, ← Real.rpow_mul (by linarith), inv_mul_eq_div]
          have h3 : 8 * r ≤ (8 * r) ^ (q / s) := by
            calc 8 * r = (8 * r) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (8 * r) ^ (q / s) :=
                Real.rpow_le_rpow_of_exponent_le h8r ((one_le_div hs).mpr hsq)
          rw [hq]
          linarith

end TailBounds

/-! ## Centered stochastic bounds, (A.12), and Lemmas A.9 and A.11 -/

section CenteredBounds

/-- **The centered stochastic bound** `X = 𝒪_s(θ)` of (A.12): for every real `t`,
`E[exp(t θ⁻¹ X)] ≤ exp(t² ∨ |t|^{s/(s-1)})`, the expectation being an integral of an
integrable function. -/
def CenteredOsBound (P : Measure Ω) (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 1 < s ∧ s ≤ 2 ∧ 0 < θ ∧
    ∀ t : ℝ, Integrable (fun ω => Real.exp (t * (θ⁻¹ * X ω))) P ∧
      ∫ ω, Real.exp (t * (θ⁻¹ * X ω)) ∂P ≤ Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1))))

theorem two_le_div_sub_one {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) : 2 ≤ s / (s - 1) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem max_sq_rpow_le_of_abs_le {s u t : ℝ} (hs1 : 1 < s) (hu : |u| ≤ |t|) :
    max (u ^ 2) (|u| ^ (s / (s - 1))) ≤ max (t ^ 2) (|t| ^ (s / (s - 1))) :=
  max_le_max (sq_le_sq.mpr hu)
    (Real.rpow_le_rpow (abs_nonneg _) hu (div_nonneg (by linarith) (by linarith)))

theorem CenteredOsBound.neg {X : Ω → ℝ} {s θ : ℝ} (h : CenteredOsBound P X s θ) :
    CenteredOsBound P (fun ω => -X ω) s θ := by
  obtain ⟨hX, hs1, hs2, hθ, hb⟩ := h
  refine ⟨hX.neg, hs1, hs2, hθ, fun t => ?_⟩
  obtain ⟨hi, hle⟩ := hb (-t)
  have e : ∀ ω, t * (θ⁻¹ * -X ω) = -t * (θ⁻¹ * X ω) := fun ω => by ring
  simp only [e]
  exact ⟨hi, hle.trans_eq (by rw [neg_sq, abs_neg])⟩

theorem CenteredOsBound.mono_scale {X : Ω → ℝ} {s θ θ' : ℝ} (h : CenteredOsBound P X s θ)
    (hθθ : θ ≤ θ') : CenteredOsBound P X s θ' := by
  obtain ⟨hX, hs1, hs2, hθ, hb⟩ := h
  have hθ' : 0 < θ' := hθ.trans_le hθθ
  refine ⟨hX, hs1, hs2, hθ', fun t => ?_⟩
  set u : ℝ := t * (θ / θ') with hudef
  have e : ∀ ω, t * (θ'⁻¹ * X ω) = u * (θ⁻¹ * X ω) := fun ω => by
    rw [hudef]
    field_simp
  obtain ⟨hi, hle⟩ := hb u
  simp only [e]
  refine ⟨hi, hle.trans (Real.exp_le_exp.mpr (max_sq_rpow_le_of_abs_le hs1 ?_))⟩
  rw [hudef, abs_mul, abs_of_pos (div_pos hθ hθ')]
  exact mul_le_of_le_one_right (abs_nonneg t) ((div_le_one hθ').mpr hθθ)

/-- Homogeneity of the centered bound. -/
theorem CenteredOsBound.const_mul {X : Ω → ℝ} {s θ c : ℝ} (h : CenteredOsBound P X s θ)
    (hc : 0 < c) : CenteredOsBound P (fun ω => c * X ω) s (c * θ) := by
  obtain ⟨hX, hs1, hs2, hθ, hb⟩ := h
  refine ⟨measurable_const.mul hX, hs1, hs2, mul_pos hc hθ, fun t => ?_⟩
  have e : ∀ ω, t * ((c * θ)⁻¹ * (c * X ω)) = t * (θ⁻¹ * X ω) := fun ω => by
    field_simp
  simp only [e]
  exact hb t

/-- **Sums of independent centered bounds**, Lemma A.11: independent `Xᵢ = 𝒪_s(θᵢ)` have
`∑ Xᵢ = 𝒪_s(√2 (∑ θᵢ²)^{1/2})`. -/
theorem centeredOsBound_sum [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ} {s : ℝ} {θ : ι → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, CenteredOsBound P (X i) s (θ i)) :
    CenteredOsBound P (fun ω => ∑ i, X i ω) s
      (Real.sqrt 2 * Real.sqrt (∑ i, θ i ^ 2)) := by
  obtain ⟨-, hs1, hs2, -, -⟩ := hX (Classical.arbitrary ι)
  have hm : ∀ i, Measurable (X i) := fun i => (hX i).1
  have hθ : ∀ i, 0 < θ i := fun i => (hX i).2.2.2.1
  have hS : 0 < ∑ i, θ i ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (hθ i) 2) Finset.univ_nonempty
  set Θ : ℝ := Real.sqrt 2 * Real.sqrt (∑ i, θ i ^ 2) with hΘdef
  have hΘ : 0 < Θ := mul_pos (Real.sqrt_pos.mpr two_pos) (Real.sqrt_pos.mpr hS)
  have hΘsq : Θ ^ 2 = 2 * ∑ i, θ i ^ 2 := by
    rw [hΘdef, mul_pow, Real.sq_sqrt two_pos.le, Real.sq_sqrt hS.le]
  have hθΘ : ∀ i, θ i ≤ Θ := by
    intro i
    have h1 : θ i ≤ Real.sqrt (∑ j, θ j ^ 2) := by
      rw [Real.le_sqrt (hθ i).le hS.le]
      exact Finset.single_le_sum (f := fun j => θ j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h2 : Real.sqrt (∑ j, θ j ^ 2) ≤ Θ := by
      rw [hΘdef]
      refine le_mul_of_one_le_left (Real.sqrt_nonneg _) ?_
      rw [Real.one_le_sqrt]
      norm_num
    exact h1.trans h2
  have hp2 := two_le_div_sub_one hs1 hs2
  refine ⟨Finset.measurable_sum _ (fun i _ => hm i), hs1, hs2, hΘ, fun t => ?_⟩
  set u : ℝ := t * Θ⁻¹ with hudef
  have hcomp : ∀ i ω, u * X i ω = (u * θ i) * ((θ i)⁻¹ * X i ω) := fun i ω => by
    have h0 := (hθ i).ne'
    field_simp
  have hint : ∀ i, Integrable (fun ω => Real.exp (u * X i ω)) P := by
    intro i
    simp only [hcomp i]
    exact ((hX i).2.2.2.2 (u * θ i)).1
  have hfun : (fun ω => Real.exp (t * (Θ⁻¹ * ∑ i, X i ω))) =
      fun ω => Real.exp (u * (∑ i, X i) ω) := by
    funext ω
    rw [Finset.sum_apply, hudef, mul_assoc]
  rw [hfun]
  refine ⟨hind.integrable_exp_mul_sum hm (fun i _ => hint i), ?_⟩
  change mgf (∑ i, X i) P u ≤ _
  rw [hind.mgf_sum hm Finset.univ]
  have hmgf : ∀ i, mgf (X i) P u ≤
      Real.exp (max ((u * θ i) ^ 2) (|u * θ i| ^ (s / (s - 1)))) := by
    intro i
    have := ((hX i).2.2.2.2 (u * θ i)).2
    simp only [← hcomp i] at this
    exact this
  calc ∏ i, mgf (X i) P u
      ≤ ∏ i, Real.exp (max ((u * θ i) ^ 2) (|u * θ i| ^ (s / (s - 1)))) :=
        Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => hmgf i)
    _ = Real.exp (∑ i, max ((u * θ i) ^ 2) (|u * θ i| ^ (s / (s - 1)))) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : ∑ i, (u * θ i) ^ 2 = t ^ 2 / 2 := by
          have : ∑ i, (u * θ i) ^ 2 = u ^ 2 * ∑ i, θ i ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
          rw [this, hudef, mul_pow, inv_pow, ← div_eq_mul_inv]
          field_simp
          rw [hΘsq]
          ring
        have hrp : ∀ i, |u * θ i| ^ (s / (s - 1)) ≤ |t| ^ (s / (s - 1)) * (θ i / Θ) ^ 2 := by
          intro i
          have hx0 : 0 < θ i / Θ := div_pos (hθ i) hΘ
          have hx1 : θ i / Θ ≤ 1 := (div_le_one hΘ).mpr (hθΘ i)
          have e1 : |u * θ i| = |t| * (θ i / Θ) := by
            rw [hudef, abs_mul, abs_mul, abs_inv, abs_of_pos hΘ, abs_of_pos (hθ i)]
            ring
          rw [e1, Real.mul_rpow (abs_nonneg t) hx0.le]
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (abs_nonneg t) _)
          rw [← Real.rpow_two]
          exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hp2
        have hsum2 : ∑ i, (θ i / Θ) ^ 2 = 1 / 2 := by
          have : ∑ i, (θ i / Θ) ^ 2 = (∑ i, θ i ^ 2) / Θ ^ 2 := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun i _ => by rw [div_pow])
          rw [this, hΘsq]
          field_simp
        calc ∑ i, max ((u * θ i) ^ 2) (|u * θ i| ^ (s / (s - 1)))
            ≤ ∑ i, ((u * θ i) ^ 2 + |t| ^ (s / (s - 1)) * (θ i / Θ) ^ 2) :=
              Finset.sum_le_sum (fun i _ => max_le
                (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
                  (sq_nonneg _)))
                ((hrp i).trans (le_add_of_nonneg_left (sq_nonneg _))))
          _ = t ^ 2 / 2 + |t| ^ (s / (s - 1)) / 2 := by
              rw [Finset.sum_add_distrib, hsq, ← Finset.mul_sum, hsum2]
              ring
          _ ≤ max (t ^ 2) (|t| ^ (s / (s - 1))) := by
              linarith [le_max_left (t ^ 2) (|t| ^ (s / (s - 1))),
                le_max_right (t ^ 2) (|t| ^ (s / (s - 1)))]

/-- The one-sided Chernoff estimate behind Lemma A.9: `P[θ⁻¹ X ≥ 4t] ≤ exp(-(2t)^s)` for
`t ≥ 1`. -/
theorem CenteredOsBound.measureReal_ge_le [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : CenteredOsBound P X s θ) {t : ℝ} (ht : 1 ≤ t) :
    P.real {ω | 4 * t ≤ θ⁻¹ * X ω} ≤ Real.exp (-((2 * t) ^ s)) := by
  obtain ⟨hX, hs1, hs2, hθ, hb⟩ := h
  set l : ℝ := (2 * t) ^ (s - 1) with hldef
  have h2t : 1 ≤ 2 * t := by linarith
  have h2t0 : 0 < 2 * t := by linarith
  have hl1 : 1 ≤ l := Real.one_le_rpow h2t (by linarith)
  have hl0 : 0 ≤ l := zero_le_one.trans hl1
  have hp2 := two_le_div_sub_one hs1 hs2
  have hlp : l ^ (s / (s - 1)) = (2 * t) ^ s := by
    rw [hldef, ← Real.rpow_mul h2t0.le]
    congr 1
    have : s - 1 ≠ 0 := by linarith
    field_simp
  have hmax : max (l ^ 2) (|l| ^ (s / (s - 1))) = (2 * t) ^ s := by
    rw [abs_of_nonneg hl0, hlp]
    refine max_eq_right ?_
    rw [← hlp, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hl1 hp2
  have hl4 : l * (4 * t) = 2 * (2 * t) ^ s := by
    rw [hldef, Real.rpow_sub_one h2t0.ne']
    field_simp
    ring
  obtain ⟨hi, hle⟩ := hb l
  have hch := measure_ge_le_exp_mul_mgf (X := fun ω => θ⁻¹ * X ω) (μ := P) (4 * t) hl0 hi
  calc P.real {ω | 4 * t ≤ θ⁻¹ * X ω}
      ≤ Real.exp (-l * (4 * t)) * mgf (fun ω => θ⁻¹ * X ω) P l := hch
    _ ≤ Real.exp (-l * (4 * t)) * Real.exp ((2 * t) ^ s) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [← hmax]
        exact hle
    _ = Real.exp (-((2 * t) ^ s)) := by
        rw [← Real.exp_add, neg_mul, hl4]
        ring_nf

/-- **From a centered bound to a stochastic bound**, Lemma A.9, first part:
`X = 𝒪_s(θ)` implies `|X| ≤ O_s(8^{1/s} · 4θ)`. -/
theorem CenteredOsBound.osBound_abs [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : CenteredOsBound P X s θ) :
    OsBound P (fun ω => |X ω|) s ((8 : ℝ) ^ s⁻¹ * (4 * θ)) := by
  have hs1 : 1 < s := h.2.1
  have hθ : 0 < θ := h.2.2.2.1
  refine osBound_of_tail (X := fun ω => |X ω|) (continuous_abs.measurable.comp h.1)
    (by linarith) le_rfl
    (by positivity) (fun t ht => ?_)
  have hsub : {ω | t * (4 * θ) ≤ |X ω|} ⊆
      {ω | 4 * t ≤ θ⁻¹ * X ω} ∪ {ω | 4 * t ≤ θ⁻¹ * -X ω} := by
    intro ω hω
    have hω' : t * (4 * θ) ≤ |X ω| := hω
    have key : 4 * t ≤ θ⁻¹ * |X ω| := by
      rw [le_inv_mul_iff₀ hθ]
      linarith [hω']
    rcases abs_cases (X ω) with ⟨hxa, -⟩ | ⟨hxa, -⟩
    · left
      simpa [hxa] using key
    · right
      simpa [hxa] using key
  have h1 := h.measureReal_ge_le ht
  have h2 := h.neg.measureReal_ge_le ht
  have hfin : P {ω | t * (4 * θ) ≤ |X ω|} ≠ ⊤ := measure_ne_top _ _
  show P {ω | t * (4 * θ) ≤ |X ω|} ≤ _
  rw [← ofReal_measureReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs0 : 0 < s := by linarith
  have htpos : 0 < t := by linarith
  have hts : 1 ≤ t ^ s := Real.one_le_rpow ht hs0.le
  have h2s : 2 ≤ (2 : ℝ) ^ s := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1.le
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  have hmul : (2 * t) ^ s = 2 ^ s * t ^ s := Real.mul_rpow (by norm_num) htpos.le
  calc P.real {ω | t * (4 * θ) ≤ |X ω|}
      ≤ P.real ({ω | 4 * t ≤ θ⁻¹ * X ω} ∪ {ω | 4 * t ≤ θ⁻¹ * -X ω}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | 4 * t ≤ θ⁻¹ * X ω} + P.real {ω | 4 * t ≤ θ⁻¹ * -X ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-((2 * t) ^ s)) + Real.exp (-((2 * t) ^ s)) := add_le_add h1 h2
    _ = Real.exp (Real.log 2 - (2 * t) ^ s) := by
        rw [Real.exp_sub, Real.exp_log two_pos, Real.exp_neg]
        ring
    _ ≤ Real.exp (-(t ^ s)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hmul]
        nlinarith

/-- **From a stochastic bound to a centered bound**, Lemma A.9, second part: for
`s ∈ (1, 2]` there is `C(s)` such that every measurable mean-zero `X` with `|X| ≤ O_s(θ)`
satisfies `X = 𝒪_s(C θ)`. The moment generating function is bounded by the one-variable
estimates of CoarseGraining: quadratically for small parameters (mean zero) and by
`2 exp(C (K t)^{s/(s-1)})` for large ones. -/
theorem exists_centeredOsBound_of_osBound_abs {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → ℝ) (θ : ℝ), Measurable X → OsBound P (fun ω => |X ω|) s θ →
        ∫ ω, X ω ∂P = 0 → CenteredOsBound P X s (C * θ) := by
  have hs0 : 0 < s := by linarith
  set p : ℝ := s / (s - 1) with hpdef
  have hp2 : 2 ≤ p := two_le_div_sub_one hs1 hs2
  have hp0 : 0 < p := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set k₀ : ℝ := (1 + Real.log 2) ^ s⁻¹ with hk₀def
  have hk₀ : 0 < k₀ := Real.rpow_pos_of_pos (by linarith) _
  set m₀ : ℝ := _root_.Homogenization.IndependentSums.gammaMomentConst s * k₀ with hm₀def
  have hm₀ : 0 < m₀ :=
    mul_pos (_root_.Homogenization.IndependentSums.gammaMomentConst_pos hs0) hk₀
  set Cg : ℝ := _root_.Homogenization.IndependentSums.gammaSigmaLargeMgfConst s with hCgdef
  have hCg : 0 < Cg := _root_.Homogenization.IndependentSums.gammaSigmaLargeMgfConst_pos hs1
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set c : ℝ := max (max (Real.sqrt 2 * Real.exp 1 * m₀) ((2 * Cg) ^ p⁻¹ * k₀))
    (4 * Real.exp 1 * m₀) with hcdef
  have hc4 : 4 * Real.exp 1 * m₀ ≤ c := le_max_right _ _
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc4
  have hc1 : Real.sqrt 2 * Real.exp 1 * m₀ ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hc2 : (2 * Cg) ^ p⁻¹ * k₀ ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hc1' : 2 * (Real.exp 1 * m₀) ^ 2 ≤ c ^ 2 := by
    have hsq : (Real.sqrt 2 * Real.exp 1 * m₀) ^ 2 = 2 * (Real.exp 1 * m₀) ^ 2 := by
      rw [mul_assoc, mul_pow, Real.sq_sqrt two_pos.le]
    rw [← hsq]
    exact pow_le_pow_left₀ (by positivity) hc1 2
  have hq : Cg * (k₀ / c) ^ p ≤ 1 / 2 := by
    have h2C : 0 < (2 * Cg) ^ p⁻¹ := Real.rpow_pos_of_pos (by positivity) _
    have h1 : k₀ / c ≤ ((2 * Cg) ^ p⁻¹)⁻¹ := by
      rw [div_le_iff₀ hc0, ← div_eq_inv_mul, le_div_iff₀ h2C, mul_comm]
      exact hc2
    have h2 : (k₀ / c) ^ p ≤ (2 * Cg)⁻¹ := by
      calc (k₀ / c) ^ p ≤ (((2 * Cg) ^ p⁻¹)⁻¹) ^ p :=
            Real.rpow_le_rpow (div_nonneg hk₀.le hc0.le) h1 hp0.le
        _ = (2 * Cg)⁻¹ := by
            rw [Real.inv_rpow h2C.le, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hp0.ne',
              Real.rpow_one]
    calc Cg * (k₀ / c) ^ p ≤ Cg * (2 * Cg)⁻¹ := mul_le_mul_of_nonneg_left h2 hCg.le
      _ = 1 / 2 := by field_simp
  refine ⟨c, hc0, ?_⟩
  intro Ω _ P _ X θ hX hOs hmean
  have hθ : 0 < θ := hOs.2.2.1
  have hK : 0 < k₀ * θ := mul_pos hk₀ hθ
  have key : ∀ Y : Ω → ℝ, Measurable Y → ∫ ω, Y ω ∂P = 0 →
      _root_.Homogenization.IndependentSums.IsBigO P
        (_root_.Homogenization.IndependentSums.gammaSigma s) Y (k₀ * θ) →
      ∀ t : ℝ, 0 ≤ t → Integrable (fun ω => Real.exp (t * ((c * θ)⁻¹ * Y ω))) P ∧
        ∫ ω, Real.exp (t * ((c * θ)⁻¹ * Y ω)) ∂P ≤ Real.exp (max (t ^ 2) (|t| ^ p)) := by
    intro Y hY hYmean hBY t ht
    set l : ℝ := t * (c * θ)⁻¹ with hldef
    have hl : 0 ≤ l := mul_nonneg ht (inv_nonneg.mpr (mul_pos hc0 hθ).le)
    have hfun : (fun ω => Real.exp (t * ((c * θ)⁻¹ * Y ω))) = fun ω => Real.exp (l * Y ω) := by
      funext ω
      rw [hldef, mul_assoc]
    rw [hfun]
    refine ⟨_root_.Homogenization.IndependentSums.integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
      hY.aemeasurable hs1 hK hl hBY, ?_⟩
    change mgf Y P l ≤ _
    set M : ℝ := _root_.Homogenization.IndependentSums.gammaMomentConst s * (k₀ * θ) with hMdef
    have hMm : M = m₀ * θ := by
      rw [hMdef, hm₀def]
      ring
    have hM : 0 < M := by
      rw [hMm]
      positivity
    have hmom := _root_.Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      hs0 hK hY.aemeasurable hBY
    rcases le_or_gt l (2 * Real.exp 1 * M)⁻¹ with hsmall | hlarge
    · have h := _root_.Homogenization.IndependentSums.mgf_le_exp_two_mul_sq_of_gammaMomentGrowth_small_of_integral_eq_zero
        hY.aemeasurable hs1.le hM.le hl hsmall hYmean hmom
      refine h.trans (Real.exp_le_exp.mpr (le_trans ?_ (le_max_left _ _)))
      have hel : Real.exp 1 * M * l = Real.exp 1 * m₀ * t / c := by
        rw [hMm, hldef]
        field_simp
      have he2 : 2 * (Real.exp 1 * m₀ * t / c) ^ 2 = (2 * (Real.exp 1 * m₀) ^ 2) * t ^ 2 / c ^ 2 := by
        ring
      rw [hel, he2, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hc1' (sq_nonneg t)]
    · have h := _root_.Homogenization.IndependentSums.mgf_le_two_mul_exp_of_isBigO_gammaSigma_of_one_lt
        hY.aemeasurable hs1 hK hl hBY
      have h1 : 1 < 2 * Real.exp 1 * M * l := by
        have := mul_lt_mul_of_pos_left hlarge (show (0 : ℝ) < 2 * Real.exp 1 * M by positivity)
        rwa [mul_inv_cancel₀ (by positivity)] at this
      have h2 : 2 * Real.exp 1 * M * l = 2 * Real.exp 1 * m₀ * t / c := by
        rw [hMm, hldef]
        field_simp
      rw [h2, lt_div_iff₀ hc0, one_mul] at h1
      have ht2 : 2 < t := by nlinarith [mul_pos he hm₀]
      have hKl : k₀ * θ * l = k₀ / c * t := by
        rw [hldef]
        field_simp
      have hconj : _root_.Homogenization.IndependentSums.gammaExpConjExponent s = p := rfl
      rw [hKl, hconj, Real.mul_rpow (div_nonneg hk₀.le hc0.le) ht] at h
      have htp : 2 ≤ t ^ p := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ t by linarith)
          (show (1 : ℝ) ≤ p by linarith)
        rw [Real.rpow_one] at this
        linarith
      have hlog : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
        linarith
      refine h.trans ?_
      rw [abs_of_nonneg ht]
      calc 2 * Real.exp (Cg * ((k₀ / c) ^ p * t ^ p))
          = Real.exp (Real.log 2 + Cg * (k₀ / c) ^ p * t ^ p) := by
            rw [Real.exp_add, Real.exp_log two_pos, mul_assoc]
        _ ≤ Real.exp (max (t ^ 2) (t ^ p)) := by
            refine Real.exp_le_exp.mpr ?_
            have := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg ht p)
            linarith [le_max_right (t ^ 2) (t ^ p)]
  have hOG := (osBound_iff_ogammaLE.1 hOs).2.2.2
  have hBabs := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE hs0 hθ
    (fun ω => abs_nonneg (X ω)) hOG
  have hBX : _root_.Homogenization.IndependentSums.IsBigO P
      (_root_.Homogenization.IndependentSums.gammaSigma s) X (k₀ * θ) := by
    unfold _root_.Homogenization.IndependentSums.IsBigO at hBabs ⊢
    simpa only [abs_abs] using hBabs
  have hBnX : _root_.Homogenization.IndependentSums.IsBigO P
      (_root_.Homogenization.IndependentSums.gammaSigma s) (fun ω => -X ω) (k₀ * θ) := by
    unfold _root_.Homogenization.IndependentSums.IsBigO at hBabs ⊢
    simpa only [abs_abs, abs_neg] using hBabs
  refine ⟨hX, hs1, hs2, mul_pos hc0 hθ, fun t => ?_⟩
  rcases le_total 0 t with ht | ht
  · exact key X hX hmean hBX t ht
  · have hneg := key (fun ω => -X ω) hX.neg (by rw [integral_neg, hmean, neg_zero]) hBnX (-t)
      (by linarith)
    have e : ∀ ω, -t * ((c * θ)⁻¹ * -X ω) = t * ((c * θ)⁻¹ * X ω) := fun ω => by ring
    simp only [e, neg_sq, abs_neg] at hneg
    exact hneg

end CenteredBounds

/-! ## Finite range of dependence: Lemmas A.10 and A.12 -/

section FiniteRange

theorem abs_apply_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem measurableSet_biInter_finset {Ω : Type*} {m : MeasurableSpace Ω} {ι : Type*}
    (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, MeasurableSet[m] (f i)) :
    MeasurableSet[m] (⋂ i ∈ s, f i) :=
  Finset.measurableSet_biInter s hf

/-- **Triangle inequality for centered bounds**, without independence:
`X + Y = 𝒪_s(θ₁ + θ₂)`. The proof is the convexity of `exp`. -/
theorem CenteredOsBound.add {X Y : Ω → ℝ} {s θ₁ θ₂ : ℝ} (hX : CenteredOsBound P X s θ₁)
    (hY : CenteredOsBound P Y s θ₂) : CenteredOsBound P (fun ω => X ω + Y ω) s (θ₁ + θ₂) := by
  obtain ⟨hXm, hs1, hs2, hθ₁, hXb⟩ := hX
  obtain ⟨hYm, -, -, hθ₂, hYb⟩ := hY
  have hθ : 0 < θ₁ + θ₂ := add_pos hθ₁ hθ₂
  refine ⟨hXm.add hYm, hs1, hs2, hθ, fun t => ?_⟩
  set a : ℝ := θ₁ / (θ₁ + θ₂) with hadef
  set b : ℝ := θ₂ / (θ₁ + θ₂) with hbdef
  have ha : 0 ≤ a := div_nonneg hθ₁.le hθ.le
  have hb : 0 ≤ b := div_nonneg hθ₂.le hθ.le
  have hab : a + b = 1 := by
    rw [hadef, hbdef, ← add_div, div_self hθ.ne']
  have hpt : ∀ ω, Real.exp (t * ((θ₁ + θ₂)⁻¹ * (X ω + Y ω))) ≤
      a * Real.exp (t * (θ₁⁻¹ * X ω)) + b * Real.exp (t * (θ₂⁻¹ * Y ω)) := by
    intro ω
    have e : t * ((θ₁ + θ₂)⁻¹ * (X ω + Y ω)) =
        a * (t * (θ₁⁻¹ * X ω)) + b * (t * (θ₂⁻¹ * Y ω)) := by
      rw [hadef, hbdef]
      field_simp
    rw [e]
    exact convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  obtain ⟨hXi, hXle⟩ := hXb t
  obtain ⟨hYi, hYle⟩ := hYb t
  have hbi : Integrable (fun ω =>
      a * Real.exp (t * (θ₁⁻¹ * X ω)) + b * Real.exp (t * (θ₂⁻¹ * Y ω))) P :=
    (hXi.const_mul a).add (hYi.const_mul b)
  have hmeas : Measurable (fun ω => Real.exp (t * ((θ₁ + θ₂)⁻¹ * (X ω + Y ω)))) :=
    (measurable_const.mul (measurable_const.mul (hXm.add hYm))).exp
  have hint : Integrable (fun ω => Real.exp (t * ((θ₁ + θ₂)⁻¹ * (X ω + Y ω)))) P :=
    Integrable.mono' hbi hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, Real.exp (t * ((θ₁ + θ₂)⁻¹ * (X ω + Y ω))) ∂P
      ≤ ∫ ω, (a * Real.exp (t * (θ₁⁻¹ * X ω)) + b * Real.exp (t * (θ₂⁻¹ * Y ω))) ∂P :=
        integral_mono hint hbi hpt
    _ = a * ∫ ω, Real.exp (t * (θ₁⁻¹ * X ω)) ∂P + b * ∫ ω, Real.exp (t * (θ₂⁻¹ * Y ω)) ∂P := by
        rw [integral_add (hXi.const_mul a) (hYi.const_mul b), integral_const_mul,
          integral_const_mul]
    _ ≤ a * Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) +
          b * Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) := by
        gcongr
    _ = Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) := by
        rw [← add_mul, hab, one_mul]

/-- **Triangle inequality for finite sums of centered bounds**, without independence. -/
theorem centeredOsBound_finset_sum_le {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    {X : ι → Ω → ℝ} {s : ℝ} {θ : ι → ℝ} (hX : ∀ i ∈ I, CenteredOsBound P (X i) s (θ i)) :
    CenteredOsBound P (fun ω => ∑ i ∈ I, X i ω) s (∑ i ∈ I, θ i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact absurd hI Finset.not_nonempty_empty
  | @insert i I hi ih =>
    by_cases hne : I.Nonempty
    · have h := (hX i (Finset.mem_insert_self _ _)).add
        (ih hne fun k hk => hX k (Finset.mem_insert_of_mem hk))
      simpa only [Finset.sum_insert hi] using h
    · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst he
      simpa using hX i (Finset.mem_insert_self _ _)

/-- Two sets of `ℝ^d` at Euclidean distance larger than one. -/
def SeparatedByUnit {d : ℕ} (U W : Set (Vec d)) : Prop :=
  ∃ t : ℝ, 1 < t ∧ ∀ x ∈ U, ∀ y ∈ W, t ≤ euclideanNorm (x - y)

/-- A family of local σ-algebras with a unit range of dependence: the σ-algebras of measurable
sets at distance larger than one are independent. For the local σ-algebras `F(U)` of (0.9) this
is the unit range of dependence (0.11). -/
def HasUnitRange {d : ℕ} (P : Measure Ω) (F : Set (Vec d) → MeasurableSpace Ω) : Prop :=
  ∀ U W : Set (Vec d), MeasurableSet U → MeasurableSet W → SeparatedByUnit U W →
    Indep (F U) (F W) P

theorem separatedByUnit_biUnion {d : ℕ} {ι : Type*} (s : Finset ι) {U : Set (Vec d)}
    {W : ι → Set (Vec d)} (h : ∀ j ∈ s, SeparatedByUnit U (W j)) :
    SeparatedByUnit U (⋃ j ∈ s, W j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨2, one_lt_two, fun x _ y hy => by simp at hy⟩
  | @insert j s hj ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := h j (Finset.mem_insert_self _ _)
    obtain ⟨t₂, ht₂, h₂⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    refine ⟨min t₁ t₂, lt_min ht₁ ht₂, fun x hx y hy => ?_⟩
    rw [Finset.set_biUnion_insert] at hy
    rcases hy with hy | hy
    · exact (min_le_left _ _).trans (h₁ x hx y hy)
    · exact (min_le_right _ _).trans (h₂ x hx y hy)

/-- **Mutual independence** of the local σ-algebras of pairwise separated measurable sets. -/
theorem iIndep_of_separated [IsProbabilityMeasure P] {d : ℕ} {F : Set (Vec d) → MeasurableSpace Ω}
    (hF : HasUnitRange P F) (hmono : Monotone F) {ι : Type*} {U : ι → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i)) (hsep : Pairwise fun i j => SeparatedByUnit (U i) (U j)) :
    iIndep (fun i => F (U i)) P := by
  classical
  rw [iIndep_iff]
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | @insert i s hi ih =>
    intro f hf
    rw [Finset.set_biInter_insert, Finset.prod_insert hi]
    have hsepU : SeparatedByUnit (U i) (⋃ j ∈ s, U j) :=
      separatedByUnit_biUnion s fun j hj => hsep (fun hij => hi (hij ▸ hj))
    have hind := hF (U i) (⋃ j ∈ s, U j) (hU i) (Finset.measurableSet_biUnion s fun j _ => hU j)
      hsepU
    have hB : MeasurableSet[F (⋃ j ∈ s, U j)] (⋂ j ∈ s, f j) :=
      measurableSet_biInter_finset s fun j hj =>
        hmono (Set.subset_biUnion_of_mem (u := U) hj) _ (hf j (Finset.mem_insert_of_mem hj))
    rw [(Indep_iff _ _ P).1 hind _ _ (hf i (Finset.mem_insert_self _ _)) hB,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- Random variables measurable for the local σ-algebras of pairwise separated sets are
independent. -/
theorem iIndepFun_of_separated [IsProbabilityMeasure P] {d : ℕ}
    {F : Set (Vec d) → MeasurableSpace Ω} (hF : HasUnitRange P F) (hmono : Monotone F)
    {ι : Type*} {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => SeparatedByUnit (U i) (U j)) {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable[F (U i)] (X i)) : iIndepFun X P := by
  rw [iIndepFun_iff_iIndep]
  exact iIndep_of_iIndep_of_le (iIndep_of_separated hF hmono hU hsep) fun i => (hX i).comap_le

theorem sum_sqrt_le_sqrt_card_mul {κ : Type*} (T : Finset κ) (S : κ → ℝ) (hS : ∀ k, 0 ≤ S k) :
    ∑ k ∈ T, Real.sqrt (S k) ≤ Real.sqrt (T.card) * Real.sqrt (∑ k ∈ T, S k) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) fun k => Real.sqrt (S k)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc (∑ k ∈ T, Real.sqrt (S k)) ^ 2 ≤ (T.card : ℝ) * ∑ k ∈ T, Real.sqrt (S k) ^ 2 := hcs
    _ = (T.card : ℝ) * ∑ k ∈ T, S k := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hS k)

/-- **Sums over a separated colouring.** If the summands of each colour class are measurable for
the local σ-algebras of pairwise separated sets, then a sum of centered bounds `𝒪_s(θᵢ)` is
`𝒪_s((2N)^{1/2} (∑ θᵢ²)^{1/2})`, where `N` is the number of colours. -/
theorem centeredOsBound_sum_of_colouring [IsProbabilityMeasure P] {d : ℕ}
    {F : Set (Vec d) → MeasurableSpace Ω} (hF : HasUnitRange P F) (hmono : Monotone F)
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (c : ι → κ)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → c i = c j → SeparatedByUnit (U i) (U j))
    {X : ι → Ω → ℝ} {s : ℝ} {θ : ι → ℝ} (hXloc : ∀ i, Measurable[F (U i)] (X i))
    (hX : ∀ i, CenteredOsBound P (X i) s (θ i)) :
    CenteredOsBound P (fun ω => ∑ i, X i ω) s
      (Real.sqrt (2 * Fintype.card κ) * Real.sqrt (∑ i, θ i ^ 2)) := by
  classical
  set T : Finset κ := Finset.univ.image c with hTdef
  set S : κ → Finset ι := fun k => Finset.univ.filter fun i => c i = k with hSdef
  have hSne : ∀ k ∈ T, (S k).Nonempty := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨i, by simp [hSdef]⟩
  have hTne : T.Nonempty := Finset.univ_nonempty.image c
  have hθ : ∀ i, 0 < θ i := fun i => (hX i).2.2.2.1
  -- each colour class
  have hclass : ∀ k ∈ T, CenteredOsBound P (fun ω => ∑ i ∈ S k, X i ω) s
      (Real.sqrt 2 * Real.sqrt (∑ i ∈ S k, θ i ^ 2)) := by
    intro k hk
    have : Nonempty (S k) := (hSne k hk).coe_sort
    have hind : iIndepFun (fun i : S k => X i) P := by
      refine iIndepFun_of_separated hF hmono (U := fun i : S k => U i) (fun i => hU i) ?_
        (fun i => hXloc i)
      intro i j hij
      have hci : c i = k := (Finset.mem_filter.mp i.2).2
      have hcj : c j = k := (Finset.mem_filter.mp j.2).2
      exact hsep i j (fun h => hij (Subtype.ext h)) (hci.trans hcj.symm)
    have h := centeredOsBound_sum hind fun i : S k => hX i
    have e : (fun ω => ∑ i : S k, X i ω) = fun ω => ∑ i ∈ S k, X i ω :=
      funext fun ω => Finset.sum_coe_sort (S k) (fun i => X i ω)
    rw [e, Finset.sum_coe_sort (S k) (fun i => θ i ^ 2)] at h
    exact h
  have hsum := centeredOsBound_finset_sum_le T hTne hclass
  have hfib : ∀ ω, ∑ k ∈ T, ∑ i ∈ S k, X i ω = ∑ i, X i ω := fun ω =>
    Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i)) _
  have hfibθ : ∑ k ∈ T, ∑ i ∈ S k, θ i ^ 2 = ∑ i, θ i ^ 2 :=
    Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i)) _
  simp only [hfib] at hsum
  refine hsum.mono_scale ?_
  rw [← Finset.mul_sum]
  have hcs := sum_sqrt_le_sqrt_card_mul T (fun k => ∑ i ∈ S k, θ i ^ 2)
    (fun k => Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hfibθ] at hcs
  have hcard : (T.card : ℝ) ≤ Fintype.card κ := by exact_mod_cast Finset.card_le_univ T
  calc Real.sqrt 2 * ∑ k ∈ T, Real.sqrt (∑ i ∈ S k, θ i ^ 2)
      ≤ Real.sqrt 2 * (Real.sqrt (T.card) * Real.sqrt (∑ i, θ i ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * (Real.sqrt (Fintype.card κ) * Real.sqrt (∑ i, θ i ^ 2)) := by
        gcongr
    _ = Real.sqrt (2 * Fintype.card κ) * Real.sqrt (∑ i, θ i ^ 2) := by
        rw [Real.sqrt_mul two_pos.le, mul_assoc]

/-- The residue of a lattice point modulo `4`. -/
def latticeResidue {d : ℕ} (k : Fin d → ℤ) : Fin d → ZMod 4 := fun i => (k i : ZMod 4)

/-- Open sets contained in the cubes of half-width `L ≥ 1` around the points `L k` of distinct
lattice indices with the same residue modulo `4` are at distance at least `2L`. -/
theorem separatedByUnit_of_latticeResidue {d : ℕ} {L : ℝ} (hL : 1 ≤ L) {k k' : Fin d → ℤ}
    (hkk : k ≠ k') (hres : latticeResidue k = latticeResidue k') {U W : Set (Vec d)}
    (hU : ∀ x ∈ U, ∀ i, |x i - L * k i| < L) (hW : ∀ y ∈ W, ∀ i, |y i - L * k' i| < L) :
    SeparatedByUnit U W := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := Function.ne_iff.mp hkk
  have hdvd : (4 : ℤ) ∣ k i - k' i := by
    have := congrFun hres i
    simp only [latticeResidue] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this.symm
  have h4 : (4 : ℤ) ≤ |k i - k' i| := by
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hi (by linarith)
    rw [hm, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 4)]
    have : 1 ≤ |m| := Int.one_le_abs hm0
    linarith
  have h4' : (4 : ℝ) ≤ |(k i : ℝ) - k' i| := by
    have := (Int.cast_le (R := ℝ)).mpr h4
    push_cast at this
    exact this
  refine ⟨2 * L, by linarith, fun x hx y hy => ?_⟩
  have h1 := hU x hx i
  have h2 := hW y hy i
  have hL0 : 0 ≤ L := by linarith
  have hdist : L * |(k i : ℝ) - k' i| ≤ |x i - y i| + |x i - L * k i| + |y i - L * k' i| := by
    rw [← abs_of_nonneg hL0, ← abs_mul, abs_of_nonneg hL0]
    calc |L * ((k i : ℝ) - k' i)| = |(L * k i - x i) + (x i - y i) + (y i - L * k' i)| := by
          ring_nf
      _ ≤ |L * k i - x i| + |x i - y i| + |y i - L * k' i| := abs_add_three _ _ _
      _ = |x i - y i| + |x i - L * k i| + |y i - L * k' i| := by
          rw [abs_sub_comm (L * k i) (x i)]
          ring
  have hcoord := abs_apply_le_euclideanNorm (x - y) i
  simp only [Pi.sub_apply] at hcoord
  nlinarith

/-- **Lemma A.12.** Let `L ≥ 1` and let `I` be a finite nonempty set of lattice indices. If,
for each `k ∈ I`, `X k = 𝒪_s(θ k)` is measurable for the local σ-algebra of a measurable set
contained in the open cube of half-width `L` around `L k`, then
`∑_{k ∈ I} X k = 𝒪_s((2 · 4^d)^{1/2} (∑ θ_k²)^{1/2})`. -/
theorem centeredOsBound_lattice_sum [IsProbabilityMeasure P] {d : ℕ}
    {F : Set (Vec d) → MeasurableSpace Ω} (hF : HasUnitRange P F) (hmono : Monotone F)
    {L : ℝ} (hL : 1 ≤ L) (I : Finset (Fin d → ℤ)) (hI : I.Nonempty)
    {U : (Fin d → ℤ) → Set (Vec d)} (hU : ∀ k, MeasurableSet (U k))
    (hUc : ∀ k ∈ I, ∀ x ∈ U k, ∀ i, |x i - L * k i| < L)
    {X : (Fin d → ℤ) → Ω → ℝ} {s : ℝ} {θ : (Fin d → ℤ) → ℝ}
    (hXloc : ∀ k ∈ I, Measurable[F (U k)] (X k)) (hX : ∀ k ∈ I, CenteredOsBound P (X k) s (θ k)) :
    CenteredOsBound P (fun ω => ∑ k ∈ I, X k ω) s
      (Real.sqrt (2 * 4 ^ d) * Real.sqrt (∑ k ∈ I, θ k ^ 2)) := by
  classical
  have : Nonempty I := hI.coe_sort
  have h := centeredOsBound_sum_of_colouring hF hmono (ι := I) (κ := Fin d → ZMod 4)
    (fun k => latticeResidue k.1) (U := fun k => U k.1) (fun k => hU k.1)
    (fun k k' hkk hres => separatedByUnit_of_latticeResidue hL (fun h => hkk (Subtype.ext h))
      hres (hUc k.1 k.2) (hUc k'.1 k'.2))
    (X := fun k => X k.1) (θ := fun k => θ k.1) (fun k => hXloc k.1 k.2) (fun k => hX k.1 k.2)
  have hcard : (Fintype.card (Fin d → ZMod 4) : ℝ) = 4 ^ d := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  have e : (fun ω => ∑ k : I, X k ω) = fun ω => ∑ k ∈ I, X k ω :=
    funext fun ω => Finset.sum_coe_sort I (fun k => X k ω)
  rw [hcard, e, Finset.sum_coe_sort I (fun k => θ k ^ 2)] at h
  exact h

/-- **Averages of centered bounds**, Lemma A.10 with a constant scale: if `X x = 𝒪_s(θ)` for
every point `x` of a finite measure space `(E, μ)` with `μ ≠ 0`, and `(x, ω) ↦ X x ω` is
measurable, then `∫ X x dμ(x) = 𝒪_s(μ(E) θ)`. -/
theorem centeredOsBound_integral [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] (hμ : μ ≠ 0) {X : E → Ω → ℝ} {s θ : ℝ}
    (hXm : Measurable (Function.uncurry X)) (hX : ∀ x, CenteredOsBound P (X x) s θ) :
    CenteredOsBound P (fun ω => ∫ x, X x ω ∂μ) s (μ.real Set.univ * θ) := by
  have : NeZero μ := ⟨hμ⟩
  obtain ⟨x₀⟩ : Nonempty E := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hμ (Measure.eq_zero_of_isEmpty μ)
  obtain ⟨-, hs1, hs2, hθ, -⟩ := hX x₀
  have hm : 0 < μ.real Set.univ := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨Measure.measure_univ_pos.mpr hμ, measure_lt_top _ _⟩
  set m : ℝ := μ.real Set.univ with hmdef
  have hmeasF : ∀ u : ℝ,
      Measurable (Function.uncurry fun x ω => Real.exp (u * (θ⁻¹ * X x ω))) :=
    fun u => (measurable_const.mul (measurable_const.mul hXm)).exp
  have hprod : ∀ u : ℝ, Integrable (Function.uncurry fun x ω => Real.exp (u * (θ⁻¹ * X x ω)))
      (μ.prod P) := by
    intro u
    refine ⟨(hmeasF u).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (f := Function.uncurry fun x ω => Real.exp (u * (θ⁻¹ * X x ω)))
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      lintegral_prod _ (hmeasF u).ennreal_ofReal.aemeasurable]
    calc ∫⁻ x, ∫⁻ ω, ENNReal.ofReal
          (Function.uncurry (fun x ω => Real.exp (u * (θ⁻¹ * X x ω))) (x, ω)) ∂P ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (max (u ^ 2) (|u| ^ (s / (s - 1))))) ∂μ := by
          refine lintegral_mono fun x => ?_
          obtain ⟨hi, hle⟩ := (hX x).2.2.2.2 u
          simp only [Function.uncurry_apply_pair]
          rw [← ofReal_integral_eq_lintegral_ofReal hi
            (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
          exact ENNReal.ofReal_le_ofReal hle
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hae : ∀ u : ℝ, ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (u * (θ⁻¹ * X x ω))) μ := by
    intro u
    simpa only [Function.uncurry_apply_pair] using (hprod u).prod_left_ae
  have haeX : ∀ᵐ ω ∂P, Integrable (fun x => X x ω) μ := by
    filter_upwards [hae 1, hae (-1)] with ω h1 h2
    have hmeasx : Measurable fun x => X x ω := hXm.comp measurable_prodMk_right
    refine Integrable.mono' ((h1.add h2).const_mul θ) hmeasx.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    have hy : |θ⁻¹ * X x ω| ≤
        Real.exp (1 * (θ⁻¹ * X x ω)) + Real.exp (-1 * (θ⁻¹ * X x ω)) := by
      rw [one_mul, neg_one_mul]
      rcases abs_cases (θ⁻¹ * X x ω) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        linarith [Real.add_one_le_exp (θ⁻¹ * X x ω), Real.exp_pos (-(θ⁻¹ * X x ω))]
      · rw [h]
        linarith [Real.add_one_le_exp (-(θ⁻¹ * X x ω)), Real.exp_pos (θ⁻¹ * X x ω)]
    have he : |X x ω| = θ * |θ⁻¹ * X x ω| := by
      rw [abs_mul, abs_inv, abs_of_pos hθ]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hy hθ.le
  have hIm : Measurable fun ω => ∫ x, X x ω ∂μ :=
    (hXm.stronglyMeasurable.integral_prod_left (μ := μ)).measurable
  refine ⟨hIm, hs1, hs2, mul_pos hm hθ, fun t => ?_⟩
  have hJ : ∀ᵐ ω ∂P, Real.exp (t * ((m * θ)⁻¹ * ∫ x, X x ω ∂μ)) ≤
      m⁻¹ * ∫ x, Real.exp (t * (θ⁻¹ * X x ω)) ∂μ := by
    filter_upwards [haeX, hae t] with ω hXω hEω
    have hJen := ConvexOn.map_average_le (μ := μ) (s := Set.univ) (g := Real.exp)
      (f := fun x => t * (θ⁻¹ * X x ω)) convexOn_exp Real.continuous_exp.continuousOn
      isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      ((hXω.const_mul θ⁻¹).const_mul t) hEω
    rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul, integral_const_mul,
      integral_const_mul] at hJen
    have e : t * ((m * θ)⁻¹ * ∫ x, X x ω ∂μ) = m⁻¹ * (t * (θ⁻¹ * ∫ x, X x ω ∂μ)) := by
      rw [mul_inv]
      ring
    rw [e]
    exact hJen
  have hdom : Integrable (fun ω => m⁻¹ * ∫ x, Real.exp (t * (θ⁻¹ * X x ω)) ∂μ) P := by
    have := (hprod t).integral_prod_right
    simp only [Function.uncurry_apply_pair] at this
    exact this.const_mul _
  have hint : Integrable (fun ω => Real.exp (t * ((m * θ)⁻¹ * ∫ x, X x ω ∂μ))) P :=
    Integrable.mono' hdom (measurable_const.mul (measurable_const.mul hIm)).exp.aestronglyMeasurable
      (by
        filter_upwards [hJ] with ω h
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact h)
  refine ⟨hint, ?_⟩
  have hinner : Integrable (fun x => ∫ ω, Real.exp (t * (θ⁻¹ * X x ω)) ∂P) μ := by
    have := (hprod t).integral_prod_left
    simpa only [Function.uncurry_apply_pair] using this
  calc ∫ ω, Real.exp (t * ((m * θ)⁻¹ * ∫ x, X x ω ∂μ)) ∂P
      ≤ ∫ ω, m⁻¹ * ∫ x, Real.exp (t * (θ⁻¹ * X x ω)) ∂μ ∂P := integral_mono_ae hint hdom hJ
    _ = m⁻¹ * ∫ x, ∫ ω, Real.exp (t * (θ⁻¹ * X x ω)) ∂P ∂μ := by
        rw [integral_const_mul, integral_integral_swap (hprod t)]
    _ ≤ m⁻¹ * ∫ _ : E, Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) ∂μ := by
        refine mul_le_mul_of_nonneg_left (integral_mono hinner (integrable_const _)
          fun x => ((hX x).2.2.2.2 t).2) (inv_nonneg.mpr hm.le)
    _ = Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) := by
        rw [integral_const, smul_eq_mul, ← hmdef]
        field_simp

end FiniteRange

/-! ## Further rules for centered stochastic bounds -/

section CenteredRules

/-- Multiplication by a constant of modulus at most one preserves a centered bound. -/
theorem CenteredOsBound.mul_of_abs_le_one {X : Ω → ℝ} {s θ c : ℝ}
    (h : CenteredOsBound P X s θ) (hc : |c| ≤ 1) :
    CenteredOsBound P (fun ω => c * X ω) s θ := by
  obtain ⟨hX, hs1, hs2, hθ, hb⟩ := h
  refine ⟨measurable_const.mul hX, hs1, hs2, hθ, fun t => ?_⟩
  have e : ∀ ω, t * (θ⁻¹ * (c * X ω)) = (t * c) * (θ⁻¹ * X ω) := fun ω => by ring
  simp only [e]
  obtain ⟨hi, hle⟩ := hb (t * c)
  refine ⟨hi, hle.trans (Real.exp_le_exp.mpr (max_sq_rpow_le_of_abs_le hs1 ?_))⟩
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg t) hc

/-- A centered bound transfers to a measurable variable that agrees with it almost everywhere. -/
theorem CenteredOsBound.congr_ae {X Y : Ω → ℝ} {s θ : ℝ} (h : CenteredOsBound P X s θ)
    (hY : Measurable Y) (hXY : X =ᵐ[P] Y) : CenteredOsBound P Y s θ := by
  obtain ⟨-, hs1, hs2, hθ, hb⟩ := h
  refine ⟨hY, hs1, hs2, hθ, fun t => ?_⟩
  have he : (fun ω => Real.exp (t * (θ⁻¹ * X ω))) =ᵐ[P] fun ω => Real.exp (t * (θ⁻¹ * Y ω)) := by
    filter_upwards [hXY] with ω hω
    rw [hω]
  obtain ⟨hi, hle⟩ := hb t
  exact ⟨hi.congr he, (integral_congr_ae he).symm.trans_le hle⟩

/-- **Sums of independent centered bounds with equal scales**: `k` independent variables
`𝒪_s(θ)` have a sum `𝒪_s(√k θ)`. -/
theorem centeredOsBound_sum_of_eq_scale [IsProbabilityMeasure P] {ι : Type*} [Fintype ι]
    [Nonempty ι] {X : ι → Ω → ℝ} {s θ : ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, CenteredOsBound P (X i) s θ) :
    CenteredOsBound P (fun ω => ∑ i, X i ω) s (Real.sqrt (Fintype.card ι) * θ) := by
  obtain ⟨-, hs1, hs2, hθ, -⟩ := hX (Classical.arbitrary ι)
  have hm : ∀ i, Measurable (X i) := fun i => (hX i).1
  set k : ℝ := (Fintype.card ι : ℝ) with hkdef
  have hk1 : 1 ≤ k := by
    rw [hkdef]
    exact_mod_cast Fintype.card_pos
  have hk0 : 0 < k := by linarith
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsk1 : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr hk1
  set Θ : ℝ := Real.sqrt k * θ with hΘdef
  have hΘ : 0 < Θ := mul_pos hsk hθ
  have hp2 := two_le_div_sub_one hs1 hs2
  refine ⟨Finset.measurable_sum _ (fun i _ => hm i), hs1, hs2, hΘ, fun t => ?_⟩
  set u : ℝ := t * Θ⁻¹ with hudef
  set v : ℝ := t / Real.sqrt k with hvdef
  have hcomp : ∀ i ω, u * X i ω = v * (θ⁻¹ * X i ω) := by
    intro i ω
    rw [hudef, hvdef, hΘdef]
    field_simp
  have hint : ∀ i, Integrable (fun ω => Real.exp (u * X i ω)) P := by
    intro i
    simp only [hcomp i]
    exact ((hX i).2.2.2.2 v).1
  have hfun : (fun ω => Real.exp (t * (Θ⁻¹ * ∑ i, X i ω))) =
      fun ω => Real.exp (u * (∑ i, X i) ω) := by
    funext ω
    rw [Finset.sum_apply, hudef, mul_assoc]
  rw [hfun]
  refine ⟨hind.integrable_exp_mul_sum hm (fun i _ => hint i), ?_⟩
  change mgf (∑ i, X i) P u ≤ _
  rw [hind.mgf_sum hm Finset.univ]
  have hmgf : ∀ i, mgf (X i) P u ≤ Real.exp (max (v ^ 2) (|v| ^ (s / (s - 1)))) := by
    intro i
    have := ((hX i).2.2.2.2 v).2
    simp only [← hcomp i] at this
    exact this
  calc ∏ i, mgf (X i) P u
      ≤ ∏ _i : ι, Real.exp (max (v ^ 2) (|v| ^ (s / (s - 1)))) :=
        Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => hmgf i)
    _ = Real.exp (k * max (v ^ 2) (|v| ^ (s / (s - 1)))) := by
        rw [Finset.prod_const, Finset.card_univ, hkdef, Real.exp_nat_mul]
    _ ≤ Real.exp (max (t ^ 2) (|t| ^ (s / (s - 1)))) := by
        refine Real.exp_le_exp.mpr ?_
        rw [mul_max_of_nonneg _ _ hk0.le]
        refine max_le_max ?_ ?_
        · rw [hvdef, div_pow, Real.sq_sqrt hk0.le]
          field_simp
          exact le_rfl
        · have hpow : k ≤ Real.sqrt k ^ (s / (s - 1)) := by
            calc k = Real.sqrt k ^ (2 : ℝ) := by
                  rw [Real.rpow_two, Real.sq_sqrt hk0.le]
              _ ≤ Real.sqrt k ^ (s / (s - 1)) :=
                  Real.rpow_le_rpow_of_exponent_le hsk1 hp2
          have hpos : 0 < Real.sqrt k ^ (s / (s - 1)) := Real.rpow_pos_of_pos hsk _
          rw [hvdef, abs_div, abs_of_pos hsk, Real.div_rpow (abs_nonneg t) hsk.le, mul_div_assoc']
          rw [div_le_iff₀ hpos, mul_comm k]
          exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg t) _)

theorem le_exp_rpow_of_nonneg {x s : ℝ} (hx : 0 ≤ x) (hs : 1 ≤ s) : x ≤ Real.exp (x ^ s) := by
  rcases le_total x 1 with h | h
  · exact h.trans (Real.one_le_exp (Real.rpow_nonneg hx _))
  · calc x ≤ x ^ s := Real.self_le_rpow_of_one_le h hs
      _ ≤ x ^ s + 1 := by linarith
      _ ≤ Real.exp (x ^ s) := Real.add_one_le_exp _

/-- **The mean of a stochastic bound**: a nonnegative `X ≤ O_s(θ)` with `s ≥ 1` is integrable with
`E[X] ≤ 2θ`. -/
theorem OsBound.integrable_and_integral_le {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ)
    (hs : 1 ≤ s) (hX0 : ∀ ω, 0 ≤ X ω) : Integrable X P ∧ ∫ ω, X ω ∂P ≤ 2 * θ := by
  obtain ⟨hX, -, hθ, hb⟩ := h
  have hpt : ∀ ω, ENNReal.ofReal (θ⁻¹ * X ω) ≤
      ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) := by
    intro ω
    rw [max_eq_left (hX0 ω)]
    exact ENNReal.ofReal_le_ofReal
      (le_exp_rpow_of_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) (hX0 ω)) hs)
  have hl : ∫⁻ ω, ENNReal.ofReal (θ⁻¹ * X ω) ∂P ≤ 2 := (lintegral_mono hpt).trans hb
  have hint : Integrable (fun ω => θ⁻¹ * X ω) P := by
    refine ⟨(measurable_const.mul hX).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      mul_nonneg (inv_nonneg.mpr hθ.le) (hX0 ω))]
    exact hl.trans_lt (by norm_num)
  have hX' : Integrable X P := by
    have := hint.const_mul θ
    simpa only [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul] using this
  refine ⟨hX', ?_⟩
  have hle : ∫ ω, θ⁻¹ * X ω ∂P ≤ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      mul_nonneg (inv_nonneg.mpr hθ.le) (hX0 ω)) hint.aestronglyMeasurable]
    have := ENNReal.toReal_mono (by norm_num) hl
    simpa using this
  rw [integral_const_mul] at hle
  have := mul_le_mul_of_nonneg_left hle hθ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul, mul_comm] at this

/-- **Centering a stochastic bound**, Lemma A.9: for `s ∈ (1, 2]` there is `C(s)` such that a
measurable `Z` with `|Z| ≤ O_s(θ)` satisfies `Z - E[Z] = 𝒪_s(C θ)`. -/
theorem exists_centeredOsBound_sub_integral {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Ω → ℝ) (θ : ℝ), Measurable Z → OsBound P (fun ω => |Z ω|) s θ →
        CenteredOsBound P (fun ω => Z ω - ∫ ω', Z ω' ∂P) s (C * θ) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_osBound_abs hs1 hs2
  have hl : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  refine ⟨C₀ * (1 + 2 / Real.log 2 ^ s⁻¹), mul_pos hC₀ (by positivity), ?_⟩
  intro Ω _ P _ Z θ hZ hb
  have hθ : 0 < θ := hb.2.2.1
  obtain ⟨hZi, hZle⟩ := OsBound.integrable_and_integral_le hb hs1.le fun ω => abs_nonneg _
  have hZi' : Integrable Z P :=
    (integrable_norm_iff (Measurable.aestronglyMeasurable hZ)).1
      (by simpa only [Real.norm_eq_abs] using hZi)
  have hmean : |∫ ω', Z ω' ∂P| ≤ 2 * θ :=
    (abs_integral_le_integral_abs).trans hZle
  have hc : OsBound P (fun _ : Ω => 2 * θ) s (2 * θ / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const (by linarith) (by positivity)
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hsum := osBound_add hb hc hs1.le
  have hm : Measurable fun ω => Z ω - ∫ ω', Z ω' ∂P := Measurable.sub hZ measurable_const
  have habs : OsBound P (fun ω => |Z ω - ∫ ω', Z ω' ∂P|) s (θ + 2 * θ / Real.log 2 ^ s⁻¹) :=
    OsBound.of_le hsum (continuous_abs.measurable.comp hm) fun ω => (abs_sub _ _).trans (by linarith)
  have hmean0 : ∫ ω, (Z ω - ∫ ω', Z ω' ∂P) ∂P = 0 := by
    rw [integral_sub hZi' (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  have := h₀ P _ _ hm habs hmean0
  convert this using 1
  field_simp

/-- **Bounded centered variables**: for `s ∈ (1, 2]` there is `C(s)` such that a measurable
mean-zero `Y` with `|Y| ≤ b` satisfies `Y = 𝒪_s(C b)`. -/
theorem exists_centeredOsBound_of_abs_le {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Ω → ℝ) (b : ℝ), Measurable Y → 0 < b → (∀ ω, |Y ω| ≤ b) → ∫ ω, Y ω ∂P = 0 →
        CenteredOsBound P Y s (C * b) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_centeredOsBound_of_osBound_abs hs1 hs2
  have hl : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  refine ⟨C₀ / Real.log 2 ^ s⁻¹, div_pos hC₀ hl, ?_⟩
  intro Ω _ P _ Y b hY hb hYb hY0
  have hc : OsBound P (fun ω => |Y ω|) s (b / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const (continuous_abs.measurable.comp hY) (by linarith) hb (Filter.Eventually.of_forall hYb)
  have := h₀ P Y _ hY hc hY0
  convert this using 1
  ring

/-- **Centered averages of stochastic bounds**, Lemmas A.9 and A.10: for `s ∈ (1, 2]` there is
`C(s)` such that, for a finite measure `μ ≠ 0` and a bounded jointly measurable family `V x` with
`|V x| ≤ O_s(θ)` for every `x`, the centered average `∫ V x dμ - E[∫ V x dμ]` is
`𝒪_s(C μ(E) θ)`. -/
theorem exists_centeredOsBound_integral_sub {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ], μ ≠ 0 →
      ∀ (V : E → Ω → ℝ) (θ B : ℝ), Measurable (Function.uncurry V) → (∀ x ω, |V x ω| ≤ B) →
        (∀ x, OsBound P (fun ω => |V x ω|) s θ) →
        CenteredOsBound P (fun ω => ∫ x, V x ω ∂μ - ∫ ω', ∫ x, V x ω' ∂μ ∂P) s
          (μ.real Set.univ * (C * θ)) := by
  obtain ⟨C, hC, h⟩ := exists_centeredOsBound_sub_integral.{u} hs1 hs2
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ E _ μ _ hμ V θ B hV hVB hVθ
  set m : E → ℝ := fun x => ∫ ω, V x ω ∂P with hmdef
  have hVx : ∀ x, Measurable (V x) := fun x => hV.comp measurable_prodMk_left
  have hVω : ∀ ω, Measurable fun x => V x ω := fun ω => hV.comp measurable_prodMk_right
  have hmm : Measurable m :=
    (hV.stronglyMeasurable.integral_prod_right (ν := P)).measurable
  set W : E → Ω → ℝ := fun x ω => V x ω - m x with hWdef
  have hW : Measurable (Function.uncurry W) :=
    hV.sub (hmm.comp measurable_fst)
  have hWc : ∀ x, CenteredOsBound P (W x) s (C * θ) := fun x => h P (V x) θ (hVx x) (hVθ x)
  have hA := centeredOsBound_integral (μ := μ) hμ hW hWc
  have hint : ∀ ω, Integrable (fun x => V x ω) μ := fun ω =>
    Integrable.of_bound (hVω ω).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hVB x ω)
  have hmint : Integrable m μ :=
    Integrable.of_bound hmm.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |V x ω| ∂P ≤ ∫ _ω, B ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const B) (Filter.Eventually.of_forall fun ω => hVB x ω)
        _ = B := by simp)
  have hprod : Integrable (Function.uncurry fun ω x => V x ω) (P.prod μ) :=
    Integrable.of_bound (hV.comp measurable_swap).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hVB w.2 w.1)
  have hswap : ∫ ω', ∫ x, V x ω' ∂μ ∂P = ∫ x, m x ∂μ := by
    rw [hmdef]
    exact integral_integral_swap hprod
  have heq : (fun ω => ∫ x, W x ω ∂μ) =
      fun ω => ∫ x, V x ω ∂μ - ∫ ω', ∫ x, V x ω' ∂μ ∂P := by
    funext ω
    rw [hswap, hWdef]
    exact integral_sub (hint ω) hmint
  rw [heq] at hA
  refine hA.mono_scale le_rfl

end CenteredRules

/-! ## The statements of the book -/

section BookStatements

/-- **Lemma A.1 (Tail probability)**, first implication: if `X ≤ O_s(θ)`, then
`P[X ≥ θ x] ≤ 2 exp(-x^s)` for every `x ≥ 0`. -/
theorem OsBound.measureReal_ge_le [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P X s θ) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | θ * x ≤ X ω} ≤ 2 * Real.exp (-(x ^ s)) := by
  obtain ⟨-, hs, hθ, h'⟩ := osBound_iff_ogammaLE.1 h
  rw [mul_comm θ x]
  exact SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound P hs hθ h' x hx

/-- **Lemma A.1 (Tail probability)**, second implication: if `P[X ≥ θ x] ≤ exp(-x^s)` for every
`x ≥ 0`, then `X ≤ O_s(2^{1/s} θ)`. -/
theorem osBound_of_measureReal_ge_le [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (hX : Measurable X) (hs : 0 < s) (hθ : 0 < θ)
    (htail : ∀ x : ℝ, 0 ≤ x → P.real {ω | θ * x ≤ X ω} ≤ Real.exp (-(x ^ s))) :
    OsBound P X s ((2 : ℝ) ^ (1 / s) * θ) := by
  refine osBound_iff_ogammaLE.2 ⟨hX, hs, mul_pos (Real.rpow_pos_of_pos two_pos _) hθ, ?_⟩
  refine SubdiffusiveProcess.Paper.app_a_orlicz_tail_converse P hs hθ hX.aemeasurable
    fun x hx => ?_
  rw [mul_comm x θ]
  exact htail x hx

/-- **Lemma A.3 (i)**: if `X` takes values in `[0, 1]`, `X ≤ O_s(θ)` and `s < s'`, then
`X ≤ O_{s'}(θ^{s/s'})`. -/
theorem OsBound.of_mem_Icc {X : Ω → ℝ} {s s' θ : ℝ} (h : OsBound P X s θ)
    (hX0 : ∀ ω, 0 ≤ X ω) (hX1 : ∀ ω, X ω ≤ 1) (hss : s < s') :
    OsBound P X s' (θ ^ (s / s')) := by
  obtain ⟨hX, hs, hθ, hint⟩ := h
  have hs' : 0 < s' := hs.trans hss
  refine ⟨hX, hs', Real.rpow_pos_of_pos hθ _, le_trans (lintegral_mono fun ω => ?_) hint⟩
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  rw [max_eq_left (hX0 ω), Real.mul_rpow (inv_nonneg.2 (Real.rpow_nonneg hθ.le _)) (hX0 ω),
    Real.mul_rpow (inv_nonneg.2 hθ.le) (hX0 ω), Real.inv_rpow (Real.rpow_nonneg hθ.le _),
    ← Real.rpow_mul hθ.le, div_mul_cancel₀ s hs'.ne', Real.inv_rpow hθ.le]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge' (hX0 ω) (hX1 ω) hs.le hss.le)
    (inv_nonneg.2 (Real.rpow_nonneg hθ.le _))

/-- **Lemma A.3 (ii)**: if `0 ≤ X₁ ≤ O_{s₁}(θ₁)` and `0 ≤ X₂ ≤ O_{s₂}(θ₂)`, then
`X₁ X₂ ≤ O_{s₁ s₂/(s₁ + s₂)}(θ₁ θ₂)`. The proof is Young's inequality followed by Hölder's
inequality. -/
theorem OsBound.mul {X₁ X₂ : Ω → ℝ} {s₁ s₂ θ₁ θ₂ : ℝ} (h₁ : OsBound P X₁ s₁ θ₁)
    (h₂ : OsBound P X₂ s₂ θ₂) (hX₁ : ∀ ω, 0 ≤ X₁ ω) (hX₂ : ∀ ω, 0 ≤ X₂ ω) :
    OsBound P (fun ω => X₁ ω * X₂ ω) (s₁ * s₂ / (s₁ + s₂)) (θ₁ * θ₂) := by
  obtain ⟨hm₁, hs₁, hθ₁, hint₁⟩ := h₁
  obtain ⟨hm₂, hs₂, hθ₂, hint₂⟩ := h₂
  have hs : 0 < s₁ + s₂ := add_pos hs₁ hs₂
  set w₁ : ℝ := s₂ / (s₁ + s₂) with hw₁
  set w₂ : ℝ := s₁ / (s₁ + s₂) with hw₂
  have hw₁0 : 0 ≤ w₁ := div_nonneg hs₂.le hs.le
  have hw₂0 : 0 ≤ w₂ := div_nonneg hs₁.le hs.le
  have hw : w₁ + w₂ = 1 := by
    rw [hw₁, hw₂, ← add_div, add_comm, div_self hs.ne']
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X₁ ω) 0) ^ s₁)) with hf
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (X₂ ω) 0) ^ s₂)) with hg
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (((θ₁ * θ₂)⁻¹ * max (X₁ ω * X₂ ω) 0) ^
      (s₁ * s₂ / (s₁ + s₂)))) ≤ f ω ^ w₁ * g ω ^ w₂ := by
    intro ω
    set a : ℝ := θ₁⁻¹ * X₁ ω with ha
    set b : ℝ := θ₂⁻¹ * X₂ ω with hb
    have ha0 : 0 ≤ a := mul_nonneg (inv_nonneg.2 hθ₁.le) (hX₁ ω)
    have hb0 : 0 ≤ b := mul_nonneg (inv_nonneg.2 hθ₂.le) (hX₂ ω)
    have hab : (θ₁ * θ₂)⁻¹ * max (X₁ ω * X₂ ω) 0 = a * b := by
      rw [max_eq_left (mul_nonneg (hX₁ ω) (hX₂ ω)), ha, hb, mul_inv]
      ring
    have hyoung : (a * b) ^ (s₁ * s₂ / (s₁ + s₂)) ≤ w₁ * a ^ s₁ + w₂ * b ^ s₂ := by
      have h := Real.geom_mean_le_arith_mean2_weighted hw₁0 hw₂0 (Real.rpow_nonneg ha0 s₁)
        (Real.rpow_nonneg hb0 s₂) hw
      rw [← Real.rpow_mul ha0, ← Real.rpow_mul hb0] at h
      have e₁ : s₁ * w₁ = s₁ * s₂ / (s₁ + s₂) := by rw [hw₁]; ring
      have e₂ : s₂ * w₂ = s₁ * s₂ / (s₁ + s₂) := by rw [hw₂]; ring
      rw [e₁, e₂, ← Real.mul_rpow ha0 hb0] at h
      exact h
    rw [hab, hf, hg]
    simp only
    rw [max_eq_left (hX₁ ω), max_eq_left (hX₂ ω), ← ha, ← hb,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hw₁0,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hw₂0,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _),
      ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    linarith [hyoung]
  have hfm : AEMeasurable f P := by
    simp only [hf]
    fun_prop
  have hgm : AEMeasurable g P := by
    simp only [hg]
    fun_prop
  refine ⟨hm₁.mul hm₂, div_pos (mul_pos hs₁ hs₂) hs, mul_pos hθ₁ hθ₂, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (((θ₁ * θ₂)⁻¹ * max (X₁ ω * X₂ ω) 0) ^
        (s₁ * s₂ / (s₁ + s₂)))) ∂P
      ≤ ∫⁻ ω, f ω ^ w₁ * g ω ^ w₂ ∂P := lintegral_mono hpt
    _ ≤ (∫⁻ ω, f ω ∂P) ^ w₁ * (∫⁻ ω, g ω ∂P) ^ w₂ :=
        ENNReal.lintegral_mul_norm_pow_le hfm hgm hw₁0 hw₂0 hw
    _ ≤ 2 ^ w₁ * 2 ^ w₂ := by
        gcongr
    _ = 2 := by
        rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, hw, ENNReal.rpow_one]

/-- **Lemma A.5 (Laplace transform)**, (A.4): for `s > 1` there is `C(s)` such that, if
`X ≤ O_s(1)`, then for every `λ ≥ 1` the variable `exp(λ X)` is integrable and
`log E[exp(λ X)] ≤ C λ^{s/(s-1)}`. The moment generating function of `X₊` is bounded by the
large-parameter estimate of the library CoarseGraining. -/
theorem exists_log_integral_exp_le_of_osBound {s : ℝ} (hs1 : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → ℝ), OsBound P X s 1 → ∀ t : ℝ, 1 ≤ t →
        Integrable (fun ω => Real.exp (t * X ω)) P ∧
          Real.log (∫ ω, Real.exp (t * X ω) ∂P) ≤ C * t ^ (s / (s - 1)) := by
  have hs0 : 0 < s := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K : ℝ := (1 + Real.log 2) ^ s⁻¹ * 1 with hKdef
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (by linarith) _) one_pos
  set Cg : ℝ := _root_.Homogenization.IndependentSums.gammaSigmaLargeMgfConst s with hCgdef
  have hCg : 0 < Cg := _root_.Homogenization.IndependentSums.gammaSigmaLargeMgfConst_pos hs1
  set p : ℝ := s / (s - 1) with hpdef
  have hp0 : 0 ≤ p := div_nonneg hs0.le (by linarith)
  refine ⟨Real.log 2 + Cg * K ^ p, by positivity, ?_⟩
  intro Ω _ P _ X hX t ht
  have ht0 : 0 ≤ t := by linarith
  set Y : Ω → ℝ := fun ω => max (X ω) 0 with hYdef
  have hYm : Measurable Y := hX.1.max measurable_const
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_max_right _ _
  have hYos : OsBound P Y s 1 := by
    obtain ⟨-, hs, hθ, hint⟩ := hX
    refine ⟨hYm, hs, hθ, ?_⟩
    simpa only [hYdef, max_assoc, max_self] using hint
  obtain ⟨-, -, -, hOG⟩ := osBound_iff_ogammaLE.1 hYos
  have hB := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE hs0 one_pos hY0 hOG
  have hYi := _root_.Homogenization.IndependentSums.integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
    hYm.aemeasurable hs1 hK ht0 hB
  have hmgf := _root_.Homogenization.IndependentSums.mgf_le_two_mul_exp_of_isBigO_gammaSigma_of_one_lt
    hYm.aemeasurable hs1 hK ht0 hB
  have hconj : _root_.Homogenization.IndependentSums.gammaExpConjExponent s = p := rfl
  rw [hconj, ← hCgdef] at hmgf
  have hle : ∀ ω, Real.exp (t * X ω) ≤ Real.exp (t * Y ω) := fun ω =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0)
  have hXi : Integrable (fun ω => Real.exp (t * X ω)) P :=
    hYi.mono' (measurable_const.mul hX.1).exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hle ω)
  refine ⟨hXi, ?_⟩
  have hpos : 0 < mgf X P t := mgf_pos hXi
  have h1 : mgf X P t ≤ 2 * Real.exp (Cg * (K * t) ^ p) :=
    (integral_mono hXi hYi hle).trans hmgf
  have htp : 1 ≤ t ^ p := Real.one_le_rpow ht hp0
  change Real.log (mgf X P t) ≤ _
  calc Real.log (mgf X P t) ≤ Real.log (2 * Real.exp (Cg * (K * t) ^ p)) :=
        Real.log_le_log hpos h1
    _ = Real.log 2 + Cg * K ^ p * t ^ p := by
        rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp,
          Real.mul_rpow hK.le ht0, mul_assoc]
    _ ≤ (Real.log 2 + Cg * K ^ p) * t ^ p := by
        nlinarith

/-- **Lemma A.5 (Laplace transform)**, (A.5): for `s > 1`, if `exp(λ X)` is integrable and
`log E[exp(λ X)] ≤ λ^{s/(s-1)}` for every `λ ≥ 1`, then `X ≤ O_s(C)` with `C = 2 · 8^{1/s}`. The
proof is the Chernoff bound at `λ = (x/2)^{s-1}`, as in the book, and `osBound_of_tail` in place
of Lemma A.1 and Remark A.2. -/
theorem osBound_of_log_integral_exp_le [IsProbabilityMeasure P] {X : Ω → ℝ} {s : ℝ}
    (hX : Measurable X) (hs1 : 1 < s)
    (h : ∀ t : ℝ, 1 ≤ t → Integrable (fun ω => Real.exp (t * X ω)) P ∧
      Real.log (∫ ω, Real.exp (t * X ω) ∂P) ≤ t ^ (s / (s - 1))) :
    OsBound P X s ((8 : ℝ) ^ s⁻¹ * 2) := by
  have hs0 : 0 < s := by linarith
  refine osBound_of_tail hX hs0 le_rfl two_pos fun u hu => ?_
  have hu0 : 0 < u := by linarith
  set l : ℝ := u ^ (s - 1) with hldef
  have hl1 : 1 ≤ l := Real.one_le_rpow hu (by linarith)
  obtain ⟨hi, hlog⟩ := h l hl1
  have hpos : 0 < mgf X P l := mgf_pos hi
  have hlp : l ^ (s / (s - 1)) = u ^ s := by
    rw [hldef, ← Real.rpow_mul hu0.le]
    congr 1
    have : s - 1 ≠ 0 := by linarith
    field_simp
  have hm : mgf X P l ≤ Real.exp (u ^ s) := by
    calc mgf X P l = Real.exp (Real.log (mgf X P l)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (u ^ s) := Real.exp_le_exp.2 (hlp ▸ hlog)
  have hlu : l * (u * 2) = 2 * u ^ s := by
    rw [hldef, Real.rpow_sub_one hu0.ne']
    field_simp
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := X) (u * 2) (zero_le_one.trans hl1) hi
  rw [← ofReal_measureReal (measure_ne_top P _)]
  refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
  calc Real.exp (-l * (u * 2)) * mgf X P l ≤ Real.exp (-l * (u * 2)) * Real.exp (u ^ s) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (-(u ^ s)) := by
        rw [← Real.exp_add, neg_mul, hlu]
        ring_nf

/-- A bound `|X| ≤ O_s(θ)` gives `X ≤ O_s(θ)` and `-X ≤ O_s(θ)`, that is, `X = O_s(θ)` in the
notation following (A.2). -/
theorem OsBound.of_abs {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P (fun ω => |X ω|) s θ)
    (hX : Measurable X) : OsBound P X s θ ∧ OsBound P (fun ω => -X ω) s θ :=
  ⟨h.of_le hX fun _ => le_abs_self _, h.of_le hX.neg fun _ => neg_le_abs _⟩

/-- Conversely, `X ≤ O_s(θ)` and `-X ≤ O_s(θ)` give `|X| ≤ O_s(2^{1/s} θ)`. -/
theorem OsBound.abs_of_neg {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ)
    (hn : OsBound P (fun ω => -X ω) s θ) :
    OsBound P (fun ω => |X ω|) s ((2 : ℝ) ^ s⁻¹ * θ) := by
  have := osBound_max h hn
  rw [max_self] at this
  simpa only [← abs_eq_max_neg] using this

/-- **Lemma A.9**, first implication, in the form of the book: `X = 𝒪_s(θ)` implies
`X = O_s(C θ)`, with `C = 4 · 8^{1/s}`. -/
theorem CenteredOsBound.osBound_and_neg [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : CenteredOsBound P X s θ) :
    OsBound P X s ((8 : ℝ) ^ s⁻¹ * (4 * θ)) ∧
      OsBound P (fun ω => -X ω) s ((8 : ℝ) ^ s⁻¹ * (4 * θ)) :=
  h.osBound_abs.of_abs h.1

/-- **Lemma A.9**, second implication, in the form of the book: for `s ∈ (1, 2]` there is `C(s)`
such that `X = O_s(θ)` and `E[X] = 0` imply `X = 𝒪_s(C θ)`. -/
theorem exists_centeredOsBound_of_osBound {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → ℝ) (θ : ℝ), OsBound P X s θ → OsBound P (fun ω => -X ω) s θ →
        ∫ ω, X ω ∂P = 0 → CenteredOsBound P X s (C * θ) := by
  obtain ⟨C, hC, h⟩ := exists_centeredOsBound_of_osBound_abs hs1 hs2
  refine ⟨C * (2 : ℝ) ^ s⁻¹, mul_pos hC (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro Ω _ P _ X θ hX hnX hmean
  have := h P X _ hX.1 (hX.abs_of_neg hnX) hmean
  simpa only [mul_assoc] using this

theorem measurableSet_cube {d : ℕ} (z : Vec d) (R : ℝ) : MeasurableSet (cube z R) := by
  have e : cube z R = ⋂ i, {x : Vec d | |x i - z i| < R / 2} := by
    ext x
    simp [cube]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const

/-- **Lemma A.12**, in the form of the book: let `R ≥ 1` and let `I` be a finite nonempty set of
lattice indices; if, for each `k ∈ I`, `X k` is `F(□_{2R}(R k))`-measurable and
`X k = 𝒪_s(θ k)`, then `∑_{k ∈ I} X k = 𝒪_s(C (∑_{k ∈ I} θ_k²)^{1/2})` with
`C = (2 · 4^d)^{1/2}`. -/
theorem centeredOsBound_sum_of_measurable_cube [IsProbabilityMeasure P] {d : ℕ}
    {F : Set (Vec d) → MeasurableSpace Ω} (hF : HasUnitRange P F) (hmono : Monotone F)
    {R : ℝ} (hR : 1 ≤ R) (I : Finset (LatticeIndex d)) (hI : I.Nonempty)
    {X : LatticeIndex d → Ω → ℝ} {s : ℝ} {θ : LatticeIndex d → ℝ}
    (hXloc : ∀ k ∈ I, Measurable[F (cube (R • latticeShift k) (2 * R))] (X k))
    (hX : ∀ k ∈ I, CenteredOsBound P (X k) s (θ k)) :
    CenteredOsBound P (fun ω => ∑ k ∈ I, X k ω) s
      (Real.sqrt (2 * 4 ^ d) * Real.sqrt (∑ k ∈ I, θ k ^ 2)) := by
  refine centeredOsBound_lattice_sum hF hmono hR I hI
    (U := fun k => cube (R • latticeShift k) (2 * R)) (fun k => measurableSet_cube _ _)
    (fun k _ x hx i => ?_) hXloc hX
  have h : |x i - (R • latticeShift k) i| < 2 * R / 2 := hx i
  rwa [show 2 * R / 2 = R by ring] at h

end BookStatements

/-! ## The local σ-algebras of the coefficient fields -/

section CoefficientFields

/-- The local σ-algebras `F(U)` of (0.9) increase with `U`. -/
theorem monotone_localSigma {d : ℕ} {Λ : ℝ} : Monotone (localSigma (d := d) (Λ := Λ)) := by
  intro U W hUW
  unfold localSigma
  exact iSup_le fun u => iSup_le fun i => iSup_le fun j =>
    le_iSup_of_le (⟨u.1, u.2.trans hUW⟩ : {u : SmoothCompactTest d // tsupport u.toFun ⊆ W})
      (le_iSup_of_le i (le_iSup_of_le j le_rfl))

/-- Under the assumptions (P1)-(P2), the local σ-algebras have a unit range of dependence. -/
theorem LawHypotheses.hasUnitRange {d : ℕ} {Λ : ℝ} {P : Measure (CoefficientField d Λ)}
    (hP : LawHypotheses P) : HasUnitRange P (localSigma (d := d) (Λ := Λ)) :=
  fun U W hU hW hsep => hP.2.2 U W hU hW hsep

/-- **Lemma A.12** for the coefficient fields under the assumptions (P1)-(P2): let `R ≥ 1` and let
`I` be a finite nonempty set of lattice indices; if, for each `k ∈ I`, `X k` is
`F(□_{2R}(R k))`-measurable and `X k = 𝒪_s(θ k)`, then
`∑_{k ∈ I} X k = 𝒪_s(C (∑_{k ∈ I} θ_k²)^{1/2})` with `C = (2 · 4^d)^{1/2}`. -/
theorem centeredOsBound_sum_of_localSigma_cube {d : ℕ} {Λ : ℝ}
    {P : Measure (CoefficientField d Λ)} (hP : LawHypotheses P) {R : ℝ} (hR : 1 ≤ R)
    (I : Finset (LatticeIndex d)) (hI : I.Nonempty) {X : LatticeIndex d → CoefficientField d Λ → ℝ}
    {s : ℝ} {θ : LatticeIndex d → ℝ}
    (hXloc : ∀ k ∈ I, Measurable[localSigma (cube (R • latticeShift k) (2 * R))] (X k))
    (hX : ∀ k ∈ I, CenteredOsBound P (X k) s (θ k)) :
    CenteredOsBound P (fun a => ∑ k ∈ I, X k a) s
      (Real.sqrt (2 * 4 ^ d) * Real.sqrt (∑ k ∈ I, θ k ^ 2)) :=
  haveI := hP.1
  centeredOsBound_sum_of_measurable_cube hP.hasUnitRange monotone_localSigma hR I hI hXloc hX

end CoefficientFields

end QSH
