import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatSemigroupAverages
import QuantitativeStochasticHomogenization.Ch04.Sec02.Theorem46Expectation
import QuantitativeStochasticHomogenization.Ch04.Sec02.UniformBootstrap

/-!
# Additivity and the expectation of `J₁` from a deterministic trial

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10 (`Add(s/2, 2α)`) and Remark 4.18, (4.70).

The proof of Proposition 4.10 used here compares `J₁(Φ_{y,r}, p, q)` with the value of the
functional of (4.8) at one corrected field with a deterministic slope, the homogenized maximizer
`c* = -p + ā⁻¹q` (`homogenizedSlope`). The same trial is available at every center and scale, and
its values are averaged by the heat semigroup, while `J₁` at the larger mask is at most the
average of `J₁` at the smaller masks (`J1Heat_le_integral_heatKernel_mul`). Hence the additivity
defect is squeezed between `0` and the average of the trial gap
`J₁(Φ_{y,r}, p, q) - L_r(c*)(y)` (`additivityDefect_le_trialGap`). Lemma A.4 then turns a bound
`O_t(C r^{-β})` on the trial gap at every center (`TrialGapEstimate`) into `Add(t, β)`
(`addJ1_of_trialGapEstimate`), and a bound on the expectation of the trial into the
expectation estimate (`expectationJ1Estimate_of_trialGap`).

The trial gap estimate with `t = s/2`, `β = 2α` under `Fluc(s, α)` is the quadratic response at
the deterministic slope; it is the analytic core of Proposition 4.10 and is an input here.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The mean of a stochastic bound for small exponents -/

/-- For `t > 0`, a nonnegative `X ≤ O_t(θ)` on a probability space is integrable with
`E[X] ≤ (1 + 2 n!) θ`, `n = ⌈1/t⌉`. -/
theorem OsBound.integral_le_factorial_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {t θ : ℝ} (h : OsBound P X t θ) (hX0 : ∀ ω, 0 ≤ X ω) :
    Integrable X P ∧ ∫ ω, X ω ∂P ≤ (1 + 2 * ((Nat.ceil t⁻¹).factorial : ℝ)) * θ := by
  obtain ⟨hXm, ht, hθ, hint⟩ := h
  set n : ℕ := Nat.ceil t⁻¹ with hn
  set y : Ω → ℝ := fun ω => (θ⁻¹ * X ω) ^ t with hy
  have hy0 : ∀ ω, 0 ≤ y ω := fun ω => Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) (hX0 ω)) _
  have hym : Measurable y := (measurable_const.mul hXm).pow_const t
  have hkey : ∀ ω, θ⁻¹ * X ω ≤ 1 + (n.factorial : ℝ) * Real.exp (y ω) := by
    intro ω
    have hu0 : 0 ≤ θ⁻¹ * X ω := mul_nonneg (inv_nonneg.mpr hθ.le) (hX0 ω)
    have hu : θ⁻¹ * X ω = y ω ^ t⁻¹ := by
      rw [hy]
      simp only
      rw [← Real.rpow_mul hu0, mul_inv_cancel₀ ht.ne', Real.rpow_one]
    have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hexp := Real.pow_div_factorial_le_exp (y ω) (hy0 ω) n
    rw [div_le_iff₀ hfac] at hexp
    rw [hu]
    rcases le_or_gt (y ω) 1 with h1 | h1
    · have : y ω ^ t⁻¹ ≤ 1 := Real.rpow_le_one (hy0 ω) h1 (inv_nonneg.mpr ht.le)
      nlinarith [Real.exp_pos (y ω)]
    · have h2 : y ω ^ t⁻¹ ≤ y ω ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1.le (Nat.le_ceil _)
      rw [Real.rpow_natCast] at h2
      nlinarith
  -- the exponential moment
  have hexpm : Measurable fun ω => Real.exp (y ω) := Real.measurable_exp.comp hym
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (y ω)) ∂P ≤ 2 := by
    refine le_trans (le_of_eq ?_) hint
    refine lintegral_congr fun ω => ?_
    rw [hy]
    simp only [max_eq_left (hX0 ω)]
  have hexpi : Integrable (fun ω => Real.exp (y ω)) P := by
    refine ⟨hexpm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact hlint.trans_lt (by norm_num)
  have hexpint : ∫ ω, Real.exp (y ω) ∂P ≤ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      (Real.exp_pos _).le) hexpm.aestronglyMeasurable]
    have : (∫⁻ ω, ENNReal.ofReal (Real.exp (y ω)) ∂P).toReal ≤ (2 : ENNReal).toReal :=
      ENNReal.toReal_mono (by norm_num) hlint
    simpa using this
  have hbound : ∀ ω, X ω ≤ θ * (1 + (n.factorial : ℝ) * Real.exp (y ω)) := by
    intro ω
    have := mul_le_mul_of_nonneg_left (hkey ω) hθ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul] at this
  have hgi : Integrable (fun ω => θ * (1 + (n.factorial : ℝ) * Real.exp (y ω))) P :=
    ((integrable_const 1).add (hexpi.const_mul _)).const_mul θ
  have hXi : Integrable X P :=
    hgi.mono' hXm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
      exact hbound ω)
  refine ⟨hXi, ?_⟩
  calc ∫ ω, X ω ∂P ≤ ∫ ω, θ * (1 + (n.factorial : ℝ) * Real.exp (y ω)) ∂P :=
        integral_mono_ae hXi hgi (Filter.Eventually.of_forall hbound)
    _ = θ * (1 + (n.factorial : ℝ) * ∫ ω, Real.exp (y ω) ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const 1) (hexpi.const_mul _),
          integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ θ * (1 + (n.factorial : ℝ) * 2) := by
        gcongr
    _ = (1 + 2 * (n.factorial : ℝ)) * θ := by ring

/-! ## The deterministic trial -/

section Trial

variable {P : Measure (CoefficientField d Λ)}

/-- The homogenized maximizer `c* = -p + A⁻¹q`. -/
def homogenizedSlope (A : Mat d) (p q : Vec d) : Vec d := A⁻¹.mulVec q - p

/-- The trial gap `J₁(Φ_{y,r}, p, q) - L_r(c*)(y)`, where `L_r(c*)(y)` is the functional of (4.8)
at the mask `Φ_{y,r}` and the corrected field of slope `c*`. -/
def trialGap (S : HomogenizationData P) (a : CoefficientField d Λ) (y : Vec d) (r : ℝ)
    (p q : Vec d) : ℝ :=
  J1Heat a y r p q -
    j1Functional a (heatKernel y r) p q (correctedField S a (homogenizedSlope S.homogenized p q))

/-- At every center `z`, almost surely the integrand of (4.8) at the trial field is integrable
against the masks `Φ_{z,R}`, `R ≥ 1`. -/
def TrialIntegrable (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P) : Prop :=
  ∀ z : Vec d, ∀ᵐ a ∂P, ∀ R : ℝ, 1 ≤ R → ∀ p q : Vec d,
    Integrable fun x => heatKernel z R x *
      j1Integrand a p q (correctedField S a (homogenizedSlope S.homogenized p q)) x

/-- **The trial gap estimate** with exponent `t` and rate `β`: the positive part of the trial gap
is jointly measurable in the center and the coefficients and is `O_t(C r^{-β})` at every center,
for `r ≥ 1` and `p, q` in the open unit ball. -/
def TrialGapEstimate (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (t β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    Measurable (Function.uncurry fun (y : Vec d) (a : CoefficientField d Λ) =>
      max (trialGap S a y r p q) 0) ∧
    ∀ y : Vec d, OsBound P (fun a => max (trialGap S a y r p q) 0) t (C * r ^ (-β))

/-- **The expectation of the trial**: `L_r(c*)(z)` is integrable and its expectation is within
`C r^{-β}` of the homogenized energy. -/
def TrialExpectationEstimate (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    Integrable (fun a => j1Functional a (heatKernel z r) p q
      (correctedField S a (homogenizedSlope S.homogenized p q))) P ∧
    |(∫ a, j1Functional a (heatKernel z r) p q
      (correctedField S a (homogenizedSlope S.homogenized p q)) ∂P) -
        homogenizedJ1 S.homogenized p q| ≤ C * r ^ (-β)

/-- The trial gap `J(y, r, p, q) - L_r(c*)(y)` of a field `J` (`J = J₁` or a jointly measurable
version of it). -/
def trialGapOf (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ)
    (S : HomogenizationData P) (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  J a y r p q -
    j1Functional a (heatKernel y r) p q (correctedField S a (homogenizedSlope S.homogenized p q))

/-- **The trial gap estimate for a field `J` with constant `C`**. -/
def TrialGapEstimateAt (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ) (t β C : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ p q : Vec d, euclideanNorm p < 1 → euclideanNorm q < 1 →
    Measurable (Function.uncurry fun (y : Vec d) (a : CoefficientField d Λ) =>
      max (trialGapOf J S a y r p q) 0) ∧
    ∀ y : Vec d, OsBound P (fun a => max (trialGapOf J S a y r p q) 0) t (C * r ^ (-β))

/-- **The expectation of the trial with constant `C`**. -/
def TrialExpectationEstimateAt (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (β C : ℝ) : Prop :=
  ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    Integrable (fun a => j1Functional a (heatKernel z r) p q
      (correctedField S a (homogenizedSlope S.homogenized p q))) P ∧
    |(∫ a, j1Functional a (heatKernel z r) p q
      (correctedField S a (homogenizedSlope S.homogenized p q)) ∂P) -
        homogenizedJ1 S.homogenized p q| ≤ C * r ^ (-β)

theorem trialGapEstimate_iff_exists_at (S : HomogenizationData P) (t β : ℝ) :
    TrialGapEstimate P S t β ↔ ∃ C > 0, TrialGapEstimateAt P S J1Heat t β C := Iff.rfl

theorem trialExpectationEstimate_iff_exists_at (S : HomogenizationData P) (β : ℝ) :
    TrialExpectationEstimate P S β ↔ ∃ C > 0, TrialExpectationEstimateAt P S β C := Iff.rfl

/-- `|J₁(Φ_{z,r}, p, q)| ≤ |Λ| + 1` for `r > 0` and `p, q` in the open unit ball. -/
theorem abs_J1Heat_le_of_pos (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r)
    {p q : Vec d} (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    |J1Heat a z r p q| ≤ |Λ| + 1 := by
  obtain ⟨h0, h1⟩ := J1Heat_nonneg_le a z hr p q
  have hp2 : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq2 : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  have : Λ * euclideanSq p ≤ |Λ| :=
    (mul_le_mul_of_nonneg_right (le_abs_self Λ) (euclideanSq_nonneg p)).trans
      (by nlinarith [abs_nonneg Λ])
  rw [abs_of_nonneg h0]
  linarith

/-- The functional of (4.8) at a corrected field is at most `J₁` when the corrected fields are
gradients of `A₁`. -/
theorem j1Functional_correctedField_le_J1Heat (S : HomogenizationData P)
    (a : CoefficientField d Λ) (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) {r : ℝ}
    (hr : 0 < r) (p q ξ : Vec d) :
    j1Functional a (heatKernel y r) p q (correctedField S a ξ) ≤ J1Heat a y r p q := by
  obtain ⟨w, hw⟩ := hspan.2 ξ
  rw [← j1Functional_congr_ae a _ p q hw]
  unfold J1Heat
  rw [J1_eq_sSup_j1Functional]
  refine le_csSup ⟨Λ * euclideanSq p + euclideanSq q, ?_⟩ ⟨w, rfl⟩
  rintro e ⟨w', rfl⟩
  exact j1Functional_le a (heatKernel_nonneg y r) (integrable_heatKernel y hr)
    (integral_heatKernel y hr).le p q w'.grad

theorem trialGap_nonneg (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) {r : ℝ} (hr : 0 < r) (p q : Vec d) :
    0 ≤ trialGap S a y r p q :=
  sub_nonneg.mpr (j1Functional_correctedField_le_J1Heat S a hspan y hr p q _)

/-- **The additivity defect and the trial gap**: for `0 < r < R` and `ρ = √(R² - r²)`,
`0 ≤ ∫ Φ_{z,ρ} J₁(Φ_{·,r}) - J₁(Φ_{z,R}) ≤ ∫ Φ_{z,ρ}(y) (J₁(Φ_{y,r}) - L_r(c*)(y))₊ dy`. -/
theorem additivityDefect_le_trialGap (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hspan : GradientsOfA1AreCorrected S a) (z : Vec d) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (p q : Vec d) (hJ : AEStronglyMeasurable (fun y => J1Heat a y r p q) volume)
    (hI : Integrable fun x => heatKernel z R x *
      j1Integrand a p q (correctedField S a (homogenizedSlope S.homogenized p q)) x) :
    0 ≤ (∫ y, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y * J1Heat a y r p q) -
        J1Heat a z R p q ∧
      (∫ y, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y * J1Heat a y r p q) - J1Heat a z R p q ≤
        ∫ y, heatKernel z (Real.sqrt (R ^ 2 - r ^ 2)) y * max (trialGap S a y r p q) 0 := by
  set ρ := Real.sqrt (R ^ 2 - r ^ 2) with hρdef
  have hρ : 0 < ρ := sqrt_sq_sub_sq_pos hrR hr.le
  have hR : 0 < R := hr.trans hrR
  set g := correctedField S a (homogenizedSlope S.homogenized p q) with hg
  have h1 := J1Heat_le_integral_heatKernel_mul a z hr hrR p q hJ
  obtain ⟨-, hint2, heq⟩ := integral_heatKernel_mul_eq_integral_integral z hr hrR hI
  have hLR : j1Functional a (heatKernel z R) p q g ≤ J1Heat a z R p q :=
    j1Functional_correctedField_le_J1Heat S a hspan z hR p q _
  have hLeq : j1Functional a (heatKernel z R) p q g =
      ∫ y, heatKernel z ρ y * j1Functional a (heatKernel y r) p q g := heq
  have hJb : ∀ y, 0 ≤ J1Heat a y r p q ∧ J1Heat a y r p q ≤ Λ * euclideanSq p + euclideanSq q :=
    fun y => J1Heat_nonneg_le a y hr p q
  have hJint : Integrable fun y => heatKernel z ρ y * J1Heat a y r p q :=
    (integrable_heatKernel z hρ).mul_bdd hJ (c := Λ * euclideanSq p + euclideanSq q)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hJb y).1]
        exact (hJb y).2)
  have hint2' : Integrable fun y => heatKernel z ρ y * j1Functional a (heatKernel y r) p q g :=
    hint2
  have hdiff : Integrable fun y => heatKernel z ρ y * J1Heat a y r p q -
      heatKernel z ρ y * j1Functional a (heatKernel y r) p q g := hJint.sub hint2'
  have hfun : (fun y => heatKernel z ρ y * max (trialGap S a y r p q) 0) =
      fun y => max (heatKernel z ρ y * J1Heat a y r p q -
        heatKernel z ρ y * j1Functional a (heatKernel y r) p q g) 0 := by
    funext y
    rw [mul_max_of_nonneg _ _ (heatKernel_nonneg z ρ y), mul_zero, trialGap, ← hg, mul_sub]
  refine ⟨sub_nonneg.mpr h1, ?_⟩
  rw [hfun]
  calc (∫ y, heatKernel z ρ y * J1Heat a y r p q) - J1Heat a z R p q
      ≤ (∫ y, heatKernel z ρ y * J1Heat a y r p q) -
          ∫ y, heatKernel z ρ y * j1Functional a (heatKernel y r) p q g := by
        rw [← hLeq]; linarith
    _ = ∫ y, (heatKernel z ρ y * J1Heat a y r p q -
          heatKernel z ρ y * j1Functional a (heatKernel y r) p q g) :=
        (integral_sub hJint hint2').symm
    _ ≤ ∫ y, max (heatKernel z ρ y * J1Heat a y r p q -
          heatKernel z ρ y * j1Functional a (heatKernel y r) p q g) 0 :=
        integral_mono_ae hdiff hdiff.pos_part
          (Filter.Eventually.of_forall fun y => le_max_left _ _)

/-- **`Add(t, β)` from the trial gap estimate, for a version of `J₁`, with an explicit constant**
(Step 3 of the proof of Proposition 4.10): if the corrected fields are almost surely the gradients
of `A₁`, the trial is almost surely integrable against every mask, `J` is jointly measurable in
the coefficients and the center, bounded by `|Λ| + 1`, almost surely equal to `J₁` at all
parameters, and the trial gap of `J` is `O_t(C r^{-β})` at every center, then `Add(t, β)` holds for
`J` with the constant `max 1 ((1 + (1 - t)/(t log 2))^{1/t}) C`. -/
theorem addEstimateAt_of_trialGapEstimateAt [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) (htrial : TrialIntegrable P S)
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ}
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J w.1 w.2 r p q)
    (hJb : ∀ a z r p q, 1 ≤ r → euclideanNorm p < 1 → euclideanNorm q < 1 →
      |J a z r p q| ≤ |Λ| + 1)
    (hJ : ∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q)
    {t β C : ℝ} (hC : 0 < C) (hgap : TrialGapEstimateAt P S J t β C) :
    AddEstimateAt P J t β (max 1 ((1 + (1 - t) / (t * Real.log 2)) ^ t⁻¹) * C) := by
  set Ct : ℝ := max 1 ((1 + (1 - t) / (t * Real.log 2)) ^ t⁻¹) with hCt
  have hCt1 : 1 ≤ Ct := le_max_left _ _
  intro z r R hr hrR p q hp hq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hR : 0 < R := hr0.trans hrR
  obtain ⟨hm, hos⟩ := hgap r hr p q hp hq
  set ρ := Real.sqrt (R ^ 2 - r ^ 2) with hρdef
  have hρ : 0 < ρ := sqrt_sq_sub_sq_pos hrR hr0.le
  have hJy : ∀ a : CoefficientField d Λ, Measurable fun y => J a y r p q := fun a =>
    (hmeasJ r p q).comp (measurable_const.prodMk measurable_id)
  have hint : ∀ a : CoefficientField d Λ,
      Integrable fun x => heatKernel z ρ x * J a x r p q := by
    intro a
    refine (integrable_heatKernel z hρ).mul_bdd (hJy a).aestronglyMeasurable
      (c := |Λ| + 1) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact hJb a y r p q hr hp hq
  refine ⟨Filter.Eventually.of_forall hint, ?_⟩
  set X : Vec d → CoefficientField d Λ → ℝ :=
    fun y a => heatKernel z ρ y * max (trialGapOf J S a y r p q) 0 with hX
  have hΦm : Measurable fun y : Vec d => heatKernel z ρ y :=
    ((continuous_heatKernel_uncurry ρ).comp (continuous_const.prodMk continuous_id)).measurable
  have hXm : Measurable (Function.uncurry X) := (hΦm.comp measurable_fst).mul hm
  have hX0 : ∀ y a, 0 ≤ X y a := fun y a =>
    mul_nonneg (heatKernel_nonneg _ _ _) (le_max_right _ _)
  set θ : Vec d → ℝ := fun y => heatKernel z ρ y * (C * r ^ (-β)) with hθ
  have hθm : Measurable θ := hΦm.mul_const _
  have hθi : Integrable θ := (integrable_heatKernel z hρ).mul_const _
  have hθint : ∫ y, θ y = C * r ^ (-β) := by
    rw [hθ, integral_mul_const, integral_heatKernel z hρ, one_mul]
  have hθpos : 0 < ∫ y, θ y := by
    rw [hθint]; exact mul_pos hC (Real.rpow_pos_of_pos hr0 _)
  have hXos : ∀ y, OsBound P (X y) t (θ y) := fun y =>
    (hos y).const_mul (heatKernel_pos z hρ y)
  have hA4 : OsBound P (fun a => ∫ y, X y a) t (Ct * (C * r ^ (-β))) := by
    rcases le_or_gt 1 t with ht1 | ht1
    · obtain ⟨-, h⟩ := osBound_integral ht1 hXm hX0 hθm hθi hθpos hXos
      rw [hθint] at h
      exact h.mono_scale (le_mul_of_one_le_left (h.scale_pos.le) hCt1)
    · obtain ⟨-, h⟩ := osBound_integral_of_lt_one ht1 hXm hX0 hθm hθi hθpos hXos
      rw [hθint] at h
      exact h.mono_scale (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_pos hC (Real.rpow_pos_of_pos hr0 _)).le)
  have hmR : Measurable fun a : CoefficientField d Λ => J a z R p q :=
    (hmeasJ R p q).comp (measurable_id.prodMk measurable_const)
  have hmI : Measurable fun a : CoefficientField d Λ =>
      ∫ x, heatKernel z ρ x * J a x r p q := by
    have hsm : StronglyMeasurable (Function.uncurry fun (a : CoefficientField d Λ) (x : Vec d) =>
        heatKernel z ρ x * J a x r p q) :=
      ((hΦm.comp measurable_snd).mul (hmeasJ r p q)).stronglyMeasurable
    exact hsm.integral_prod_right.measurable
  have hmY : Measurable fun a : CoefficientField d Λ =>
      |J a z R p q - ∫ x, heatKernel z ρ x * J a x r p q| :=
    continuous_abs.measurable.comp (hmR.sub hmI)
  rw [mul_assoc]
  refine hA4.of_le_ae hmY ?_
  filter_upwards [hspan, htrial z, hJ] with a hsa hta hJa
  have hJya : AEStronglyMeasurable (fun y => J1Heat a y r p q) volume :=
    (hJy a).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun y => hJa y r p q)
  obtain ⟨h0, h1⟩ := additivityDefect_le_trialGap S a hsa z hr0 hrR p q hJya
    (hta R (hr.trans hrR.le) p q)
  simp only [hX, trialGapOf, hJa]
  simp only [trialGap] at h1
  rw [abs_sub_comm, abs_of_nonneg h0]
  exact h1

/-- **`Add(t, β)` from the trial gap estimate** (Step 3 of the proof of Proposition 4.10): if the
corrected fields are almost surely the gradients of `A₁`, the trial is almost surely integrable
against every mask, `(a, x) ↦ J₁(Φ_{x,r}, p, q)` is measurable, and the trial gap is
`O_t(C r^{-β})` at every center, then `Add(t, β)` holds for `J₁`. -/
theorem addJ1_of_trialGapEstimate [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) (htrial : TrialIntegrable P S)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    {t β : ℝ} (hgap : TrialGapEstimate P S t β) : AddJ1 P t β := by
  obtain ⟨C, hC, hgap⟩ := hgap
  exact ⟨max 1 ((1 + (1 - t) / (t * Real.log 2)) ^ t⁻¹) * C,
    mul_pos (zero_lt_one.trans_le (le_max_left _ _)) hC,
    addEstimateAt_of_trialGapEstimateAt S hspan htrial hmeasJ
      (fun a z r p q hr hp hq => abs_J1Heat_le_of_pos a z (zero_lt_one.trans_le hr) hp hq)
      (ae_of_all _ fun _ _ _ _ _ => rfl) hC hgap⟩

/-- **The expectation estimate from the trial, for a version of `J₁`, with an explicit constant**
(Remark 4.18): if the corrected fields are almost surely the gradients of `A₁`, `J` is almost
surely equal to `J₁` at all parameters, the trial gap of `J` is `O_t(C₁ r^{-β})` and the
expectation of the trial is within `C₂ r^{-β}` of the homogenized energy, then the expectation of
`J₁` is within `(K C₁ + C₂) r^{-β}` of it, `K = 1 + 2 ⌈1/t⌉!`. -/
theorem abs_integral_J1Heat_sub_le_of_trialGap [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ}
    (hJ : ∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q) {t β C₁ C₂ : ℝ}
    (hgap : TrialGapEstimateAt P S J t β C₁) (hexp : TrialExpectationEstimateAt P S β C₂)
    (z : Vec d) (r : ℝ) (hr : 1 ≤ r) (p q : Vec d) (hp : euclideanNorm p < 1)
    (hq : euclideanNorm q < 1) :
    |(∫ a, J1Heat a z r p q ∂P) - homogenizedJ1 S.homogenized p q| ≤
      ((1 + 2 * ((Nat.ceil t⁻¹).factorial : ℝ)) * C₁ + C₂) * r ^ (-β) := by
  set K : ℝ := 1 + 2 * ((Nat.ceil t⁻¹).factorial : ℝ) with hK
  have hK0 : 0 < K := by positivity
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨-, hos⟩ := hgap r hr p q hp hq
  obtain ⟨hLint, hL⟩ := hexp z r hr p q hp hq
  obtain ⟨hZint, hZ⟩ := (hos z).integral_le_factorial_mul fun a => le_max_right _ _
  set L : CoefficientField d Λ → ℝ := fun a => j1Functional a (heatKernel z r) p q
    (correctedField S a (homogenizedSlope S.homogenized p q)) with hLdef
  have hJe : (fun a => J1Heat a z r p q) =ᵐ[P] fun a => max (trialGapOf J S a z r p q) 0 + L a := by
    filter_upwards [hspan, hJ] with a hsa hJa
    have h0 := trialGap_nonneg S a hsa z hr0 p q
    simp only [trialGap] at h0
    simp only [trialGapOf, hJa]
    rw [max_eq_left h0]
    ring
  have hJint : ∫ a, J1Heat a z r p q ∂P =
      (∫ a, max (trialGapOf J S a z r p q) 0 ∂P) + ∫ a, L a ∂P := by
    rw [integral_congr_ae hJe, integral_add hZint hLint]
  have hZ0 : 0 ≤ ∫ a, max (trialGapOf J S a z r p q) 0 ∂P :=
    integral_nonneg fun a => le_max_right _ _
  have hρ : 0 ≤ r ^ (-β) := Real.rpow_nonneg hr0.le _
  have hKC : 0 ≤ K * (C₁ * r ^ (-β)) := hZ0.trans hZ
  rw [hJint]
  obtain ⟨hL1, hL2⟩ := abs_le.mp hL
  rw [abs_le]
  constructor <;> nlinarith

/-- **The expectation estimate from the trial** (Remark 4.18): if the corrected fields are almost
surely the gradients of `A₁`, the trial gap is `O_t(C r^{-β})` and the expectation of the trial is
within `C r^{-β}` of the homogenized energy, then so is the expectation of `J₁`. -/
theorem expectationJ1Estimate_of_trialGap [IsProbabilityMeasure P] (S : HomogenizationData P)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) {t β : ℝ}
    (hgap : TrialGapEstimate P S t β) (hexp : TrialExpectationEstimate P S β) :
    ExpectationJ1Estimate P S.homogenized β := by
  obtain ⟨C₁, hC₁, hgap⟩ := hgap
  obtain ⟨C₂, hC₂, hexp⟩ := hexp
  exact ⟨_, by positivity, abs_integral_J1Heat_sub_le_of_trialGap S hspan
    (ae_of_all _ fun _ _ _ _ _ => rfl) hgap hexp⟩

end Trial

end QSH
