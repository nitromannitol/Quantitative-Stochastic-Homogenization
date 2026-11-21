import QuantitativeStochasticHomogenization.AppA.OsNotation
import QuantitativeStochasticHomogenization.Ch04.Sec02AdditiveStructureOfJ1
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses

/-!
# Block integrals of random fields

For a bounded random field `X : Ω → ℝ^d → ℝ` and a bounded weight `f`, the block integral
`∫ f(x) X(·, x) dx` is the basic random variable of the proof of Proposition 4.12 of Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, Section 4.5.
Proved here:

* if `f` vanishes off a measurable set `U` and `X` is local in the sense of `LocFieldEstimate`, the
  block integral is measurable for the coefficients in the neighbourhood of `U`
  (`measurable_integral_mul_local`);
* if `X` is centered, so is every block integral (`integral_integral_mul_eq_zero`), and it is
  bounded by the bound of `X` times `∫ |f|`;
* a weighted average over a closed cube of a field of centered bounds `𝒪_s(θ)` is `𝒪_s(R^d θ)`
  (`centeredOsBound_integral_closedCube`, Lemma A.10);
* `exp(-c x^κ) ≤ C x^{-p}` for `x ≥ 1` (`exists_exp_neg_rpow_le`).
-/

open MeasureTheory ProbabilityTheory

namespace QSH

variable {d : ℕ}

/-! ### Measurability -/

theorem measurable_integral_mul {α : Type*} [m : MeasurableSpace α] {f : Vec d → ℝ}
    {G : α → Vec d → ℝ} (hf : Measurable f) (hG : Measurable fun w : α × Vec d => G w.1 w.2) :
    Measurable fun a => ∫ x, f x * G a x :=
  ((hf.comp measurable_snd).mul hG).stronglyMeasurable.integral_prod_right'.measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
/-- **Local measurability of block integrals.** If `f` vanishes off `U` and
`(a, x) ↦ 1_U(x) X(a, x)` is measurable for `F(V) ⊗ Borel`, the block integral `∫ f X(a, ·)` is
`F(V)`-measurable. -/
theorem measurable_integral_mul_local {m : MeasurableSpace Ω} {X : Ω → Vec d → ℝ}
    {U : Set (Vec d)}
    (hX : @Measurable (Ω × Vec d) ℝ (@Prod.instMeasurableSpace Ω (Vec d) m _) _
      (fun w => U.indicator (X w.1) w.2))
    {f : Vec d → ℝ} (hf : Measurable f) (hfU : ∀ x ∉ U, f x = 0) :
    @Measurable Ω ℝ m _ (fun a => ∫ x, f x * X a x) := by
  have e : (fun a => ∫ x, f x * X a x) = fun a => ∫ x, f x * U.indicator (X a) x := by
    funext a
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
    · rw [hfU x hx, zero_mul, zero_mul]
  rw [e]
  exact @measurable_integral_mul d Ω m f (fun a x => U.indicator (X a) x) hf hX

/-! ### Means and bounds -/

theorem integrable_mul_field [IsProbabilityMeasure P] {X : Ω → Vec d → ℝ} {B : ℝ}
    (hXm : Measurable fun w : Ω × Vec d => X w.1 w.2) (hXb : ∀ a x, |X a x| ≤ B)
    {f : Vec d → ℝ} (hf : Integrable f) :
    Integrable (fun w : Ω × Vec d => f w.2 * X w.1 w.2) (P.prod volume) := by
  have hg : Integrable (fun w : Ω × Vec d => (1 : ℝ) * (B * |f w.2|)) (P.prod volume) :=
    (integrable_const (μ := P) (1 : ℝ)).mul_prod (hf.abs.const_mul B)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact (hf.aestronglyMeasurable.comp_snd).mul hXm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, one_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hXb w.1 w.2) (abs_nonneg _)

/-- **Centered block integrals.** -/
theorem integral_integral_mul_eq_zero [IsProbabilityMeasure P] {X : Ω → Vec d → ℝ} {B : ℝ}
    (hXm : Measurable fun w : Ω × Vec d => X w.1 w.2) (hXb : ∀ a x, |X a x| ≤ B)
    (hX0 : ∀ x, ∫ a, X a x ∂P = 0) {f : Vec d → ℝ} (hf : Integrable f) :
    ∫ a, (∫ x, f x * X a x) ∂P = 0 := by
  have hint := integrable_mul_field (P := P) hXm hXb hf
  have hswap := integral_integral_swap (μ := P) (ν := volume)
    (f := fun a x => f x * X a x) hint
  rw [hswap]
  have : ∀ x, ∫ a, f x * X a x ∂P = 0 := fun x => by rw [integral_const_mul, hX0 x, mul_zero]
  simp only [this, integral_zero]

omit [MeasurableSpace Ω] in
theorem abs_integral_mul_le {X : Ω → Vec d → ℝ} {B : ℝ} (hXb : ∀ a x, |X a x| ≤ B)
    {f : Vec d → ℝ} (hf : Integrable f) (a : Ω) :
    |∫ x, f x * X a x| ≤ B * ∫ x, |f x| := by
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => abs_nonneg _) (hf.abs.const_mul B)
    (Filter.Eventually.of_forall fun x => ?_))
  show |f x * X a x| ≤ B * |f x|
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hXb a x) (abs_nonneg _)

/-! ### Closed cubes -/

theorem closedCube_eq_closedBall (z : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    closedCube z R = Metric.closedBall z (R / 2) := by
  ext x
  rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)]
  simp only [closedCube, Set.mem_ofPred_eq, Real.dist_eq]

theorem volume_closedCube (z : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedCube z R) = ENNReal.ofReal (R ^ d) := by
  rw [closedCube_eq_closedBall z hR, Real.volume_pi_closedBall _ (by positivity), Fintype.card_fin]
  congr 1
  ring

theorem volume_real_closedCube (z : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedCube z R) = R ^ d := by
  rw [measureReal_def, volume_closedCube z hR, ENNReal.toReal_ofReal (by positivity)]

theorem integrable_of_abs_le_one_of_closedCube {f : Vec d → ℝ} (hf : Measurable f)
    (hf1 : ∀ x, |f x| ≤ 1) {z : Vec d} {R : ℝ} (hR : 0 ≤ R)
    (hfz : ∀ x ∉ closedCube z R, f x = 0) : Integrable f := by
  have he : f = (closedCube z R).indicator f := by
    funext x
    by_cases hx : x ∈ closedCube z R
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hfz x hx]
  rw [he, integrable_indicator_iff (measurableSet_closedCube z R)]
  have : IsFiniteMeasure (volume.restrict (closedCube z R)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_closedCube z hR]; exact ENNReal.ofReal_lt_top⟩
  exact Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf1 x)

theorem integral_abs_le_of_closedCube {f : Vec d → ℝ} (hf : Measurable f)
    (hf1 : ∀ x, |f x| ≤ 1) {z : Vec d} {R : ℝ} (hR : 0 ≤ R)
    (hfz : ∀ x ∉ closedCube z R, f x = 0) : ∫ x, |f x| ≤ R ^ d := by
  have hi := integrable_of_abs_le_one_of_closedCube hf hf1 hR hfz
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedCube z R)
    (fun x hx => by rw [hfz x hx, abs_zero])]
  calc ∫ x in closedCube z R, |f x| ≤ ∫ _x in closedCube z R, (1 : ℝ) :=
        setIntegral_mono_on hi.abs.integrableOn (integrableOn_const (by
          rw [volume_closedCube z hR]; exact ENNReal.ofReal_ne_top)) (measurableSet_closedCube z R)
          fun x _ => hf1 x
    _ = R ^ d := by rw [setIntegral_const, smul_eq_mul, mul_one, volume_real_closedCube z hR]

/-- **Lemma A.10 on a closed cube.** A weighted average of a jointly measurable field of centered
bounds `𝒪_s(θ)`, with weight of modulus at most one vanishing off `closedCube z R`, is
`𝒪_s(R^d θ)`. -/
theorem centeredOsBound_integral_closedCube [IsProbabilityMeasure P] {D : Ω → Vec d → ℝ}
    {s θ : ℝ} (hDm : Measurable fun w : Ω × Vec d => D w.1 w.2)
    (hD : ∀ x, CenteredOsBound P (fun a => D a x) s θ) {f : Vec d → ℝ} (hf : Measurable f)
    (hf1 : ∀ x, |f x| ≤ 1) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hfz : ∀ x ∉ closedCube z R, f x = 0) :
    CenteredOsBound P (fun a => ∫ x, f x * D a x) s (R ^ d * θ) := by
  have hfin : IsFiniteMeasure (volume.restrict (closedCube z R)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_closedCube z hR.le]; exact ENNReal.ofReal_lt_top⟩
  have hne : volume.restrict (closedCube z R) ≠ 0 := by
    intro h
    have := congrArg (fun μ : Measure (Vec d) => μ Set.univ) h
    simp only [Measure.restrict_apply_univ, volume_closedCube z hR.le, Measure.coe_zero,
      Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact absurd this (not_le.mpr (by positivity))
  have hXm : Measurable (Function.uncurry fun x a => f x * D a x) :=
    (hf.comp measurable_fst).mul (hDm.comp measurable_swap)
  have h := centeredOsBound_integral (μ := volume.restrict (closedCube z R)) hne hXm
    fun x => (hD x).mul_of_abs_le_one (hf1 x)
  rw [measureReal_restrict_apply_univ, volume_real_closedCube z hR.le] at h
  have he : (fun a => ∫ x in closedCube z R, f x * D a x) = fun a => ∫ x, f x * D a x := by
    funext a
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hfz x hx, zero_mul]
  rwa [he] at h

/-! ### Exponentials and powers -/

/-- `exp(-c x^κ) ≤ C x^{-p}` for `x ≥ 1`, with `C` depending on `c, κ, p`. -/
theorem exists_exp_neg_rpow_le {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → Real.exp (-(c * x ^ κ)) ≤ C * x ^ (-p) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (p / κ)
  have hnp : p ≤ κ * n := by
    have := (div_le_iff₀ hκ).mp hn
    linarith
  refine ⟨(n.factorial : ℝ) / c ^ n, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy : 0 < c * x ^ κ := by positivity
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  have h1 : (c * x ^ κ) ^ n / n.factorial ≤ Real.exp (c * x ^ κ) :=
    Real.pow_div_factorial_le_exp _ hy.le n
  have h2 : Real.exp (-(c * x ^ κ)) ≤ n.factorial / (c * x ^ κ) ^ n := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact h1
  refine h2.trans ?_
  rw [mul_pow, ← Real.rpow_natCast (x ^ κ) n, ← Real.rpow_mul hx0.le, div_mul_eq_div_div,
    div_eq_mul_inv _ (x ^ (κ * n)), ← Real.rpow_neg hx0.le]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    (by positivity)

end QSH
