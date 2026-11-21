import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapBounds

/-!
# The quadratic response at the deterministic slope

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Proposition 4.10: the trial gap estimate `O_{s/2}(C r^{-2α})` under `Fluc(s, α)`
(Step 2 of the route used here), from three inputs stated as definitions:

* `LinearAverageEstimate P S s α`: the gradient averages of the corrected fields,
  `|∫ Φ_{z,r} G ξ - ξ| ≤ O_s(C (1 + |ξ|) r^{-α})` (the linear estimate of Step 1);
* `TrialObjectiveExpectation P S β`: the expectation of the functional of (4.8) at a deterministic
  slope `k` is within `C (1 + |k|²) r^{-β}` of `-½ k·āk - p·āk + q·k`;
* `GaussianEnergyBound P S τ C`: a jointly measurable family of scales `X ≤ O_τ(C)` with
  `∫ Φ_{z,r} G ξ·aG ξ ≤ C (1 + (X/r)^d) |ξ|²`.

Proved here: `trialGapEstimate_of_linearAverages`. The polarization vector of `J₁` is the
averaged gradient `m` of the maximizer at good scales, and its fluctuations are controlled by
`Fluc(s, α)`. The expectation of the gap at the deterministic slope `m₀ = E[m]`, compared with
the expectation of the trial at `c*`, gives `|m₀ - c*| ≤ C r^{-α}`; then the trial gap at `c*` is
at most a multiple of `|P c* - c*|² + |c* - m₀|² + |m₀ - m|²` at good scales, and of
`(M/r)^d` below the scales.

Also proved: the stochastic bound of finite sums at every exponent (`osBound_sum_fin_of_pos`) and
of squares (`OsBound.sq`), and the second moment of a stochastic bound (`OsBound.integral_sq_le`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Rules of `O_s` -/

section Rules

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Finite sums at every exponent: `∑_{i<n} Xᵢ ≤ O_s((2·2^{1/s})^n θ)`. -/
theorem osBound_sum_fin_of_pos {s θ : ℝ} :
    ∀ (n : ℕ) (X : Fin (n + 1) → Ω → ℝ), (∀ i, OsBound P (X i) s θ) →
      OsBound P (fun ω => ∑ i, X i ω) s ((2 * (2 : ℝ) ^ s⁻¹) ^ (n + 1) * θ)
  | 0, X, h => by
    have hθ := (h 0).scale_pos
    have hs := (h 0).exponent_pos
    have h2 : 1 ≤ 2 * (2 : ℝ) ^ s⁻¹ := by
      have : 1 ≤ (2 : ℝ) ^ s⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hs.le)
      linarith
    simpa using (h 0).mono_scale (le_mul_of_one_le_left hθ.le (by simpa using h2))
  | n + 1, X, h => by
    have hθ := (h 0).scale_pos
    have hs := (h 0).exponent_pos
    have hc : 1 ≤ 2 * (2 : ℝ) ^ s⁻¹ := by
      have : 1 ≤ (2 : ℝ) ^ s⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hs.le)
      linarith
    have ih := osBound_sum_fin_of_pos n (fun i => X i.succ) fun i => h i.succ
    have hsum := osBound_add_of_pos (h 0) ih
    have e : (fun ω => ∑ i : Fin (n + 2), X i ω) = fun ω => X 0 ω + ∑ i : Fin (n + 1), X i.succ ω :=
      funext fun ω => Fin.sum_univ_succ _
    rw [e]
    refine hsum.mono_scale (le_of_eq ?_)
    have hpow : θ ≤ (2 * (2 : ℝ) ^ s⁻¹) ^ (n + 1) * θ :=
      le_mul_of_one_le_left hθ.le (one_le_pow₀ hc)
    rw [max_eq_right hpow, pow_succ]
    ring

/-- Squares: a nonnegative `X ≤ O_s(θ)` has `X² ≤ O_{s/2}(θ²)`. -/
theorem OsBound.sq {X : Ω → ℝ} {s θ : ℝ} (h : OsBound P X s θ) (hX0 : ∀ ω, 0 ≤ X ω) :
    OsBound P (fun ω => X ω ^ 2) (s / 2) (θ ^ 2) := by
  have h2 := h.rpow hX0 (by norm_num : (0 : ℝ) < 2)
  simpa only [Real.rpow_two] using h2

/-- The constant `1 + 2 ⌈1/t⌉!` of the mean of `O_t` variables. -/
def momentConstant (t : ℝ) : ℝ := 1 + 2 * ((Nat.ceil t⁻¹).factorial : ℝ)

theorem momentConstant_pos (t : ℝ) : 0 < momentConstant t := by
  unfold momentConstant; positivity

/-- Second moments: a nonnegative `X ≤ O_s(θ)` on a probability space has `X²` integrable with
`E[X²] ≤ (1 + 2 ⌈2/s⌉!) θ²`. -/
theorem OsBound.integral_sq_le [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P X s θ) (hX0 : ∀ ω, 0 ≤ X ω) :
    Integrable (fun ω => X ω ^ 2) P ∧ ∫ ω, X ω ^ 2 ∂P ≤ momentConstant (s / 2) * θ ^ 2 :=
  (h.sq hX0).integral_le_factorial_mul fun _ => sq_nonneg _

end Rules

/-! ## The inputs -/

section Inputs

variable {P : Measure (CoefficientField d Λ)}

/-- **The linear estimate of Step 1**: `|∫ Φ_{z,r} G ξ - ξ| ≤ O_s(C (1 + |ξ|) r^{-α})`. -/
def LinearAverageEstimate (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (s α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
    OsBound P (fun a => euclideanNorm ((∫ x, heatKernel z r x • correctedField S a ξ x) - ξ)) s
      (C * (1 + euclideanNorm ξ) * r ^ (-α))

/-- **The expectation of the trial at a deterministic slope**: the functional of (4.8) at `G k` is
integrable and its expectation is within `C (1 + |k|²) r^{-β}` of `-½ k·āk - p·āk + q·k`. -/
def TrialObjectiveExpectation (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
    euclideanNorm p < 1 → euclideanNorm q < 1 → ∀ k : Vec d,
    Integrable (fun a => j1Functional a (heatKernel z r) p q (correctedField S a k)) P ∧
    |(∫ a, j1Functional a (heatKernel z r) p q (correctedField S a k) ∂P) -
        homogenizedJ1Objective S.homogenized p q k| ≤ C * (1 + euclideanSq k) * r ^ (-β)

/-- **The energy of the corrected fields below the scale**: a jointly measurable family of scales
`1 ≤ X(·, z) ≤ O_τ(C)` with `∫ Φ_{z,r} G ξ·aG ξ ≤ C (1 + (X/r)^d) |ξ|²` almost surely. -/
def GaussianEnergyBound (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (τ C : ℝ) : Prop :=
  ∃ X : CoefficientField d Λ → Vec d → ℝ, Measurable (Function.uncurry X) ∧
    (∀ a z, 1 ≤ X a z) ∧ (∀ z, OsBound P (fun a => X a z) τ C) ∧
    ∀ᵐ a ∂P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
      Integrable (fun x => heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∧
      (∫ x, heatKernel z r x * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ≤
        C * (1 + (X a z / r) ^ d) * euclideanSq ξ

/-- **The trial gap at a slope `k`, pointwise**: at a good scale it is at most
`(8/9)(Λ + 1/2) |∫ Φ_{y,r} G k - m|²` with `m` the polarization vector, and below the scale the
energy bound applies; together,
`(gap)₊ ≤ (8/9)(Λ + 1/2) |∫ Φ_{y,r} G k - m|² + (2(Λ + 1) + 2 C |k|²) (M/r)^d` for any `M` above both
scales. -/
theorem trialGap_pos_le (S : HomogenizationData P) (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (hspan : GradientsOfA1AreCorrected S a)
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) {ε Xg XN M CN : ℝ} (hε : ε ≤ 1 / 4)
    (hgood : Xg ≤ r → GaussianAverageBounds a S.homogenized (correctedField S a) y r ε)
    (hXg : Xg ≤ M) (hXN : XN ≤ M) (hXN0 : 0 ≤ XN) (hCN : 0 ≤ CN) {p q : Vec d}
    (hp : euclideanNorm p ≤ 1) (hq : euclideanNorm q ≤ 1) (k : Vec d)
    (hEint : Integrable fun x => heatKernel y r x *
      dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x)))
    (hEb : (∫ x, heatKernel y r x *
      dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x))) ≤
        CN * (1 + (XN / r) ^ d) * euclideanSq k) :
    max (J1Heat a y r p q - j1Functional a (heatKernel y r) p q (correctedField S a k)) 0 ≤
      8 / 9 * (Λ + 1 / 2) * euclideanNorm ((∫ x, heatKernel y r x • correctedField S a k x) -
        polarizationVector a y r p q) ^ 2 + (2 * (Λ + 1) + 2 * CN * euclideanSq k) * (M / r) ^ d := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hgap0 : 0 ≤ J1Heat a y r p q - j1Functional a (heatKernel y r) p q (correctedField S a k) :=
    sub_nonneg.mpr (j1Functional_correctedField_le_J1Heat S a hspan y hr0 p q k)
  rw [max_eq_left hgap0]
  have hk0 := euclideanSq_nonneg k
  have hfirst : 0 ≤ 8 / 9 * (Λ + 1 / 2) * euclideanNorm ((∫ x, heatKernel y r x •
      correctedField S a k x) - polarizationVector a y r p q) ^ 2 := by positivity
  have hp2 : euclideanSq p ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg p]
  have hq2 : euclideanSq q ≤ 1 := by
    rw [← euclideanNorm_sq]; nlinarith [euclideanNorm_nonneg q]
  by_cases hXr : Xg ≤ r
  · have h := trialGap_le_polarization S a hΛ hA hspan y r hε (hgood hXr) p q k
    have : 0 ≤ (2 * (Λ + 1) + 2 * CN * euclideanSq k) * (M / r) ^ d := by
      have hM0 : 0 ≤ M := hXN0.trans hXN
      positivity
    linarith
  · push_neg at hXr
    have hMr : 1 ≤ M / r := by rw [le_div_iff₀ hr0]; linarith
    have hMd : 1 ≤ (M / r) ^ d := one_le_pow₀ hMr
    have hXNd : (XN / r) ^ d ≤ (M / r) ^ d :=
      pow_le_pow_left₀ (div_nonneg hXN0 hr0.le) (div_le_div_of_nonneg_right hXN hr0.le) d
    have h1 := trialGap_le_energy a y hr0 p q (correctedField S a k) hEint
    have hK : Λ * euclideanSq p + euclideanSq q ≤ Λ + 1 := by nlinarith
    have h2 : CN * (1 + (XN / r) ^ d) * euclideanSq k ≤ 2 * CN * euclideanSq k * (M / r) ^ d := by
      have : 1 + (XN / r) ^ d ≤ 2 * (M / r) ^ d := by linarith
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hCN hk0)
      nlinarith
    have h3 : 2 * (Λ + 1) ≤ 2 * (Λ + 1) * (M / r) ^ d := le_mul_of_one_le_right (by linarith) hMd
    nlinarith

end Inputs

end QSH
