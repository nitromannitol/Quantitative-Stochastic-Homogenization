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
  (h.sq hX0).integral_le_factorial_mul fun ω => sq_nonneg _

end Rules

end QSH
