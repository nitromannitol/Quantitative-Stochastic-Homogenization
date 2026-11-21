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

/-- Finite sums over a finset at every exponent on a probability space:
`∑_{i∈I} Xᵢ ≤ O_s((2·2^{1/s})^{|I|} θ)`. -/
theorem osBound_finset_sum_of_pos [IsProbabilityMeasure P] {ι : Type*} (I : Finset ι)
    {X : ι → Ω → ℝ} {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (h : ∀ i ∈ I, OsBound P (X i) s θ) :
    OsBound P (fun ω => ∑ i ∈ I, X i ω) s ((2 * (2 : ℝ) ^ s⁻¹) ^ I.card * θ) := by
  classical
  have hc : 1 ≤ 2 * (2 : ℝ) ^ s⁻¹ := by
    have : 1 ≤ (2 : ℝ) ^ s⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hs.le)
    linarith
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, pow_zero, one_mul]
    refine ⟨measurable_const, hs, hθ, ?_⟩
    simp only [max_self, mul_zero, Real.zero_rpow hs.ne', Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, measure_univ, mul_one]
    norm_num
  | insert i I hi ih =>
    have hI := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hsum := osBound_add_of_pos (h i (Finset.mem_insert_self i I)) hI
    have e : (fun ω => ∑ j ∈ insert i I, X j ω) = fun ω => X i ω + ∑ j ∈ I, X j ω :=
      funext fun ω => Finset.sum_insert hi
    rw [e, Finset.card_insert_of_notMem hi]
    refine hsum.mono_scale (le_of_eq ?_)
    have hpow : θ ≤ (2 * (2 : ℝ) ^ s⁻¹) ^ I.card * θ :=
      le_mul_of_one_le_left hθ.le (one_le_pow₀ hc)
    rw [max_eq_right hpow, pow_succ]
    ring

/-- The triangle inequality at every exponent with the sum of the scales. -/
theorem osBound_add_le_sum {X Y : Ω → ℝ} {s θ₁ θ₂ : ℝ} (hX : OsBound P X s θ₁)
    (hY : OsBound P Y s θ₂) :
    OsBound P (fun ω => X ω + Y ω) s (2 * (2 : ℝ) ^ s⁻¹ * (θ₁ + θ₂)) := by
  refine (osBound_add_of_pos hX hY).mono_scale ?_
  have h1 := hX.scale_pos
  have h2 := hY.scale_pos
  have h3 : 0 ≤ (2 : ℝ) ^ s⁻¹ := Real.rpow_nonneg (by norm_num) _
  have h4 : max θ₁ θ₂ ≤ θ₁ + θ₂ := max_le (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h4 h3]

/-- Powers of a scaled variable: `0 ≤ X ≤ O_τ(θ)` gives `(X/r)^n ≤ O_{τ/n}((θ/r)^n)`. -/
theorem OsBound.div_pow {X : Ω → ℝ} {τ θ r : ℝ} (h : OsBound P X τ θ) (hX0 : ∀ ω, 0 ≤ X ω)
    (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    OsBound P (fun ω => (X ω / r) ^ n) (τ / n) ((θ / r) ^ n) := by
  have h1 := (h.const_mul (inv_pos.mpr hr)).rpow
    (fun ω => mul_nonneg (inv_nonneg.mpr hr.le) (hX0 ω)) (by exact_mod_cast hn : (0 : ℝ) < n)
  simpa only [Real.rpow_natCast, div_eq_inv_mul] using h1

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
  · replace hXr := not_le.mp hXr
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

/-! ## Fluctuations of the polarization vector -/

theorem euclideanSq_smul (t : ℝ) (v : Vec d) : euclideanSq (t • v) = t ^ 2 * euclideanSq v := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem euclideanNorm_smul (t : ℝ) (v : Vec d) : euclideanNorm (t • v) = |t| * euclideanNorm v := by
  rw [euclideanNorm, euclideanSq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]; rfl

theorem euclideanNorm_unitVector (i : Fin d) : euclideanNorm (unitVector i : Vec d) = 1 := by
  simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply]

section Fluctuation

variable {P : Measure (CoefficientField d Λ)}

/-- **Fluctuations of the polarization vector**: under `Fluc(s, α)` with constant `C_F`, the
squared distance of the polarization vector to its expectation is `O_{s/2}(C r^{-2α})` and has
mean at most `C' r^{-2α}`. -/
theorem polarizationVector_fluctuation [IsProbabilityMeasure P] {s α CF : ℝ} (hs0 : 0 < s)
    (hCF : 0 < CF)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J1Heat a z r p q) P ∧
      OsBound P (fun a => |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|) s (CF * r ^ (-α)))
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) {p q : Vec d} (hp : euclideanNorm p < 1)
    (hq : euclideanNorm q < 1) :
    OsBound P (fun a => euclideanSq (polarizationVector a y r p q -
        fun i => ∫ a', polarizationVector a' y r p q i ∂P)) (s / 2)
      ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * (16 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) ∧
    Integrable (fun a => euclideanSq (polarizationVector a y r p q -
        fun i => ∫ a', polarizationVector a' y r p q i ∂P)) P ∧
    ∫ a, euclideanSq (polarizationVector a y r p q -
        fun i => ∫ a', polarizationVector a' y r p q i ∂P) ∂P ≤
      d * (16 * (momentConstant (s / 2) * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  set θ : ℝ := CF * r ^ (-α) with hθ
  have hθ0 : 0 < θ := mul_pos hCF (Real.rpow_pos_of_pos hr0 _)
  set c : ℝ := 2 * (2 : ℝ) ^ s⁻¹ with hc
  have hc1 : 1 ≤ c := by
    have : 1 ≤ (2 : ℝ) ^ s⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hs0.le)
    linarith
  -- the three loads
  have hhalf : ∀ v : Vec d, euclideanNorm v < 2 → euclideanNorm ((1 / 2 : ℝ) • v) < 1 := by
    intro v hv
    rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hp' : euclideanNorm ((1 / 2 : ℝ) • p) < 1 := hhalf p (by linarith)
  have hq' : euclideanNorm ((1 / 2 : ℝ) • q) < 1 := hhalf q (by linarith)
  have hqe : ∀ i, euclideanNorm ((1 / 2 : ℝ) • (q + unitVector i)) < 1 := fun i =>
    hhalf _ (lt_of_le_of_lt (euclideanNorm_add_le _ _) (by rw [euclideanNorm_unitVector]; linarith))
  have he : ∀ i, euclideanNorm ((1 / 2 : ℝ) • (unitVector i : Vec d)) < 1 := fun i =>
    hhalf _ (by rw [euclideanNorm_unitVector]; norm_num)
  have h0 : euclideanNorm (0 : Vec d) < 1 := by simp [euclideanNorm, euclideanSq, dot]
  set J₁ : Fin d → CoefficientField d Λ → ℝ :=
    fun i a => J1Heat a y r ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • (q + unitVector i)) with hJ₁
  set J₂ : CoefficientField d Λ → ℝ := fun a => J1Heat a y r ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q)
    with hJ₂
  set J₃ : Fin d → CoefficientField d Λ → ℝ :=
    fun i a => J1Heat a y r 0 ((1 / 2 : ℝ) • unitVector i) with hJ₃
  have hF₁ := fun i => hF y r hr _ _ hp' (hqe i)
  have hF₂ := hF y r hr _ _ hp' hq'
  have hF₃ := fun i => hF y r hr _ _ h0 (he i)
  set T : Fin d → CoefficientField d Λ → ℝ := fun i a =>
    |J₁ i a - ∫ a', J₁ i a' ∂P| + |J₂ a - ∫ a', J₂ a' ∂P| + |J₃ i a - ∫ a', J₃ i a' ∂P| with hT
  have hT0 : ∀ i a, 0 ≤ T i a := fun i a => by positivity
  have hTos : ∀ i, OsBound P (T i) s (c ^ 2 * θ) := by
    intro i
    have h12 := osBound_add_of_pos (hF₁ i).2 hF₂.2
    have h123 := osBound_add_of_pos h12 (hF₃ i).2
    refine h123.mono_scale (le_of_eq ?_)
    have e1 : (2 : ℝ) * ((2 : ℝ) ^ s⁻¹ * max (CF * r ^ (-α)) (CF * r ^ (-α))) = c * θ := by
      rw [max_self, hc, hθ]; ring
    rw [e1, max_eq_left (le_mul_of_one_le_left hθ0.le hc1), hc]
    ring
  -- the polarization vector and its mean
  have hpol : ∀ (a : CoefficientField d Λ) (i : Fin d),
      polarizationVector a y r p q i = 4 * (J₁ i a - J₂ a - J₃ i a) := fun a i => rfl
  have hmean : ∀ i, ∫ a', polarizationVector a' y r p q i ∂P =
      4 * ((∫ a', J₁ i a' ∂P) - (∫ a', J₂ a' ∂P) - ∫ a', J₃ i a' ∂P) := by
    intro i
    have i12 : Integrable (fun a => J₁ i a - J₂ a) P := (hF₁ i).1.sub hF₂.1
    simp only [hpol]
    rw [integral_const_mul, integral_sub i12 (hF₃ i).1, integral_sub (hF₁ i).1 hF₂.1]
  have hcomp : ∀ (a : CoefficientField d Λ) (i : Fin d), (polarizationVector a y r p q -
      fun i => ∫ a', polarizationVector a' y r p q i ∂P) i ^ 2 ≤ 16 * T i a ^ 2 := by
    intro a i
    have hdiff : (polarizationVector a y r p q -
        fun i => ∫ a', polarizationVector a' y r p q i ∂P) i =
        4 * ((J₁ i a - ∫ a', J₁ i a' ∂P) - (J₂ a - ∫ a', J₂ a' ∂P) -
          (J₃ i a - ∫ a', J₃ i a' ∂P)) := by
      simp only [Pi.sub_apply]
      rw [hmean, hpol]
      ring
    rw [hdiff]
    have hb : |(J₁ i a - ∫ a', J₁ i a' ∂P) - (J₂ a - ∫ a', J₂ a' ∂P) -
        (J₃ i a - ∫ a', J₃ i a' ∂P)| ≤ T i a := by
      have h1 := abs_sub (J₁ i a - ∫ a', J₁ i a' ∂P - (J₂ a - ∫ a', J₂ a' ∂P))
        (J₃ i a - ∫ a', J₃ i a' ∂P)
      have h2 := abs_sub (J₁ i a - ∫ a', J₁ i a' ∂P) (J₂ a - ∫ a', J₂ a' ∂P)
      simp only [hT]
      linarith
    have hb2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
    nlinarith
  have hbound : ∀ a : CoefficientField d Λ, euclideanSq (polarizationVector a y r p q -
      fun i => ∫ a', polarizationVector a' y r p q i ∂P) ≤ ∑ i, 16 * T i a ^ 2 := by
    intro a
    simp only [euclideanSq, dot, ← sq]
    exact Finset.sum_le_sum fun i _ => hcomp a i
  -- measurability
  have hJm : ∀ p' q' : Vec d, Measurable fun a : CoefficientField d Λ => J1Heat a y r p' q' :=
    fun p' q' => (hmeasJ r p' q').comp (measurable_id.prodMk measurable_const)
  have hpolm : ∀ i, Measurable fun a : CoefficientField d Λ => polarizationVector a y r p q i :=
    fun i =>
    measurable_const.mul (((hJm _ _).sub (hJm _ _)).sub (hJm _ _))
  have hYm : Measurable fun a : CoefficientField d Λ => euclideanSq (polarizationVector a y r p q -
      fun i => ∫ a', polarizationVector a' y r p q i ∂P) := by
    simp only [euclideanSq, dot, Pi.sub_apply]
    exact Finset.measurable_sum _ fun i _ =>
      ((hpolm i).sub measurable_const).mul ((hpolm i).sub measurable_const)
  -- the stochastic bound
  have hsq : ∀ i, OsBound P (fun a => 16 * T i a ^ 2) (s / 2) (16 * (c ^ 2 * θ) ^ 2) := fun i =>
    ((hTos i).sq (hT0 i)).const_mul (by norm_num)
  have hsum := osBound_finset_sum_of_pos (P := P) Finset.univ (by positivity) (by positivity)
    fun i _ => hsq i
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hos := hsum.of_le hYm hbound
  -- the mean
  have hmom : ∀ i, Integrable (fun a => T i a ^ 2) P ∧
      ∫ a, T i a ^ 2 ∂P ≤ momentConstant (s / 2) * (c ^ 2 * θ) ^ 2 := fun i =>
    (hTos i).integral_sq_le (hT0 i)
  have hsumi : Integrable (fun a => ∑ i, 16 * T i a ^ 2) P :=
    integrable_finsetSum _ fun i _ => (hmom i).1.const_mul 16
  have hYi : Integrable (fun a => euclideanSq (polarizationVector a y r p q -
      fun i => ∫ a', polarizationVector a' y r p q i ∂P)) P :=
    hsumi.mono' hYm.aestronglyMeasurable (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg _)]
      exact hbound a)
  refine ⟨hos, hYi, ?_⟩
  calc ∫ a, euclideanSq (polarizationVector a y r p q -
        fun i => ∫ a', polarizationVector a' y r p q i ∂P) ∂P
      ≤ ∫ a, ∑ i, 16 * T i a ^ 2 ∂P :=
        integral_mono_ae hYi hsumi (Filter.Eventually.of_forall hbound)
    _ = ∑ i, 16 * ∫ a, T i a ^ 2 ∂P := by
        rw [integral_finsetSum _ fun i _ => (hmom i).1.const_mul 16]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ ≤ ∑ _i : Fin d, 16 * (momentConstant (s / 2) * (c ^ 2 * θ) ^ 2) :=
        Finset.sum_le_sum fun i _ => by linarith [(hmom i).2]
    _ = d * (16 * (momentConstant (s / 2) * (c ^ 2 * θ) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Fluctuation

end QSH
