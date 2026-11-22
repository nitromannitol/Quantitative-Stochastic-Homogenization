import QuantitativeStochasticHomogenization.Ch04.Sec03.HeatIdentityFromPathwise

/-!
# Decay of the expected commutator from Proposition 3.21

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the absolute convergence of the time integral in the heat identity (H).

At a center `y` and a scale `ρ ≥ 1`, on the event `X(·, y) ≤ ρ` of Proposition 3.21 the commutator
`|∫ Φ_{y,ρ} (a - ā)(eᵢ + ∇φ_{eᵢ})|` is at most `(1 + |ā|) C ρ^{-μ}`; on its complement it is bounded by
the Gaussian averages of `|G eᵢ|` and `|a G eᵢ|`, which the energy bound below the scale controls,
and the complement has indicator at most `(max(X, 1)/ρ)^μ`. The moments of `O_s` variables are
bounded in terms of `s` and the scale only (`OsBound.integral_le_of_nonneg`), so
`E |commutator| ≤ C' ρ^{-μ}` with `C'` independent of the center
(`expectedCommutatorDecay_of_rate`). With `heatIdentityBound_of_pathwise` this gives
`heatIdentityBound_of_pathwise_of_rate`.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

/-! ## Moments -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The mean of a nonnegative `X ≤ O_s(θ)`** is at most `θ (1 + 2 ⌈1/s⌉!)`, for every `s > 0`. -/
theorem OsBound.integral_le_of_nonneg [IsProbabilityMeasure P] {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P X s θ) (hX0 : ∀ ω, 0 ≤ X ω) :
    ∫ ω, X ω ∂P ≤ θ * (1 + 2 * (⌈s⁻¹⌉₊.factorial : ℝ)) := by
  have hXi := h.integrable_of_nonneg hX0
  obtain ⟨hXm, hs, hθ, hint⟩ := h
  set k := ⌈s⁻¹⌉₊
  have hEm := measurable_osIntegrand hXm s θ
  have hEi : Integrable (fun ω => Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) P := by
    refine ⟨hEm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact hint.trans_lt (by norm_num)
  have hE2 : ∫ ω, Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) ∂P ≤ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le)
      hEm.aestronglyMeasurable]
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P).toReal
        ≤ (2 : ℝ≥0∞).toReal := ENNReal.toReal_mono h2 hint
      _ = 2 := by norm_num
  have hB : Integrable (fun ω => θ * (1 + (k.factorial : ℝ) *
      Real.exp ((θ⁻¹ * max (X ω) 0) ^ s))) P :=
    ((integrable_const 1).add (hEi.const_mul _)).const_mul _
  have hpt : ∀ ω, X ω ≤ θ * (1 + (k.factorial : ℝ) * Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) := by
    intro ω
    have hy : 0 ≤ θ⁻¹ * max (X ω) 0 := mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_right _ _)
    have h1 := le_one_add_factorial_mul_exp_rpow hy hs
    have h2 : X ω = θ * (θ⁻¹ * max (X ω) 0) := by
      rw [max_eq_left (hX0 ω), ← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
    calc X ω = θ * (θ⁻¹ * max (X ω) 0) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hθ.le
  have hf : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
  calc ∫ ω, X ω ∂P
      ≤ ∫ ω, θ * (1 + (k.factorial : ℝ) * Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P :=
        integral_mono hXi hB hpt
    _ = θ * (1 + (k.factorial : ℝ) * ∫ ω, Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _) (hEi.const_mul _),
          integral_const_mul]
        simp
    _ ≤ θ * (1 + (k.factorial : ℝ) * 2) := by gcongr
    _ = θ * (1 + 2 * (k.factorial : ℝ)) := by ring

end Moments

/-! ## A crude operator bound -/

theorem abs_dot_mulVec_le_sum (M : Mat d) (ξ : Vec d) :
    |dot ξ (M.mulVec ξ)| ≤ (∑ i, ∑ j, |M i j|) * euclideanSq ξ := by
  have hb : ∀ i j, |ξ i * (M i j * ξ j)| ≤ |M i j| * euclideanSq ξ := by
    intro i j
    have h1 := abs_apply_le_euclideanNorm ξ i
    have h2 := abs_apply_le_euclideanNorm ξ j
    have h3 : |ξ i| * |ξ j| ≤ euclideanSq ξ := by
      rw [← euclideanNorm_sq]
      nlinarith [abs_nonneg (ξ i), abs_nonneg (ξ j), euclideanNorm_nonneg ξ]
    calc |ξ i * (M i j * ξ j)| = |M i j| * (|ξ i| * |ξ j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ |M i j| * euclideanSq ξ := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  calc |dot ξ (M.mulVec ξ)| = |∑ i, ∑ j, ξ i * (M i j * ξ j)| := by
        simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ ∑ i, |∑ j, ξ i * (M i j * ξ j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |ξ i * (M i j * ξ j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |M i j| * euclideanSq ξ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = (∑ i, ∑ j, |M i j|) * euclideanSq ξ := by simp only [Finset.sum_mul]

theorem euclideanNorm_homogenized_mulVec_le_sum {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (v : Vec d) :
    euclideanNorm (S.homogenized.mulVec v) ≤
      (∑ i, ∑ j, |S.homogenized i j|) * euclideanNorm v :=
  euclideanNorm_mulVec_le_of_abs_dot_le S.symmetric
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (abs_dot_mulVec_le_sum S.homogenized) v

/-! ## The expected commutator -/

theorem euclideanNorm_integral_heatKernel_smul_le {f : Vec d → Vec d} (z : Vec d) (r : ℝ) :
    euclideanNorm (∫ x, heatKernel z r x • f x) ≤
      ((d : ℝ) + 1) * ∫ x, heatKernel z r x * ‖f x‖ := by
  refine (euclideanNorm_le_dimension_mul_norm _).trans (mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (by positivity))
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [norm_smul, Real.norm_of_nonneg (heatKernel_nonneg z r x)]

theorem mul_le_quadratic_majorant (t s : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (1 + c * (1 + s)) * t ≤ (1 + c) + (1 + 2 * c) * t ^ 2 + c * s ^ 2 := by
  have h1 : 0 ≤ 1 - t + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have h2 : 0 ≤ t ^ 2 + s ^ 2 - s * t := by nlinarith [sq_nonneg (s - t)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c) h1, mul_nonneg hc h2]

section Commutator

variable {P : Measure (CoefficientField d Λ)}

/-- On the event of Proposition 3.21 the commutator is at most `(1 + |ā|) ε`. -/
theorem commutatorNorm_le_of_close (S : HomogenizationData P) (a : CoefficientField d Λ)
    (y : Vec d) (ρ : ℝ) (i : Fin d) {ε KD : ℝ}
    (hKDb : ∀ v : Vec d, euclideanNorm (S.homogenized.mulVec v) ≤ KD * euclideanNorm v)
    (hKD : 0 ≤ KD)
    (hg : euclideanNorm (gradientAverage S a y ρ (unitVector i) - unitVector i) ≤ ε)
    (hf : euclideanNorm (fluxAverage S a y ρ (unitVector i) -
      S.homogenized.mulVec (unitVector i)) ≤ ε) :
    commutatorNorm S a y ρ i ≤ (1 + KD) * ε := by
  unfold commutatorNorm
  have he : fluxAverage S a y ρ (unitVector i) -
      S.homogenized.mulVec (gradientAverage S a y ρ (unitVector i)) =
      (fluxAverage S a y ρ (unitVector i) - S.homogenized.mulVec (unitVector i)) -
        S.homogenized.mulVec (gradientAverage S a y ρ (unitVector i) - unitVector i) := by
    rw [Matrix.mulVec_sub]; abel
  rw [he]
  have h3 := euclideanNorm_sub_le
    (fluxAverage S a y ρ (unitVector i) - S.homogenized.mulVec (unitVector i))
    (S.homogenized.mulVec (gradientAverage S a y ρ (unitVector i) - unitVector i))
  have h5 := hKDb (gradientAverage S a y ρ (unitVector i) - unitVector i)
  have h6 := mul_le_mul_of_nonneg_left hg hKD
  linarith

/-- Below the scale the commutator is bounded through the energy bound. -/
theorem commutatorNorm_le_of_energy (hΛ : 0 ≤ Λ) (S : HomogenizationData P)
    (a : CoefficientField d Λ) (y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) (i : Fin d) {KD B : ℝ}
    (hKDb : ∀ v : Vec d, euclideanNorm (S.homogenized.mulVec v) ≤ KD * euclideanNorm v)
    (hKD : 0 ≤ KD)
    (hEi : Integrable fun x => heatKernel y ρ x * dot (correctedField S a (unitVector i) x)
      ((a x).mulVec (correctedField S a (unitVector i) x)))
    (hEb : ∫ x, heatKernel y ρ x * dot (correctedField S a (unitVector i) x)
      ((a x).mulVec (correctedField S a (unitVector i) x)) ≤ B * euclideanSq (unitVector i)) :
    commutatorNorm S a y ρ i ≤ ((d : ℝ) + 1) * (Λ + KD) / 2 * (1 + B) := by
  obtain ⟨⟨-, hG2⟩, ⟨-, hF2⟩⟩ := gradient_flux_envelope hΛ S (unitVector i) a y hρ hEi hEb
  rw [euclideanNorm_unitVector] at hG2 hF2
  have hgrad : euclideanNorm (gradientAverage S a y ρ (unitVector i)) ≤
      ((d : ℝ) + 1) * (1 / 2 * (1 + B)) := by
    rw [gradientAverage]
    refine (euclideanNorm_integral_heatKernel_smul_le y ρ).trans ?_
    exact mul_le_mul_of_nonneg_left (hG2.trans (le_of_eq (by ring))) (by positivity)
  have hflux : euclideanNorm (fluxAverage S a y ρ (unitVector i)) ≤
      ((d : ℝ) + 1) * (Λ * (1 / 2 * (1 + B))) := by
    rw [fluxAverage_eq_integral_fluxDensity]
    refine (euclideanNorm_integral_heatKernel_smul_le y ρ).trans ?_
    exact mul_le_mul_of_nonneg_left (hF2.trans (le_of_eq (by ring))) (by positivity)
  unfold commutatorNorm
  have h3 := euclideanNorm_sub_le (fluxAverage S a y ρ (unitVector i))
    (S.homogenized.mulVec (gradientAverage S a y ρ (unitVector i)))
  have h4 := hKDb (gradientAverage S a y ρ (unitVector i))
  have h5 := mul_le_mul_of_nonneg_left hgrad hKD
  have h6 : ((d : ℝ) + 1) * (Λ + KD) / 2 * (1 + B) = ((d : ℝ) + 1) * (Λ * (1 / 2 * (1 + B))) +
      KD * (((d : ℝ) + 1) * (1 / 2 * (1 + B))) := by ring
  linarith

end Commutator

/-- The pointwise majorant of the commutator at one center and one scale. -/
theorem commutatorNorm_le_majorant (hΛ : 0 ≤ Λ) {P : Measure (CoefficientField d Λ)}
    (S : HomogenizationData P) (a : CoefficientField d Λ) (y : Vec d) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (i : Fin d) {C μ CN KD Xr Xe : ℝ} (hC : 0 ≤ C) (hμ : 0 < μ) (hCN : 0 ≤ CN) (hXe : 0 ≤ Xe)
    (hKDb : ∀ v : Vec d, euclideanNorm (S.homogenized.mulVec v) ≤ KD * euclideanNorm v)
    (hKD : 0 ≤ KD)
    (hra : ∀ r : ℝ, 1 ≤ r → Xr ≤ r →
      GaussianAverageBounds a S.homogenized (correctedField S a) y r (C * r ^ (-μ)))
    (hEi : Integrable fun x => heatKernel y ρ x * dot (correctedField S a (unitVector i) x)
      ((a x).mulVec (correctedField S a (unitVector i) x)))
    (hEb : ∫ x, heatKernel y ρ x * dot (correctedField S a (unitVector i) x)
      ((a x).mulVec (correctedField S a (unitVector i) x)) ≤
        CN * (1 + (Xe / ρ) ^ d) * euclideanSq (unitVector i)) :
    commutatorNorm S a y ρ i ≤ (1 + KD) * C * ρ ^ (-μ) +
      ((d : ℝ) + 1) * (Λ + KD) / 2 * ρ ^ (-μ) * ((1 + CN) + (1 + 2 * CN) *
        (max Xr 1 ^ μ) ^ 2 + CN * (Xe ^ d) ^ 2) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hρμ : 0 < ρ ^ (-μ) := Real.rpow_pos_of_pos hρ0 _
  have hXm0 : 0 ≤ max Xr 1 := zero_le_one.trans (le_max_right _ _)
  have ht0 : 0 ≤ max Xr 1 ^ μ := Real.rpow_nonneg hXm0 _
  have hs0 : 0 ≤ Xe ^ d := pow_nonneg hXe d
  have hA1 : 0 ≤ ((d : ℝ) + 1) * (Λ + KD) / 2 := by positivity
  have hQ : 0 ≤ (1 + CN) + (1 + 2 * CN) * (max Xr 1 ^ μ) ^ 2 + CN * (Xe ^ d) ^ 2 := by positivity
  have hsecond : 0 ≤ ((d : ℝ) + 1) * (Λ + KD) / 2 * ρ ^ (-μ) *
      ((1 + CN) + (1 + 2 * CN) * (max Xr 1 ^ μ) ^ 2 + CN * (Xe ^ d) ^ 2) := by positivity
  by_cases hX : Xr ≤ ρ
  · have hb := hra ρ hρ hX (unitVector i)
    have hg := hb.2.2.2.1
    have hf := hb.2.2.2.2.1
    rw [euclideanNorm_unitVector, mul_one] at hg hf
    have h := commutatorNorm_le_of_close S a y ρ i hKDb hKD hg hf
    have : (1 + KD) * (C * ρ ^ (-μ)) = (1 + KD) * C * ρ ^ (-μ) := by ring
    linarith
  · replace hX := not_le.mp hX
    have hbad := commutatorNorm_le_of_energy hΛ S a y hρ0 i hKDb hKD hEi hEb
    have hge : 1 ≤ max Xr 1 / ρ := by
      rw [le_div_iff₀ hρ0, one_mul]
      exact hX.le.trans (le_max_left _ _)
    have hratio : 1 ≤ max Xr 1 ^ μ * ρ ^ (-μ) := by
      rw [Real.rpow_neg hρ0.le, ← div_eq_mul_inv, ← Real.div_rpow hXm0 hρ0.le]
      exact Real.one_le_rpow hge hμ.le
    have hB1 : 1 + CN * (1 + (Xe / ρ) ^ d) ≤ 1 + CN * (1 + Xe ^ d) := by
      have : (Xe / ρ) ^ d ≤ Xe ^ d := pow_le_pow_left₀ (div_nonneg hXe hρ0.le) (div_le_self hXe hρ) d
      have := mul_le_mul_of_nonneg_left this hCN
      linarith
    have hW0 : 0 ≤ 1 + CN * (1 + Xe ^ d) := by positivity
    have h7 : 1 + CN * (1 + (Xe / ρ) ^ d) ≤
        (1 + CN * (1 + Xe ^ d)) * (max Xr 1 ^ μ * ρ ^ (-μ)) :=
      hB1.trans (le_mul_of_one_le_right hW0 hratio)
    have hTU := mul_le_quadratic_majorant (max Xr 1 ^ μ) (Xe ^ d) hCN
    have h8 : ((d : ℝ) + 1) * (Λ + KD) / 2 * (1 + CN * (1 + (Xe / ρ) ^ d)) ≤
        ((d : ℝ) + 1) * (Λ + KD) / 2 * ρ ^ (-μ) *
          ((1 + CN) + (1 + 2 * CN) * (max Xr 1 ^ μ) ^ 2 + CN * (Xe ^ d) ^ 2) := by
      calc ((d : ℝ) + 1) * (Λ + KD) / 2 * (1 + CN * (1 + (Xe / ρ) ^ d))
          ≤ ((d : ℝ) + 1) * (Λ + KD) / 2 * ((1 + CN * (1 + Xe ^ d)) *
              (max Xr 1 ^ μ * ρ ^ (-μ))) := mul_le_mul_of_nonneg_left h7 hA1
        _ = ((d : ℝ) + 1) * (Λ + KD) / 2 * ρ ^ (-μ) *
              ((1 + CN * (1 + Xe ^ d)) * max Xr 1 ^ μ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hTU (by positivity)
    have hfirst : 0 ≤ (1 + KD) * C * ρ ^ (-μ) := by positivity
    linarith [hbad.trans h8]

theorem sq_rpow_eq_rpow_two_mul {x μ : ℝ} (hx : 0 ≤ x) : (x ^ μ) ^ 2 = x ^ (2 * μ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

theorem sq_pow_eq_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x ^ n) ^ 2 = x ^ (2 * (n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- **The expected commutator decays at the rate of Proposition 3.21**, uniformly in the
center. -/
theorem expectedCommutatorDecay_of_rate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {τ C μ : ℝ} (hτ : 0 < τ)
    (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) :
    ∃ C' : ℝ, 0 < C' ∧ ExpectedCommutatorDecay P S μ C' := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨1, one_pos, fun y ρ hρ i => i.elim0⟩
  obtain ⟨K, hK⟩ := exists_dot_mulVec_le S.homogenized
  obtain ⟨CN, hCN, hN⟩ := gaussianEnergyBound_of_rate S hK hτ hμ.le hrate
  obtain ⟨Xe, -, hXe1, hXeos, hXeb⟩ := hN
  obtain ⟨Xr, -, hXr⟩ := hrate
  have hC : 0 < C := (hXr 0).1.scale_pos
  obtain ⟨KD, hKD, hKDb⟩ : ∃ KD : ℝ, 0 ≤ KD ∧ ∀ v : Vec d,
      euclideanNorm (S.homogenized.mulVec v) ≤ KD * euclideanNorm v :=
    ⟨_, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _,
      euclideanNorm_homogenized_mulVec_le_sum S⟩
  have hXm0 : ∀ a y, 0 ≤ max (Xr a y) 1 := fun a y => zero_le_one.trans (le_max_right _ _)
  have hXe0 : ∀ a y, 0 ≤ Xe a y := fun a y => zero_le_one.trans (hXe1 a y)
  have h2μ : (0 : ℝ) < 2 * μ := by linarith
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by have : (0 : ℝ) < d := Nat.cast_pos.mpr hd; linarith
  obtain ⟨M1, hT2⟩ : ∃ M1 : ℝ, ∀ y, Integrable (fun a => (max (Xr a y) 1 ^ μ) ^ 2) P ∧
      ∫ a, (max (Xr a y) 1 ^ μ) ^ 2 ∂P ≤ M1 := by
    refine ⟨((2 : ℝ) ^ τ⁻¹ * max C (1 / Real.log 2 ^ τ⁻¹)) ^ (2 * μ) *
      (1 + 2 * (⌈(τ / (2 * μ))⁻¹⌉₊.factorial : ℝ)), fun y => ?_⟩
    have hXmos : OsBound P (fun a => max (Xr a y) 1) τ
        ((2 : ℝ) ^ τ⁻¹ * max C (1 / Real.log 2 ^ τ⁻¹)) :=
      osBound_max (hXr y).1 (osBound_of_le_const measurable_const hτ one_pos
        (Eventually.of_forall fun _ => le_rfl))
    have h := hXmos.rpow (fun a => hXm0 a y) h2μ
    have he : (fun a => (max (Xr a y) 1 ^ μ) ^ 2) = fun a => max (Xr a y) 1 ^ (2 * μ) :=
      funext fun a => sq_rpow_eq_rpow_two_mul (hXm0 a y)
    rw [he]
    exact ⟨h.integrable_of_nonneg fun a => Real.rpow_nonneg (hXm0 a y) _,
      h.integral_le_of_nonneg fun a => Real.rpow_nonneg (hXm0 a y) _⟩
  obtain ⟨M2, hU2⟩ : ∃ M2 : ℝ, ∀ y, Integrable (fun a => (Xe a y ^ d) ^ 2) P ∧
      ∫ a, (Xe a y ^ d) ^ 2 ∂P ≤ M2 := by
    refine ⟨CN ^ (2 * (d : ℝ)) * (1 + 2 * (⌈(τ / (2 * (d : ℝ)))⁻¹⌉₊.factorial : ℝ)),
      fun y => ?_⟩
    have h := (hXeos y).rpow (fun a => hXe0 a y) h2d
    have he : (fun a => (Xe a y ^ d) ^ 2) = fun a => Xe a y ^ (2 * (d : ℝ)) :=
      funext fun a => sq_pow_eq_rpow_two_mul (hXe0 a y) d
    rw [he]
    exact ⟨h.integrable_of_nonneg fun a => Real.rpow_nonneg (hXe0 a y) _,
      h.integral_le_of_nonneg fun a => Real.rpow_nonneg (hXe0 a y) _⟩
  have hM1 : 0 ≤ M1 := (integral_nonneg fun a => sq_nonneg _).trans (hT2 0).2
  have hM2 : 0 ≤ M2 := (integral_nonneg fun a => sq_nonneg _).trans (hU2 0).2
  obtain ⟨A1, hA1def⟩ : ∃ A1 : ℝ, A1 = ((d : ℝ) + 1) * (Λ + KD) / 2 := ⟨_, rfl⟩
  have hA1 : 0 ≤ A1 := by rw [hA1def]; positivity
  refine ⟨(1 + KD) * C + A1 * ((1 + CN) + (1 + 2 * CN) * M1 + CN * M2), by positivity,
    fun y ρ hρ i => ?_⟩
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hρμ : 0 < ρ ^ (-μ) := Real.rpow_pos_of_pos hρ0 _
  obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = (1 + KD) * C * ρ ^ (-μ) + A1 * ρ ^ (-μ) * (1 + CN) :=
    ⟨_, rfl⟩
  obtain ⟨c1, hc1def⟩ : ∃ c1 : ℝ, c1 = A1 * ρ ^ (-μ) * (1 + 2 * CN) := ⟨_, rfl⟩
  obtain ⟨c2, hc2def⟩ : ∃ c2 : ℝ, c2 = A1 * ρ ^ (-μ) * CN := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  have hc1 : 0 ≤ c1 := by rw [hc1def]; positivity
  have hc2 : 0 ≤ c2 := by rw [hc2def]; positivity
  have hpt : ∀ᵐ a ∂P, commutatorNorm S a y ρ i ≤
      c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2 := by
    filter_upwards [(hXr y).2, hXeb y] with a hra hea
    obtain ⟨h1, h2⟩ := hea ρ hρ (unitVector i)
    have h := commutatorNorm_le_majorant hΛ S a y hρ i hC.le hμ hCN.le (hXe0 a y) hKDb hKD hra
      h1 h2
    have he : (1 + KD) * C * ρ ^ (-μ) + ((d : ℝ) + 1) * (Λ + KD) / 2 * ρ ^ (-μ) *
        ((1 + CN) + (1 + 2 * CN) * (max (Xr a y) 1 ^ μ) ^ 2 + CN * (Xe a y ^ d) ^ 2) =
        c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2 := by
      rw [hc0def, hc1def, hc2def, hA1def]; ring
    linarith
  have hbndi : Integrable (fun a => c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2)
      P := ((integrable_const _).add ((hT2 y).1.const_mul _)).add ((hU2 y).1.const_mul _)
  have hbnd0 : ∀ a, 0 ≤ c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2 :=
    fun a => by positivity
  have hint : ∫ a, (c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2) ∂P ≤
      ((1 + KD) * C + A1 * ((1 + CN) + (1 + 2 * CN) * M1 + CN * M2)) * ρ ^ (-μ) := by
    have hI0 : Integrable (fun _ : CoefficientField d Λ => c0) P := integrable_const _
    have hI1 : Integrable (fun a => c1 * (max (Xr a y) 1 ^ μ) ^ 2) P := (hT2 y).1.const_mul _
    have hI2 : Integrable (fun a => c2 * (Xe a y ^ d) ^ 2) P := (hU2 y).1.const_mul _
    have hI01 : Integrable (fun a => c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2) P := hI0.add hI1
    rw [integral_add hI01 hI2, integral_add hI0 hI1, integral_const_mul,
      integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    have h9 := mul_le_mul_of_nonneg_left (hT2 y).2 hc1
    have h10 := mul_le_mul_of_nonneg_left (hU2 y).2 hc2
    have h11 : ((1 + KD) * C + A1 * ((1 + CN) + (1 + 2 * CN) * M1 + CN * M2)) * ρ ^ (-μ) =
        c0 + c1 * M1 + c2 * M2 := by rw [hc0def, hc1def, hc2def]; ring
    linarith
  calc ∫⁻ a, ENNReal.ofReal (commutatorNorm S a y ρ i) ∂P
      ≤ ∫⁻ a, ENNReal.ofReal (c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2) ∂P :=
        lintegral_mono_ae (by
          filter_upwards [hpt] with a ha
          exact ENNReal.ofReal_le_ofReal ha)
    _ = ENNReal.ofReal (∫ a, (c0 + c1 * (max (Xr a y) 1 ^ μ) ^ 2 + c2 * (Xe a y ^ d) ^ 2) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hbndi (Eventually.of_forall hbnd0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hint

/-- **`HeatIdentityBound` from the lower-integral bound and Proposition 3.21.** -/
theorem heatIdentityBound_of_pathwise_of_rate {P : Measure (CoefficientField d Λ)}
    [IsProbabilityMeasure P] (S : HomogenizationData P) (hΛ : 0 ≤ Λ) {k : ℝ → ℝ → Vec d → ℝ}
    {Ck : ℝ} (hkm : ∀ r, Measurable (Function.uncurry (k r))) (hk0 : ∀ r u x, 0 < k r u x)
    (hki : ∀ r u, 1 ≤ u → Integrable (k r u) ∧ ∫ x, k r u x ≤ Ck * u⁻¹)
    (hpath : HeatPathwiseBound P S k) {τ C μ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ)
    (hrate : GaussianCorrectorRate P S τ C μ) : HeatIdentityBound P S Ck := by
  obtain ⟨C', hC', hdec⟩ := expectedCommutatorDecay_of_rate S hΛ hτ hμ hrate
  exact heatIdentityBound_of_pathwise S hkm hk0 hki hpath hμ hC'.le hdec

end QSH
