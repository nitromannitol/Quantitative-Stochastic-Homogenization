import QuantitativeStochasticHomogenization.Ch04.Sec03.Proposition410Linear

/-!
# The expectations of the Gaussian averages of the corrected fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) used in the route of Proposition 4.10 here (in the book, Lemma 3.23
and (3.92)–(3.93)).

`ExpectedAveragesEstimate P S β`: the expectations of the `Φ_{z,r}`-averages of the corrected field
`G ξ`, of its flux and of its energy density are within `C |ξ| r^{-β}`, `C |ξ| r^{-β}` and
`C |ξ|² r^{-β}` of `ξ`, `āξ` and `ξ·āξ`, with the integrability of the three averages.

`trialObjectiveExpectation_of_expectedAverages`: these give the expectation of the trial at
deterministic slopes (`TrialObjectiveExpectation`), when the bounds (3.101)–(3.103) hold almost
surely at some error (so that the functional of (4.8) splits into the three averages).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

section Expected

variable {P : Measure (CoefficientField d Λ)}

/-- **The expectations of the Gaussian averages**: for `z`, `r ≥ 1` and every slope `ξ`, the three
averages are integrable and their expectations are within `C |ξ| r^{-β}`, `C |ξ| r^{-β}` and
`C |ξ|² r^{-β}` of `ξ`, `āξ` and `ξ·āξ`. -/
def ExpectedAveragesEstimate (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
    Integrable (fun a => ∫ x, heatKernel z r x • correctedField S a ξ x) P ∧
    Integrable (fun a => ∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) P ∧
    Integrable (fun a => ∫ x, heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) P ∧
    euclideanNorm ((∫ a, (∫ x, heatKernel z r x • correctedField S a ξ x) ∂P) - ξ) ≤
      C * euclideanNorm ξ * r ^ (-β) ∧
    euclideanNorm ((∫ a, (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) ∂P) -
      S.homogenized.mulVec ξ) ≤ C * euclideanNorm ξ * r ^ (-β) ∧
    |(∫ a, (∫ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ∂P) -
      dot ξ (S.homogenized.mulVec ξ)| ≤ C * euclideanSq ξ * r ^ (-β)

/-- Almost surely, at every center and scale `r ≥ 1`, the three averages of the corrected fields
exist. -/
def AveragesIntegrable (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P) : Prop :=
  ∀ᵐ a ∂P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ ξ : Vec d,
    Integrable (fun x => heatKernel z r x • correctedField S a ξ x) ∧
    Integrable (fun x => heatKernel z r x • (a x).mulVec (correctedField S a ξ x)) ∧
    Integrable (fun x => heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)))

/-- The functional of (4.8) at an integrable gradient field splits into its three averages. -/
theorem j1Functional_eq_averages (a : CoefficientField d Λ) (mask : Vec d → ℝ) (p q : Vec d)
    (g : Vec d → Vec d) (hgrad : Integrable fun x => mask x • g x)
    (hflux : Integrable fun x => mask x • (a x).mulVec (g x))
    (henergy : Integrable fun x => mask x * dot (g x) ((a x).mulVec (g x))) :
    j1Functional a mask p q g =
      -(1 / 2 : ℝ) * (∫ x, mask x * dot (g x) ((a x).mulVec (g x))) -
        dot p (∫ x, mask x • (a x).mulVec (g x)) + dot q (∫ x, mask x • g x) := by
  have hfl := integrable_dot_left p hflux
  have hgr := integrable_dot_left q hgrad
  have hfun : (fun x => mask x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x))) = fun x =>
        -(1 / 2 : ℝ) * (mask x * dot (g x) ((a x).mulVec (g x))) -
          dot p (mask x • (a x).mulVec (g x)) + dot q (mask x • g x) := by
    funext x
    simp only [dot_eq_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hI : Integrable (fun x => -(1 / 2 : ℝ) * (mask x * dot (g x) ((a x).mulVec (g x))) -
      dot p (mask x • (a x).mulVec (g x))) := (henergy.const_mul _).sub hfl
  unfold j1Functional
  rw [hfun, integral_add hI hgr, integral_sub (henergy.const_mul _) hfl, integral_const_mul,
    dot_integral p hflux, dot_integral q hgrad]

/-- **The expectation of the trial at deterministic slopes from the expected averages.** -/
theorem trialObjectiveExpectation_of_expectedAverages [IsProbabilityMeasure P]
    (S : HomogenizationData P) (hint : AveragesIntegrable P S) {β : ℝ}
    (hE : ExpectedAveragesEstimate P S β) : TrialObjectiveExpectation P S β := by
  obtain ⟨C, hC, hE⟩ := hE
  refine ⟨2 * C, by positivity, fun z r hr p q hp hq k => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨hi1, hi2, hi3, hb1, hb2, hb3⟩ := hE z r hr k
  have hsplit : (fun a => j1Functional a (heatKernel z r) p q (correctedField S a k)) =ᵐ[P]
      fun a => -(1 / 2 : ℝ) * (∫ x, heatKernel z r x *
          dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x))) -
        dot p (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a k x)) +
        dot q (∫ x, heatKernel z r x • correctedField S a k x) := by
    filter_upwards [hint] with a ha
    obtain ⟨h1, h2, h3⟩ := ha z r hr k
    exact j1Functional_eq_averages a _ p q _ h1 h2 h3
  have hI1 : Integrable (fun a => -(1 / 2 : ℝ) * (∫ x, heatKernel z r x *
      dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x)))) P := hi3.const_mul _
  have hI2 : Integrable (fun a =>
      dot p (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a k x))) P :=
    integrable_dot_left p hi2
  have hI3 : Integrable (fun a => dot q (∫ x, heatKernel z r x • correctedField S a k x)) P :=
    integrable_dot_left q hi1
  have hI : Integrable (fun a => -(1 / 2 : ℝ) * (∫ x, heatKernel z r x *
      dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x))) -
        dot p (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a k x))) P := hI1.sub hI2
  refine ⟨(hI.add hI3).congr hsplit.symm, ?_⟩
  rw [integral_congr_ae hsplit, integral_add hI hI3, integral_sub hI1 hI2, integral_const_mul,
    ← dot_integral p hi2, ← dot_integral q hi1]
  have hdiff : -(1 / 2 : ℝ) * (∫ a, (∫ x, heatKernel z r x *
        dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x))) ∂P) -
      dot p (∫ a, (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a k x)) ∂P) +
      dot q (∫ a, (∫ x, heatKernel z r x • correctedField S a k x) ∂P) -
      homogenizedJ1Objective S.homogenized p q k =
      -(1 / 2 : ℝ) * ((∫ a, (∫ x, heatKernel z r x *
        dot (correctedField S a k x) ((a x).mulVec (correctedField S a k x))) ∂P) -
          dot k (S.homogenized.mulVec k)) -
      dot p ((∫ a, (∫ x, heatKernel z r x • (a x).mulVec (correctedField S a k x)) ∂P) -
        S.homogenized.mulVec k) +
      dot q ((∫ a, (∫ x, heatKernel z r x • correctedField S a k x) ∂P) - k) := by
    simp only [homogenizedJ1Objective, dot_eq_dotProduct, dotProduct_sub]
    ring
  rw [hdiff]
  have hρ : 0 ≤ r ^ (-β) := Real.rpow_nonneg hr0.le _
  have hp1 := euclideanNorm_nonneg p
  have hq1 := euclideanNorm_nonneg q
  have hk1 := euclideanNorm_nonneg k
  have h2 := (abs_dot_le p _).trans (mul_le_mul_of_nonneg_left hb2 hp1)
  have h1 := (abs_dot_le q _).trans (mul_le_mul_of_nonneg_left hb1 hq1)
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h3l, h3u⟩ := abs_le.mp hb3
  -- `|ξ| ≤ (1 + |ξ|²)/2` and `|p|, |q| < 1`
  have hk2 : euclideanNorm k ≤ (1 + euclideanSq k) / 2 := by
    rw [← euclideanNorm_sq]; nlinarith [sq_nonneg (euclideanNorm k - 1)]
  have hk0 := euclideanSq_nonneg k
  have e1 : euclideanNorm p * (C * euclideanNorm k * r ^ (-β)) ≤
      C * ((1 + euclideanSq k) / 2) * r ^ (-β) := by
    have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hC.le hρ)
    nlinarith [mul_nonneg (mul_nonneg hC.le hk1) hρ]
  have e2 : euclideanNorm q * (C * euclideanNorm k * r ^ (-β)) ≤
      C * ((1 + euclideanSq k) / 2) * r ^ (-β) := by
    have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hC.le hρ)
    nlinarith [mul_nonneg (mul_nonneg hC.le hk1) hρ]
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (mul_nonneg hC.le hk0) hρ]

end Expected

end QSH
