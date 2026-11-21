import QuantitativeStochasticHomogenization.Ch04.Sec03.TrialGapGoodEvent

/-!
# Pointwise bounds on the trial gap

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the deterministic bounds of the proof of Proposition 4.10 used here.

* `polarizationVector`: the vector with entries
  `4 (J₁(p/2, (q + eᵢ)/2) - J₁(p/2, q/2) - J₁(0, eᵢ/2))`, defined for every coefficient field;
  at a good scale it is the averaged gradient of the maximizer
  (`integral_maximizer_eq_polarizationVector`), by (4.16) and the homogeneity of the maximizing
  slope.
* `trialGap_le_polarization`: at a good scale the gap to the trial at a slope `k` is at most
  `(8/9)(Λ + 1/2) |∫ Φ_{y,r} G k - polarizationVector|²`.
* `j1Functional_ge`: the functional of (4.8) at `g` is at least
  `-(∫ Ψ g·ag + Λ|p|² + |q|²)` for a nonnegative mask of mass one; hence at every scale the gap to
  the trial is at most `2(Λ|p|² + |q|²) + ∫ Φ_{y,r} G k·aG k` (`trialGap_le_energy`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## Homogeneity of the maximizing slope -/

theorem loadVector_smul (a : CoefficientField d Λ) (mask : Vec d → ℝ) (W : Fin d → Vec d → Vec d)
    (t : ℝ) (p q : Vec d) :
    loadVector a mask W (t • p) (t • q) = t • loadVector a mask W p q := by
  funext j
  simp only [loadVector, Pi.smul_apply, smul_eq_mul, dot_eq_dotProduct, smul_dotProduct]
  ring

theorem maximizerSlope_smul (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (W : Fin d → Vec d → Vec d) (t : ℝ) (p q : Vec d) :
    maximizerSlope a mask W (t • p) (t • q) = t • maximizerSlope a mask W p q := by
  simp only [maximizerSlope, loadVector_smul, Matrix.mulVec_smul]

theorem fieldOf_smul (W : Fin d → Vec d → Vec d) (t : ℝ) (ξ x : Vec d) :
    fieldOf W (t • ξ) x = t • fieldOf W ξ x := by
  simp only [fieldOf, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

/-! ## The polarization vector -/

/-- The vector `4 (J₁(p/2, (q + eᵢ)/2) - J₁(p/2, q/2) - J₁(0, eᵢ/2))`, `i = 1, …, d`. -/
def polarizationVector (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (p q : Vec d) : Vec d :=
  fun i => 4 * (J1Heat a y r ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • (q + unitVector i)) -
    J1Heat a y r ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) - J1Heat a y r 0 ((1 / 2 : ℝ) • unitVector i))

section Polarization

variable {P : Measure (CoefficientField d Λ)}

/-- At a good scale, the polarization vector is the averaged gradient of the maximizer. -/
theorem integral_maximizer_eq_polarizationVector (S : HomogenizationData P)
    (a : CoefficientField d Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) (r : ℝ) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (p q : Vec d) :
    (∫ x, heatKernel y r x • correctedField S a
      (maximizerSlope a (heatKernel y r) (correctedCoordinate S a) p q) x) =
      polarizationVector a y r p q := by
  set W := correctedCoordinate S a with hWdef
  set mask := heatKernel y r with hmask
  have hW := integrableFamily_of_averages S a y r ε havg
  set A := energyMatrix a mask W with hAdef
  -- the energy matrix is positive definite
  have hAξ : ∀ ξ, (1 - 2 * ε) * euclideanSq ξ ≤ dot ξ (A.mulVec ξ) := by
    intro ξ
    rw [dot_energyMatrix_eq_integral a mask W hW ξ]
    have h0 : |(∫ x, mask x * dot (fieldOf W ξ x) ((a x).mulVec (fieldOf W ξ x))) -
        dot ξ (S.homogenized.mulVec ξ)| ≤ 2 * ε * euclideanNorm ξ ^ 2 := (havg ξ).2.2.2.2.2
    have h := abs_le.mp h0
    have h1 := (hA ξ).1
    rw [euclideanNorm_sq] at h
    nlinarith [h.1]
  have hpos : ∀ ξ, ξ ≠ 0 → 0 < dot ξ (A.mulVec ξ) := by
    intro ξ hξ
    have h1 := hAξ ξ
    have h2 : 0 < euclideanSq ξ := by
      rcases (euclideanSq_nonneg ξ).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_zero_of_euclideanSq_le_zero h.symm.le) hξ
    nlinarith
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hpos v hv0
    rw [hv, dot_eq_dotProduct, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hpsd : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ) := fun ξ =>
    (mul_nonneg (by linarith) (euclideanSq_nonneg ξ)).trans (hAξ ξ)
  funext i
  have hpol := dot_integral_fieldOf_maximizer a mask W hW hspan.1 hspan.2 hdet hpsd
    ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) ((1 / 2 : ℝ) • unitVector i)
  rw [maximizerSlope_smul] at hpol
  have hlin : (∫ x, mask x • fieldOf W ((1 / 2 : ℝ) • maximizerSlope a mask W p q) x) =
      (1 / 2 : ℝ) • ∫ x, mask x • fieldOf W (maximizerSlope a mask W p q) x := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fieldOf_smul, smul_comm (mask x)]
  rw [hlin, ← smul_add] at hpol
  have hdot : dot ((1 / 2 : ℝ) • unitVector i)
      ((1 / 2 : ℝ) • ∫ x, mask x • fieldOf W (maximizerSlope a mask W p q) x) =
      (1 / 4 : ℝ) * (∫ x, mask x • fieldOf W (maximizerSlope a mask W p q) x) i := by
    simp only [dot_eq_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, unitVector,
      single_dotProduct, one_mul]
    ring
  rw [hdot] at hpol
  simp only [polarizationVector, J1Heat]
  show (∫ x, mask x • fieldOf W (maximizerSlope a mask W p q) x) i = _
  linarith

/-- **The trial gap at a good scale and the polarization vector.** -/
theorem trialGap_le_polarization (S : HomogenizationData P) (a : CoefficientField d Λ)
    (hΛ : 0 ≤ Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : GradientsOfA1AreCorrected S a) (y : Vec d) (r : ℝ) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (havg : GaussianAverageBounds a S.homogenized (correctedField S a) y r ε) (p q k : Vec d) :
    J1Heat a y r p q - j1Functional a (heatKernel y r) p q (correctedField S a k) ≤
      8 / 9 * (Λ + 1 / 2) * euclideanNorm ((∫ x, heatKernel y r x • correctedField S a k x) -
        polarizationVector a y r p q) ^ 2 := by
  have h := trialGap_le_of_averages S a hΛ hA hspan y r hε havg p q k
  rwa [integral_maximizer_eq_polarizationVector S a hA hspan y r hε havg p q] at h

end Polarization

/-! ## The trial gap at every scale -/

theorem neg_le_j1Integrand (a : CoefficientField d Λ) (p q g x : Vec d) :
    -(dot g ((a x).mulVec g) + Λ * euclideanSq p + euclideanSq q) ≤
      -(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g) + dot q g := by
  have hsymm := a.symmetric x
  have hpos : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ) := fun ξ => (a.elliptic x ξ).1
  have hcs := dot_mulVec_sq_le hsymm hpos p g
  have hg := hpos g
  have hp := (a.elliptic x p).2
  have hp0 := (euclideanSq_nonneg p).trans (hpos p)
  have hg0 := euclideanSq_nonneg g
  have hq := abs_dot_le q g
  rw [euclideanNorm, euclideanNorm] at hq
  set X := dot g ((a x).mulVec g)
  set y := dot p ((a x).mulVec g)
  set u := dot p ((a x).mulVec p)
  have h1 : y ≤ X / 4 + u := by nlinarith [sq_nonneg (X / 4 - u), sq_nonneg (y - (X / 4 + u))]
  have hsq := Real.sq_sqrt (euclideanSq_nonneg g)
  have hsq' := Real.sq_sqrt (euclideanSq_nonneg q)
  have hs0 := Real.sqrt_nonneg (euclideanSq g)
  have hs0' := Real.sqrt_nonneg (euclideanSq q)
  have h2 : -dot q g ≤ X / 4 + euclideanSq q := by
    have := (neg_le_abs (dot q g)).trans hq
    nlinarith [sq_nonneg (Real.sqrt (euclideanSq g) / 2 - Real.sqrt (euclideanSq q))]
  linarith

/-- The functional of (4.8) is at least `-(∫ Ψ g·ag + Λ|p|² + |q|²)` for a nonnegative integrable
mask of mass one. -/
theorem j1Functional_ge (a : CoefficientField d Λ) {mask : Vec d → ℝ} (hmask0 : ∀ x, 0 ≤ mask x)
    (hmask : Integrable mask) (hmass : ∫ x, mask x = 1) (p q : Vec d) (g : Vec d → Vec d)
    (hE : Integrable fun x => mask x * dot (g x) ((a x).mulVec (g x))) :
    -((∫ x, mask x * dot (g x) ((a x).mulVec (g x))) + Λ * euclideanSq p + euclideanSq q) ≤
      j1Functional a mask p q g := by
  have hK : 0 ≤ Λ * euclideanSq p + euclideanSq q :=
    add_nonneg (euclideanSq_mul_nonneg_of_coefficientField a p) (euclideanSq_nonneg q)
  have hE0 : 0 ≤ ∫ x, mask x * dot (g x) ((a x).mulVec (g x)) :=
    integral_nonneg fun x => mul_nonneg (hmask0 x)
      ((euclideanSq_nonneg _).trans (a.elliptic x (g x)).1)
  unfold j1Functional
  by_cases hint : Integrable (fun x => mask x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x)))
  · have hlow : Integrable fun x => -(mask x * dot (g x) ((a x).mulVec (g x)) +
        mask x * (Λ * euclideanSq p + euclideanSq q)) :=
      (hE.add (hmask.mul_const _)).neg
    calc -((∫ x, mask x * dot (g x) ((a x).mulVec (g x))) + Λ * euclideanSq p + euclideanSq q)
        = ∫ x, -(mask x * dot (g x) ((a x).mulVec (g x)) +
            mask x * (Λ * euclideanSq p + euclideanSq q)) := by
          rw [integral_neg, integral_add hE (hmask.mul_const _), integral_mul_const, hmass]
          ring
      _ ≤ _ := integral_mono_ae hlow hint (Filter.Eventually.of_forall fun x => by
          have h := mul_le_mul_of_nonneg_left (neg_le_j1Integrand a p q (g x) x) (hmask0 x)
          linarith)
  · rw [integral_undef hint]
    linarith

/-- **The trial gap at every scale**: `J₁(Φ_{y,r}, p, q) - L(k) ≤ 2(Λ|p|² + |q|²) + ∫ Φ_{y,r} Gk·aGk`
whenever the energy density of the trial is integrable. -/
theorem trialGap_le_energy (a : CoefficientField d Λ) (y : Vec d) {r : ℝ} (hr : 0 < r)
    (p q : Vec d) (g : Vec d → Vec d)
    (hE : Integrable fun x => heatKernel y r x * dot (g x) ((a x).mulVec (g x))) :
    J1Heat a y r p q - j1Functional a (heatKernel y r) p q g ≤
      2 * (Λ * euclideanSq p + euclideanSq q) +
        ∫ x, heatKernel y r x * dot (g x) ((a x).mulVec (g x)) := by
  have h1 := (J1Heat_nonneg_le a y hr p q).2
  have h2 := j1Functional_ge a (heatKernel_nonneg y r) (integrable_heatKernel y hr)
    (integral_heatKernel y hr) p q g hE
  linarith

end QSH
