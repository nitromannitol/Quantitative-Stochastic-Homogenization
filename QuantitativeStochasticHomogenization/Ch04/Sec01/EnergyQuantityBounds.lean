import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43

/-!
# Deterministic bounds on `J₁`

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.1, the bounds (4.15) and (4.22) of Lemma 4.4: for a nonnegative mask `Ψ` of mass at most
one,
`0 ≤ J₁(Ψ, p, q) ≤ Λ|p|² + |q|²` for every coefficient field (`J1_nonneg`, `J1_le`).

The lower bound is the value `0` of the functional of (4.8) at the zero element of `A₁`. The upper
bound is pointwise: with `X = ∇w·a∇w ≥ |∇w|²`, the Cauchy–Schwarz inequality for the form of `a`
gives `|p·a∇w| ≤ X/4 + p·ap` and `|q·∇w| ≤ X/4 + |q|²`. It holds for every coefficient field, without
the structure of `A₁` given by Theorem 3.8, and with the constant `Λ|p|² + |q|²` in place of
`C(|p|² + |q|²)`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-! ## The zero element of `A₁` -/

/-- The zero function, an element of `A₁`. -/
def zeroHarmonicA1 (a : CoefficientField d Λ) : HarmonicA1 a where
  potential := fun _ => 0
  grad := fun _ => 0
  weak_gradient := fun _ => ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun φ _ => by
    simp⟩
  local_energy := fun R _ => ⟨MemLp.zero, by simp [euclideanNorm, euclideanSq, dot]⟩
  harmonic := by
    refine ⟨fun i => ?_, locallyIntegrableOn_zero, fun φ _ => ?_⟩
    · simpa [Matrix.mulVec_zero] using
        (locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ : Vec d => (0 : ℝ)) Set.univ volume)
    · simp [Matrix.mulVec_zero, dot]
  growth := by simp

theorem j1Functional_zeroHarmonicA1 (a : CoefficientField d Λ) (mask : Vec d → ℝ)
    (p q : Vec d) : j1Functional a mask p q (zeroHarmonicA1 a).grad = 0 := by
  simp [j1Functional, zeroHarmonicA1, dot, Matrix.mulVec_zero]

/-! ## Cauchy–Schwarz for the form of a coefficient matrix -/

/-- `(p·Mg)² ≤ (p·Mp)(g·Mg)` for a symmetric `M` with `|ξ|² ≤ ξ·Mξ`. -/
theorem dot_mulVec_sq_le {M : Mat d} (hsymm : M.transpose = M)
    (hpos : ∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (M.mulVec ξ)) (p g : Vec d) :
    dot p (M.mulVec g) ^ 2 ≤ dot p (M.mulVec p) * dot g (M.mulVec g) := by
  have hexp : dot (dot g (M.mulVec g) • p - dot p (M.mulVec g) • g)
      (M.mulVec (dot g (M.mulVec g) • p - dot p (M.mulVec g) • g)) =
      dot g (M.mulVec g) * (dot g (M.mulVec g) * dot p (M.mulVec p) - dot p (M.mulVec g) ^ 2) := by
    have hc := dot_mulVec_comm hsymm g p
    simp only [dot_eq_dotProduct] at hc ⊢
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hc]
    ring
  have hv := (euclideanSq_nonneg _).trans
    (hpos (dot g (M.mulVec g) • p - dot p (M.mulVec g) • g))
  rw [hexp] at hv
  have hX0 : 0 ≤ dot g (M.mulVec g) := (euclideanSq_nonneg g).trans (hpos g)
  rcases hX0.lt_or_eq with hX | hX
  · have := (mul_nonneg_iff_of_pos_left hX).mp hv
    nlinarith
  · have hg : g = 0 := eq_zero_of_euclideanSq_le_zero (by rw [hX]; exact hpos g)
    subst hg
    simp [dot, Matrix.mulVec_zero]

/-! ## The bounds (4.15) and (4.22) -/

/-- The integrand of (4.8) is at most `Λ|p|² + |q|²` pointwise. -/
theorem j1Integrand_le (a : CoefficientField d Λ) (p q g x : Vec d) :
    -(1 / 2 : ℝ) * dot g ((a x).mulVec g) - dot p ((a x).mulVec g) + dot q g ≤
      Λ * euclideanSq p + euclideanSq q := by
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
  have h2 : dot q g ≤ X / 4 + euclideanSq q := by
    have := (le_abs_self (dot q g)).trans hq
    nlinarith [sq_nonneg (Real.sqrt (euclideanSq g) / 2 - Real.sqrt (euclideanSq q))]
  have h3 : -y ≤ X / 4 + u := by
    nlinarith [sq_nonneg (X / 4 - u), sq_nonneg (y + (X / 4 + u))]
  linarith

theorem euclideanSq_mul_nonneg_of_coefficientField (a : CoefficientField d Λ) (p : Vec d) :
    0 ≤ Λ * euclideanSq p :=
  ((euclideanSq_nonneg p).trans (a.elliptic 0 p).1).trans (a.elliptic 0 p).2

/-- Every value of the functional of (4.8) is at most `Λ|p|² + |q|²` for a nonnegative integrable
mask of mass at most one. -/
theorem j1Functional_le (a : CoefficientField d Λ) {mask : Vec d → ℝ} (hmask0 : ∀ x, 0 ≤ mask x)
    (hmask : Integrable mask) (hmass : ∫ x, mask x ≤ 1) (p q : Vec d) (g : Vec d → Vec d) :
    j1Functional a mask p q g ≤ Λ * euclideanSq p + euclideanSq q := by
  have hK : 0 ≤ Λ * euclideanSq p + euclideanSq q :=
    add_nonneg (euclideanSq_mul_nonneg_of_coefficientField a p) (euclideanSq_nonneg q)
  unfold j1Functional
  by_cases hint : Integrable (fun x => mask x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
      dot p ((a x).mulVec (g x)) + dot q (g x)))
  · calc (∫ x, mask x * (-(1 / 2 : ℝ) * dot (g x) ((a x).mulVec (g x)) -
          dot p ((a x).mulVec (g x)) + dot q (g x)))
        ≤ ∫ x, mask x * (Λ * euclideanSq p + euclideanSq q) :=
          integral_mono_ae hint (hmask.mul_const _) (Filter.Eventually.of_forall fun x =>
            mul_le_mul_of_nonneg_left (j1Integrand_le a p q (g x) x) (hmask0 x))
      _ = (∫ x, mask x) * (Λ * euclideanSq p + euclideanSq q) := integral_mul_const _ _
      _ ≤ 1 * (Λ * euclideanSq p + euclideanSq q) := mul_le_mul_of_nonneg_right hmass hK
      _ = Λ * euclideanSq p + euclideanSq q := one_mul _
  · rw [integral_undef hint]
    exact hK

/-- **(4.15), (4.22)**: `J₁(Ψ, p, q) ≤ Λ|p|² + |q|²` for a nonnegative integrable mask of mass at
most one. -/
theorem J1_le (a : CoefficientField d Λ) {mask : Vec d → ℝ} (hmask0 : ∀ x, 0 ≤ mask x)
    (hmask : Integrable mask) (hmass : ∫ x, mask x ≤ 1) (p q : Vec d) :
    J1 a mask p q ≤ Λ * euclideanSq p + euclideanSq q := by
  rw [J1_eq_sSup_j1Functional]
  refine csSup_le ⟨0, zeroHarmonicA1 a, (j1Functional_zeroHarmonicA1 a mask p q).symm⟩ ?_
  rintro e ⟨w, rfl⟩
  exact j1Functional_le a hmask0 hmask hmass p q w.grad

/-- **`J₁ ≥ 0`**, from the zero element of `A₁`, for a nonnegative integrable mask of mass at most
one. -/
theorem J1_nonneg (a : CoefficientField d Λ) {mask : Vec d → ℝ} (hmask0 : ∀ x, 0 ≤ mask x)
    (hmask : Integrable mask) (hmass : ∫ x, mask x ≤ 1) (p q : Vec d) :
    0 ≤ J1 a mask p q := by
  rw [J1_eq_sSup_j1Functional]
  refine le_csSup ⟨Λ * euclideanSq p + euclideanSq q, ?_⟩
    ⟨zeroHarmonicA1 a, (j1Functional_zeroHarmonicA1 a mask p q).symm⟩
  rintro e ⟨w, rfl⟩
  exact j1Functional_le a hmask0 hmask hmass p q w.grad

end QSH
