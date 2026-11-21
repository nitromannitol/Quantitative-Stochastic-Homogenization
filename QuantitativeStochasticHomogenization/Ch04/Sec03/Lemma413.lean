import QuantitativeStochasticHomogenization.Ch04.Sec03.Lemma413Pieces

/-!
# Lemma 4.13: the commutator of the corrected coordinates

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, Lemma 4.13, (4.34), for the corrected coordinates `eⱼ + ∇φ_{eⱼ}` (the first part of
Step 1 of the route of Proposition 4.10 used here).

`CommutatorEstimate P S s α`: `|∫ Φ_{z,r} (a - ā)(eⱼ + ∇φ_{eⱼ})| ≤ O_s(C r^{-α})` at every center
and scale.

This file proves the stochastic bounds used in the proof: the vector mean is bounded by the mean
of the norm (`euclideanNorm_integral_le`), and the powers of scaled random scales have stochastic
bounds at every exponent (`osBound_rpow_div`).
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

open BaseExponent

/-- **The commutator estimate** for the corrected coordinates, (4.34). -/
def CommutatorEstimate (P : Measure (CoefficientField d Λ)) (S : HomogenizationData P)
    (s α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
    OsBound P (fun a => euclideanNorm (fluxAverage S a z r (unitVector j) -
      S.homogenized.mulVec (gradientAverage S a z r (unitVector j)))) s (C * r ^ (-α))

section Means

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `|E V| ≤ √d E|V|` for an integrable random vector. -/
theorem euclideanNorm_integral_le [IsProbabilityMeasure P] {V : Ω → Vec d}
    (hV : ∀ k, Integrable (fun ω => V ω k) P) (hVn : Integrable (fun ω => euclideanNorm (V ω)) P) :
    euclideanNorm (fun k => ∫ ω, V ω k ∂P) ≤ Real.sqrt d * ∫ ω, euclideanNorm (V ω) ∂P := by
  refine euclideanNorm_le_of_abs_le (integral_nonneg fun ω => euclideanNorm_nonneg _) fun k => ?_
  refine (abs_integral_le_integral_abs).trans (integral_mono (hV k).abs hVn fun ω => ?_)
  exact abs_apply_le_euclideanNorm (V ω) k

/-- Powers of scaled random scales: `0 ≤ M ≤ O_τ(θ)` gives `(M/r)^t ≤ O_{τ/t}((θ/r)^t)`. -/
theorem osBound_rpow_div {M : Ω → ℝ} {τ θ r t : ℝ} (h : OsBound P M τ θ) (hM0 : ∀ ω, 0 ≤ M ω)
    (hr : 0 < r) (ht : 0 < t) :
    OsBound P (fun ω => (M ω / r) ^ t) (τ / t) ((θ / r) ^ t) := by
  have h1 := (h.const_mul (inv_pos.mpr hr)).rpow
    (fun ω => mul_nonneg (inv_nonneg.mpr hr.le) (hM0 ω)) ht
  simpa only [div_eq_inv_mul] using h1

end Means

end QSH
