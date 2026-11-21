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

section MatchingMatrix

variable {P : Measure (CoefficientField d Λ)}

/-- **The matrix matching the means** (Step 1 of Lemma 4.13): if the means `E Bᵢ` of
`Bᵢ = 2 m(0, eᵢ/2)` are within `δ` of `ā⁻¹ eᵢ` with `Λ √d δ ≤ 1/2`, and the means `E Cᵢ` of the
flux polarization vectors are bounded by `K`, there is `D₀` with `D₀ (E Bᵢ) = E Cᵢ` and
`|D₀ w| ≤ 2 Λ √d K |w|`. -/
theorem exists_matching_matrix (S : HomogenizationData P) (hΛ : 0 < Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ) (mB mC : Fin d → Vec d) {δ K : ℝ}
    (hδ0 : 0 ≤ δ) (hK : 0 ≤ K) (hmB : ∀ i, euclideanNorm (mB i - S.homogenized⁻¹.mulVec (unitVector i)) ≤ δ)
    (hδ : Λ * (Real.sqrt d * δ) ≤ 1 / 2) (hmC : ∀ i, euclideanNorm (mC i) ≤ K) :
    ∃ D₀ : Mat d, (∀ i, D₀.mulVec (mB i) = mC i) ∧
      ∀ w, euclideanNorm (D₀.mulVec w) ≤ 2 * Λ * Real.sqrt d * K * euclideanNorm w := by
  set D := S.homogenized with hD
  have hDdet : IsUnit D.det := isUnit_det_of_coercive fun ξ => (hA ξ).1
  have hDop : ∀ z, euclideanNorm (D.mulVec z) ≤ Λ * euclideanNorm z :=
    euclideanNorm_homogenized_mulVec_le S.symmetric hA hΛ.le
  set MB : Mat d := Matrix.of fun k i => mB i k with hMB
  set MC : Mat d := Matrix.of fun k i => mC i k with hMC
  have hcol : ∀ (M : Mat d) (i : Fin d), M.mulVec (unitVector i) = fun k => M k i := by
    intro M i
    funext k
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  have hMBi : ∀ i, MB.mulVec (unitVector i) = mB i := fun i => by
    rw [hcol]; funext k; simp [hMB]
  have hMCi : ∀ i, MC.mulVec (unitVector i) = mC i := fun i => by
    rw [hcol]; funext k; simp [hMC]
  have hnear : ∀ v, euclideanNorm ((MB - D⁻¹).mulVec v) ≤ Real.sqrt d * δ * euclideanNorm v :=
    euclideanNorm_sub_mulVec_le_of_columns hδ0 fun i => by rw [hMBi]; exact hmB i
  obtain ⟨hMBdet, hMBinv⟩ := isUnit_det_of_near_inverse hDdet hΛ hDop
    (η := Real.sqrt d * δ) hδ (fun v => by simpa [mul_assoc] using hnear v)
  refine ⟨MC * MB⁻¹, fun i => ?_, fun w => ?_⟩
  · rw [← hMBi i, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul MB hMBdet,
      Matrix.mul_one, hMCi]
  · have hMCop : ∀ v, euclideanNorm (MC.mulVec v) ≤ Real.sqrt d * K * euclideanNorm v := by
      intro v
      have hv : v = ∑ i, v i • (unitVector i : Vec d) := by
        funext k; simp [unitVector, Pi.single_apply, Finset.sum_apply]
      rw [hv, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hMCi]
      refine (euclideanNorm_finset_sum_le _ _).trans ?_
      calc ∑ i, euclideanNorm (v i • mC i) ≤ ∑ i, |v i| * K := Finset.sum_le_sum fun i _ => by
            rw [euclideanNorm_smul]; exact mul_le_mul_of_nonneg_left (hmC i) (abs_nonneg _)
        _ = (∑ i, |v i|) * K := by rw [Finset.sum_mul]
        _ ≤ Real.sqrt d * euclideanNorm v * K := by
            exact mul_le_mul_of_nonneg_right (sum_abs_le_sqrt_mul_euclideanNorm v) hK
        _ = Real.sqrt d * K * euclideanNorm (∑ i, v i • (unitVector i : Vec d)) := by
            rw [← hv]; ring
    rw [← Matrix.mulVec_mulVec]
    refine (hMCop _).trans ?_
    have := hMBinv w
    have h0 : 0 ≤ Real.sqrt d * K := mul_nonneg (Real.sqrt_nonneg _) hK
    calc Real.sqrt d * K * euclideanNorm (MB⁻¹.mulVec w)
        ≤ Real.sqrt d * K * (2 * Λ * euclideanNorm w) := mul_le_mul_of_nonneg_left this h0
      _ = 2 * Λ * Real.sqrt d * K * euclideanNorm w := by ring

end MatchingMatrix

section EStep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The expectation step** (Step 2 of Lemma 4.13): if the means of the gradient and flux
averages `P eₗ`, `F eₗ` are within `η` of `eₗ` and `ā eₗ`, and `E|F eₗ - D₀ P eₗ| ≤ ξ`, then
`|(D₀ - ā) v| ≤ √d (η + √d ξ + K₀ η) |v|`, where `|D₀ w| ≤ K₀ |w|`. -/
theorem matching_matrix_near [IsProbabilityMeasure P] {D D₀ : Mat d} {K₀ η ξ : ℝ}
    (hK₀ : 0 ≤ K₀) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hD₀ : ∀ w, euclideanNorm (D₀.mulVec w) ≤ K₀ * euclideanNorm w)
    (Pv Fv : Fin d → Ω → Vec d) (hPi : ∀ l k, Integrable (fun ω => Pv l ω k) P)
    (hFi : ∀ l k, Integrable (fun ω => Fv l ω k) P)
    (hEP : ∀ l, euclideanNorm ((fun k => ∫ ω, Pv l ω k ∂P) - unitVector l) ≤ η)
    (hEF : ∀ l, euclideanNorm ((fun k => ∫ ω, Fv l ω k ∂P) - D.mulVec (unitVector l)) ≤ η)
    (hdi : ∀ l, Integrable (fun ω => euclideanNorm (Fv l ω - D₀.mulVec (Pv l ω))) P)
    (hdm : ∀ l, ∫ ω, euclideanNorm (Fv l ω - D₀.mulVec (Pv l ω)) ∂P ≤ ξ) (v : Vec d) :
    euclideanNorm ((D₀ - D).mulVec v) ≤
      Real.sqrt d * (η + Real.sqrt d * ξ + K₀ * η) * euclideanNorm v := by
  have hcol : ∀ l, euclideanNorm (D₀.mulVec (unitVector l) - D.mulVec (unitVector l)) ≤
      η + Real.sqrt d * ξ + K₀ * η := by
    intro l
    set EP : Vec d := fun k => ∫ ω, Pv l ω k ∂P with hEPdef
    set EF : Vec d := fun k => ∫ ω, Fv l ω k ∂P with hEFdef
    have hlin : (fun k => ∫ ω, (Fv l ω - D₀.mulVec (Pv l ω)) k ∂P) = EF - D₀.mulVec EP := by
      funext k
      simp only [Pi.sub_apply, hEFdef, hEPdef, Matrix.mulVec, dotProduct]
      have hint : ∀ m, Integrable (fun ω => D₀ k m * Pv l ω m) P := fun m => (hPi l m).const_mul _
      rw [integral_sub (hFi l k) (integrable_finsetSum _ fun m _ => hint m),
        integral_finsetSum _ fun m _ => hint m]
      congr 1
      exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
    have hEdiff : euclideanNorm (EF - D₀.mulVec EP) ≤ Real.sqrt d * ξ := by
      rw [← hlin]
      refine (euclideanNorm_integral_le (fun k => ?_) (hdi l)).trans
        (mul_le_mul_of_nonneg_left (hdm l) (Real.sqrt_nonneg _))
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
      exact (hFi l k).sub (integrable_finsetSum _ fun m _ => (hPi l m).const_mul _)
    have hdec : D₀.mulVec (unitVector l) - D.mulVec (unitVector l) =
        (EF - D.mulVec (unitVector l)) - (EF - D₀.mulVec EP) - D₀.mulVec (EP - unitVector l) := by
      rw [Matrix.mulVec_sub]; abel
    rw [hdec]
    have h1 := euclideanNorm_sub_le ((EF - D.mulVec (unitVector l)) - (EF - D₀.mulVec EP))
      (D₀.mulVec (EP - unitVector l))
    have h2 := euclideanNorm_sub_le (EF - D.mulVec (unitVector l)) (EF - D₀.mulVec EP)
    have h3 := (hD₀ (EP - unitVector l)).trans (mul_le_mul_of_nonneg_left (hEP l) hK₀)
    have h4 := hEF l
    linarith
  exact euclideanNorm_sub_mulVec_le_of_columns (by positivity) hcol v

end EStep

end QSH
