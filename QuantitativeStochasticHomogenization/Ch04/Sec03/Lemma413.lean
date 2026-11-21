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

section Polarizations

/-- From a stochastic bound on `|V|²` to one on `|V|`, with its mean. -/
theorem osBound_euclideanNorm_of_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → Vec d} {s σ : ℝ}
    (h : OsBound P (fun ω => euclideanSq (V ω)) (s / 2) σ) :
    OsBound P (fun ω => euclideanNorm (V ω)) s (σ ^ (1 / 2 : ℝ)) ∧
      Integrable (fun ω => euclideanNorm (V ω)) P ∧
      ∫ ω, euclideanNorm (V ω) ∂P ≤ momentConstant s * σ ^ (1 / 2 : ℝ) := by
  have h1 := h.rpow (fun ω => euclideanSq_nonneg _) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [show s / 2 / (1 / 2) = s by ring] at h1
  have h2 : OsBound P (fun ω => euclideanNorm (V ω)) s (σ ^ (1 / 2 : ℝ)) := by
    simpa only [euclideanNorm, Real.sqrt_eq_rpow] using h1
  obtain ⟨hi, hm⟩ := h2.integral_le_factorial_mul fun ω => euclideanNorm_nonneg _
  exact ⟨h2, hi, hm⟩

variable {P : Measure (CoefficientField d Λ)}

theorem half_loads_norm (i k : Fin d) :
    euclideanNorm ((1 / 2 : ℝ) • (0 : Vec d)) < 1 ∧
      euclideanNorm ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • unitVector i + unitVector k)) < 1 ∧
      euclideanNorm ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))) < 1 ∧
      euclideanNorm ((1 / 2 : ℝ) • (unitVector k : Vec d)) < 1 ∧
      euclideanNorm ((1 / 2 : ℝ) • ((0 : Vec d) + unitVector k)) < 1 ∧
      euclideanNorm (0 : Vec d) < 1 := by
  have h0 : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
  have hk := euclideanNorm_unitVector (d := d) k
  have hi := euclideanNorm_unitVector (d := d) i
  refine ⟨by rw [smul_zero, h0]; norm_num, ?_, ?_, ?_, ?_, by rw [h0]; norm_num⟩
  · rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := euclideanNorm_add_le ((1 / 2 : ℝ) • (unitVector i : Vec d)) (unitVector k)
    rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hi, hk] at this
    linarith
  · rw [euclideanNorm_smul, euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hi]
    norm_num
  · rw [euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hk]; norm_num
  · rw [zero_add, euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hk]; norm_num

/-- **Fluctuations of `Bᵢ = 2 m(0, eᵢ/2)` and `Cᵢ = 2 f(0, eᵢ/2)`** under `Fluc(s, α)`. -/
theorem polarization_pair_fluctuation [IsProbabilityMeasure P] {s α CF : ℝ} (hs0 : 0 < s)
    (hCF : 0 < CF)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J1Heat w.1 w.2 r p q)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J1Heat a z r p q) P ∧
      OsBound P (fun a => |J1Heat a z r p q - ∫ a', J1Heat a' z r p q ∂P|) s (CF * r ^ (-α)))
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) (i : Fin d) :
    let σ := (2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * (8 ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)
    let B := fun a => (2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)
    let C := fun a => (2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)
    (OsBound P (fun a => euclideanNorm (B a - fun k => ∫ a', B a' k ∂P)) s (σ ^ (1 / 2 : ℝ)) ∧
      Integrable (fun a => euclideanNorm (B a - fun k => ∫ a', B a' k ∂P)) P ∧
      ∫ a, euclideanNorm (B a - fun k => ∫ a', B a' k ∂P) ∂P ≤
        momentConstant s * σ ^ (1 / 2 : ℝ)) ∧
    (OsBound P (fun a => euclideanNorm (C a - fun k => ∫ a', C a' k ∂P)) s (σ ^ (1 / 2 : ℝ)) ∧
      Integrable (fun a => euclideanNorm (C a - fun k => ∫ a', C a' k ∂P)) P ∧
      ∫ a, euclideanNorm (C a - fun k => ∫ a', C a' k ∂P) ∂P ≤
        momentConstant s * σ ^ (1 / 2 : ℝ)) := by
  intro σ B C
  have hl := half_loads_norm (d := d) i
  have hB := threeLoad_fluctuation hs0 hCF hmeasJ hF y hr
    (fun k => ((1 / 2 : ℝ) • (0 : Vec d), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • unitVector i + unitVector k)))
    (fun _ => ((1 / 2 : ℝ) • (0 : Vec d), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))))
    (fun k => (0, (1 / 2 : ℝ) • unitVector k))
    (fun k => ⟨(hl k).1, (hl k).2.1⟩) (fun k => ⟨(hl k).1, (hl k).2.2.1⟩)
    (fun k => ⟨(hl k).2.2.2.2.2, (hl k).2.2.2.1⟩) (c := 8) (by norm_num) B (fun a k => by
      simp only [B, polarizationVector, Pi.smul_apply, smul_eq_mul]
      ring)
  have hC := threeLoad_fluctuation hs0 hCF hmeasJ hF y hr
    (fun k => ((1 / 2 : ℝ) • ((0 : Vec d) + unitVector k), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))))
    (fun _ => ((1 / 2 : ℝ) • (0 : Vec d), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))))
    (fun k => ((1 / 2 : ℝ) • (unitVector k : Vec d), 0))
    (fun k => ⟨(hl k).2.2.2.2.1, (hl k).2.2.1⟩) (fun k => ⟨(hl k).1, (hl k).2.2.1⟩)
    (fun k => ⟨(hl k).2.2.2.1, (hl k).2.2.2.2.2⟩) (c := -8) (by norm_num) C (fun a k => by
      simp only [C, fluxPolarizationVector, Pi.smul_apply, smul_eq_mul]
      ring)
  rw [show ((-8 : ℝ)) ^ 2 = 8 ^ 2 by norm_num] at hC
  exact ⟨osBound_euclideanNorm_of_sq hB.1, osBound_euclideanNorm_of_sq hC.1⟩

end Polarizations

section EnergyBounds

variable {P : Measure (CoefficientField d Λ)}

/-- **The averaged gradient and flux of a corrected coordinate from the energy bound**:
`|P eₗ| ≤ √C_N (1 + (X/r)^{d/2})` and `|F eₗ| ≤ Λ √C_N (1 + (X/r)^{d/2})` when the averaged energy
is at most `C_N (1 + (X/r)^d)`. -/
theorem averages_le_of_energy (S : HomogenizationData P) (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ)
    (y : Vec d) {r : ℝ} (hr : 0 < r) {CN X : ℝ} (hCN : 0 ≤ CN) (hX : 0 ≤ X) (l : Fin d)
    (hint : Integrable (fun x => heatKernel y r x • correctedField S a (unitVector l) x) ∧
      Integrable (fun x => heatKernel y r x • (a x).mulVec (correctedField S a (unitVector l) x)) ∧
      Integrable (fun x => heatKernel y r x *
        dot (correctedField S a (unitVector l) x) ((a x).mulVec (correctedField S a (unitVector l) x))))
    (hE : (∫ x, heatKernel y r x * dot (correctedField S a (unitVector l) x)
        ((a x).mulVec (correctedField S a (unitVector l) x))) ≤
      CN * (1 + (X / r) ^ d) * euclideanSq (unitVector l : Vec d)) :
    euclideanNorm (gradientAverage S a y r (unitVector l)) ≤
        Real.sqrt CN * (1 + (X / r) ^ ((d : ℝ) / 2)) ∧
      euclideanNorm (fluxAverage S a y r (unitVector l)) ≤
        Λ * (Real.sqrt CN * (1 + (X / r) ^ ((d : ℝ) / 2))) := by
  obtain ⟨h1, h2⟩ := euclideanSq_averages_le_energy a hΛ y hr hint.1 hint.2.1 hint.2.2
  have hel : euclideanSq (unitVector l : Vec d) = 1 := by
    rw [← euclideanNorm_sq, euclideanNorm_unitVector]; norm_num
  rw [hel, mul_one] at hE
  have ht : 0 ≤ X / r := div_nonneg hX hr.le
  have hpow : ((X / r) ^ ((d : ℝ) / 2)) ^ 2 = (X / r) ^ d := by
    rw [← Real.rpow_natCast ((X / r) ^ ((d : ℝ) / 2)), ← Real.rpow_mul ht, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hp0 : 0 ≤ (X / r) ^ ((d : ℝ) / 2) := Real.rpow_nonneg ht _
  have hN0 : 0 ≤ Real.sqrt CN * (1 + (X / r) ^ ((d : ℝ) / 2)) := by positivity
  have hsq : CN * (1 + (X / r) ^ d) ≤ (Real.sqrt CN * (1 + (X / r) ^ ((d : ℝ) / 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCN, ← hpow]
    nlinarith [mul_nonneg hCN hp0]
  constructor
  · have := (h1.trans hE).trans hsq
    rw [← euclideanNorm_sq] at this
    exact abs_le_of_sq_le_sq' this hN0 |>.2
  · have := (h2.trans (mul_le_mul_of_nonneg_left hE (sq_nonneg Λ))).trans
      (mul_le_mul_of_nonneg_left hsq (sq_nonneg Λ))
    rw [← euclideanNorm_sq, ← mul_pow] at this
    exact abs_le_of_sq_le_sq' this (mul_nonneg hΛ hN0) |>.2

end EnergyBounds

section Pointwise

variable {P : Measure (CoefficientField d Λ)}

/-- **The commutator against `D₀`, pointwise**: almost surely, outside `Bad` (good scales) by the
fluctuations of the polarization vectors, and on `Bad` by the energy bound,
`|F eₗ - D₀ P eₗ| ≤ 2√d(Λ+1) ∑ᵢ (|Cᵢ - E Cᵢ| + K₀ |Bᵢ - E Bᵢ|) + 1_Bad (Λ + K₀) √C_N (1 + (X/r)^{d/2})`. -/
theorem commutator_matching_le (S : HomogenizationData P) (hΛ : 0 ≤ Λ)
    (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a) (y : Vec d) {r : ℝ} (hr : 0 < r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hεd : Real.sqrt d * ε ≤ 1 / 2)
    {Bad : Set (CoefficientField d Λ)}
    (hgood : ∀ᵐ a ∂P, a ∉ Bad → GaussianAverageBounds a S.homogenized (correctedField S a) y r ε)
    {CN : ℝ} (hCN : 0 ≤ CN) (XN : CoefficientField d Λ → ℝ) (hXN : ∀ a, 0 ≤ XN a)
    (havg : ∀ᵐ a ∂P, ∀ l : Fin d,
      (Integrable (fun x => heatKernel y r x • correctedField S a (unitVector l) x) ∧
        Integrable (fun x => heatKernel y r x • (a x).mulVec (correctedField S a (unitVector l) x)) ∧
        Integrable (fun x => heatKernel y r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x)))) ∧
      (∫ x, heatKernel y r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x))) ≤
        CN * (1 + (XN a / r) ^ d) * euclideanSq (unitVector l : Vec d))
    (D₀ : Mat d) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hD₀op : ∀ w, euclideanNorm (D₀.mulVec w) ≤ K₀ * euclideanNorm w)
    (mB mC : Fin d → Vec d) (hD₀m : ∀ i, D₀.mulVec (mB i) = mC i) :
    ∀ᵐ a ∂P, ∀ l : Fin d,
      euclideanNorm (fluxAverage S a y r (unitVector l) -
          D₀.mulVec (gradientAverage S a y r (unitVector l))) ≤
        2 * (Real.sqrt d * (Λ + 1)) * ∑ i,
          (euclideanNorm ((2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) -
              mC i) +
            K₀ * euclideanNorm ((2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) -
              mB i)) +
        Bad.indicator (fun a => (Λ + K₀) * (Real.sqrt CN * (1 + (XN a / r) ^ ((d : ℝ) / 2)))) a := by
  filter_upwards [hgood, hspan, havg] with a hga hsa hav
  intro l
  have hY0 : 0 ≤ 2 * (Real.sqrt d * (Λ + 1)) * ∑ i,
      (euclideanNorm ((2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) - mC i) +
        K₀ * euclideanNorm ((2 : ℝ) • polarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i) - mB i)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      add_nonneg (euclideanNorm_nonneg _) (mul_nonneg hK₀ (euclideanNorm_nonneg _)))
  by_cases hab : a ∈ Bad
  · rw [Set.indicator_of_mem hab]
    obtain ⟨hP, hF⟩ := averages_le_of_energy S a hΛ y hr hCN (hXN a) l (hav l).1 (hav l).2
    have h1 := euclideanNorm_sub_le (fluxAverage S a y r (unitVector l))
      (D₀.mulVec (gradientAverage S a y r (unitVector l)))
    have h2 := (hD₀op (gradientAverage S a y r (unitVector l))).trans
      (mul_le_mul_of_nonneg_left hP hK₀)
    nlinarith
  · rw [Set.indicator_of_notMem hab, add_zero]
    exact commutator_good_le S a hΛ hA hsa y r hε0 hε hεd (hga hab) D₀ hK₀ hD₀op mB mC hD₀m l

end Pointwise

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The final assembly of Lemma 4.13** for abstract random vectors: from the pointwise bound of
the commutator against `D₀` by `Y + B` (fluctuations and bad part), the expectations of the
averages, and stochastic bounds and means of `Y`, `B` and the size `N` of the gradient average,
`|F eⱼ - ā P eⱼ| ≤ O_s(c (c (θ_Y + θ_B) + ζ θ_N))` with `c = 2·2^{1/s}` and
`ζ = √d (η + √d (m_Y + m_B) + K₀ η)`. -/
theorem commutator_assembly [IsProbabilityMeasure P] (hd : 1 ≤ d) {D D₀ : Mat d} {K₀ η : ℝ}
    (hK₀ : 0 ≤ K₀) (hη : 0 < η) (hD₀ : ∀ w, euclideanNorm (D₀.mulVec w) ≤ K₀ * euclideanNorm w)
    (Pv Fv : Fin d → Ω → Vec d) (hPm : ∀ l, Measurable (Pv l)) (hFm : ∀ l, Measurable (Fv l))
    (hPi : ∀ l k, Integrable (fun ω => Pv l ω k) P) (hFi : ∀ l k, Integrable (fun ω => Fv l ω k) P)
    (hEP : ∀ l, euclideanNorm ((fun k => ∫ ω, Pv l ω k ∂P) - unitVector l) ≤ η)
    (hEF : ∀ l, euclideanNorm ((fun k => ∫ ω, Fv l ω k ∂P) - D.mulVec (unitVector l)) ≤ η)
    {Y Bp N : Ω → ℝ} {s θY θB θN mY mB : ℝ}
    (hY : OsBound P Y s θY) (hYi : Integrable Y P) (hYm : ∫ ω, Y ω ∂P ≤ mY) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hB : OsBound P Bp s θB) (hBi : Integrable Bp P) (hBm : ∫ ω, Bp ω ∂P ≤ mB) (hB0 : ∀ ω, 0 ≤ Bp ω)
    (hN : OsBound P N s θN)
    (hpt : ∀ᵐ ω ∂P, ∀ l, euclideanNorm (Fv l ω - D₀.mulVec (Pv l ω)) ≤ Y ω + Bp ω)
    (j : Fin d) (hPN : ∀ᵐ ω ∂P, euclideanNorm (Pv j ω) ≤ N ω) :
    OsBound P (fun ω => euclideanNorm (Fv j ω - D.mulVec (Pv j ω))) s
      (2 * (2 : ℝ) ^ s⁻¹ * (2 * (2 : ℝ) ^ s⁻¹ * (θY + θB) +
        Real.sqrt d * (η + Real.sqrt d * (mY + mB) + K₀ * η) * θN)) := by
  have hmY0 : 0 ≤ mY := (integral_nonneg hY0).trans hYm
  have hmB0 : 0 ≤ mB := (integral_nonneg hB0).trans hBm
  -- measurability
  have hXm : ∀ (M : Mat d) l, Measurable fun ω => euclideanNorm (Fv l ω - M.mulVec (Pv l ω)) := by
    intro M l
    have hc : Measurable fun ω => Fv l ω - M.mulVec (Pv l ω) :=
      (hFm l).sub ((Matrix.mulVecLin M).continuous_of_finiteDimensional.measurable.comp (hPm l))
    simp only [euclideanNorm, euclideanSq, dot]
    exact (Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp hc).mul ((measurable_pi_apply k).comp hc)).sqrt
  -- the expectation step
  have hdi : ∀ l, Integrable (fun ω => euclideanNorm (Fv l ω - D₀.mulVec (Pv l ω))) P := fun l =>
    (hYi.add hBi).mono' (hXm D₀ l).aestronglyMeasurable (by
      filter_upwards [hpt] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)]
      exact hω l)
  have hYB : Integrable (fun ω => Y ω + Bp ω) P := hYi.add hBi
  have hdm : ∀ l, ∫ ω, euclideanNorm (Fv l ω - D₀.mulVec (Pv l ω)) ∂P ≤ mY + mB := fun l =>
    (integral_mono_ae (hdi l) hYB (by
      filter_upwards [hpt] with ω hω
      exact hω l)).trans (by rw [integral_add hYi hBi]; linarith)
  have hop := matching_matrix_near hK₀ hη.le (add_nonneg hmY0 hmB0) hD₀ Pv Fv hPi hFi hEP hEF hdi hdm
  set ζ := Real.sqrt d * (η + Real.sqrt d * (mY + mB) + K₀ * η) with hζ
  have hsd : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hζ0 : 0 < ζ := by
    rw [hζ]; have : 0 < η + Real.sqrt d * (mY + mB) + K₀ * η := by positivity
    nlinarith
  -- the pointwise bound
  have hle : ∀ᵐ ω ∂P, euclideanNorm (Fv j ω - D.mulVec (Pv j ω)) ≤ (Y ω + Bp ω) + ζ * N ω := by
    filter_upwards [hpt, hPN] with ω hω hωN
    have hdec : Fv j ω - D.mulVec (Pv j ω) =
        (Fv j ω - D₀.mulVec (Pv j ω)) + (D₀ - D).mulVec (Pv j ω) := by
      rw [Matrix.sub_mulVec]; abel
    rw [hdec]
    refine (euclideanNorm_add_le _ _).trans (add_le_add (hω j) ?_)
    exact (hop _).trans (mul_le_mul_of_nonneg_left hωN hζ0.le)
  have hsum := osBound_add_le_sum (osBound_add_le_sum hY hB) (hN.const_mul hζ0)
  refine (hsum.of_le_ae (hXm D j) ?_).mono_scale (le_of_eq ?_)
  · filter_upwards [hle] with ω hω
    simpa [add_assoc] using hω
  · simp only [hζ]

end Assembly

end QSH
