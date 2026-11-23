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

/-- The vector `fluxPolarizationVector` with a field `J` in place of `J₁(Φ_{y,r}, ·, ·)`. -/
def fluxPolarizationVectorOf (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : CoefficientField d Λ) (y : Vec d) (r : ℝ) (p q : Vec d) : Vec d :=
  fun i => -4 * (J a y r ((1 / 2 : ℝ) • (p + unitVector i)) ((1 / 2 : ℝ) • q) -
    J a y r ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q) - J a y r ((1 / 2 : ℝ) • unitVector i) 0)

theorem fluxPolarizationVectorOf_eq {J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ}
    {a : CoefficientField d Λ} (h : ∀ z r p q, J a z r p q = J1Heat a z r p q) (y : Vec d)
    (r : ℝ) (p q : Vec d) :
    fluxPolarizationVectorOf J a y r p q = fluxPolarizationVector a y r p q := by
  funext i
  simp only [fluxPolarizationVectorOf, fluxPolarizationVector, h]

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

/-- **Fluctuations of `Bᵢ = 2 m(0, eᵢ/2)` and `Cᵢ = 2 f(0, eᵢ/2)`** under `Fluc(s, α)`, for the
polarization vectors of a field `J` (`J = J₁` or a jointly measurable version of it). -/
theorem polarization_pair_fluctuation [IsProbabilityMeasure P]
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ) {s α CF : ℝ} (hs0 : 0 < s)
    (hCF : 0 < CF)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J w.1 w.2 r p q)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J a z r p q) P ∧
      OsBound P (fun a => |J a z r p q - ∫ a', J a' z r p q ∂P|) s (CF * r ^ (-α)))
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) (i : Fin d) :
    let σ := (2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * (8 ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)
    let B := fun a => (2 : ℝ) • polarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i)
    let C := fun a => (2 : ℝ) • fluxPolarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i)
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
  have hB := threeLoad_fluctuation J hs0 hCF hmeasJ hF y hr
    (fun k => ((1 / 2 : ℝ) • (0 : Vec d), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • unitVector i + unitVector k)))
    (fun _ => ((1 / 2 : ℝ) • (0 : Vec d), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))))
    (fun k => (0, (1 / 2 : ℝ) • unitVector k))
    (fun k => ⟨(hl k).1, (hl k).2.1⟩) (fun k => ⟨(hl k).1, (hl k).2.2.1⟩)
    (fun k => ⟨(hl k).2.2.2.2.2, (hl k).2.2.2.1⟩) (c := 8) (by norm_num) B (fun a k => by
      simp only [B, polarizationVectorOf, Pi.smul_apply, smul_eq_mul]
      ring)
  have hC := threeLoad_fluctuation J hs0 hCF hmeasJ hF y hr
    (fun k => ((1 / 2 : ℝ) • ((0 : Vec d) + unitVector k), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))))
    (fun _ => ((1 / 2 : ℝ) • (0 : Vec d), (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (unitVector i : Vec d))))
    (fun k => ((1 / 2 : ℝ) • (unitVector k : Vec d), 0))
    (fun k => ⟨(hl k).2.2.2.2.1, (hl k).2.2.1⟩) (fun k => ⟨(hl k).1, (hl k).2.2.1⟩)
    (fun k => ⟨(hl k).2.2.2.1, (hl k).2.2.2.2.2⟩) (c := -8) (by norm_num) C (fun a k => by
      simp only [C, fluxPolarizationVectorOf, Pi.smul_apply, smul_eq_mul]
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

section Large

variable {P : Measure (CoefficientField d Λ)}

theorem rpow_half_mul_sq_rpow {X B r α : ℝ} (hX : 0 ≤ X) (hB : 0 ≤ B) (hr : 0 < r) :
    (X * (B * r ^ (-α)) ^ 2) ^ (1 / 2 : ℝ) = X ^ (1 / 2 : ℝ) * B * r ^ (-α) := by
  have h1 : 0 ≤ B * r ^ (-α) := mul_nonneg hB (Real.rpow_nonneg hr.le _)
  rw [Real.mul_rpow hX (sq_nonneg _), show ((B * r ^ (-α)) ^ 2) ^ (1 / 2 : ℝ) = B * r ^ (-α) by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq h1]]
  ring

/-- The scale of the commutator bound of Lemma 4.13 as a linear function of the size `u` of the
fluctuations, the size `v` of the bad part and the error `w` of the expectations. -/
def commutatorScaleOf (d : ℕ) (Λ s CN τ CMd u v w : ℝ) : ℝ :=
  let cs : ℝ := 2 * (2 : ℝ) ^ s⁻¹
  let K₀ : ℝ := 2 * Λ * Real.sqrt d * (Real.sqrt d * (16 * (Λ + 1)))
  let Kq : ℝ := 2 * (Real.sqrt d * (Λ + 1))
  let θY : ℝ := Kq * ((2 * (2 : ℝ) ^ s⁻¹) ^ d * (cs * (u + K₀ * u)))
  let mY : ℝ := Kq * (d * (momentConstant s * u + K₀ * (momentConstant s * u)))
  let θB : ℝ := (Λ + K₀) * Real.sqrt CN * 2 * ((2 * Real.exp 1 - 1) ^ s⁻¹ * v)
  let mB : ℝ := (Λ + K₀) * Real.sqrt CN * 2 * (momentConstant (τ / ((d : ℝ) / 2)) * v)
  let θN : ℝ := Real.sqrt CN * (cs * (1 / Real.log 2 ^ s⁻¹ + (2 * Real.exp 1 - 1) ^ s⁻¹ * CMd))
  cs * (cs * (θY + θB) + Real.sqrt d * (w + Real.sqrt d * (mY + mB) + K₀ * w) * θN)

/-- The scale of the commutator bound of Lemma 4.13 at one large scale `r`. -/
def commutatorScale (d : ℕ) (Λ s α CF CM CN τ η r : ℝ) : ℝ :=
  commutatorScaleOf d Λ s CN τ (CM ^ ((d : ℝ) / 2))
    (((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d *
      (8 ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) ^ (1 / 2 : ℝ))
    ((CM / r) ^ ((d : ℝ) / 2)) η

theorem commutatorScaleOf_mono {Λ s CN τ CMd u v w u' v' w' : ℝ} (hΛ : 0 ≤ Λ) (hCMd : 0 ≤ CMd)
    (hu : u ≤ u') (hv : v ≤ v') (hw : w ≤ w') :
    commutatorScaleOf d Λ s CN τ CMd u v w ≤ commutatorScaleOf d Λ s CN τ CMd u' v' w' := by
  have hm1 := (momentConstant_pos s).le
  have hm2 := (momentConstant_pos (τ / ((d : ℝ) / 2))).le
  have hl : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  have he : 0 ≤ 2 * Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hK₀ : 0 ≤ 2 * Λ * Real.sqrt d * (Real.sqrt d * (16 * (Λ + 1))) := by positivity
  have hθN : 0 ≤ Real.sqrt CN * (2 * (2 : ℝ) ^ s⁻¹ * (1 / Real.log 2 ^ s⁻¹ +
      (2 * Real.exp 1 - 1) ^ s⁻¹ * CMd)) := by positivity
  simp only [commutatorScaleOf]
  gcongr

theorem commutatorScaleOf_smul {Λ s CN τ CMd u v w ρ : ℝ} :
    commutatorScaleOf d Λ s CN τ CMd (ρ * u) (ρ * v) (ρ * w) =
      ρ * commutatorScaleOf d Λ s CN τ CMd u v w := by
  simp only [commutatorScaleOf]
  ring

/-- **The scale of Lemma 4.13 is of order `r^{-α}`** when the error of the expectations is
`C_E r^{-α}` and `α ≤ d/2`. -/
theorem commutatorScale_le {Λ s α CF CM CN τ CE r : ℝ} (hΛ : 0 ≤ Λ) (hCF : 0 < CF) (hCM : 0 ≤ CM)
    (hr : 1 ≤ r) (hα : α ≤ (d : ℝ) / 2) :
    commutatorScale d Λ s α CF CM CN τ (CE * r ^ (-α)) r ≤
      commutatorScale d Λ s α CF CM CN τ CE 1 * r ^ (-α) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hσ : ∀ r' : ℝ, 0 < r' → ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d *
      (8 ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r' ^ (-α))) ^ 2)) ^ (1 / 2 : ℝ) =
      r' ^ (-α) * (((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * 8 ^ 2) ^ (1 / 2 : ℝ) *
        ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * CF)) := by
    intro r' hr'
    rw [show (2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d *
        (8 ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r' ^ (-α))) ^ 2) =
        ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d * 8 ^ 2) * (((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * CF) * r' ^ (-α)) ^ 2
        by ring, rpow_half_mul_sq_rpow (by positivity) (by positivity) hr']
    ring
  have hv : (CM / r) ^ ((d : ℝ) / 2) ≤ r ^ (-α) * CM ^ ((d : ℝ) / 2) := by
    rw [Real.div_rpow hCM hr0.le, div_eq_mul_inv, mul_comm, ← Real.rpow_neg hr0.le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hr (neg_le_neg hα))
      (Real.rpow_nonneg hCM _)
  unfold commutatorScale
  rw [hσ r hr0, hσ 1 one_pos, Real.one_rpow, div_one, one_mul]
  refine le_trans (commutatorScaleOf_mono hΛ (Real.rpow_nonneg hCM _) le_rfl hv
    (le_of_eq (mul_comm _ _))) (le_of_eq ?_)
  rw [commutatorScaleOf_smul, mul_comm]

/-- The fluctuation part of the commutator bound: the sum over `i` of the fluctuations of
`Cᵢ = 2 f(0, eᵢ/2)` and `K₀`-times those of `Bᵢ = 2 m(0, eᵢ/2)`, under `Fluc(s, α)`. -/
theorem polarization_sum_fluctuation [IsProbabilityMeasure P]
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ) {s α CF : ℝ} (hs0 : 0 < s)
    (hCF : 0 < CF)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J w.1 w.2 r p q)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J a z r p q) P ∧
      OsBound P (fun a => |J a z r p q - ∫ a', J a' z r p q ∂P|) s (CF * r ^ (-α)))
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) {K₀ Kq : ℝ} (hK₀ : 0 < K₀) (hKq : 0 < Kq) :
    let σh := ((2 * (2 : ℝ) ^ (s / 2)⁻¹) ^ d *
      (8 ^ 2 * ((2 * (2 : ℝ) ^ s⁻¹) ^ 2 * (CF * r ^ (-α))) ^ 2)) ^ (1 / 2 : ℝ)
    let Y := fun a : CoefficientField d Λ => Kq * ∑ i,
      (euclideanNorm ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • fluxPolarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P) +
        K₀ * euclideanNorm ((2 : ℝ) • polarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • polarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P))
    OsBound P Y s (Kq * ((2 * (2 : ℝ) ^ s⁻¹) ^ d * (2 * (2 : ℝ) ^ s⁻¹ * (σh + K₀ * σh)))) ∧
      Integrable Y P ∧
      ∫ a, Y a ∂P ≤ Kq * (d * (momentConstant s * σh + K₀ * (momentConstant s * σh))) ∧
      ∀ a, 0 ≤ Y a := by
  intro σh Y
  have hσh : 0 < σh := Real.rpow_pos_of_pos (by positivity) _
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), OsBound P (fun a =>
      euclideanNorm ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • fluxPolarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P) +
        K₀ * euclideanNorm ((2 : ℝ) • polarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • polarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P)) s (2 * (2 : ℝ) ^ s⁻¹ * (σh + K₀ * σh)) := by
    intro i _
    obtain ⟨⟨hBo, -, -⟩, ⟨hCo, -, -⟩⟩ :=
      polarization_pair_fluctuation (P := P) J hs0 hCF hmeasJ hF y hr i
    exact osBound_add_le_sum hCo (hBo.const_mul hK₀)
  have hsum := osBound_finset_sum_of_pos Finset.univ hs0 (by positivity) hterm
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hint : ∀ i : Fin d, Integrable (fun a =>
      euclideanNorm ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • fluxPolarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P) +
        K₀ * euclideanNorm ((2 : ℝ) • polarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • polarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P)) P := by
    intro i
    obtain ⟨⟨-, hBi, -⟩, ⟨-, hCi, -⟩⟩ :=
      polarization_pair_fluctuation (P := P) J hs0 hCF hmeasJ hF y hr i
    exact hCi.add (hBi.const_mul K₀)
  have hsi : Integrable (fun a => ∑ i, (
      euclideanNorm ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • fluxPolarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P) +
        K₀ * euclideanNorm ((2 : ℝ) • polarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • polarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P))) P :=
    integrable_finsetSum _ fun i _ => hint i
  refine ⟨hsum.const_mul hKq, hsi.const_mul Kq, ?_, fun a => ?_⟩
  · simp only [Y]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    refine mul_le_mul_of_nonneg_left ?_ hKq.le
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin d)), (∫ a,
        (euclideanNorm ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • fluxPolarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P) +
        K₀ * euclideanNorm ((2 : ℝ) • polarizationVectorOf J a y r 0 ((1 / 2 : ℝ) • unitVector i) -
          fun k => ∫ a', ((2 : ℝ) • polarizationVectorOf J a' y r 0
            ((1 / 2 : ℝ) • unitVector i)) k ∂P)) ∂P) ≤
        momentConstant s * σh + K₀ * (momentConstant s * σh) := by
      intro i _
      obtain ⟨⟨-, hBi, hBm⟩, ⟨-, hCi, hCm⟩⟩ :=
        polarization_pair_fluctuation (P := P) J hs0 hCF hmeasJ hF y hr i
      rw [integral_add hCi (hBi.const_mul K₀), integral_const_mul]
      exact add_le_add hCm (mul_le_mul_of_nonneg_left hBm hK₀.le)
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · exact mul_nonneg hKq.le (Finset.sum_nonneg fun i _ =>
      add_nonneg (euclideanNorm_nonneg _) (mul_nonneg hK₀.le (euclideanNorm_nonneg _)))

/-- The bad part of the commutator bound: on the bad set `{r ≤ X_g}`, where `r ≤ M`, the energy
bound `(Λ + K₀) √C_N (1 + (X_N/r)^{d/2})` is at most `2 (Λ + K₀) √C_N (M/r)^{d/2}`, which is
`O_s` of order `(C_M/r)^{d/2}` when `M ≤ O_τ(C_M)` and `s ≤ 2τ/d`. -/
theorem bad_part_bound [IsProbabilityMeasure P] (hd : 1 ≤ d) {s τ CM CN r K₀ : ℝ} (hs0 : 0 < s)
    (hr : 1 ≤ r) (hCN : 0 < CN) (hΛ : 0 < Λ) (hK₀ : 0 ≤ K₀) (Xg XN M : CoefficientField d Λ → ℝ)
    (hXgm : Measurable Xg) (hXNm : Measurable XN) (hXN0 : ∀ a, 0 ≤ XN a) (hM1 : ∀ a, 1 ≤ M a)
    (hXNM : ∀ a, XN a ≤ M a) (hXgM : ∀ a, r ≤ Xg a → r ≤ M a)
    (hτs : s ≤ τ / ((d : ℝ) / 2)) (hMos : OsBound P M τ CM) :
    let Bp := fun a => {a | r ≤ Xg a}.indicator
      (fun a => (Λ + K₀) * (Real.sqrt CN * (1 + (XN a / r) ^ ((d : ℝ) / 2)))) a
    OsBound P Bp s ((Λ + K₀) * Real.sqrt CN * 2 *
        ((2 * Real.exp 1 - 1) ^ s⁻¹ * (CM / r) ^ ((d : ℝ) / 2))) ∧
      Integrable Bp P ∧
      ∫ a, Bp a ∂P ≤ (Λ + K₀) * Real.sqrt CN * 2 *
        (momentConstant (τ / ((d : ℝ) / 2)) * (CM / r) ^ ((d : ℝ) / 2)) ∧
      ∀ a, 0 ≤ Bp a := by
  intro Bp
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hBad : MeasurableSet {a : CoefficientField d Λ | r ≤ Xg a} :=
    measurableSet_le measurable_const hXgm
  have hM0 : ∀ a, 0 ≤ M a := fun a => zero_le_one.trans (hM1 a)
  set c : ℝ := (Λ + K₀) * Real.sqrt CN * 2 with hc
  have hc0 : 0 < c := by
    have : 0 < Real.sqrt CN := Real.sqrt_pos.mpr hCN
    rw [hc]; have : 0 < Λ + K₀ := by linarith
    positivity
  have hfac : 0 ≤ (Λ + K₀) * Real.sqrt CN := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hB0 : ∀ a, 0 ≤ Bp a := fun a => Set.indicator_nonneg (fun a _ =>
    mul_nonneg (by linarith) (mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg zero_le_one (Real.rpow_nonneg (div_nonneg (hXN0 a) hr0.le) _)))) a
  have hle : ∀ a, Bp a ≤ c * (M a / r) ^ ((d : ℝ) / 2) := by
    intro a
    by_cases ha : a ∈ {a : CoefficientField d Λ | r ≤ Xg a}
    · simp only [Bp]
      rw [Set.indicator_of_mem ha]
      have h1 : 1 ≤ M a / r := (one_le_div hr0).mpr (hXgM a ha)
      have h2 : 1 ≤ (M a / r) ^ ((d : ℝ) / 2) := Real.one_le_rpow h1 hd2.le
      have h3 : (XN a / r) ^ ((d : ℝ) / 2) ≤ (M a / r) ^ ((d : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg (hXN0 a) hr0.le)
          (div_le_div_of_nonneg_right (hXNM a) hr0.le) hd2.le
      calc (Λ + K₀) * (Real.sqrt CN * (1 + (XN a / r) ^ ((d : ℝ) / 2)))
          = ((Λ + K₀) * Real.sqrt CN) * (1 + (XN a / r) ^ ((d : ℝ) / 2)) := by ring
        _ ≤ ((Λ + K₀) * Real.sqrt CN) * (2 * (M a / r) ^ ((d : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hfac
        _ = c * (M a / r) ^ ((d : ℝ) / 2) := by rw [hc]; ring
    · simp only [Bp]
      rw [Set.indicator_of_notMem ha]
      exact mul_nonneg hc0.le (Real.rpow_nonneg (div_nonneg (hM0 a) hr0.le) _)
  have hBm : Measurable Bp := by
    refine Measurable.indicator ?_ hBad
    exact (((hXNm.div_const r).pow_const _).const_add 1 |>.const_mul _).const_mul _
  have hMr := osBound_rpow_div hMos hM0 hr0 hd2
  obtain ⟨hMri, hMrm⟩ := hMr.integral_le_factorial_mul fun a =>
    Real.rpow_nonneg (div_nonneg (hM0 a) hr0.le) _
  have hBi : Integrable Bp P := (hMri.const_mul c).mono' hBm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hB0 a)]; exact hle a)
  refine ⟨((hMr.mono_exponent hs0 hτs).const_mul hc0).of_le hBm hle, hBi, ?_, hB0⟩
  calc ∫ a, Bp a ∂P ≤ ∫ a, c * (M a / r) ^ ((d : ℝ) / 2) ∂P :=
        integral_mono hBi (hMri.const_mul c) hle
    _ = c * ∫ a, (M a / r) ^ ((d : ℝ) / 2) ∂P := integral_const_mul _ _
    _ ≤ c * (momentConstant (τ / ((d : ℝ) / 2)) * (CM / r) ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hMrm hc0.le

/-- The size of the averaged gradient: `√C_N (1 + M^{d/2}) ≤ O_s(√C_N c (1/(log 2)^{1/s} +
κ^{1/s} C_M^{d/2}))` when `M ≤ O_τ(C_M)` and `s ≤ 2τ/d`. -/
theorem size_bound [IsProbabilityMeasure P] (hd : 1 ≤ d) {s τ CM CN : ℝ} (hs0 : 0 < s)
    (hCN : 0 < CN) (M : CoefficientField d Λ → ℝ) (hM1 : ∀ a, 1 ≤ M a)
    (hτs : s ≤ τ / ((d : ℝ) / 2)) (hMos : OsBound P M τ CM) :
    OsBound P (fun a => Real.sqrt CN * (1 + M a ^ ((d : ℝ) / 2))) s
      (Real.sqrt CN * (2 * (2 : ℝ) ^ s⁻¹ * (1 / Real.log 2 ^ s⁻¹ +
        (2 * Real.exp 1 - 1) ^ s⁻¹ * CM ^ ((d : ℝ) / 2)))) := by
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : OsBound P (fun _ : CoefficientField d Λ => (1 : ℝ)) s (1 / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const hs0 one_pos (Filter.Eventually.of_forall fun _ => le_rfl)
  have h2 := (hMos.rpow (fun a => zero_le_one.trans (hM1 a)) hd2).mono_exponent hs0 hτs
  exact (osBound_add_le_sum h1 h2).const_mul (Real.sqrt_pos.mpr hCN)

/-- **Lemma 4.13 at one center and one large scale**, under `Fluc(s, α)` for a jointly measurable
field `J` equal to `J₁` at all parameters almost surely (`J = J₁` when `J₁` is jointly
measurable). -/
theorem commutator_osBound_large [IsProbabilityMeasure P] (hd : 1 ≤ d)
    (S : HomogenizationData P) (hΛ : 0 < Λ) (hA : HomogenizedMatrixBounds S.homogenized Λ)
    (hspan : ∀ᵐ a ∂P, GradientsOfA1AreCorrected S a)
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ)
    (hmeasJ : ∀ (r : ℝ) (p q : Vec d),
      Measurable fun w : CoefficientField d Λ × Vec d => J w.1 w.2 r p q)
    (hJ : ∀ᵐ a ∂P, ∀ z r p q, J a z r p q = J1Heat a z r p q)
    {s α CF : ℝ} (hs0 : 0 < s) (hCF : 0 < CF)
    (hF : ∀ (z : Vec d) (r : ℝ), 1 ≤ r → ∀ p q : Vec d,
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      Integrable (fun a => J a z r p q) P ∧
      OsBound P (fun a => |J a z r p q - ∫ a', J a' z r p q ∂P|) s (CF * r ^ (-α)))
    (y : Vec d) {r : ℝ} (hr : 1 ≤ r) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hεd : Real.sqrt d * ε ≤ 1 / 2) (Xg XN M : CoefficientField d Λ → ℝ)
    (hXgm : Measurable Xg) (hXNm : Measurable XN) (hXN0 : ∀ a, 0 ≤ XN a) (hM1 : ∀ a, 1 ≤ M a)
    (hXNM : ∀ a, XN a ≤ M a) (hXgM : ∀ a, r ≤ Xg a → r ≤ M a) {τ CM CN : ℝ} (hCN : 0 < CN)
    (hτs : s ≤ τ / ((d : ℝ) / 2)) (hMos : OsBound P M τ CM)
    (hgood : ∀ᵐ a ∂P, ¬ r ≤ Xg a →
      GaussianAverageBounds a S.homogenized (correctedField S a) y r ε)
    (hδ : Λ * (Real.sqrt d * (Real.sqrt d * ((9 + Real.sqrt d) * ε +
      (16 * (Λ + 1) + 1) * P.real {a | r ≤ Xg a}))) ≤ 1 / 2)
    (havg : ∀ᵐ a ∂P, ∀ l : Fin d,
      (Integrable (fun x => heatKernel y r x • correctedField S a (unitVector l) x) ∧
        Integrable (fun x => heatKernel y r x • (a x).mulVec (correctedField S a (unitVector l) x)) ∧
        Integrable (fun x => heatKernel y r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x)))) ∧
      (∫ x, heatKernel y r x * dot (correctedField S a (unitVector l) x)
          ((a x).mulVec (correctedField S a (unitVector l) x))) ≤
        CN * (1 + (XN a / r) ^ d) * euclideanSq (unitVector l : Vec d))
    (hPm : ∀ l, Measurable fun a => gradientAverage S a y r (unitVector l))
    (hFm : ∀ l, Measurable fun a => fluxAverage S a y r (unitVector l))
    {η : ℝ} (hη : 0 < η)
    (hPi : ∀ l k, Integrable (fun a => gradientAverage S a y r (unitVector l) k) P)
    (hFi : ∀ l k, Integrable (fun a => fluxAverage S a y r (unitVector l) k) P)
    (hEP : ∀ l, euclideanNorm ((fun k => ∫ a, gradientAverage S a y r (unitVector l) k ∂P) -
      unitVector l) ≤ η)
    (hEF : ∀ l, euclideanNorm ((fun k => ∫ a, fluxAverage S a y r (unitVector l) k ∂P) -
      S.homogenized.mulVec (unitVector l)) ≤ η) (j : Fin d) :
    OsBound P (fun a => euclideanNorm (fluxAverage S a y r (unitVector j) -
      S.homogenized.mulVec (gradientAverage S a y r (unitVector j)))) s
      (commutatorScale d Λ s α CF CM CN τ η r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have hBad : MeasurableSet {a : CoefficientField d Λ | r ≤ Xg a} :=
    measurableSet_le measurable_const hXgm
  have hgood' : ∀ᵐ a ∂P, a ∉ {a : CoefficientField d Λ | r ≤ Xg a} →
      GaussianAverageBounds a S.homogenized (correctedField S a) y r ε := hgood
  have hJy : ∀ p q : Vec d, Measurable fun a : CoefficientField d Λ => J a y r p q :=
    fun p q => (hmeasJ r p q).comp (measurable_id.prodMk measurable_const)
  have hJae : ∀ p q : Vec d, AEStronglyMeasurable (fun a => J1Heat a y r p q) P :=
    fun p q => (hJy p q).aestronglyMeasurable.congr (hJ.mono fun a ha => ha y r p q)
  have hmeanB : ∀ i : Fin d, (fun k => ∫ a, ((2 : ℝ) • polarizationVectorOf J a y r 0
      ((1 / 2 : ℝ) • unitVector i)) k ∂P) = fun k => ∫ a, ((2 : ℝ) • polarizationVector a y r 0
      ((1 / 2 : ℝ) • unitVector i)) k ∂P := fun i => funext fun k =>
    integral_congr_ae (by
      filter_upwards [hJ] with a ha
      rw [polarizationVectorOf_eq ha])
  have hmeanC : ∀ i : Fin d, (fun k => ∫ a, ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0
      ((1 / 2 : ℝ) • unitVector i)) k ∂P) = fun k => ∫ a, ((2 : ℝ) • fluxPolarizationVector a y r 0
      ((1 / 2 : ℝ) • unitVector i)) k ∂P := fun i => funext fun k =>
    integral_congr_ae (by
      filter_upwards [hJ] with a ha
      rw [fluxPolarizationVectorOf_eq ha])
  have hmB : ∀ i : Fin d, euclideanNorm ((fun k => ∫ a, ((2 : ℝ) • polarizationVectorOf J a y r 0
      ((1 / 2 : ℝ) • unitVector i)) k ∂P) - S.homogenized⁻¹.mulVec (unitVector i)) ≤
      Real.sqrt d * ((9 + Real.sqrt d) * ε + (16 * (Λ + 1) + 1) *
        P.real {a : CoefficientField d Λ | r ≤ Xg a}) := fun i => by
    rw [hmeanB i]
    exact mean_polarization_near_inverse S hΛ.le hA hspan y hr0 hJae hε0 hε hεd hBad hgood' i
  have h00 : euclideanNorm (0 : Vec d) < 1 := by simp [euclideanNorm, euclideanSq, dot]
  have hmC : ∀ i, euclideanNorm (fun k => ∫ a, ((2 : ℝ) • fluxPolarizationVectorOf J a y r 0
      ((1 / 2 : ℝ) • unitVector i)) k ∂P) ≤ Real.sqrt d * (16 * (Λ + 1)) := by
    intro i
    rw [hmeanC i]
    have hl : euclideanNorm ((1 / 2 : ℝ) • (unitVector i : Vec d)) < 1 := by
      rw [euclideanNorm_smul, euclideanNorm_unitVector]; norm_num
    refine euclideanNorm_le_of_abs_le (by positivity) fun k => ?_
    have hb : ∀ a, |((2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)) k| ≤
        16 * (Λ + 1) := fun a => by
      have := abs_fluxPolarizationVector_le a hΛ.le y hr0 h00 hl k
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_two]
      linarith
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ a, |((2 : ℝ) • fluxPolarizationVector a y r 0 ((1 / 2 : ℝ) • unitVector i)) k| ∂P
        ≤ ∫ _a, 16 * (Λ + 1) ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = 16 * (Λ + 1) := by simp
  obtain ⟨D₀, hD₀m, hD₀op⟩ := exists_matching_matrix S hΛ hA _ _ (by positivity) (by positivity)
    hmB hδ hmC
  have hK₀ : 0 < 2 * Λ * Real.sqrt d * (Real.sqrt d * (16 * (Λ + 1))) := by positivity
  have hpt := commutator_matching_le S hΛ.le hA hspan y hr0 hε0 hε hεd hgood' hCN.le XN hXN0 havg
    D₀ hK₀.le hD₀op _ _ hD₀m
  obtain ⟨hYo, hYi, hYm, hY0⟩ := polarization_sum_fluctuation (P := P) J hs0 hCF hmeasJ hF y hr hK₀
    (Kq := 2 * (Real.sqrt d * (Λ + 1))) (by positivity)
  obtain ⟨hBo, hBi, hBm, hB0⟩ := bad_part_bound (P := P) hd hs0 hr hCN hΛ hK₀.le Xg XN M hXgm hXNm
    hXN0 hM1 hXNM hXgM hτs hMos
  have hN := size_bound (P := P) hd hs0 hCN M hM1 hτs hMos
  have hPN : ∀ᵐ a ∂P, euclideanNorm (gradientAverage S a y r (unitVector j)) ≤
      Real.sqrt CN * (1 + M a ^ ((d : ℝ) / 2)) := by
    filter_upwards [havg] with a ha
    refine (averages_le_of_energy S a hΛ.le y hr0 hCN.le (hXN0 a) j (ha j).1 (ha j).2).1.trans ?_
    have h3 : (XN a / r) ^ ((d : ℝ) / 2) ≤ M a ^ ((d : ℝ) / 2) := Real.rpow_le_rpow
      (div_nonneg (hXN0 a) hr0.le) ((div_le_self (hXN0 a) hr).trans (hXNM a)) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
  have := commutator_assembly hd hK₀.le hη hD₀op (fun l a => gradientAverage S a y r (unitVector l))
    (fun l a => fluxAverage S a y r (unitVector l)) hPm hFm hPi hFi hEP hEF hYo hYi hYm hY0
    hBo hBi hBm hB0 hN (by
      filter_upwards [hpt, hJ] with a ha hJa
      simp only [← polarizationVectorOf_eq hJa, ← fluxPolarizationVectorOf_eq hJa] at ha
      exact ha) j hPN
  simp only [commutatorScale, commutatorScaleOf]
  exact this

end Large

end QSH
