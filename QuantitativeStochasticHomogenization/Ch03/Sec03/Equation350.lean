import QuantitativeStochasticHomogenization.Ch03.Sec03.Implication348
import QuantitativeStochasticHomogenization.Ch03.Sec02.Lemma36

/-!
# The estimate (3.50)

Armstrong–Kuusi–Mourrat, Section 3.3: "Proposition 3.2 and Lemma 3.6 yield the existence of
`θ(s, k, d, Λ) ∈ (0, 1)` such that, for every `r ≥ r₀`, `u ∈ A(B_r)`, `k ∈ ℕ`, (3.50)
`E_k(θ r) ≤ ¼ θ^{1-δ/2} E_k(r) + C r^{-(k+δ)} ‖u‖_{L̲²(B_r)}`", with `δ = α(d - s) ∧ ½`, (3.44).
`equation_3_50` is this estimate multiplied by `(θ r)^k`, for the distance `harmonicFlatness ā k`
to `Ā_k`, above the random scale of Proposition 3.2: Proposition 3.2 at every radius
`r' ∈ [X, r]` gives the harmonic approximations (3.28) with the exponent `α(d - s) ≥ δ`, and
Lemma 3.6 for `k` and `δ` concludes.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **(3.50)** above the random scale of Proposition 3.2, for `d ≥ 2`, `Λ > 1`, `s ∈ (0, d)` and
`k ∈ ℕ`, with `δ = min(α(d - s), ½)`. -/
theorem equation_3_50 (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    (k : ℕ) :
    ∃ δ θ C : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < θ ∧ θ < 1 / 2 ∧ 0 < C ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s C ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ r : ℝ, X a ≤ r → ∀ v, IsSolutionBall a r v →
          harmonicFlatness (homogenizedMatrix P) k v (θ * r) ≤
            1 / 4 * θ ^ ((k : ℝ) + 1 - δ / 2) * harmonicFlatness (homogenizedMatrix P) k v r +
              C * r ^ (-δ) * scalarRms volume (ball 0 r) v := by
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  obtain ⟨α, hα, hprop⟩ := proposition_3_2 hd hΛ
  obtain ⟨CP, hCP, hP⟩ := hprop s hs hsd
  have hds : 0 < (d : ℝ) - s := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (α * ((d : ℝ) - s)) (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (mul_pos hα hds) (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδα : δ ≤ α * ((d : ℝ) - s) := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨θ, C₃₆, hθ0, hθ1, hC₃₆, h36⟩ := lemma_3_6 hd hΛ.le hδ0 k
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max CP 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_right _ _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max CP (C₃₆ * K + 1) := ⟨_, rfl⟩
  have hCP_C : CP ≤ C := by rw [hC]; exact le_max_left _ _
  have hC36 : C₃₆ * K ≤ C := by rw [hC]; exact (le_max_right _ _).trans' (by linarith)
  have hC0 : 0 < C := lt_of_lt_of_le hCP hCP_C
  refine ⟨δ, θ, C, hδ0, hδ2, hθ0, hθ1, hC0, fun P hPlaw => ?_⟩
  obtain ⟨X, hXos, hX1, hXae⟩ := hP P hPlaw
  refine ⟨X, hXos.mono_scale hCP_C, hX1, ?_⟩
  filter_upwards [hXae] with a ha
  intro r hXr v hv
  have hsym := homogenizedMatrix_transpose hPlaw hΛ0
  have hbd : HomogenizedMatrixBounds (homogenizedMatrix P) Λ := fun ξ =>
    ⟨euclideanSq_le_dot_homogenizedMatrix hPlaw hΛ0 ξ, (homogenizedMatrix_dot_bounds hPlaw hΛ0 ξ).2⟩
  have hr1 : 1 ≤ r := (hX1 a).trans hXr
  have hr0 : 0 < r := by linarith
  have h := h36 (homogenizedMatrix P) hsym hbd K (X a) r (hX1 a) v hv.1 (fun ρ h1 h2 => by
    have hρ1 : 1 ≤ ρ := (hX1 a).trans h1
    obtain ⟨-, g, hg, hgrad, hdiv⟩ := hv.mono h2
    obtain ⟨uh, gh, huh, hgh, hugh, hdivh, hbound⟩ :=
      ha ρ h1 v g (hv.mono h2).1 hg hgrad hdiv
    refine ⟨uh, ⟨huh, gh, hgh, hugh, hdivh⟩, hbound.trans ?_⟩
    have hpow : ρ ^ (-(α * ((d : ℝ) - s))) ≤ ρ ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul (by rw [hK]; exact le_max_left _ _) hpow
      (Real.rpow_nonneg (by linarith) _) (by linarith)) (scalarRms_nonneg _ _))
    r hXr le_rfl
  refine h.trans (add_le_add le_rfl ?_)
  have hosc : scalarRms volume (ball 0 r) (fun x => v x - ⨍ y in ball 0 r, v y) ≤
      scalarRms volume (ball 0 r) v := by
    refine (scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' 0 r) hv.1 0).trans ?_
    simp only [sub_zero, le_refl]
  have hrδ : 0 ≤ r ^ (-δ) := Real.rpow_nonneg hr0.le _
  calc C₃₆ * K * r ^ (-δ) * scalarRms volume (ball 0 r) (fun x => v x - ⨍ y in ball 0 r, v y)
      ≤ C₃₆ * K * r ^ (-δ) * scalarRms volume (ball 0 r) v :=
        mul_le_mul_of_nonneg_left hosc (by positivity)
    _ ≤ C * r ^ (-δ) * scalarRms volume (ball 0 r) v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC36 hrδ) (scalarRms_nonneg _ _)

/-- **The implication (3.48) above the random scale**: for almost every coefficient field, every
scale `r₀ ≥ X` large enough for the constants of (3.50) and of `(ii)_k` (the book's `r₀ = H ∨ X_s`)
at which `(ii)_k` holds gives `(iii')_k` above `r₀`. -/
theorem implication_348_random (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) (k : ℕ) :
    ∃ δ θ C : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < θ ∧ θ < 1 / 2 ∧ 0 < C ∧ ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s C ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ r₀ C₂ : ℝ, X a ≤ r₀ → 0 ≤ C₂ →
        C * r₀ ^ (-δ) ≤ 1 / 8 * θ ^ ((k : ℝ) + 1 - δ / 2) →
        C₂ * r₀ ^ (-δ) * (Real.sqrt ((1 / θ) ^ d) + 1) ≤ 1 / 2 * θ ^ ((k : ℝ) + 1 - δ / 2) →
        C₂ * r₀ ^ (-δ) ≤ 1 / 2 →
        (∀ p ∈ harmonicPolys (homogenizedMatrix P) k, ∃ φ ∈ solutionGrowthSpace a k,
          ∀ s' : ℝ, r₀ ≤ s' → scalarRms volume (ball 0 s') (fun x => φ x - p x) ≤
            C₂ * s' ^ (-δ) * scalarRms volume (ball 0 s') p) →
        ∀ R : ℝ, r₀ ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a k,
          ∀ r : ℝ, r₀ ≤ r → r ≤ R →
            scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
              (Real.sqrt ((1 / θ) ^ d) + Cg * (Real.sqrt ((1 / θ) ^ d) + 1) /
                (1 - θ ^ (1 - δ / 2))) * θ ^ (-((k : ℝ) + 1 - δ / 2)) *
                (r / R) ^ ((k : ℝ) + 1 - δ / 2) * scalarRms volume (ball 0 R) u := by
  obtain ⟨δ, θ, C, hδ0, hδ2, hθ0, hθ1, hC0, h350⟩ := equation_3_50 hd hΛ hs hsd k
  obtain ⟨Cg, hCg, h348⟩ := implication_348 (d := d) (Λ := Λ) k
  refine ⟨δ, θ, C, hδ0, hδ2, hθ0, hθ1, hC0, Cg, hCg, fun P hP => ?_⟩
  obtain ⟨X, hXos, hX1, hXae⟩ := h350 P hP
  refine ⟨X, hXos, hX1, ?_⟩
  filter_upwards [hXae] with a ha
  intro r₀ C₂ hXr₀ hC₂ hs50 hs2 hs2' Hii
  have hr₀ : 0 < r₀ := lt_of_lt_of_le one_pos ((hX1 a).trans hXr₀)
  exact h348 a (homogenizedMatrix P) r₀ θ δ C C₂ hr₀ hθ0 (by linarith) hδ0 (by linarith) hC₂
    (fun r hr v hv => ha r (hXr₀.trans hr) v hv) Hii hs50 hs2 hs2'

end QSH
