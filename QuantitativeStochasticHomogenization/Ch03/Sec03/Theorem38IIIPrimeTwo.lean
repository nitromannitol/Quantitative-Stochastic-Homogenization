import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IITwo

/-!
# The estimate `(iii')₂` of Theorem 3.8

Armstrong–Kuusi–Mourrat, (3.45) for `k = 2`, through (3.48): (3.50) above the random scale of
Proposition 3.2 and `(ii)₂` (`theorem_3_8_ii_two`) give, above a random scale `X ≤ O_s(C)` and for
almost every coefficient field, for every `R ≥ X` and every solution `u` in `B_R` some `φ ∈ A_2` with
`‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)^{3-δ/2} ‖u‖_{L̲²(B_R)}` for every `r ∈ [X, R]`
(`theorem_3_8_iii_prime_two`). The passage from `(ii)_k` to `(iii')_k` is `iii_prime_of_ii`, for
every `k`.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- **(3.48) above a random scale, for every `k`**: `(ii)_k` with some exponent gives `(iii')_k` for
every exponent `δ` below some `δ₁ ∈ (0, ½]`. -/
theorem iii_prime_of_ii (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    (k : ℕ)
    (hii : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ p ∈ harmonicPolys (homogenizedMatrix P) k, ∃ u ∈ solutionGrowthSpace a k,
          ∀ R : ℝ, X a ≤ R → scalarRms volume (ball 0 R) (fun x => u x - p x) ≤
            C * R ^ (-δ) * scalarRms volume (ball 0 R) p) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ R : ℝ, X a ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a k,
          ∀ r : ℝ, X a ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
            C * (r / R) ^ ((k : ℝ) + 1 - δ / 2) * scalarRms volume (ball 0 R) u := by
  obtain ⟨δ₂, hδ₂, hδ₂', C₂, CX₂, hC₂, hCX₂, hii⟩ := hii
  obtain ⟨δ₀, hδ₀, hδ₀', h348⟩ := implication_348_random hd hΛ hs hsd
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, (min_le_left _ _).trans hδ₂', fun δ hδ0 hδm => ?_⟩
  have hδ2 : δ ≤ δ₂ := hδm.trans (min_le_left _ _)
  have hδ3 : δ ≤ δ₀ := hδm.trans (min_le_right _ _)
  obtain ⟨θ, C, Cg, CX₃, hCX₃, hθC, h348δ⟩ := h348 δ hδ0 hδ3
  obtain ⟨hθ0, hθ1, hC0, hCg0⟩ := hθC k
  have hβ : 0 < θ k ^ ((k : ℝ) + 1 - δ / 2) := Real.rpow_pos_of_pos hθ0 _
  obtain ⟨H₁, hH₁, hH₁r⟩ := exists_scale_rpow_le (C k) (by positivity : 0 < 1 / 8 *
    θ k ^ ((k : ℝ) + 1 - δ / 2)) hδ0
  obtain ⟨H₂, hH₂, hH₂r⟩ := exists_scale_rpow_le (C₂ * (Real.sqrt ((1 / θ k) ^ d) + 1))
    (by positivity : 0 < 1 / 2 * θ k ^ ((k : ℝ) + 1 - δ / 2)) hδ0
  obtain ⟨H₃, hH₃, hH₃r⟩ := exists_scale_rpow_le C₂ (by norm_num : (0 : ℝ) < 1 / 2) hδ0
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = max H₁ (max H₂ H₃) := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := by rw [hHdef]; exact le_max_of_le_left hH₁
  refine ⟨(Real.sqrt ((1 / θ k) ^ d) + Cg k * (Real.sqrt ((1 / θ k) ^ d) + 1) /
      (1 - θ k ^ (1 - δ / 2))) * θ k ^ (-((k : ℝ) + 1 - δ / 2)),
    (2 : ℝ) ^ s⁻¹ * max ((2 : ℝ) ^ s⁻¹ * max CX₂ CX₃) (H / Real.log 2 ^ s⁻¹), ?_, by positivity,
    fun P hP => ?_⟩
  · have h1 : 0 < 1 - θ k ^ (1 - δ / 2) := by
      have : θ k ^ (1 - δ / 2) < 1 := Real.rpow_lt_one hθ0.le (by linarith) (by linarith)
      linarith
    have := Real.rpow_pos_of_pos hθ0 (-((k : ℝ) + 1 - δ / 2))
    positivity
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X₂, hX₂os, hX₂1, hX₂ae⟩ := hii P hP
  obtain ⟨X₃, hX₃os, hX₃1, hX₃ae⟩ := h348δ P hP
  have hHos : OsBound P (fun _ => H) s (H / Real.log 2 ^ s⁻¹) :=
    osBound_of_le_const measurable_const hs (by linarith) (Eventually.of_forall fun _ => le_rfl)
  refine ⟨fun a => max (max (X₂ a) (X₃ a)) H, osBound_max (osBound_max hX₂os hX₃os) hHos,
    fun a => le_max_of_le_right hH1, ?_⟩
  filter_upwards [hX₂ae, hX₃ae] with a ha2 ha3
  intro R hR u hu
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, r₀ = max (max (X₂ a) (X₃ a)) H := ⟨_, rfl⟩
  rw [← hr₀def] at hR ⊢
  have hX₂r : X₂ a ≤ r₀ := by rw [hr₀def]; exact le_max_of_le_left (le_max_left _ _)
  have hX₃r : X₃ a ≤ r₀ := by rw [hr₀def]; exact le_max_of_le_left (le_max_right _ _)
  have hHr : H ≤ r₀ := by rw [hr₀def]; exact le_max_right _ _
  have hr₀1 : 1 ≤ r₀ := hH1.trans hHr
  have hs50 := hH₁r r₀ ((show H₁ ≤ H by rw [hHdef]; exact le_max_left _ _).trans hHr)
  have hs2 := hH₂r r₀ ((show H₂ ≤ H by rw [hHdef]; exact le_max_of_le_right (le_max_left _ _)).trans
    hHr)
  have hs2' := hH₃r r₀ ((show H₃ ≤ H by rw [hHdef]; exact le_max_of_le_right (le_max_right _ _)).trans
    hHr)
  have hs2m : C₂ * r₀ ^ (-δ) * (Real.sqrt ((1 / θ k) ^ d) + 1) ≤
      1 / 2 * θ k ^ ((k : ℝ) + 1 - δ / 2) := (le_of_eq (by ring)).trans hs2
  have hb := ha3 k r₀ C₂ hX₃r hC₂ hs50 hs2m hs2'
    (fun p hp => by
      obtain ⟨v, hv, hvb⟩ := ha2 p hp
      refine ⟨v, hv, fun s' hs' => (hvb s' (hX₂r.trans hs')).trans ?_⟩
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₂) (scalarRms_nonneg _ _)
      exact Real.rpow_le_rpow_of_exponent_le (hr₀1.trans hs') (by linarith))
    R hR u hu
  obtain ⟨φ, hφ, hφb⟩ := hb
  exact ⟨φ, hφ, fun r hr hrR => hφb r hr hrR⟩

/-- **`(iii')₂`**, for `d ≥ 2`, `Λ > 1` and `s ∈ (0, d)`: there are `δ ∈ (0, ½]`, `C` and, for every
law satisfying the assumptions, a random variable `X ≥ 1` with `X ≤ O_s(C)` such that, for almost
every coefficient field, every `R ≥ X` and every solution `u` in `B_R`, some `φ ∈ A_2` satisfies
`‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)^{3-δ/2} ‖u‖_{L̲²(B_R)}` for every `r ∈ [X, R]`. -/
theorem theorem_3_8_iii_prime_two (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 < Λ) {s : ℝ} (hs : 0 < s)
    (hsd : s < d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ C CX : ℝ, 0 ≤ C ∧ 0 < CX ∧
      ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ X : CoefficientField d Λ → ℝ, OsBound P X s CX ∧ (∀ a, 1 ≤ X a) ∧ ∀ᵐ a ∂P,
        ∀ R : ℝ, X a ≤ R → ∀ u, IsSolutionBall a R u → ∃ φ ∈ solutionGrowthSpace a 2,
          ∀ r : ℝ, X a ≤ r → r ≤ R → scalarRms volume (ball 0 r) (fun x => u x - φ x) ≤
            C * (r / R) ^ ((3 : ℝ) - δ / 2) * scalarRms volume (ball 0 R) u := by
  obtain ⟨δ₁, hδ₁0, hδ₁2, h⟩ := iii_prime_of_ii hd hΛ hs hsd 2 (theorem_3_8_ii_two hd hΛ hs hsd)
  have e : ((2 : ℕ) : ℝ) + 1 - δ₁ / 2 = 3 - δ₁ / 2 := by push_cast; ring
  refine ⟨δ₁, hδ₁0, hδ₁2, ?_⟩
  rw [← e]
  exact h δ₁ hδ₁0 le_rfl

end QSH
