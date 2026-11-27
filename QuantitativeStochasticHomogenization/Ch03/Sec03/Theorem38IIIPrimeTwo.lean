import QuantitativeStochasticHomogenization.Ch03.Sec03.Theorem38IITwo

/-!
# The estimate `(iii')₂` of Theorem 3.8

Armstrong–Kuusi–Mourrat, (3.45) for `k = 2`, through (3.48): (3.50) above the random scale of
Proposition 3.2 and `(ii)₂` (`theorem_3_8_ii_two`) give, above a random scale `X ≤ O_s(C)` and for
almost every coefficient field, for every `R ≥ X` and every solution `u` in `B_R` some `φ ∈ A_2` with
`‖u - φ‖_{L̲²(B_r)} ≤ C (r/R)^{3-δ/2} ‖u‖_{L̲²(B_R)}` for every `r ∈ [X, R]`
(`theorem_3_8_iii_prime_two`), by `iii_prime_of_ii`.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

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
