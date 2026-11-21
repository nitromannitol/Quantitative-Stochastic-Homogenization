import QuantitativeStochasticHomogenization.Ch04.Sec04LocalizationEstimates
import QuantitativeStochasticHomogenization.AppA.OsNotation

/-!
# Section 5.4: A Central Limit Theorem for J₁

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 5 (Scaling Limits of First-Order Correctors), Section 5.4. Numbered results of this section:
Theorem 5.26; Proposition 5.25; Lemmas 5.27–5.30.

Defined here: the two properties (5.85) of a localization, the exponents (5.82)-(5.83) and the
blocks of (5.86) and (5.90)-(5.92).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-- The structural constants of the localization: `α ∈ (0, d/2]` with `γ < α(1+δ) + δ`,
`σ, θ ∈ (0, 1/2]`, `C₀, C > 0`. -/
def LocalizationConstants (d : ℕ) (δ γ α σ θ C₀ C : ℝ) : Prop :=
  0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
    0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧ 0 < C

/-- A family of localized bases, one for each coefficient field, center and scale `r ≥ 2`. -/
abbrev LocalizedFamily (d : ℕ) (Λ δ γ α σ θ C₀ : ℝ) : Type :=
  ∀ (a : CoefficientField d Λ) (z : Vec d) (r : ℝ), 2 ≤ r →
    LocalizedBasis a z (localizationOuterRadius δ r) (localizationIntermediateRadius δ α γ r)
      σ θ C₀

/-- The two properties of (5.85) for a localized family with constant `C`: `J₁^{(δ)}(z, r, p, q)`
is `F(B_{r^{1+δ}}(z))`-measurable and `|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)| ≤ O_s(C r^{-γ})`,
the difference being almost surely measurable (Remark 5.17), since `J₁(Φ_{z,r}, p, q)` is
identified with its finite-dimensional form (4.12) only almost surely. -/
def IsLocalization {d : ℕ} {Λ : ℝ} (P : Measure (CoefficientField d Λ)) (s δ γ α σ θ C₀ C : ℝ)
    (W : LocalizedFamily d Λ δ γ α σ θ C₀) : Prop :=
  ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
    euclideanNorm p < 1 → euclideanNorm q < 1 →
    @Measurable (CoefficientField d Λ) ℝ (localSigma (ball z (localizationOuterRadius δ r)))
      inferInstance (fun a => localizedJ1 (W a z r hr) r p q) ∧
    AEOsBound P (fun a => |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|) s (C * r ^ (-γ))

/-! ## Blocks of Section 5.4 -/

/-- The exponents (5.82) and the part of (5.83) used in Lemma 5.29. -/
def BlockWindow (d : ℕ) (s δ γ η : ℝ) : Prop :=
  1 < s ∧ s < 2 ∧ 0 < δ ∧
  (d : ℝ) / 2 * (1 + δ) < γ ∧
  γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) ∧
  1 / 2 < η ∧ η * γ > (d : ℝ) / 2 ∧ η < (1 + δ)⁻¹

/-- The localized energy of a family, extended by zero below `r = 2`. -/
def familyJ1 {d : ℕ} {Λ δ γ α σ θ C₀ : ℝ} (W : LocalizedFamily d Λ δ γ α σ θ C₀)
    (a : CoefficientField d Λ) (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  if hr : 2 ≤ r then localizedJ1 (W a z r hr) r p q else 0

/-- **The block** `R^{-d} ∫_{□_R(z)} f (J - E J)(·, r, p, q)` of (5.86) and (5.90)-(5.92). -/
def centeredBlock {d : ℕ} {Λ : ℝ} (P : Measure (CoefficientField d Λ))
    (J : CoefficientField d Λ → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : CoefficientField d Λ) (z : Vec d) (R r : ℝ) (f : Vec d → ℝ) (p q : Vec d) : ℝ :=
  R ^ (-(d : ℝ)) * ∫ x in cube z R, f x * (J a x r p q - ∫ a', J a' x r p q ∂P)

end QSH
