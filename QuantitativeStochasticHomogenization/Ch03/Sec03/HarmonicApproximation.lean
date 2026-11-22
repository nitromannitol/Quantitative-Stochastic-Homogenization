import QuantitativeStochasticHomogenization.Ch03.Sec03.QuarterExcessStep

/-!
# Harmonic approximation on nearly full ellipsoids and the harmonic expansion

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3: the two deterministic estimates of the first-order proof of Theorem 3.8 for
`k = 1`, on the ellipsoids `E_R = M B_R` with `M Mᵀ = B = ½(D + Dᵀ)`.

`harmonicApproximationStatement` is the approximation (2): for a `SublinearCorrectorFamily`
with homogenized matrix `D`, every element of `A₁` minus a corrected affine function, `v`, is
close to a `B`-harmonic function `h` on the nearly full ellipsoid `E_b`, `b = (1 - 3R^{-ν})R`:
`‖v - h‖_{L̲²(E_b)} ≤ C R^{-ν} ‖v‖_{L̲²(E_R)}`. Its proof uses the identity
`((a - Dᵀ)∇v)ᵢ = ∂ₖ[(σᵢⱼₖ - cᵢⱼₖ)∂ⱼv - (φᵢ - cᵢ)(a∇v)ₖ]`, the Caccioppoli inequality, a
mollification, and the orthogonal projection onto the closure of the Laplacians of test functions with
Weyl's lemma (`HarmonicApproximationProof.lean`; the book's route uses the comparison principle for `B` on
`E_b`, see CORRESPONDENCE.md).

`harmonicExpansionStatement` is the expansion of `B`-harmonic functions: after the change of
variables `x = M y`, a `B`-harmonic function on `E_b` is harmonic on `B_b`, its homogeneous
harmonic polynomials are orthogonal on balls, and the terms of degree at least two decay like
`(t/b)²` for `t < b`; the first-order term has slope at most `C b⁻¹ ‖h‖_{L̲²(E_b)}`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- `h` belongs to `H¹(U)` and is weakly `B`-harmonic in `U`. -/
def IsL2HarmonicOn (B : Mat d) (U : Set (Vec d)) (h : Vec d → ℝ) : Prop :=
  MemLp h 2 (volume.restrict U) ∧ ∃ gh : Vec d → Vec d,
    (∀ i, MemLp (fun x => gh x i) 2 (volume.restrict U)) ∧ HasWeakGradient U h gh ∧
    HasWeakDivergence U (fun x => B.mulVec (gh x)) (fun _ => 0)

/-- **Harmonic approximation on nearly full ellipsoids**, (2) of the first-order proof of
Theorem 3.8, `k = 1` (deterministic). -/
def harmonicApproximationStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ μ C₁ : ℝ, 1 ≤ Λ → 0 < μ → μ ≤ 1 / 2 → 0 ≤ C₁ →
  ∀ D M : Mat d, (∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (D.mulVec ξ)) → M.det ≠ 0 →
    M * M.transpose = (1 / 2 : ℝ) • (D + D.transpose) →
  ∃ C ν : ℝ, 0 < ν ∧ ∀ R₀ : ℝ, 1 ≤ R₀ → ∃ R₁ : ℝ, R₀ ≤ R₁ ∧
    ∀ (a : CoefficientField d Λ) (F : SublinearCorrectorFamily a D μ C₁ R₀) (w : HarmonicA1 a),
    ∀ R : ℝ, R₁ ≤ R → ∀ (c : ℝ) (p : Vec d), ∃ h : Vec d → ℝ,
      IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M ((1 - 3 * R ^ (-ν)) * R)) h ∧
      scalarRms volume (matrixEllipsoid M ((1 - 3 * R ^ (-ν)) * R))
          (fun x => (w.potential x - correctedAffineOf F.φ c p x) - h x) ≤
        C * R ^ (-ν) * scalarRms volume (matrixEllipsoid M R)
          (fun x => w.potential x - correctedAffineOf F.φ c p x)

/-- **The harmonic expansion on ellipsoids** (deterministic): the part of degree at least two of
a `B`-harmonic function decays like `(t/b)²` in the normalized `L²` norm. -/
def harmonicExpansionStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ D : Mat d, (∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (D.mulVec ξ)) →
  ∃ M : Mat d, M.det ≠ 0 ∧ M * M.transpose = (1 / 2 : ℝ) • (D + D.transpose) ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → ∀ h : Vec d → ℝ,
    IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M b) h →
    ∃ (c : ℝ) (p : Vec d),
      (∀ t : ℝ, 0 < t → t < b →
        scalarRms volume (matrixEllipsoid M t) (fun x => h x - (c + dot p x)) ≤
          (t / b) ^ 2 * scalarRms volume (matrixEllipsoid M b) h) ∧
      euclideanNorm p ≤ C / b * scalarRms volume (matrixEllipsoid M b) h

end QSH
