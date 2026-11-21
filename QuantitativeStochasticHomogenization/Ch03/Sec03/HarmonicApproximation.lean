import QuantitativeStochasticHomogenization.Ch03.Sec03HigherOrderRegularityAndLiouville

/-!
# Harmonic approximation on nearly full ellipsoids

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3: the deterministic step of the first-order proof of Theorem 3.8 for `k = 1`. If the
coordinate correctors `φᵢ` and skew flux correctors `σᵢ` of a coefficient field `a` satisfy
`-∇·a(eᵢ + ∇φᵢ) = 0`, `∇·σᵢ = a(eᵢ + ∇φᵢ) - D eᵢ` and the oscillation bound
`‖φᵢ - (φᵢ)_R‖ + ‖σᵢ - (σᵢ)_R‖ ≤ C₁ R^{1-μ}` on balls `B_R`, `R ≥ R₀`, then every `a`-harmonic `v`
on the ellipsoid `E_R = {x · D⁻¹ x < R²}` is close to a `D`-harmonic function `h` on the nearly
full ellipsoid `E_b`, `b = (1 - 3R^{-ν})R`:
`‖v - h‖_{L̲²(E_b)} ≤ C R^{-ν} ‖v‖_{L̲²(E_R)}`.

The proof uses the identity `((a - D)∇v)ᵢ = ∂ₖ[(σᵢⱼₖ - cᵢⱼₖ)∂ⱼv - (φᵢ - cᵢ)(a∇v)ₖ]`, the
Caccioppoli inequality, a mollification at scale `R^{1-2ν}` and the energy estimate of the
Dirichlet problem for `D` on `E_b`. The statement is recorded here as
`harmonicApproximationStatement`.
-/

open MeasureTheory

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The ellipsoid `E_R = {x · D⁻¹ x < R²}` of a matrix `D`. -/
def ellipsoid (D : Mat d) (R : ℝ) : Set (Vec d) := {x | dot x (D⁻¹.mulVec x) < R ^ 2}

/-- **Harmonic approximation on nearly full ellipsoids** (deterministic). -/
def harmonicApproximationStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ μ C₁ : ℝ, 1 ≤ Λ → 0 < μ → μ ≤ 1 / 2 → 0 ≤ C₁ →
  ∀ D : Mat d, D.transpose = D →
    (∀ ξ : Vec d, euclideanSq ξ ≤ dot ξ (D.mulVec ξ) ∧ dot ξ (D.mulVec ξ) ≤ Λ * euclideanSq ξ) →
  ∃ C ν : ℝ, 0 < ν ∧ ∀ R₀ : ℝ, 1 ≤ R₀ → ∃ R₁ : ℝ, ∀ (a : CoefficientField d Λ)
    (φ : Fin d → Vec d → ℝ) (gφ : Fin d → Vec d → Vec d)
    (σ : Fin d → Vec d → Mat d) (gσ : Fin d → Fin d → Fin d → Vec d → Vec d),
    (∀ i, HasWeakGradient Set.univ (φ i) (gφ i)) →
    (∀ i j k, HasWeakGradient Set.univ (fun x => σ i x j k) (gσ i j k)) →
    (∀ i (R : ℝ), 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (gφ i) 2 (volume.restrict (ball 0 R)) ∧
      ∀ j k, MemLp (fun x => σ i x j k) 2 (volume.restrict (ball 0 R)) ∧
        MemLp (gσ i j k) 2 (volume.restrict (ball 0 R))) →
    (∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + gφ i x))
      (fun _ => 0)) →
    (∀ i j, HasWeakDivergence Set.univ (fun x k => σ i x j k)
      (fun x => ((a x).mulVec (unitVector i + gφ i x)) j - (D.mulVec (unitVector i)) j)) →
    (∀ i x j k, σ i x j k = -σ i x k j) →
    (∀ i (R : ℝ), R₀ ≤ R →
      scalarRms volume (ball 0 R) (fun x => φ i x - ⨍ y in ball 0 R, φ i y) +
        ∑ j, ∑ k, scalarRms volume (ball 0 R)
          (fun x => σ i x j k - ⨍ y in ball 0 R, σ i y j k) ≤ C₁ * R ^ (1 - μ)) →
    ∀ R : ℝ, R₁ ≤ R → ∀ (v : Vec d → ℝ) (gv : Vec d → Vec d),
      MemLp v 2 (volume.restrict (ellipsoid D R)) →
      MemLp gv 2 (volume.restrict (ellipsoid D R)) →
      HasWeakGradient (ellipsoid D R) v gv →
      HasWeakDivergence (ellipsoid D R) (fun x => (a x).mulVec (gv x)) (fun _ => 0) →
      ∃ (h : Vec d → ℝ) (gh : Vec d → Vec d),
        MemLp h 2 (volume.restrict (ellipsoid D ((1 - 3 * R ^ (-ν)) * R))) ∧
        HasWeakGradient (ellipsoid D ((1 - 3 * R ^ (-ν)) * R)) h gh ∧
        HasWeakDivergence (ellipsoid D ((1 - 3 * R ^ (-ν)) * R)) (fun x => D.mulVec (gh x))
          (fun _ => 0) ∧
        scalarRms volume (ellipsoid D ((1 - 3 * R ^ (-ν)) * R)) (fun x => v x - h x) ≤
          C * R ^ (-ν) * scalarRms volume (ellipsoid D R) v

end QSH
