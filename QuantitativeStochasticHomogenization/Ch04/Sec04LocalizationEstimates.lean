import QuantitativeStochasticHomogenization.Ch04.Sec01EnergyQuantityJ1

/-!
# Section 4.4: Localization Estimates

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 4 (Quantitative Description of First-Order Correctors), Section 4.4. Numbered results of
this section: Lemmas 4.19–4.22.

Defined here: the localization of pp. 155-156 (the coordinate minimizers of the objective `I`
with the least-norm choice) and the localized energy `J₁^{(δ)}` of (4.103).
-/

open MeasureTheory

noncomputable section

namespace QSH

/-! ## The localization of Section 4.4 (pp. 155-156, (4.103)) -/

/-- The exponent `ε` following (4.85). -/
def localizationEpsilon (δ α γ : ℝ) : ℝ := min ((α * (1 + δ) + δ - γ) / (1 + α)) (δ / 2)

/-- The outer radius `T = r^{1+δ}`, p. 155. -/
def localizationOuterRadius (δ r : ℝ) : ℝ := r ^ (1 + δ)

/-- The intermediate radius `S = r^{1+δ-ε}`, p. 155. -/
def localizationIntermediateRadius (δ α γ r : ℝ) : ℝ := r ^ (1 + δ - localizationEpsilon δ α γ)

/-- `a`-harmonic functions in `H¹(B_T(z))`, the space `A(B_T(z))`. -/
structure LocalHarmonic {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T : ℝ) where
  potential : Vec d → ℝ
  grad : Vec d → Vec d
  square_integrable : MemLp potential 2 (volume.restrict (ball z T))
  gradient_square_integrable :
    MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict (ball z T))
  weak_gradient : HasWeakGradient (ball z T) potential grad
  harmonic : HasWeakDivergence (ball z T) (fun x => (a x).mulVec (grad x)) (fun _ => 0)

/-- The admissible class `K` of p. 155: normalized gradient `L²(B_T)` norm at most `C`. -/
def IsLocalizationAdmissible {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T : ℝ}
    (C : ℝ) (w : LocalHarmonic a z T) : Prop :=
  vectorRms volume (ball z T) w.grad ≤ C

/-- The objective `I` of p. 155. -/
def localizationObjective {d : ℕ} (z : Vec d) (T S σ θ : ℝ) (w : Vec d → ℝ) : ℝ :=
  ⨍ y in ball z (S / θ), (∫ x in ball z T, heatKernel y (σ * S) x * w x) ^ 2

/-- The coordinate minimization of p. 155 (`ℓ_{e_i}(x) = (x - z)_i`). -/
def IsCoordinateMinimizer {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T : ℝ}
    (S σ θ C : ℝ) (i : Fin d) (w : LocalHarmonic a z T) : Prop :=
  IsLocalizationAdmissible C w ∧
    ∀ v : LocalHarmonic a z T, IsLocalizationAdmissible C v →
      localizationObjective z T S σ θ (fun x => w.potential x - (x - z) i) ≤
        localizationObjective z T S σ θ (fun x => v.potential x - (x - z) i)

/-- The minimizer of smallest `L²(B_T)` norm, p. 156. -/
def IsLeastNormCoordinateMinimizer {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d}
    {T : ℝ} (S σ θ C : ℝ) (i : Fin d) (w : LocalHarmonic a z T) : Prop :=
  IsCoordinateMinimizer S σ θ C i w ∧
    ∀ v : LocalHarmonic a z T, IsCoordinateMinimizer S σ θ C i v →
      (∫ x in ball z T, w.potential x ^ 2) ≤ ∫ x in ball z T, v.potential x ^ 2

/-- The `d` selected coordinate minimizers spanning `V_r^δ`, p. 156. -/
structure LocalizedBasis {d : ℕ} {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d)
    (T S σ θ C : ℝ) where
  coordinate : Fin d → LocalHarmonic a z T
  selected : ∀ i, IsLeastNormCoordinateMinimizer S σ θ C i (coordinate i)

/-- The gradient of `∑ c_i w_i ∈ V_r^δ`. -/
def localizedGradient {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (c : Vec d) (x : Vec d) : Vec d :=
  ∑ i, c i • (W.coordinate i).grad x

/-- **The localized energy `J₁^{(δ)}(z, r, p, q)`**, (4.103). -/
def localizedJ1 {d : ℕ} {Λ : ℝ} {a : CoefficientField d Λ} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q : Vec d) : ℝ :=
  sSup {e : ℝ | ∃ c : Vec d,
    e = ∫ x in ball z T, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (localizedGradient W c x) ((a x).mulVec (localizedGradient W c x)) -
        dot p ((a x).mulVec (localizedGradient W c x)) + dot q (localizedGradient W c x))}

end QSH
