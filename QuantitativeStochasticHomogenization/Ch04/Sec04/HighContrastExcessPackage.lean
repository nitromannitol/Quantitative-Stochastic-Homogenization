import QuantitativeStochasticHomogenization.Ch03.Sec04.HighContrastCorrectors

/-!
# Theorem C of Armstrong, Kuusi and Loher with the excess decay of one slope

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21. The zoom from the intermediate scale to the scale `r` uses the last clause of
Theorem C of Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high
contrast*, for the dilated law: above the homogenization scale `X`, every solution `u` on the
ellipsoid of radius `R` of the homogenized matrix has, for each `ϑ ∈ (0, 1)`, one slope `e` with
`‖∇u - (e + ∇φ_e)‖_{E_t} ≤ C_ϑ (t/R)^ϑ ‖∇u‖_{E_R}` for all `X ≤ t ≤ R` (coefficient-weighted
gradient norms). `HighContrastExcessPackage` extends `HighContrastCorrectorPackage` by this
clause together with the linearity of the corrector gradients in the slope, their stationarity
and the translation invariance of the event of full probability.
-/

open MeasureTheory

namespace QSH

open _root_.Homogenization hiding euclideanBall Vec Mat

open _root_.Homogenization.HighContrast

/-- The conclusions of Theorem C of Armstrong, Kuusi and Loher for the dilated law, with the
excess decay of one slope, the linearity and stationarity of the corrector gradients and the
translation invariance of the event of full probability. -/
structure HighContrastExcessPackage {d : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (P : Measure (CoefficientField d K)) (κ C : ℝ) (C₁ : ℝ → ℝ) extends
    HighContrastCorrectorPackage hK P κ C where
  linear : ∀ (c : ℝ) (e e' : Vec d) (b : CoeffSpace d),
    gradPhi (c • e + e') b =ᵐ[volume] fun x => c • gradPhi e b x + gradPhi e' b x
  stationary : ∀ (z : Fin d → ℤ) (e : Vec d) (b : CoeffSpace d),
    gradPhi e (translateCoeff z b) =ᵐ[volume] fun x => gradPhi e b (x + Source.AKL.intTranslation z)
  invariant : ∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend
  excess : ∀ b ∈ Ωend, ∀ R : ℝ, X b ≤ R →
    ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
      MemH1a (fun x => b.1 x) (ellipsoid abar R) u Du →
      IsWeakSolutionOn (fun x => b.1 x) (ellipsoid abar R) Du →
      ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc (X b) R →
          weightedGradNorm (fun x => b.1 x) (ellipsoid abar r)
              (fun x => Du x - (e + gradPhi e b x)) ≤
            ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
              weightedGradNorm (fun x => b.1 x) (ellipsoid abar R) Du

/-- Theorem C of Armstrong, Kuusi and Loher, with the excess decay of one slope, applies to the
dilated law of every law, with constants depending only on the dimension. -/
theorem exists_highContrastExcessPackage (d : ℕ) (hd : 2 ≤ d) :
    ∃ (κ C : ℝ) (C₁ : ℝ → ℝ), 0 < κ ∧ 0 < C ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      ∀ (K : ℝ) (hK : 1 ≤ K) (P : Measure (CoefficientField d K)), LawHypotheses P →
        Nonempty (HighContrastExcessPackage hK P κ C C₁) := by
  obtain ⟨κ, C, C₀, C₁, hκ, hC, -, hC₁, hmain⟩ := HCPoly.uniform_homogenization d hd
  refine ⟨κ, C, C₁, hκ, hC, hC₁, fun K hK P hP => ?_⟩
  have := isProbabilityMeasure_map_toHighContrast hK hP
  obtain ⟨abar, X, Phi, gradPhi, hXm, hX1, hlin, hstat, htail, hpos, Ωend, hΩm, hΩ, hinv, -,
      heq, hcorr, hliou, hreg⟩ :=
    hmain 1 K one_pos le_rfl hK (P.map (toHighContrast hK)) inferInstance
      (isStationaryLaw_map_toHighContrast hK hP) (isUnitRangeLaw_map_toHighContrast hK hP)
      (ae_isEllipticMatrix_map_toHighContrast hK)
  exact ⟨{
    abar := abar
    X := X
    Phi := Phi
    gradPhi := gradPhi
    Ωend := Ωend
    measurable_X := hXm
    one_le_X := hX1
    tail := htail
    posDef := hpos
    measurableSet_Ωend := hΩm
    full := hΩ
    equation := heq
    corrector := hcorr
    liouville := fun b hb ϑ hϑ => (hliou b hb ϑ hϑ).1
    liouville_mem := fun b hb ϑ hϑ => (hliou b hb ϑ hϑ).2
    lipschitz := fun b hb R hR u Du hu hsol => (hreg b hb R hR u Du hu hsol).1
    linear := hlin
    stationary := hstat
    invariant := hinv
    excess := fun b hb R hR u Du hu hsol => (hreg b hb R hR u Du hu hsol).2 }⟩

end QSH
