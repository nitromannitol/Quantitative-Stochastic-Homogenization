import QuantitativeStochasticHomogenization.Ch10.Sec02.Quantities
import Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix

/-!
# The quantities of Section 10.2 are those of the coarse-graining library

On a bounded open convex domain `D` (a `Homogenization.Book.Ch02.Domain`), the space `S(D)` of
(10.19), `μ(D, p, q)` of (10.15) and `J(D, X, X*)` of (10.20) for a field `a` of `Ω` are the
doubled response space, the doubled `μ` and the doubled response functional of the
coarse-graining library (Armstrong and Kuusi) for `a.toCGCoeffOn D`. The pointwise identity is
`blockVecDot_blockMatrixField`; the integrals agree because both sides average over `D` with
Lebesgue measure.
-/

open MeasureTheory

namespace QSH

variable {d : ℕ} {Λ : ℝ}

theorem cgAverage_eq_setAverage (D : _root_.Homogenization.Book.Ch02.Domain d)
    (f : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch02.average D f = ⨍ x in (D : Set (Vec d)), f x := by
  unfold _root_.Homogenization.Book.Ch02.average
  rw [setAverage_eq, smul_eq_mul]
  rfl

namespace GeneralCoefficientField

variable (a : GeneralCoefficientField d Λ) (D : _root_.Homogenization.Book.Ch02.Domain d)

theorem doubledBlockPairingIntegrand_eq (Y X : _root_.Homogenization.Book.Ch02.DoubledField d)
    (x : Vec d) :
    _root_.Homogenization.Book.Ch02.doubledBlockPairingIntegrand D (a.toCGCoeffOn D) Y X x =
      representativePairing (a x) (Y.potential x) (Y.flux x) (X.potential x) (X.flux x) :=
  blockVecDot_blockMatrixField a x _ _ _ _

theorem blockEnergyDensityAt_eq (p q x : Vec d) :
    _root_.Homogenization.Book.Ch02.blockEnergyDensityAt (a.toCGCoeffOn D) (p, q) x =
      linearRepresentative (a x) p q := by
  unfold _root_.Homogenization.Book.Ch02.blockEnergyDensityAt
  rw [blockVecDot_blockMatrixField a x, linearRepresentative_eq_half_representativePairing]

/-- **`S(D)` is the doubled response space of the library.** -/
theorem isResponseField_iff (S₁ S₂ : Vec d → Vec d) :
    a.IsResponseField D S₁ S₂ ↔
      _root_.Homogenization.Book.Ch02.IsDoubledResponseField D (a.toCGCoeffOn D) ⟨S₁, S₂⟩ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun Y hY => ?_⟩
    have := h3 Y.potential Y.flux hY.1 hY.2
    simpa only [a.doubledBlockPairingIntegrand_eq D] using this
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun T₁ T₂ hT₁ hT₂ => ?_⟩
    have := h3 ⟨T₁, T₂⟩ ⟨hT₁, hT₂⟩
    simpa only [a.doubledBlockPairingIntegrand_eq D] using this

/-- **`μ(D, p, q)` is the doubled `μ` of the library.** -/
theorem doubleMu_eq (p q : Vec d) :
    a.doubleMu D p q = _root_.Homogenization.Book.Ch02.doubledMu D (a.toCGCoeffOn D) (p, q) := by
  unfold doubleMu _root_.Homogenization.Book.Ch02.doubledMu
  congr 1
  ext E
  constructor
  · rintro ⟨V, h, hV, hh, rfl⟩
    refine ⟨⟨V, h⟩, ⟨hV, hh⟩, ?_⟩
    simp only [_root_.Homogenization.Book.Ch02.doubledMuValue, cgAverage_eq_setAverage,
      _root_.Homogenization.Book.Ch02.DoubledField.eval, a.blockEnergyDensityAt_eq D]
  · rintro ⟨X, ⟨hV, hh⟩, rfl⟩
    refine ⟨X.potential, X.flux, hV, hh, ?_⟩
    simp only [_root_.Homogenization.Book.Ch02.doubledMuValue, cgAverage_eq_setAverage,
      _root_.Homogenization.Book.Ch02.DoubledField.eval, a.blockEnergyDensityAt_eq D]

theorem responseValue_eq (p q qs ps : Vec d) (S₁ S₂ : Vec d → Vec d) :
    a.responseValue D p q qs ps S₁ S₂ =
      _root_.Homogenization.Book.Ch02.doubledResponseValue D (a.toCGCoeffOn D) (p, q) (qs, ps)
        ⟨S₁, S₂⟩ := by
  unfold responseValue _root_.Homogenization.Book.Ch02.doubledResponseValue
  rw [cgAverage_eq_setAverage]
  congr 1
  funext x
  simp only [_root_.Homogenization.Book.Ch02.doubledResponseIntegrand,
    _root_.Homogenization.Book.Ch02.DoubledField.eval, a.blockEnergyDensityAt_eq D,
    blockVecDot_blockMatrixField a x, linearRepresentative_eq_half_representativePairing]
  simp only [_root_.Homogenization.blockVecDot]
  change _ = _ - _ + (dot qs (S₁ x) + dot ps (S₂ x))
  ring

/-- **`J(D, X, X*)` is the doubled response functional of the library.** -/
theorem doubleJ_eq (p q qs ps : Vec d) :
    a.doubleJ D p q qs ps =
      _root_.Homogenization.Book.Ch02.doubledResponseJ D (a.toCGCoeffOn D) (p, q) (qs, ps) := by
  unfold doubleJ _root_.Homogenization.Book.Ch02.doubledResponseJ
  congr 1
  ext E
  constructor
  · rintro ⟨S₁, S₂, hS, rfl⟩
    exact ⟨⟨S₁, S₂⟩, (a.isResponseField_iff D S₁ S₂).1 hS, a.responseValue_eq D _ _ _ _ _ _⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X.potential, X.flux, (a.isResponseField_iff D _ _).2 hX,
      (a.responseValue_eq D _ _ _ _ _ _).symm⟩

theorem isResponseMaximizer_iff (p q qs ps : Vec d) (S₁ S₂ : Vec d → Vec d) :
    a.IsResponseMaximizer D p q qs ps S₁ S₂ ↔
      _root_.Homogenization.Book.Ch02.IsDoubledResponseMaximizer D (a.toCGCoeffOn D) (p, q)
        (qs, ps) ⟨S₁, S₂⟩ := by
  constructor
  · rintro ⟨hS, hmax⟩
    refine ⟨(a.isResponseField_iff D S₁ S₂).1 hS, fun Y hY => ?_⟩
    have := hmax Y.potential Y.flux ((a.isResponseField_iff D _ _).2 hY)
    rwa [a.responseValue_eq, a.responseValue_eq] at this
  · rintro ⟨hS, hmax⟩
    refine ⟨(a.isResponseField_iff D S₁ S₂).2 hS, fun T₁ T₂ hT => ?_⟩
    have := hmax ⟨T₁, T₂⟩ ((a.isResponseField_iff D _ _).1 hT)
    rwa [← a.responseValue_eq, ← a.responseValue_eq] at this

end GeneralCoefficientField

end QSH
