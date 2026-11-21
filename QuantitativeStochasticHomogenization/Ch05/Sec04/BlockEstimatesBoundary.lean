import QuantitativeStochasticHomogenization.Ch05.Sec04.BlockEstimates
import QuantitativeStochasticHomogenization.Ch05.Sec04.Lemma529Boundary
import QuantitativeStochasticHomogenization.Frozen.BlockBoundary

/-!
# Lemma 5.29 (ii) for the localized energy

Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 5.29 (ii), (5.91)-(5.92), for the localized energy of Section 4.4:
`QSH.Frozen.blockBoundary` from the two properties `LocalizedFieldInput` and
`LocalizedAdditivityInput` (`blockBoundary_of_inputs`), by Lemma 5.29 (ii) for centered local
additive fields (`exists_blockBound_layer`).
-/

open MeasureTheory ProbabilityTheory

namespace QSH

/-- **Lemma 5.29 (ii)** for the localized energy (`QSH.Frozen.blockBoundary`). -/
theorem blockBoundary_of_inputs (hloc : LocalizedFieldInput) (hadd : LocalizedAdditivityInput) :
    QSH.Frozen.blockBoundary := by
  intro d hd Λ s δ γ η hΛ hw β hβ0 hβ1 α σ θ C₀ C' hc
  obtain ⟨M, A, hM, hA, hX⟩ := exists_centeredLocalFields_familyJ1 hloc hadd hd hΛ hw hc
  obtain ⟨η₂, hηη₂, hη₂⟩ := hw.exists_eta₂
  obtain ⟨hs1, hs2, hδ, hγ1, -, hη1, hηγ, -⟩ := hw
  have hd1 : 1 ≤ d := by omega
  have hη0 : 0 < η := by linarith
  obtain ⟨Cl, hCl, hlay⟩ := exists_blockBound_layer (Ω := CoefficientField d Λ)
    (F := localSigma) (δ := δ) (α := γ) (B := 2 * M) (A := A) hd1 localSigma_mono hs1 hs2.le
    (by positivity) hA hδ hη0 hηη₂ hη₂ hηγ
  refine ⟨(8 : ℝ) ^ s⁻¹ * (4 * Cl), by positivity,
    fun P hP W hW R r hR hr2 hr1 hrR z p q hp hq f hf hf1 hfs => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨X, hXeq⟩ := hX P hP W hW p q hp hq
  have hf' : Measurable ((cube z R).indicator f) := hf.indicator (measurableSet_cube z R)
  have hf1' : ∀ x, |(cube z R).indicator f x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ cube z R
    · rw [Set.indicator_of_mem hx]; exact hf1 x
    · rw [Set.indicator_of_notMem hx, abs_zero]; exact zero_le_one
  have hfs' : ∀ x, (cube z R).indicator f x ≠ 0 → x ∈ cube z R \ cube z (R - R ^ β) := by
    intro x hx
    have hfx : f x ≠ 0 := by
      intro h
      apply hx
      by_cases hc : x ∈ cube z R
      · rw [Set.indicator_of_mem hc, h]
      · rw [Set.indicator_of_notMem hc]
    exact hfs hfx
  have h := (hlay P (hasUnitRange_of_lawHypotheses hP) X R hR β hβ0 hβ1 r hr1 hrR z _ hf' hf1'
    hfs').osBound_abs
  have e : (fun a => |centeredBlock P (familyJ1 W) a z R r f p q|) = fun a =>
      |R ^ (-(d : ℝ)) * ∫ x, (cube z R).indicator f x * X.field r a x| := by
    funext a
    rw [centeredBlock_eq_integral_indicator]
    congr 3
    funext x
    rw [hXeq r (by linarith) a x]
  rw [e]
  exact h.mono_scale (le_of_eq (by ring))

end QSH
